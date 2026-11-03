module

public import Feec.Models.Cube.PolyFiniteElementConvergence
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Rates of convergence of the higher-order finite element methods on the cube

For an admissible sequence `S` reproducing polynomial forms of degree `s` in every form degree
(`FEM.PolyOrder n S s`: `P_sΛᵏ ⊆ P(T)ᵏ`; every sequence has order `0`, `polyOrder_zero`), the
canonical interpolant of `S` on the Freudenthal meshes of `Q = (0, ½)ⁿ` is of order `h^{s+1}` for
`C^{s+2}` forms (`FEM.exists_mem_poly_le`), and the rate passes to the finite element methods:

* `FEM.IsCsForm s j L x` (resp. `FEM.IsCsFormMin`, vanishing outside `Q`): `x` is a `C^{s+2}`
  `j`-form whose `(s+1)`-st derivatives and those of `dx` are bounded by `L` on `cl Q`
  (satisfiable: `exists_isCsFormMin`).
* **Degreewise**: `‖x - v‖, ‖d(x - v)‖ ≤ B_j L h_N^{s+1}` for some `v ∈ Vₕʲ`
  (`IsCsForm.exists_mem_poly_le`, `IsCsFormMin.exists_mem_polyMin_le`), and the graph-norm
  distances (`IsCsForm.infDist_domainSub_poly_le`).
* **Mixed Hodge–Laplace problem** ([AFW2010], Thm 3.9; [Arnold2018], Ch. 7): error
  `≤ K L h_N^{s+1}` for solutions with `IsCsForm s` components (`mixed_rate_poly`,
  `mixed_rate_polyMin`, unconditionally). Only the degrees used matter (`FEM.PolyOrderAt n S s j`: `P_s` in degrees `j` and
  `j + 1`; `mixed_rate_poly_of_polyOrderAt`, `mixed_rate_polyMin_of_polyOrderAt`): the bottom row
  `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` of Tables 5.1/6.1 has global order `h` only (because of `P₀Λ³`),
  but converges at order `h²` for the Hodge Laplacian on `1`-forms (`mixed_rate_lagrangeP2`,
  `mixed_rate_lagrangeP2Min`) and for the Hodge wave equation on the window of degrees `0, 1`
  (`norm_sub_le_windowMin_lagrangeP2`).
* **Semi-discrete Hodge wave equation** ([QuennevilleBelair2015], Thm 4.14) on every window:
  `‖ξ(t) - ξₕ(t)‖ ≤ A (1 + (t - t₀))² (m + m²) (Σᵢ B_{a+i}) L h_N^{s+1}`
  (`norm_sub_le_window_poly_smooth`; no smoothed projection is needed).
* The rates in `H̊Λ(Q)` above are stated for the flat class `IsCsFormMin`; their versions for the
  natural class `FEM.IsCsFormTr` (`C^{s+2}` up to `∂Q` with vanishing tangential traces, no
  condition on the normal components) are `mixed_rate_polyTr`, `mixed_rate_lagrangeP2Tr`,
  `norm_sub_le_windowTr_poly_smooth`, `norm_sub_le_windowTr_lagrangeP2` in
  `Feec.Models.Cube.TangentialRate`.
* **`H¹` approximation of the smoothed projections** ([AFW2010], §5.5; needed by the BGG
  discretization): for `y ∈ L²(Q; Λᵏ)` whose coefficients `yₛ` (as `0`-forms, `coeffForm`) lie in
  the domain of the maximal gradient (`H¹(Q)`), resp. of the minimal gradient (`H¹₀(Q)`: the
  extension by zero is in `H¹(ℝⁿ)`), `‖y - π_N y‖ ≤ (1 + 2C) K_k h_N Σₛ ‖∇ yₛ‖` with `K_k`
  independent of `N` (`PolySmoothingEstimates.norm_sub_proj_le_grad`,
  `PolySmoothingEstimatesMin.norm_sub_proj_le_grad`; both rows of Tables 5.1/6.1 with one smoother: `tableRows_H1`). The approximant is
  `c⁻ᵏ Q_N y`: **mollification at scale `h_N`**, `‖f - R f‖ ≤ γ h_N √(n 2ⁿ) ‖∇f‖`
  (`norm_sub_smoothL2_le_pMax`, `norm_sub_smoothL2_le_pMin`: for smooth `f` by the fundamental
  theorem of calculus along segments, Jensen's inequality, Tonelli and the change of variables
  of the dilations, `lintegral_sq_sub_molli_dil_le`; for `H¹` by density); the **commutation of
  the smoother with the gradient** (`partialDeriv_smoothExt_eq_of_maximal`, `_of_minimal`); and
  the **local interpolation error of the smoothed field** `‖R y - Π_h R y‖ ≲ h_N ‖∇y‖`
  (`Poly.sq_norm_formL2_sub_smoothedInterp_le`: `h_N sup_T ‖D(R y)‖` on each simplex, Jensen for
  the smoothed gradient, bounded overlap).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  Thm 3.9 (quasi-optimality of the mixed method), §5.5 (smoothed projections)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (approximation
  estimates, rates for smooth solutions)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.14 (convergence of the semi-discrete Hodge wave equation)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff ENNReal

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex Feec.ExteriorFibre

variable {n : ℕ}

/-! ### The approximation order of an admissible sequence -/

variable (n) in
/-- The sequence `S` **reproduces polynomial forms of degree `s`** in every form degree:
`P_sΛᵏ ⊆ P(T)ᵏ` for all `k`, so that its canonical interpolant is of order `h^{s+1}`. -/
def PolyOrder (S : PolySeq) (s : ℕ) : Prop := ∀ k, polySpace n s k ≤ S.space n k

/-- Every admissible sequence has order `h` (`s = 0`). -/
theorem polyOrder_zero (S : PolySeq) : PolyOrder n S 0 := fun k => polySpace_zero_le_space S k

variable (n) in
/-- **Degreewise order**: `S` reproduces polynomial forms of degree `s` in the form degrees `j`
and `j + 1` (vacuous for `j < 0`), which is all the interpolation error in the graph norm of
degree `j` uses. -/
def PolyOrderAt (S : PolySeq) (s : ℕ) (j : ℤ) : Prop :=
  ∀ k : ℕ, (k : ℤ) = j → polySpace n s k ≤ S.space n k ∧ polySpace n s (k + 1) ≤ S.space n (k + 1)

/-- An order in every degree is an order in each degree. -/
theorem PolyOrder.polyOrderAt {S : PolySeq} {s : ℕ} (h : PolyOrder n S s) (j : ℤ) :
    PolyOrderAt n S s j := fun k _ => ⟨h k, h (k + 1)⟩

/-- The bottom row `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` reproduces `P₁` in the form degrees `0, 1`. -/
theorem lagrangeP2_polyOrderAt_zero : PolyOrderAt n PolySeq.lagrangeP2 1 0 := by
  intro k hk
  obtain rfl : k = 0 := by exact_mod_cast hk
  exact ⟨Poly.polySpace_le_space_of_full _ (by simp) (by simp), Poly.polySpace_le_space _ (by simp)⟩

/-- The bottom row `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` reproduces `P₁` in the form degrees `1, 2`. -/
theorem lagrangeP2_polyOrderAt_one : PolyOrderAt n PolySeq.lagrangeP2 1 1 := by
  intro k hk
  obtain rfl : k = 1 := by exact_mod_cast hk
  exact ⟨Poly.polySpace_le_space _ (by simp), Poly.polySpace_le_space_of_full _ (by simp) (by simp)⟩

/-- The bottom row reproduces `P₁` on the window `0, 1` (form degrees `0, 1, 2`). -/
theorem lagrangeP2_polyOrderAt_window : ∀ i : Fin 2, PolyOrderAt n PolySeq.lagrangeP2 1 (0 + i) :=
  fun i => by
    fin_cases i
    · simpa using lagrangeP2_polyOrderAt_zero (n := n)
    · simpa using lagrangeP2_polyOrderAt_one (n := n)

/-! ### Smooth forms of order `s` -/

/-- `x ∈ L²(Q; Λʲ)` is a `C^{s+2}` form of degree `j` whose `(s+1)`-st derivative and that of
its exterior derivative are bounded by `L` on `cl Q` (trivially true in negative degrees). For
`s = 0` this is the `C²` class of `FEM.IsC2Form` (with `‖D^1 w‖ = ‖Dw‖`). -/
def IsCsForm (s : ℕ) (j : ℤ) (L : ℝ) (x : L2F ℝ (cubeDomain n) (formIdx n j)) : Prop :=
  j < 0 ∨ ∃ k : ℕ, (k : ℤ) = j ∧ ∃ w : FormField n,
    ∃ hw : ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w, (∀ y, IsDeg k (w y)) ∧
    (∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L) ∧
    (∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L) ∧
    x = formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) j ⟨w, hw.continuous⟩

/-- `x ∈ L²(Q; Λʲ)` is a `C^{s+2}` form of degree `j` **vanishing outside `Q`**, with the bounds of
`IsCsForm`. Since the representative is `C^{s+2}` on `ℝⁿ`, this is flatness of order `s + 2` at
`∂Q`, stronger than vanishing tangential traces (e.g. `∏ᵢ sin (2π xᵢ)` on `(0, ½)ⁿ` is excluded);
the rates with vanishing traces below are stated for this class. The general case of `H̊Λ(Q)` is
covered, without a rate, by the quasi-optimality of the static FEEC theorem for `polyFamilyMin`
(`Feec.HilbertComplex.ConformingFamily.StaticVerdict.quasiOptimal`). The class with
vanishing tangential traces only, `FEM.IsCsFormTr` of `Feec.Models.Cube.TangentialRate`, contains
this one with the same bound (`IsCsFormMin.isCsFormTr`) and carries the same rates. -/
def IsCsFormMin (s : ℕ) (j : ℤ) (L : ℝ) (x : L2F ℝ (cubeDomain n) (formIdx n j)) : Prop :=
  j < 0 ∨ ∃ k : ℕ, (k : ℤ) = j ∧ ∃ w : FormField n,
    ∃ hw : ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w, (∀ y, IsDeg k (w y)) ∧
    (∀ y ∉ cubeDomain n, w y = 0) ∧
    (∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L) ∧
    (∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L) ∧
    x = formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) j ⟨w, hw.continuous⟩

/-- **Every `C^{s+2}` form vanishing outside `Q` is `IsCsFormMin s`** for some bound. -/
theorem exists_isCsFormMin (s : ℕ) {k : ℕ} {w : FormField n}
    (hw : ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w) (hdeg : ∀ y, IsDeg k (w y))
    (hsupp : ∀ y ∉ cubeDomain n, w y = 0) :
    ∃ L, 0 ≤ L ∧ IsCsFormMin s (k : ℤ) L
      (formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
        ⟨w, hw.continuous⟩) := by
  obtain ⟨L, hL0, hL⟩ := exists_bound_iteratedFDeriv (m := s + 1)
    (hw.of_le (by exact_mod_cast Nat.le_succ (s + 1)))
  have hw' : ContDiff ℝ (((s + 1 : ℕ) : WithTop ℕ∞) + 1) w := by exact_mod_cast hw
  have hdw : ContDiff ℝ ((s + 1 : ℕ) : WithTop ℕ∞) (extDeriv w) := contDiff_extDeriv hw'
  obtain ⟨L', hL'0, hL'⟩ := exists_bound_iteratedFDeriv (m := s + 1) hdw
  exact ⟨max L L', le_max_of_le_left hL0, Or.inr ⟨k, rfl, w, hw, hdeg, hsupp,
    fun y hy => (hL y hy).trans (le_max_left _ _),
    fun y hy => (hL' y hy).trans (le_max_right _ _), rfl⟩⟩

theorem IsCsForm.mono {s : ℕ} {j : ℤ} {L L' : ℝ} {x : L2F ℝ (cubeDomain n) (formIdx n j)}
    (hx : IsCsForm s j L x) (hLL' : L ≤ L') : IsCsForm s j L' x := by
  rcases hx with hj | ⟨k, hk, w, hw, hdeg, hL, hL', he⟩
  · exact Or.inl hj
  · exact Or.inr ⟨k, hk, w, hw, hdeg, fun y hy => (hL y hy).trans hLL',
      fun y hy => (hL' y hy).trans hLL', he⟩

theorem IsCsFormMin.isCsForm {s : ℕ} {j : ℤ} {L : ℝ} {x : L2F ℝ (cubeDomain n) (formIdx n j)}
    (hx : IsCsFormMin s j L x) : IsCsForm s j L x := by
  rcases hx with hj | ⟨k, hk, w, hw, hdeg, -, hL, hL', he⟩
  · exact Or.inl hj
  · exact Or.inr ⟨k, hk, w, hw, hdeg, hL, hL', he⟩

variable (n) in
/-- The constant `B_j = A_j + A_{j+1}` of the graph-norm interpolation error of `S` in degree
`j`. -/
def polyInterpBound (S : PolySeq) (j : ℤ) : ℝ :=
  polyInterpConst n S j.toNat + polyInterpConst n S (j.toNat + 1)

theorem polyInterpBound_nonneg (S : PolySeq) (j : ℤ) : 0 ≤ polyInterpBound n S j :=
  add_nonneg (polyInterpConst_nonneg _ _) (polyInterpConst_nonneg _ _)

variable [NeZero n]

/-! ### Degreewise rates -/

/-- **Degreewise interpolation error of order `s + 1`**: for `x` with `IsCsForm s j L x` and a
sequence of order `s`, some `v ∈ Vₕʲ` has `‖x - v‖ ≤ B_j L h_N^{s+1}` and
`‖d (x - v)‖ ≤ B_j L h_N^{s+1}`. -/
theorem IsCsForm.exists_mem_poly_le {S : PolySeq} {s : ℕ} {j : ℤ}
    (hS : PolyOrderAt n S s j)
    {L : ℝ} {x : L2F ℝ (cubeDomain n) (formIdx n j)} (hx : IsCsForm s j L x) (hL0 : 0 ≤ L)
    (N : ℕ) :
    ∃ v, ∃ hv : v ∈ (poly n S N).V j, ‖x - v‖ ≤ polyInterpBound n S j * L * meshSize N ^ (s + 1) ∧
      ∀ j' (hxj : x ∈ ((complex n).d j j').domain),
        ‖(complex n).d j j' ⟨x - v, Submodule.sub_mem _ hxj ((poly n S N).le_domain j j' hv)⟩‖ ≤
          polyInterpBound n S j * L * meshSize N ^ (s + 1) := by
  have hh := pow_nonneg (meshSize_pos N).le (s + 1)
  have hB0 := mul_nonneg (mul_nonneg (polyInterpBound_nonneg (n := n) S j) hL0) hh
  rcases hx with hj | ⟨k, rfl, w, hw, hdeg, hL, hL', rfl⟩
  · have := LocalElement.subsingleton_L2F_of_neg (cubeDomain n) (n := n) hj
    exact (poly n S N).exists_mem_le_of_subsingleton hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ :=
    FEM.exists_mem_poly_le S N k s (hS k rfl).1 (hS k rfl).2 hw hdeg hL hL'
  obtain ⟨hdom, hval⟩ := formL2_mem_domain k
    (hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1))) hdeg
  have hA0 := mul_nonneg (polyInterpConst_nonneg (n := n) S k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (polyInterpConst_nonneg (n := n) S (k + 1)) (mul_nonneg hh hL0)
  have e : polyInterpBound n S k * L * meshSize N ^ (s + 1) =
      polyInterpConst n S k * (meshSize N ^ (s + 1) * L) +
        polyInterpConst n S (k + 1) * (meshSize N ^ (s + 1) * L) := by
    simp only [polyInterpBound, Int.toNat_natCast]; ring
  refine HilbertComplex.Subcomplex.exists_mem_le_of_succ _ hv hB0 (by rw [e]; linarith)
    fun hxj => ?_
  rw [hval, e]
  linarith

/-- **Graph-norm distance of a smooth form to the higher-order space**:
`dist_V(σ, Vₕʲ) ≤ 2 B_j L h_N^{s+1}`. -/
theorem IsCsForm.infDist_domainSub_poly_le {S : PolySeq} {s : ℕ} {j : ℤ}
    (hS : PolyOrderAt n S s j)
    {L : ℝ} {σ : (complex n).domainSpace j} (hσ : IsCsForm s j L ((complex n).domainIncl j σ))
    (hL0 : 0 ≤ L) (N : ℕ) :
    Metric.infDist σ ((poly n S N).domainSub j) ≤
      2 * (polyInterpBound n S j * L * meshSize N ^ (s + 1)) := by
  obtain ⟨v, hv, h1, h2⟩ := hσ.exists_mem_poly_le hS hL0 N
  exact Subcomplex.infDist_domainSub_le_two_mul _ rfl σ hv h1 (h2 _)

/-- **Degreewise interpolation error of order `s + 1` with vanishing boundary DOFs** in `H̊Λ(Q)`. -/
theorem IsCsFormMin.exists_mem_polyMin_le {S : PolySeq} {s : ℕ} {j : ℤ}
    (hS : PolyOrderAt n S s j)
    {L : ℝ} {x : L2F ℝ (cubeDomain n) (formIdx n j)} (hx : IsCsFormMin s j L x) (hL0 : 0 ≤ L)
    (N : ℕ) :
    ∃ v, ∃ hv : v ∈ (polyMin n S N).V j,
      ‖x - v‖ ≤ polyInterpBound n S j * L * meshSize N ^ (s + 1) ∧
      ∀ j' (hxj : x ∈ ((complexMin n).d j j').domain),
        ‖(complexMin n).d j j'
            ⟨x - v, Submodule.sub_mem _ hxj ((polyMin n S N).le_domain j j' hv)⟩‖ ≤
          polyInterpBound n S j * L * meshSize N ^ (s + 1) := by
  have hh := pow_nonneg (meshSize_pos N).le (s + 1)
  have hB0 := mul_nonneg (mul_nonneg (polyInterpBound_nonneg (n := n) S j) hL0) hh
  rcases hx with hj | ⟨k, rfl, w, hw, hdeg, hsupp, hL, hL', rfl⟩
  · have := LocalElement.subsingleton_L2F_of_neg (cubeDomain n) (n := n) hj
    exact (polyMin n S N).exists_mem_le_of_subsingleton hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ :=
    FEM.exists_mem_polyMin_le S N k s (hS k rfl).1 (hS k rfl).2 hw hdeg hsupp hL hL'
  have hA0 := mul_nonneg (polyInterpConst_nonneg (n := n) S k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (polyInterpConst_nonneg (n := n) S (k + 1)) (mul_nonneg hh hL0)
  have e : polyInterpBound n S k * L * meshSize N ^ (s + 1) =
      polyInterpConst n S k * (meshSize N ^ (s + 1) * L) +
        polyInterpConst n S (k + 1) * (meshSize N ^ (s + 1) * L) := by
    simp only [polyInterpBound, Int.toNat_natCast]; ring
  refine HilbertComplex.Subcomplex.exists_mem_le_of_succ _ hv hB0 (by rw [e]; linarith)
    fun hxj => ?_
  rw [complexMin_d_formL2 k (hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1))) hdeg
    ⟨_, hxj⟩ rfl, e]
  linarith

/-- **Graph-norm distance of a smooth form vanishing outside `Q` to `V̊ₕʲ`**:
`dist_V(σ, V̊ₕʲ) ≤ 2 B_j L h_N^{s+1}`. -/
theorem IsCsFormMin.infDist_domainSub_polyMin_le {S : PolySeq} {s : ℕ} {j : ℤ}
    (hS : PolyOrderAt n S s j) {L : ℝ} {σ : (complexMin n).domainSpace j}
    (hσ : IsCsFormMin s j L ((complexMin n).domainIncl j σ)) (hL0 : 0 ≤ L) (N : ℕ) :
    Metric.infDist σ ((polyMin n S N).domainSub j) ≤
      2 * (polyInterpBound n S j * L * meshSize N ^ (s + 1)) := by
  obtain ⟨v, hv, h1, h2⟩ := hσ.exists_mem_polyMin_le hS hL0 N
  exact Subcomplex.infDist_domainSub_le_two_mul _ rfl σ hv h1 (h2 _)

/-! ### Rates for the mixed Hodge Laplacian -/

variable (n) in
/-- **The Jackson estimate of the complexes of `S`**: for `s : ℕ`, the `C^{s+2}` forms
(`IsCsForm s`) of the degrees where `S` reproduces `P_s` (`PolyOrderAt`) are approximated at the
order `h_N^{s+1}` with the constants `polyInterpBound` (`IsCsForm.exists_mem_poly_le`). -/
def polyJackson (S : PolySeq) : (polyFamily n S).Jackson ℕ where
  meshSize := meshSize
  meshSize_nonneg N := (meshSize_pos N).le
  tendsto_meshSize := tendsto_meshSize
  Reg s j L x := PolyOrderAt n S s j ∧ IsCsForm s j L x
  ord s := ((s + 1 : ℕ) : ℝ)
  B _ := polyInterpBound n S
  B_nonneg _ := polyInterpBound_nonneg S
  jackson s N _ _ _ hL hx := by
    rw [Real.rpow_natCast, ← mul_assoc]; exact hx.2.exists_mem_poly_le hx.1 hL N

variable (n) in
/-- **The Jackson estimate of the complexes of `S` with vanishing boundary DOFs**: the forms of
class `IsCsFormMin s` at the order `h_N^{s+1}` (`IsCsFormMin.exists_mem_polyMin_le`). -/
def polyJacksonMin (S : PolySeq) : (polyFamilyMin n S).Jackson ℕ where
  meshSize := meshSize
  meshSize_nonneg N := (meshSize_pos N).le
  tendsto_meshSize := tendsto_meshSize
  Reg s j L x := PolyOrderAt n S s j ∧ IsCsFormMin s j L x
  ord s := ((s + 1 : ℕ) : ℝ)
  B _ := polyInterpBound n S
  B_nonneg _ := polyInterpBound_nonneg S
  jackson s N _ _ _ hL hx := by
    rw [Real.rpow_natCast, ← mul_assoc]; exact hx.2.exists_mem_polyMin_le hx.1 hL N

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method on the cube**, with no
hypothesis beyond the data ([AFW2010], Thm 3.9; [Arnold2018], Ch. 7): for an admissible sequence
of order `s` (`PolyOrder`, e.g. `s + 1 ≤ r_k` in every degree) and a solution `(σ, u, q)` of the
mixed problem whose components, the boundary part of `u` and `q` are `C^{s+2}` with
`(s+1)`-st derivatives bounded by `L`, the error of the discrete mixed solution on the
level-`(N + 1)` mesh is `≤ K L h_N^{s+1}`, with `K` independent of `N` and of the solution. -/
theorem mixed_rate_poly_of_polyOrderAt (S : PolySeq) {s : ℕ} {i j k : ℤ}
    (hSi : PolyOrderAt n S s i) (hSj : PolyOrderAt n S s j) (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j},
    (complex n).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    IsCsForm s i L ((complex n).domainIncl i σ) →
    IsCsForm s j L ((complex n).domainIncl j u) →
    IsCsForm s j L ((complex n).domainIncl j
      ((complex n).boundaryPart j ((complex n).domainIncl j u))) →
    IsCsForm s j L (q : L2F ℝ (cubeDomain n) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (poly n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).fst‖ +
        ‖u - (poly n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (poly n S N) hij hjk f).snd.snd :
            (poly n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * L * meshSize N ^ (s + 1) := by
  obtain ⟨K, hK⟩ := ((polyFamily n S).staticFEEC closedRangeAt j).rate (polyJackson n S) s hij hjk
  refine ⟨K, fun hs _ hL hσ hu hb hq N => ?_⟩
  have h := hK hs hL ⟨hSi, hσ⟩ ⟨hSj, hu⟩ ⟨hSj, hb⟩ ⟨hSj, hq⟩ N
  simp only [polyFamily_V] at h
  rw [← Real.rpow_natCast]
  exact h

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method on the cube** for a
sequence of order `s` in every degree (`PolyOrder`); see `mixed_rate_poly_of_polyOrderAt` for
the degreewise form. -/
theorem mixed_rate_poly (S : PolySeq) {s : ℕ} (hS : PolyOrder n S s) {i j k : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j},
    (complex n).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    IsCsForm s i L ((complex n).domainIncl i σ) →
    IsCsForm s j L ((complex n).domainIncl j u) →
    IsCsForm s j L ((complex n).domainIncl j
      ((complex n).boundaryPart j ((complex n).domainIncl j u))) →
    IsCsForm s j L (q : L2F ℝ (cubeDomain n) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (poly n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).fst‖ +
        ‖u - (poly n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (poly n S N) hij hjk f).snd.snd :
            (poly n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * L * meshSize N ^ (s + 1) :=
  mixed_rate_poly_of_polyOrderAt S (hS.polyOrderAt i) (hS.polyOrderAt j) hij hjk

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method with vanishing traces on
the cube**, with no hypothesis beyond the regularity of the solution (components `IsCsFormMin`,
i.e. `C^{s+2}` and vanishing outside `Q`). -/
theorem mixed_rate_polyMin_of_polyOrderAt (S : PolySeq) {s : ℕ} {i j k : ℤ}
    (hSi : PolyOrderAt n S s i) (hSj : PolyOrderAt n S s j) (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j},
    (complexMin n).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    IsCsFormMin s i L ((complexMin n).domainIncl i σ) →
    IsCsFormMin s j L ((complexMin n).domainIncl j u) →
    IsCsFormMin s j L ((complexMin n).domainIncl j
      ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))) →
    IsCsFormMin s j L (q : L2F ℝ (cubeDomain n) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (polyMin n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).fst‖ +
        ‖u - (polyMin n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (polyMin n S N) hij hjk f).snd.snd :
            (polyMin n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * L * meshSize N ^ (s + 1) := by
  obtain ⟨K, hK⟩ := ((polyFamilyMin n S).staticFEEC closedRangeAt_min j).rate
    (polyJacksonMin n S) s hij hjk
  refine ⟨K, fun hs _ hL hσ hu hb hq N => ?_⟩
  have h := hK hs hL ⟨hSi, hσ⟩ ⟨hSj, hu⟩ ⟨hSj, hb⟩ ⟨hSj, hq⟩ N
  simp only [polyFamilyMin_V] at h
  rw [← Real.rpow_natCast]
  exact h

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method with vanishing traces** for
a sequence of order `s` in every degree; see `mixed_rate_polyMin_of_polyOrderAt`. -/
theorem mixed_rate_polyMin (S : PolySeq) {s : ℕ} (hS : PolyOrder n S s) {i j k : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j},
    (complexMin n).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    IsCsFormMin s i L ((complexMin n).domainIncl i σ) →
    IsCsFormMin s j L ((complexMin n).domainIncl j u) →
    IsCsFormMin s j L ((complexMin n).domainIncl j
      ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))) →
    IsCsFormMin s j L (q : L2F ℝ (cubeDomain n) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (polyMin n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).fst‖ +
        ‖u - (polyMin n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (polyMin n S N) hij hjk f).snd.snd :
            (polyMin n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * L * meshSize N ^ (s + 1) :=
  mixed_rate_polyMin_of_polyOrderAt S (hS.polyOrderAt i) (hS.polyOrderAt j) hij hjk

/-! ### Second-order rates for the bottom row of Tables 5.1/6.1 -/

/-- **Second-order convergence of the mixed method of the bottom row of Tables 5.1/6.1 for the
Hodge Laplacian on `1`-forms** (`(i, j, k) = (0, 1, 2)`, `HΛ(Q)`; [AFW2010], Thm 3.9): although
`P₀Λ³` limits the global order to `h` (`PolyOrder` holds only for `s = 0`), the problem in degree
`1` only uses `P₂Λ⁰, P₂⁻Λ¹, P₁Λ²`, which contain `P₁`, so the error is `≤ K L h_N²` for `C³`
solutions. -/
theorem mixed_rate_lagrangeP2 :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n 1)} {σ : (complex n).domainSpace 0}
    {u : (complex n).domainSpace 1} {q : (complex n).harmonic 1},
    (complex n).IsMixedSolution 0 1 2 f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    IsCsForm 1 0 L ((complex n).domainIncl 0 σ) →
    IsCsForm 1 1 L ((complex n).domainIncl 1 u) →
    IsCsForm 1 1 L ((complex n).domainIncl 1
      ((complex n).boundaryPart 1 ((complex n).domainIncl 1 u))) →
    IsCsForm 1 1 L (q : L2F ℝ (cubeDomain n) (formIdx n 1)) → ∀ N : ℕ,
    ‖σ - (poly n PolySeq.lagrangeP2 N).embD 0
          (Subcomplex.CochainProjection.discreteMixedSolution
            (poly n PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl f).fst‖ +
        ‖u - (poly n PolySeq.lagrangeP2 N).embD 1
          (Subcomplex.CochainProjection.discreteMixedSolution
            (poly n PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n 1)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (poly n PolySeq.lagrangeP2 N)
            (i := 0) (j := 1) (k := 2) rfl rfl f).snd.snd :
            (poly n PolySeq.lagrangeP2 N).V 1) : L2F ℝ (cubeDomain n) (formIdx n 1))‖ ≤
      K * L * meshSize N ^ 2 :=
  mixed_rate_poly_of_polyOrderAt (n := n) PolySeq.lagrangeP2 lagrangeP2_polyOrderAt_zero
    lagrangeP2_polyOrderAt_one rfl rfl

/-- **Second-order convergence of the mixed method of the bottom row of Tables 5.1/6.1 with
vanishing boundary DOFs for the Hodge Laplacian on `1`-forms** (`H̊Λ(Q)`, data vanishing outside
`Q`): error `≤ K L h_N²`. -/
theorem mixed_rate_lagrangeP2Min :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n 1)} {σ : (complexMin n).domainSpace 0}
    {u : (complexMin n).domainSpace 1} {q : (complexMin n).harmonic 1},
    (complexMin n).IsMixedSolution 0 1 2 f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    IsCsFormMin 1 0 L ((complexMin n).domainIncl 0 σ) →
    IsCsFormMin 1 1 L ((complexMin n).domainIncl 1 u) →
    IsCsFormMin 1 1 L ((complexMin n).domainIncl 1
      ((complexMin n).boundaryPart 1 ((complexMin n).domainIncl 1 u))) →
    IsCsFormMin 1 1 L (q : L2F ℝ (cubeDomain n) (formIdx n 1)) → ∀ N : ℕ,
    ‖σ - (polyMin n PolySeq.lagrangeP2 N).embD 0
          (Subcomplex.CochainProjection.discreteMixedSolution
            (polyMin n PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl f).fst‖ +
        ‖u - (polyMin n PolySeq.lagrangeP2 N).embD 1
          (Subcomplex.CochainProjection.discreteMixedSolution
            (polyMin n PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n 1)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (polyMin n PolySeq.lagrangeP2 N)
            (i := 0) (j := 1) (k := 2) rfl rfl f).snd.snd :
            (polyMin n PolySeq.lagrangeP2 N).V 1) : L2F ℝ (cubeDomain n) (formIdx n 1))‖ ≤
      K * L * meshSize N ^ 2 :=
  mixed_rate_polyMin_of_polyOrderAt (n := n) PolySeq.lagrangeP2 lagrangeP2_polyOrderAt_zero
    lagrangeP2_polyOrderAt_one rfl rfl

/-! ### Rates for the semi-discrete Hodge wave equation -/

/-- **Graph-norm rate in the total space of a window** for a sequence of order `s`: if every
component of `ζ ∈ Γ(𝐝)` is `IsCsForm s` with bound `L`, some point of the window of `Vₕ` is
within `(m + m²) (Σᵢ B_{a+i}) L h_N^{s+1}` of `ζ`. -/
theorem exists_mem_window_poly_le {S : PolySeq} {s : ℕ} {a : ℤ} {m : ℕ}
    (hS : ∀ i : Fin m, PolyOrderAt n S s (a + i))
    (ζ : ((complex n).window a m).totalD.GraphSpace) {L : ℝ} (hL0 : 0 ≤ L)
    (hζ : ∀ i : Fin m, IsCsForm s (a + i) L (((complex n).window a m).totalD.graphFst ζ i))
    (N : ℕ) :
    ∃ w ∈ ((poly n S N).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * (∑ i : Fin m, polyInterpBound n S (a + i)) * L *
        meshSize N ^ (s + 1) :=
  ((poly n S N).exists_mem_window_graphSub_le ζ (fun i => polyInterpBound n S (a + i))
    (fun _ => polyInterpBound_nonneg _ _) (mul_nonneg hL0 (pow_nonneg (meshSize_pos N).le _))
    fun i => by
      obtain ⟨v, hv, h1, h2⟩ := (hζ i).exists_mem_poly_le (hS i) hL0 N
      exact ⟨v, hv, h1.trans_eq (mul_assoc _ _ _),
        fun j hx => (h2 j hx).trans_eq (mul_assoc _ _ _)⟩).imp
    fun _ h => ⟨h.1, h.2.trans_eq (mul_assoc _ _ _).symm⟩

/-- **Convergence of order `h^{s+1}` of the semi-discrete Hodge wave equation** for the
higher-order complexes ([QuennevilleBelair2015], Thm 4.14; [Arnold2018], Ch. 7), on every window
of `HΛ(Q)`: for a weak solution `ξ` in `C¹([t₀, t₁]; Γ(𝐝))` whose values and time derivatives
have `IsCsForm s` components with bound `L`, and the semi-discrete solutions `ξₕ` started at the
elliptic projection,
`‖ξ(t) - ξₕ(t)‖ ≤ A (1 + (t - t₀))² (m + m²) (Σᵢ B_{a+i}) L h_N^{s+1}` with `A` independent of `N`
(`Feec.HilbertComplex.Subcomplex.norm_sub_le_of_approx`). -/
theorem norm_sub_le_window_poly_smooth_of_polyOrderAt {S : PolySeq} {s : ℕ} {a : ℤ}
    {m : ℕ} (hS : ∀ i : Fin m, PolyOrderAt n S s (a + i)) {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complex n).window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complex n).window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((poly n S N).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((poly n S N).window a m).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ τ ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
      IsCsForm s (a + i) L (((complex n).window a m).totalD.graphFst (ξ τ) i) ∧
        IsCsForm s (a + i) L (((complex n).window a m).totalD.graphFst (ξ' τ) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complex n).window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complex n).window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          (((m : ℝ) + m * m) * (∑ i : Fin m, polyInterpBound n S (a + i)) * L *
            meshSize N ^ (s + 1)) :=
  ((poly n S N).window a m).norm_sub_le_of_approx hξ (hξh N) (h0 N) (fun τ hτ =>
    ⟨exists_mem_window_poly_le hS (ξ τ) hL0 (fun i => (hreg τ hτ i).1) N,
      exists_mem_window_poly_le hS (ξ' τ) hL0 (fun i => (hreg τ hτ i).2) N⟩) ht

/-- The case of a sequence of order `s` in every degree (`PolyOrder`) of
`norm_sub_le_window_poly_smooth_of_polyOrderAt`. -/
theorem norm_sub_le_window_poly_smooth {S : PolySeq} {s : ℕ} (hS : PolyOrder n S s) (a : ℤ)
    (m : ℕ) {t₀ t₁ : ℝ} {ξ ξ' : ℝ → ((complex n).window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complex n).window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((poly n S N).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((poly n S N).window a m).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ τ ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
      IsCsForm s (a + i) L (((complex n).window a m).totalD.graphFst (ξ τ) i) ∧
        IsCsForm s (a + i) L (((complex n).window a m).totalD.graphFst (ξ' τ) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complex n).window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complex n).window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          (((m : ℝ) + m * m) * (∑ i : Fin m, polyInterpBound n S (a + i)) * L *
            meshSize N ^ (s + 1)) :=
  norm_sub_le_window_poly_smooth_of_polyOrderAt (fun _ => hS.polyOrderAt _) hξ hξh h0 hL0 hreg
    N ht

/-- **Graph-norm rate in the total space of a window of `H̊Λ(Q)`** for a sequence of order `s`. -/
theorem exists_mem_windowMin_poly_le {S : PolySeq} {s : ℕ} {a : ℤ} {m : ℕ}
    (hS : ∀ i : Fin m, PolyOrderAt n S s (a + i))
    (ζ : ((complexMin n).window a m).totalD.GraphSpace) {L : ℝ} (hL0 : 0 ≤ L)
    (hζ : ∀ i : Fin m,
      IsCsFormMin s (a + i) L (((complexMin n).window a m).totalD.graphFst ζ i))
    (N : ℕ) :
    ∃ w ∈ ((polyMin n S N).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * (∑ i : Fin m, polyInterpBound n S (a + i)) * L *
        meshSize N ^ (s + 1) :=
  ((polyMin n S N).exists_mem_window_graphSub_le ζ (fun i => polyInterpBound n S (a + i))
    (fun _ => polyInterpBound_nonneg _ _) (mul_nonneg hL0 (pow_nonneg (meshSize_pos N).le _))
    fun i => by
      obtain ⟨v, hv, h1, h2⟩ := (hζ i).exists_mem_polyMin_le (hS i) hL0 N
      exact ⟨v, hv, h1.trans_eq (mul_assoc _ _ _),
        fun j hx => (h2 j hx).trans_eq (mul_assoc _ _ _)⟩).imp
    fun _ h => ⟨h.1, h.2.trans_eq (mul_assoc _ _ _).symm⟩

/-- **Convergence of order `h^{s+1}` of the semi-discrete Hodge wave equation with vanishing
traces** for the higher-order complexes, on every window of `H̊Λ(Q)` (components vanishing
outside `Q`). -/
theorem norm_sub_le_windowMin_poly_smooth_of_polyOrderAt {S : PolySeq} {s : ℕ} {a : ℤ}
    {m : ℕ} (hS : ∀ i : Fin m, PolyOrderAt n S s (a + i)) {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complexMin n).window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complexMin n).window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((polyMin n S N).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ =
      HodgeWave.ellipticProjection (((polyMin n S N).window a m).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ τ ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
      IsCsFormMin s (a + i) L (((complexMin n).window a m).totalD.graphFst (ξ τ) i) ∧
        IsCsFormMin s (a + i) L (((complexMin n).window a m).totalD.graphFst (ξ' τ) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complexMin n).window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complexMin n).window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          (((m : ℝ) + m * m) * (∑ i : Fin m, polyInterpBound n S (a + i)) * L *
            meshSize N ^ (s + 1)) :=
  ((polyMin n S N).window a m).norm_sub_le_of_approx hξ (hξh N) (h0 N) (fun τ hτ =>
    ⟨exists_mem_windowMin_poly_le hS (ξ τ) hL0 (fun i => (hreg τ hτ i).1) N,
      exists_mem_windowMin_poly_le hS (ξ' τ) hL0 (fun i => (hreg τ hτ i).2) N⟩) ht

/-- **Second-order convergence of the semi-discrete Hodge wave equation for the bottom row of
Tables 5.1/6.1 with vanishing boundary DOFs** on the window `H̊Λ⁰ → H̊Λ¹ → H̊Λ²` (degrees `0, 1`
of `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ²`; [QuennevilleBelair2015], Thm 4.14): for `C³` data vanishing outside
`Q`, `‖ξ(t) - ξₕ(t)‖ ≤ A (1 + (t - t₀))² · 6 (B₀ + B₁) L h_N²`. -/
theorem norm_sub_le_windowMin_lagrangeP2 {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complexMin n).window 0 2).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complexMin n).window 0 2).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution
      (((polyMin n PolySeq.lagrangeP2 N).window 0 2).graphSub) (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ = HodgeWave.ellipticProjection
      (((polyMin n PolySeq.lagrangeP2 N).window 0 2).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ τ ∈ Set.Icc t₀ t₁, ∀ i : Fin 2,
      IsCsFormMin 1 (0 + i) L (((complexMin n).window 0 2).totalD.graphFst (ξ τ) i) ∧
        IsCsFormMin 1 (0 + i) L (((complexMin n).window 0 2).totalD.graphFst (ξ' τ) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complexMin n).window 0 2).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complexMin n).window 0 2).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          (((2 : ℕ) + (2 : ℕ) * (2 : ℕ) : ℝ) *
            (∑ i : Fin 2, polyInterpBound n PolySeq.lagrangeP2 (0 + i)) * L * meshSize N ^ 2) :=
  norm_sub_le_windowMin_poly_smooth_of_polyOrderAt lagrangeP2_polyOrderAt_window hξ hξh h0 hL0
    hreg N ht

/-! ### The `H¹` approximation of the smoothed projections: analytic lemmas -/

section H1Lemmas

/-- `(∫₀¹ f)² ≤ ∫₀¹ f²` for continuous `f`. -/
theorem sq_intervalIntegral_le {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ τ in (0 : ℝ)..1, f τ) ^ 2 ≤ ∫ τ in (0 : ℝ)..1, f τ ^ 2 := by
  set a := ∫ τ in (0 : ℝ)..1, f τ
  have h0 : 0 ≤ ∫ τ in (0 : ℝ)..1, (f τ - a) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
  have hi1 : IntervalIntegrable (fun τ => f τ ^ 2) volume 0 1 := (hf.pow 2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun τ => 2 * a * f τ) volume 0 1 :=
    (continuous_const.mul hf).intervalIntegrable _ _
  have e : ∫ τ in (0 : ℝ)..1, (f τ - a) ^ 2 = (∫ τ in (0 : ℝ)..1, f τ ^ 2) - 2 * a * a + a ^ 2 := by
    have : (fun τ => (f τ - a) ^ 2) = fun τ => (f τ ^ 2 - 2 * a * f τ) + a ^ 2 := by
      funext τ; ring
    rw [this, intervalIntegral.integral_add (hi1.sub hi2) intervalIntegrable_const,
      intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul, one_mul]
    rfl
  rw [e] at h0
  nlinarith

/-- `|L v| ≤ ‖v‖ Σⱼ |L eⱼ|` for a linear form on `ℝⁿ` with the sup norm. -/
theorem abs_apply_le_norm_mul_sum {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    |L v| ≤ ‖v‖ * ∑ j, |L (Pi.single j 1)| := by
  have hv : v = ∑ j, v j • (Pi.single j 1 : Fin n → ℝ) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [map_smul, smul_eq_mul, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have := norm_le_pi_norm v j
  rwa [Real.norm_eq_abs] at this

/-- **The fundamental theorem of calculus with Cauchy–Schwarz** along a segment:
`(w z - w x)² ≤ ‖z - x‖² n ∫₀¹ Σⱼ (∂ⱼ w)²(x + τ (z - x)) dτ` for `w ∈ C¹(ℝⁿ)`. -/
theorem sq_sub_le_integral_grad {n : ℕ} {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ 1 w)
    (x z : Fin n → ℝ) :
    (w z - w x) ^ 2 ≤ ‖z - x‖ ^ 2 * n *
      ∫ τ in (0 : ℝ)..1, ∑ j, (partialDeriv j w (x + τ • (z - x))) ^ 2 := by
  set v := z - x
  set g : ℝ → ℝ := fun τ => w (x + τ • v)
  have hline : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => x + τ • v) v τ := fun τ => by
    simpa using ((hasDerivAt_id τ).smul_const v).const_add x
  have hg : ∀ τ, HasDerivAt g (fderiv ℝ w (x + τ • v) v) τ := fun τ =>
    ((hw.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt τ (hline τ)
  have hfd := hw.continuous_fderiv one_ne_zero
  have hgc : Continuous fun τ : ℝ => fderiv ℝ w (x + τ • v) v := by fun_prop
  have hftc : w z - w x = ∫ τ in (0 : ℝ)..1, fderiv ℝ w (x + τ • v) v := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hg τ)
      (hgc.intervalIntegrable _ _)]
    simp [g, v]
  have hpt : ∀ τ : ℝ, (fderiv ℝ w (x + τ • v) v) ^ 2 ≤
      ‖v‖ ^ 2 * n * ∑ j, (partialDeriv j w (x + τ • v)) ^ 2 := by
    intro τ
    have h1 := abs_apply_le_norm_mul_sum (fderiv ℝ w (x + τ • v)) v
    have h2 : (∑ j, |fderiv ℝ w (x + τ • v) (Pi.single j 1)|) ^ 2 ≤
        n * ∑ j, (partialDeriv j w (x + τ • v)) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun j : Fin n => |fderiv ℝ w (x + τ • v) (Pi.single j 1)|)
      simpa [partialDeriv, sq_abs] using this
    calc (fderiv ℝ w (x + τ • v) v) ^ 2 = |fderiv ℝ w (x + τ • v) v| ^ 2 := (sq_abs _).symm
      _ ≤ (‖v‖ * ∑ j, |fderiv ℝ w (x + τ • v) (Pi.single j 1)|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = ‖v‖ ^ 2 * (∑ j, |fderiv ℝ w (x + τ • v) (Pi.single j 1)|) ^ 2 := by ring
      _ ≤ ‖v‖ ^ 2 * (n * ∑ j, (partialDeriv j w (x + τ • v)) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  have hGc : Continuous fun τ : ℝ => ∑ j, (partialDeriv j w (x + τ • v)) ^ 2 := by
    simp only [partialDeriv]; fun_prop
  rw [hftc]
  refine (sq_intervalIntegral_le hgc).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on (by norm_num) ((hgc.pow 2).intervalIntegrable _ _)
    ((continuous_const.mul hGc).intervalIntegrable _ _) fun τ _ => hpt τ

/-- **Change of variables for affine dilations** in `ℝⁿ`:
`∫⁻ F(l x + β) dx = l⁻ⁿ ∫⁻ F` for `l > 0`. -/
theorem lintegral_comp_smul_add {n : ℕ} (F : (Fin n → ℝ) → ℝ≥0∞) {l : ℝ} (hl : 0 < l)
    (β : Fin n → ℝ) :
    ∫⁻ x, F (l • x + β) = ENNReal.ofReal ((l ^ n)⁻¹) * ∫⁻ x, F x := by
  have hl0 := hl.ne'
  have h1 : ∫⁻ x, F (l • x + β) =
      ∫⁻ y, (fun y => F (y + β)) y ∂(Measure.map (fun x : Fin n → ℝ => l • x) volume) :=
    (lintegral_map_equiv (fun y => F (y + β))
      (Homeomorph.smul (isUnit_iff_ne_zero.2 hl0).unit).toMeasurableEquiv).symm
  rw [h1, Measure.map_addHaar_smul volume hl0, lintegral_smul_measure, Module.finrank_fin_fun,
    lintegral_add_right_eq_self F β, abs_of_pos (inv_pos.2 (pow_pos hl n)), smul_eq_mul]

theorem ofReal_intervalIntegral_le_lintegral {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ τ, 0 ≤ g τ) :
    ENNReal.ofReal (∫ τ in (0 : ℝ)..1, g τ) ≤ ∫⁻ τ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (g τ) := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    ofReal_integral_eq_lintegral_ofReal
      (hg.continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Set.Ioc_subset_Icc_self)
      (Eventually.of_forall hg0)]
  exact lintegral_mono_set Set.Ioc_subset_Icc_self

/-- **The pointwise error of the mollifier at a displaced point**, in the form needed for the
`L²` estimate: for `‖ŷ - x‖ ≤ δ`,
`|w x - (w ⋆ ρ)(ŷ)|² ≤ (δ + r)² n ∫ ρ(u) ∫₀¹ |∇w|²(x + τ (ŷ - u - x)) dτ du`. -/
theorem ofReal_sq_sub_molli_le {n : ℕ} {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ 1 w)
    (φ : ContDiffBump (0 : Fin n → ℝ)) (x ŷ : Fin n → ℝ) {δ : ℝ} (hδ : ‖ŷ - x‖ ≤ δ) :
    ENNReal.ofReal ((w x - molli φ w ŷ) ^ 2) ≤ ENNReal.ofReal ((δ + φ.rOut) ^ 2 * n) *
      ∫⁻ u, ENNReal.ofReal (φ.normed volume u) * ∫⁻ τ in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal (∑ j, (partialDeriv j w (x + τ • (ŷ - u - x))) ^ 2) := by
  have hwc : Continuous w := hw.continuous
  have hρi : Integrable fun t => φ.normed volume (ŷ - t) :=
    (isTest_normed_comp_sub φ ŷ).continuous.integrable_of_hasCompactSupport
      (isTest_normed_comp_sub φ ŷ).hasCompactSupport
  have hρ1 : ∫ t, φ.normed volume (ŷ - t) = 1 := integral_normed_comp_sub φ ŷ
  set f : (Fin n → ℝ) → ℝ := fun t => w x - w t
  have hfc : Continuous f := continuous_const.sub hwc
  have hwi : Integrable fun t => w t * φ.normed volume (ŷ - t) :=
    integrable_mul_isTest hwc.locallyIntegrable (isTest_normed_comp_sub φ ŷ)
  have e1 : w x - molli φ w ŷ = ∫ t, f t * φ.normed volume (ŷ - t) := by
    symm
    calc ∫ t, f t * φ.normed volume (ŷ - t) =
          ∫ t, (w x * φ.normed volume (ŷ - t) - w t * φ.normed volume (ŷ - t)) :=
          integral_congr_ae (Eventually.of_forall fun t => by simp only [f]; ring)
      _ = w x * (∫ t, φ.normed volume (ŷ - t)) - ∫ t, w t * φ.normed volume (ŷ - t) := by
          rw [integral_sub (hρi.const_mul _) hwi, integral_const_mul]
      _ = w x - molli φ w ŷ := by
          rw [hρ1, mul_one, molli_apply]
  have hJ := sq_integral_mul_normed_le φ hfc.locallyIntegrable (hfc.pow 2).locallyIntegrable ŷ
  rw [e1]
  have hf2i : Integrable fun t => f t ^ 2 * φ.normed volume (ŷ - t) :=
    integrable_mul_isTest (hfc.pow 2).locallyIntegrable (isTest_normed_comp_sub φ ŷ)
  refine (ENNReal.ofReal_le_ofReal hJ).trans ?_
  rw [ofReal_integral_eq_lintegral_ofReal hf2i
    (Eventually.of_forall fun t => mul_nonneg (sq_nonneg _) (φ.nonneg_normed _))]
  rw [← lintegral_sub_left_eq_self (fun t => ENNReal.ofReal (f t ^ 2 * φ.normed volume (ŷ - t))) ŷ,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun u => ?_
  simp only [sub_sub_cancel]
  by_cases hu : φ.normed volume u = 0
  · rw [hu]; simp
  · have hu' : ‖u‖ < φ.rOut := by
      have : u ∈ Function.support (φ.normed volume) := hu
      rw [φ.support_normed_eq, Metric.mem_ball, dist_zero_right] at this
      exact this
    set t := ŷ - u
    have hxt : ‖t - x‖ ≤ δ + φ.rOut := by
      calc ‖t - x‖ = ‖(ŷ - x) - u‖ := by simp only [t]; congr 1; abel
        _ ≤ ‖ŷ - x‖ + ‖u‖ := norm_sub_le _ _
        _ ≤ δ + φ.rOut := add_le_add hδ hu'.le
    have hL1 := sq_sub_le_integral_grad hw x t
    have hft : f t ^ 2 = (w t - w x) ^ 2 := by simp only [f]; ring
    have hGc : Continuous fun τ : ℝ => ∑ j, (partialDeriv j w (x + τ • (t - x))) ^ 2 := by
      have hfd := hw.continuous_fderiv one_ne_zero
      simp only [partialDeriv]; fun_prop
    have hG0 : ∀ τ : ℝ, 0 ≤ ∑ j, (partialDeriv j w (x + τ • (t - x))) ^ 2 := fun τ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hI0 : 0 ≤ ∫ τ in (0 : ℝ)..1, ∑ j, (partialDeriv j w (x + τ • (t - x))) ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one fun τ _ => hG0 τ
    have hK : (w t - w x) ^ 2 ≤ (δ + φ.rOut) ^ 2 * n *
        ∫ τ in (0 : ℝ)..1, ∑ j, (partialDeriv j w (x + τ • (t - x))) ^ 2 := by
      refine hL1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
        hI0)
      exact pow_le_pow_left₀ (norm_nonneg _) hxt 2
    rw [ENNReal.ofReal_mul (sq_nonneg _), hft]
    calc ENNReal.ofReal ((w t - w x) ^ 2) * ENNReal.ofReal (φ.normed volume u)
        ≤ ENNReal.ofReal ((δ + φ.rOut) ^ 2 * n *
            ∫ τ in (0 : ℝ)..1, ∑ j, (partialDeriv j w (x + τ • (t - x))) ^ 2) *
            ENNReal.ofReal (φ.normed volume u) := by gcongr
      _ = ENNReal.ofReal ((δ + φ.rOut) ^ 2 * n) * ENNReal.ofReal
            (∫ τ in (0 : ℝ)..1, ∑ j, (partialDeriv j w (x + τ • (t - x))) ^ 2) *
            ENNReal.ofReal (φ.normed volume u) := by
          rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ((δ + φ.rOut) ^ 2 * n) * (∫⁻ τ in Set.Icc (0 : ℝ) 1,
            ENNReal.ofReal (∑ j, (partialDeriv j w (x + τ • (t - x))) ^ 2)) *
            ENNReal.ofReal (φ.normed volume u) := by
          gcongr
          exact ofReal_intervalIntegral_le_lintegral hGc hG0
      _ = _ := by ring

/-- **The `L²` error of the dilated mollifier** for a `C¹` function: if the dilation moves the
points of `U` by at most `δ`, and the segments from `x ∈ U` to the points sampled by the mollifier
stay in `V`, then
`∫_U |w - (w ⋆ ρ) ∘ dil|² ≤ (δ + r)² n 2ⁿ ∫_V |∇w|²` (`r` the outer radius of the bump, the
dilation factor `c ≥ ½`). -/
theorem lintegral_sq_sub_molli_dil_le {n : ℕ} {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ 1 w)
    (φ : ContDiffBump (0 : Fin n → ℝ)) (x₀ : Fin n → ℝ) {c : ℝ} (hc1 : 1 / 2 ≤ c)
    {U V : Set (Fin n → ℝ)} (hU : MeasurableSet U) (hV : MeasurableSet V) {δ : ℝ}
    (hδ : ∀ x ∈ U, ‖(x₀ + c • (x - x₀)) - x‖ ≤ δ)
    (hseg : ∀ x ∈ U, ∀ u : Fin n → ℝ, ‖u‖ ≤ φ.rOut → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      x + τ • ((x₀ + c • (x - x₀)) - u - x) ∈ V) :
    ∫⁻ x in U, ENNReal.ofReal ((w x - molli φ w (x₀ + c • (x - x₀))) ^ 2) ≤
      ENNReal.ofReal ((δ + φ.rOut) ^ 2 * n * 2 ^ n) *
        ∫⁻ x in V, ENNReal.ofReal (∑ j, (partialDeriv j w x) ^ 2) := by
  have hfd := hw.continuous_fderiv one_ne_zero
  obtain ⟨G, hG⟩ : ∃ G : (Fin n → ℝ) → ℝ≥0∞,
      G = fun y => ENNReal.ofReal (∑ j, (partialDeriv j w y) ^ 2) := ⟨_, rfl⟩
  have hGc : Continuous G := by
    rw [hG]; simp only [partialDeriv]
    exact ENNReal.continuous_ofReal.comp (by fun_prop)
  obtain ⟨A, hAdef⟩ : ∃ A : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → (Fin n → ℝ),
      A = fun u τ x => x + τ • ((x₀ + c • (x - x₀)) - u - x) := ⟨_, rfl⟩
  have hAc : Continuous fun q : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ => G (A q.1.2 q.2 q.1.1) :=
    hGc.comp (by rw [hAdef]; fun_prop)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞,
      Ψ = fun x u => ∫⁻ τ in Set.Icc (0 : ℝ) 1, G (A u τ x) := ⟨_, rfl⟩
  have hΨm : Measurable fun q : (Fin n → ℝ) × (Fin n → ℝ) => Ψ q.1 q.2 := by
    rw [hΨ]; exact hAc.measurable.lintegral_prod_right'
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (Fin n → ℝ) → ℝ≥0∞, ρ = fun u => ENNReal.ofReal (φ.normed volume u) :=
    ⟨_, rfl⟩
  have hρm : Measurable ρ := by
    rw [hρ]; exact (ENNReal.continuous_ofReal.comp φ.continuous_normed).measurable
  set K₀ := (δ + φ.rOut) ^ 2 * n
  -- step 1: the pointwise bound
  have h1 : ∫⁻ x in U, ENNReal.ofReal ((w x - molli φ w (x₀ + c • (x - x₀))) ^ 2) ≤
      ∫⁻ x in U, ENNReal.ofReal K₀ * ∫⁻ u, ρ u * Ψ x u := by
    refine setLIntegral_mono' hU fun x hx => ?_
    have := ofReal_sq_sub_molli_le hw φ x _ (hδ x hx)
    simpa only [hρ, hΨ, hAdef, hG] using this
  -- step 2: exchange the integrals
  have h2 : ∫⁻ x in U, ENNReal.ofReal K₀ * ∫⁻ u, ρ u * Ψ x u =
      ENNReal.ofReal K₀ * ∫⁻ u, ρ u * ∫⁻ x in U, Ψ x u := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    rw [lintegral_lintegral_swap ((hρm.comp measurable_snd).mul hΨm).aemeasurable]
    refine lintegral_congr fun u => ?_
    have hm : Measurable fun x => Ψ x u := hΨm.comp measurable_prodMk_right
    exact lintegral_const_mul _ hm
  -- step 3: the change of variables for each sample
  set Y := ENNReal.ofReal (2 ^ n) * ∫⁻ x in V, G x
  have h3 : ∀ u, ρ u * ∫⁻ x in U, Ψ x u ≤ ρ u * Y := by
    intro u
    by_cases hu : φ.normed volume u = 0
    · simp [hρ, hu]
    have hu' : ‖u‖ ≤ φ.rOut := by
      have : u ∈ Function.support (φ.normed volume) := hu
      rw [φ.support_normed_eq, Metric.mem_ball, dist_zero_right] at this
      exact this.le
    refine mul_le_mul' le_rfl ?_
    have hswap : ∫⁻ x in U, Ψ x u = ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ x in U, G (A u τ x) := by
      rw [hΨ]
      refine lintegral_lintegral_swap ?_
      exact (hGc.comp (by rw [hAdef]; fun_prop : Continuous fun q : (Fin n → ℝ) × ℝ =>
        A u q.2 q.1)).measurable.aemeasurable
    rw [hswap]
    calc ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ x in U, G (A u τ x)
        ≤ ∫⁻ τ in Set.Icc (0 : ℝ) 1, Y := by
          refine setLIntegral_mono' measurableSet_Icc fun τ hτ => ?_
          set l : ℝ := 1 + τ * (c - 1)
          have hl : 1 / 2 ≤ l := by
            rcases le_total c 1 with h | h
            · have : τ * (c - 1) ≥ (c - 1) := by nlinarith [hτ.1, hτ.2]
              simp only [l]; linarith
            · have : 0 ≤ τ * (c - 1) := mul_nonneg hτ.1 (by linarith)
              simp only [l]; linarith
          have hl0 : 0 < l := by linarith
          have hA : ∀ x, A u τ x = l • x + τ • (x₀ - c • x₀ - u) := fun x => by
            rw [hAdef]
            simp only [l]
            module
          calc ∫⁻ x in U, G (A u τ x) = ∫⁻ x in U, V.indicator G (l • x + τ • (x₀ - c • x₀ - u)) := by
                refine setLIntegral_congr_fun hU fun x hx => ?_
                have hm := hseg x hx u hu' τ hτ
                rw [← hA, Set.indicator_of_mem (by rw [hAdef]; exact hm)]
            _ ≤ ∫⁻ x, V.indicator G (l • x + τ • (x₀ - c • x₀ - u)) := setLIntegral_le_lintegral _ _
            _ = ENNReal.ofReal ((l ^ n)⁻¹) * ∫⁻ x, V.indicator G x := lintegral_comp_smul_add _ hl0 _
            _ = ENNReal.ofReal ((l ^ n)⁻¹) * ∫⁻ x in V, G x := by rw [lintegral_indicator hV]
            _ ≤ Y := by
                refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
                rw [inv_le_iff_one_le_mul₀ (pow_pos hl0 n), ← mul_pow]
                exact one_le_pow₀ (by linarith)
      _ = Y := by rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
  -- step 4: the mollifier has mass one
  have hρ1 : ∫⁻ u, ρ u = 1 := by
    rw [hρ, ← ofReal_integral_eq_lintegral_ofReal (φ.integrable_normed)
      (Eventually.of_forall fun u => φ.nonneg_normed u), φ.integral_normed, ENNReal.ofReal_one]
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ ENNReal.ofReal K₀ * ∫⁻ u, ρ u * Y := mul_le_mul' le_rfl (lintegral_mono fun u => h3 u)
    _ = ENNReal.ofReal K₀ * Y := by
        rw [lintegral_mul_const _ hρm, hρ1, one_mul]
    _ = _ := by
        simp only [Y, K₀, hG]
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

/-- `‖g‖² ≤ B` for an `L²` class with an a.e. representative `F` with `∫⁻ F² ≤ B`. -/
theorem sq_norm_le_of_ae_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} (g : Lp ℝ 2 μ)
    {F : α → ℝ} (hgF : (g : α → ℝ) =ᵐ[μ] F) {B : ℝ≥0∞}
    (h : ∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂μ ≤ B) (hB : B ≠ ⊤) : ‖g‖ ^ 2 ≤ B.toReal := by
  rw [norm_sq_eq_integral_sq, integral_congr_ae (hgF.mono fun x hx => by rw [hx])]
  have hm : AEStronglyMeasurable (fun x => F x ^ 2) μ :=
    (((Lp.aestronglyMeasurable g).congr hgF).pow 2)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _) hm]
  exact ENNReal.toReal_mono hB h

/-- The singletons `{j}` enumerate the `1`-form indices. -/
def singletonEquiv (n : ℕ) : Fin n ≃ formIdx n 1 :=
  Equiv.ofBijective (fun j => ⟨{j}, by simp⟩) ⟨fun i j h => by
    simpa using congrArg Subtype.val h, fun s => by
    obtain ⟨j, hj⟩ := Finset.card_eq_one.1 (by exact_mod_cast s.2)
    exact ⟨j, Subtype.ext hj.symm⟩⟩

omit [NeZero n] in
theorem extDeriv_apply_singleton (w : FormField n) (x : Fin n → ℝ) (j : Fin n) :
    extDeriv w x {j} = partialDeriv j (fun y => w y ∅) x := by
  rw [extDeriv_apply, Finset.sum_singleton, Finset.erase_singleton]
  simp [ExteriorFibre.sgn, Finset.filter_singleton]

omit [NeZero n] in
/-- `‖d w‖²_{L²(Ω)} = Σⱼ ∫_Ω (∂ⱼ w)²` for a smooth `0`-form `w`. -/
theorem norm_sq_formL2_extDeriv_zero {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) {w : FormField n} (hw : ContDiff ℝ 1 w) :
    ‖formL2 hΩ hb (((0 : ℕ) : ℤ) + 1) ⟨extDeriv w, continuous_extDeriv hw⟩‖ ^ 2 =
      ∫ x in Ω, ∑ j, (partialDeriv j (fun y => w y ∅) x) ^ 2 := by
  have hcomp : ∀ s : formIdx n (((0 : ℕ) : ℤ) + 1), Continuous fun x => extDeriv w x s.1 :=
    fun s => (continuous_apply s.1).comp (continuous_extDeriv hw)
  rw [PiLp.norm_sq_eq_of_L2]
  have e : ∀ s : formIdx n (((0 : ℕ) : ℤ) + 1),
      ‖formL2 hΩ hb (((0 : ℕ) : ℤ) + 1) ⟨extDeriv w, continuous_extDeriv hw⟩ s‖ ^ 2 =
        ∫ x in Ω, (extDeriv w x s.1) ^ 2 := fun s => by
    rw [norm_sq_eq_integral_sq]
    exact integral_congr_ae ((coeFn_formL2 hΩ hb _ ⟨extDeriv w, continuous_extDeriv hw⟩ s).mono
      fun x hx => by dsimp only; rw [hx])
  simp_rw [e]
  rw [← integral_finsetSum _ fun s _ => (memLp_of_continuous hΩ hb (hcomp s)).integrable_sq]
  refine setIntegral_congr_fun hΩ fun x _ => ?_
  have : ∀ s : formIdx n 1, (extDeriv w x s.1) ^ 2 =
      (fun s : formIdx n 1 => (extDeriv w x s.1) ^ 2) s := fun s => rfl
  change ∑ s : formIdx n 1, (extDeriv w x s.1) ^ 2 = _
  rw [← (singletonEquiv n).sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  change (extDeriv w x {j}) ^ 2 = _
  rw [extDeriv_apply_singleton]

omit [NeZero n] in
/-- The lintegral of `|∇w|²` over `Q` is `‖d w‖²_{L²(Q)}` for a smooth `0`-form. -/
theorem lintegral_grad_eq {w : FormField n} (hw : ContDiff ℝ 1 w) :
    ∫⁻ x in cubeDomain n, ENNReal.ofReal (∑ j, (partialDeriv j (fun y => w y ∅) x) ^ 2) =
      ENNReal.ofReal (‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n)
        (((0 : ℕ) : ℤ) + 1) ⟨extDeriv w, continuous_extDeriv hw⟩‖ ^ 2) := by
  have hd : Continuous (fderiv ℝ (fun y => w y ∅)) :=
    (contDiff_pi.1 hw ∅).continuous_fderiv one_ne_zero
  have hc : Continuous fun x => ∑ j, (partialDeriv j (fun y => w y ∅) x) ^ 2 :=
    continuous_finsetSum _ fun j _ => (hd.clm_apply continuous_const).pow 2
  rw [norm_sq_formL2_extDeriv_zero _ _ hw, ofReal_integral_eq_lintegral_ofReal
    ((hc.continuousOn.integrableOn_compact (isCompact_closure_cubeDomain n)).mono_set
      subset_closure)
    (Eventually.of_forall fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _)]

omit [NeZero n] in
theorem mem_cubeDomain_seg {x t : Fin n → ℝ} (hx : x ∈ cubeDomain n) (ht : t ∈ cubeDomain n)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) : x + τ • (t - x) ∈ cubeDomain n :=
  (convex_cubeDomain n).add_smul_sub_mem hx ht hτ

omit [NeZero n] in
/-- **`‖f - R f‖ ≲ γ h ‖∇f‖` for smooth `f`, maximal family**: for the parameters `pMax γ` and a
smooth `0`-form `w`, the smoother moves the class of `w` on `Q` by at most
`γ h_N √(n 2ⁿ) ‖dw‖_{L²(Q)}`. -/
theorem sq_norm_sub_smoothL2_le_pMax {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ)
    {w : FormField n} (hw : ContDiff ℝ 1 w) :
    ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((0 : ℕ) : ℤ)
          ⟨w, hw.continuous⟩ ⟨∅, by simp⟩ -
        smoothL2 (pMax γ hγ hγ1 N) (isOpen_cubeDomain n).measurableSet
          (formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((0 : ℕ) : ℤ)
            ⟨w, hw.continuous⟩ ⟨∅, by simp⟩)‖ ^ 2 ≤
      (γ * hN N) ^ 2 * n * 2 ^ n *
        ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n)
          (((0 : ℕ) : ℤ) + 1) ⟨extDeriv w, continuous_extDeriv hw⟩‖ ^ 2 := by
  set hQ := (isOpen_cubeDomain n).measurableSet
  set p := pMax (n := n) γ hγ hγ1 N
  have hp := pMax_isMaximal (n := n) (γ := γ) (hγ := hγ) (hγ1 := hγ1) N
  have hpa := pMax_isAdm (n := n) (γ := γ) (hγ := hγ) (hγ1 := hγ1) N
  set f := formL2 hQ (isBounded_cubeDomain n) ((0 : ℕ) : ℤ) ⟨w, hw.continuous⟩ ⟨∅, by simp⟩
  set w₀ : (Fin n → ℝ) → ℝ := fun y => w y ∅
  have hw₀ : ContDiff ℝ 1 w₀ := contDiff_pi.1 hw ∅
  have hf : (f : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict (cubeDomain n)] w₀ :=
    coeFn_formL2 hQ (isBounded_cubeDomain n) _ ⟨w, hw.continuous⟩ ⟨∅, by simp⟩
  have hball : ∀ x ∈ cubeDomain n, Metric.closedBall (p.center + p.factor • (x - p.center))
      p.bump.rOut ⊆ cubeDomain n := fun x hx => by
    have := closedBall_dil_subset_of_starBall (starBall n) p.half_le_factor hp.factor_lt_one
      hp.rOut_lt (subset_closure hx)
    rwa [← hp.center_eq] at this
  have hmol : ∀ x ∈ cubeDomain n, smoothExt (cubeDomain n) p w₀ x =
      molli p.bump w₀ (p.center + p.factor • (x - p.center)) := by
    intro x hx
    simp only [smoothExt, dil, molli_apply]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : p.bump.normed volume (p.center + p.factor • (x - p.center) - t) = 0
    · simp only [ht, mul_zero]
    · have : t ∈ cubeDomain n := by
        refine hball x hx (Metric.mem_closedBall.2 ?_)
        have hs : _ ∈ Function.support (p.bump.normed volume) := ht
        rw [p.bump.support_normed_eq, Metric.mem_ball, dist_zero_right, ← dist_eq_norm,
          dist_comm] at hs
        exact hs.le
      simp only [Set.indicator_of_mem this]
  have hdiff : ((f - smoothL2 p hQ f : L2 ℝ (cubeDomain n)) : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict
      (cubeDomain n)] fun x => w₀ x - molli p.bump w₀ (p.center + p.factor • (x - p.center)) := by
    filter_upwards [Lp.coeFn_sub f (smoothL2 p hQ f), hf, coeFn_smoothL2 hQ f,
      ae_restrict_mem hQ] with x h1 h2 h3 hx
    rw [h1, Pi.sub_apply, h2, h3, smoothExt_congr_ae hQ hf, hmol x hx]
  have hmain := lintegral_sq_sub_molli_dil_le hw₀ p.bump p.center p.half_le_factor hQ hQ
    (δ := γ * hN N / 4) (fun x hx => hpa.norm_dil_sub_le (subset_closure hx))
    (fun x hx u hu τ hτ => mem_cubeDomain_seg hx (hball x hx (Metric.mem_closedBall.2 (by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hu))) hτ)
  rw [lintegral_grad_eq hw, ← ENNReal.ofReal_mul (by positivity)] at hmain
  refine (sq_norm_le_of_ae_eq _ hdiff hmain ENNReal.ofReal_ne_top).trans ?_
  rw [ENNReal.toReal_ofReal (by positivity), hpa.rOut_eq]
  have hh := (hN_pos N).le
  have hγ0 := hγ.le
  have : (γ * hN N / 4 + γ * hN N / 32) ^ 2 ≤ (γ * hN N) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) 2
  gcongr

omit [NeZero n] in
/-- **`‖f - R f‖ ≲ γ h ‖∇f‖` for smooth `f` vanishing outside `Q`, minimal family** (the
parameters `pMin γ`). -/
theorem sq_norm_sub_smoothL2_le_pMin {γ : ℝ} (hγ : 0 < γ) (N : ℕ)
    {w : FormField n} (hw : ContDiff ℝ 1 w) (hsupp : ∀ x ∉ cubeDomain n, w x = 0) :
    ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((0 : ℕ) : ℤ)
          ⟨w, hw.continuous⟩ ⟨∅, by simp⟩ -
        smoothL2 (pMin γ hγ N) (isOpen_cubeDomain n).measurableSet
          (formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((0 : ℕ) : ℤ)
            ⟨w, hw.continuous⟩ ⟨∅, by simp⟩)‖ ^ 2 ≤
      (γ * hN N) ^ 2 * n * 2 ^ n *
        ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n)
          (((0 : ℕ) : ℤ) + 1) ⟨extDeriv w, continuous_extDeriv hw⟩‖ ^ 2 := by
  set hQ := (isOpen_cubeDomain n).measurableSet
  set p := pMin (n := n) γ hγ N
  have hpa := pMin_isAdm (n := n) (γ := γ) (hγ := hγ) N
  set f := formL2 hQ (isBounded_cubeDomain n) ((0 : ℕ) : ℤ) ⟨w, hw.continuous⟩ ⟨∅, by simp⟩
  set w₀ : (Fin n → ℝ) → ℝ := fun y => w y ∅
  have hw₀ : ContDiff ℝ 1 w₀ := contDiff_pi.1 hw ∅
  have hf : (f : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict (cubeDomain n)] w₀ :=
    coeFn_formL2 hQ (isBounded_cubeDomain n) _ ⟨w, hw.continuous⟩ ⟨∅, by simp⟩
  have hind : (cubeDomain n).indicator w₀ = w₀ := by
    funext x
    by_cases hx : x ∈ cubeDomain n
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]; simp [w₀, hsupp x hx]
  have hmol : ∀ x, smoothExt (cubeDomain n) p w₀ x =
      molli p.bump w₀ (p.center + p.factor • (x - p.center)) := fun x => by
    simp only [smoothExt, dil, hind]
  have hdiff : ((f - smoothL2 p hQ f : L2 ℝ (cubeDomain n)) : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict
      (cubeDomain n)] fun x => w₀ x - molli p.bump w₀ (p.center + p.factor • (x - p.center)) := by
    filter_upwards [Lp.coeFn_sub f (smoothL2 p hQ f), hf, coeFn_smoothL2 hQ f] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, smoothExt_congr_ae hQ hf, hmol x]
  have hmain := lintegral_sq_sub_molli_dil_le hw₀ p.bump p.center p.half_le_factor hQ
    MeasurableSet.univ (δ := γ * hN N / 4) (fun x hx => hpa.norm_dil_sub_le (subset_closure hx))
    (fun _ _ _ _ _ _ => Set.mem_univ _)
  -- the gradient vanishes outside `cl Q`
  have hG0 : ∀ x ∉ closure (cubeDomain n),
      ENNReal.ofReal (∑ j, (partialDeriv j w₀ x) ^ 2) = 0 := by
    intro x hx
    have hev : w₀ =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      have : y ∉ cubeDomain n := fun h => hy (subset_closure h)
      simp [w₀, hsupp y this]
    have hfd : fderiv ℝ w₀ x = 0 := by rw [hev.fderiv_eq]; simp
    simp [partialDeriv, hfd]
  have hsupp' : Function.support (fun x => ENNReal.ofReal (∑ j, (partialDeriv j w₀ x) ^ 2)) ⊆
      closure (cubeDomain n) := fun x hx => by
    by_contra h; exact hx (hG0 x h)
  have hnull : volume (frontier (cubeDomain n)) = 0 :=
    Convex.addHaar_frontier volume (convex_cubeDomain n)
  have hR : ∫⁻ x, ENNReal.ofReal (∑ j, (partialDeriv j w₀ x) ^ 2) =
      ∫⁻ x in cubeDomain n, ENNReal.ofReal (∑ j, (partialDeriv j w₀ x) ^ 2) := by
    rw [← setLIntegral_eq_of_support_subset hsupp',
      Measure.restrict_congr_set (closure_ae_eq_of_null_frontier hnull)]
  rw [Measure.restrict_univ, hR] at hmain
  rw [lintegral_grad_eq hw, ← ENNReal.ofReal_mul (by positivity)] at hmain
  refine (sq_norm_le_of_ae_eq _ hdiff hmain ENNReal.ofReal_ne_top).trans ?_
  rw [ENNReal.toReal_ofReal (by positivity), hpa.rOut_eq]
  have hh := (hN_pos N).le
  have hγ0 := hγ.le
  have : (γ * hN N / 4 + γ * hN N / 32) ^ 2 ≤ (γ * hN N) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) 2
  gcongr

/-- The `0`-form with the coefficient `f`. -/
def coeffForm {Ω : Set (Fin n → ℝ)} (f : L2 ℝ Ω) : L2F ℝ Ω (formIdx n 0) :=
  WithLp.toLp 2 fun _ => f

omit [NeZero n] in
theorem coeffForm_apply {Ω : Set (Fin n → ℝ)} (f : L2 ℝ Ω) (s : formIdx n 0) :
    coeffForm f s = f := rfl

omit [NeZero n] in
/-- **Density step**: an estimate `‖f - S f‖ ≤ K ‖∇f‖` for the classes of smooth `0`-forms
(`P`) passes to all `f` that are graph-norm limits of such classes, for a bounded `S`. -/
theorem norm_sub_le_of_approx {Ω : Set (Fin n → ℝ)} (S : L2 ℝ Ω →L[ℝ] L2 ℝ Ω) {K : ℝ}
    (hK : 0 ≤ K) (f : L2 ℝ Ω) {g : ℝ}
    (happ : ∀ ε > 0, ∃ f₀ : L2 ℝ Ω, ∃ g₀ : ℝ, ‖f - f₀‖ < ε ∧ g₀ < g + ε ∧
      ‖f₀ - S f₀‖ ≤ K * g₀) :
    ‖f - S f‖ ≤ K * g := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set A := 1 + ‖S‖ + K
  have hA : 0 < A := by positivity
  obtain ⟨f₀, g₀, h1, h2, h3⟩ := happ (ε / A) (div_pos hε hA)
  have e : f - S f = ((f - f₀) - S (f - f₀)) + (f₀ - S f₀) := by rw [map_sub]; abel
  calc ‖f - S f‖ ≤ ‖(f - f₀) - S (f - f₀)‖ + ‖f₀ - S f₀‖ := by rw [e]; exact norm_add_le _ _
    _ ≤ (‖f - f₀‖ + ‖S‖ * ‖f - f₀‖) + K * g₀ :=
        add_le_add ((norm_sub_le _ _).trans (add_le_add le_rfl (S.le_opNorm _))) h3
    _ ≤ (ε / A + ‖S‖ * (ε / A)) + K * (g + ε / A) := by
        gcongr
    _ = K * g + ε := by field_simp; ring

omit [NeZero n] in
theorem norm_le_of_sq_le {a K g : ℝ} (hK : 0 ≤ K) (hg : 0 ≤ g)
    (h : a ^ 2 ≤ K ^ 2 * g ^ 2) : a ≤ K * g := by
  rw [← mul_pow] at h
  exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hK hg) h

omit [NeZero n] in
/-- **`‖f - R f‖ ≤ γ h_N √(n 2ⁿ) ‖∇f‖` for `f ∈ H¹(Q)`, maximal family** (the parameters
`pMax γ`; `f` in the domain of the maximal gradient, as the coefficient of a `0`-form). -/
theorem norm_sub_smoothL2_le_pMax {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ)
    (f : L2 ℝ (cubeDomain n)) (hf : coeffForm f ∈ ((complex n).d 0 1).domain) :
    ‖f - smoothL2 (pMax γ hγ hγ1 N) (isOpen_cubeDomain n).measurableSet f‖ ≤
      γ * hN N * √(n * 2 ^ n) * ‖(complex n).d 0 1 ⟨coeffForm f, hf⟩‖ := by
  have hK : 0 ≤ γ * hN N * √(n * 2 ^ n) := by have := (hN_pos N).le; positivity
  refine norm_sub_le_of_approx _ hK f fun ε hε => ?_
  obtain ⟨w, hw, -, h1, h2⟩ := exists_smooth_near (n := n) 0 ⟨coeffForm f, hf⟩ hε
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by exact_mod_cast le_top)
  refine ⟨formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((0 : ℕ) : ℤ)
      ⟨w, hw1.continuous⟩ ⟨∅, by simp⟩,
    ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) (((0 : ℕ) : ℤ) + 1)
      ⟨extDeriv w, continuous_extDeriv hw1⟩‖, ?_, ?_, ?_⟩
  · refine lt_of_le_of_lt ?_ h1
    exact PiLp.norm_apply_le ((coeffForm f : L2F ℝ (cubeDomain n) (formIdx n ((0 : ℕ) : ℤ))) -
      formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((0 : ℕ) : ℤ)
        ⟨w, hw.continuous⟩) (⟨∅, by simp⟩ : formIdx n 0)
  · set D : L2F ℝ (cubeDomain n) (formIdx n (((0 : ℕ) : ℤ) + 1)) :=
      (complex n).d 0 1 ⟨coeffForm f, hf⟩
    have h2' : ‖D -
        formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) (((0 : ℕ) : ℤ) + 1)
          ⟨extDeriv w, continuous_extDeriv hw1⟩‖ < ε := h2
    have := norm_sub_le D (D -
        formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) (((0 : ℕ) : ℤ) + 1)
          ⟨extDeriv w, continuous_extDeriv hw1⟩)
    rw [sub_sub_cancel] at this
    change _ < ‖D‖ + ε
    linarith
  · refine norm_le_of_sq_le (by have := (hN_pos N).le; positivity) (norm_nonneg _)
      ((sq_norm_sub_smoothL2_le_pMax hγ hγ1 N hw1).trans (le_of_eq ?_))
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring

omit [NeZero n] in
/-- **`‖f - R f‖ ≤ γ h_N √(n 2ⁿ) ‖∇f‖` for `f ∈ H¹₀(Q)`, minimal family** (the parameters
`pMin γ`; `f` in the domain of the minimal gradient, i.e. its extension by zero is in
`H¹(ℝⁿ)`). -/
theorem norm_sub_smoothL2_le_pMin {γ : ℝ} (hγ : 0 < γ) (N : ℕ)
    (f : L2 ℝ (cubeDomain n)) (hf : coeffForm f ∈ ((complexMin n).d 0 1).domain) :
    ‖f - smoothL2 (pMin γ hγ N) (isOpen_cubeDomain n).measurableSet f‖ ≤
      γ * hN N * √(n * 2 ^ n) * ‖(complexMin n).d 0 1 ⟨coeffForm f, hf⟩‖ := by
  have hK : 0 ≤ γ * hN N * √(n * 2 ^ n) := by have := (hN_pos N).le; positivity
  refine norm_sub_le_of_approx _ hK f fun ε hε => ?_
  obtain ⟨w, hw, -, hsupp, h1, h2⟩ := exists_smooth_near_min_deg (n := n) 0 ⟨coeffForm f, hf⟩ hε
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by exact_mod_cast le_top)
  refine ⟨formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((0 : ℕ) : ℤ)
      ⟨w, hw1.continuous⟩ ⟨∅, by simp⟩,
    ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) (((0 : ℕ) : ℤ) + 1)
      ⟨extDeriv w, continuous_extDeriv hw1⟩‖, ?_, ?_, ?_⟩
  · refine lt_of_le_of_lt ?_ h1
    exact PiLp.norm_apply_le ((coeffForm f : L2F ℝ (cubeDomain n) (formIdx n ((0 : ℕ) : ℤ))) -
      formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((0 : ℕ) : ℤ)
        ⟨w, hw.continuous⟩) (⟨∅, by simp⟩ : formIdx n 0)
  · set D : L2F ℝ (cubeDomain n) (formIdx n (((0 : ℕ) : ℤ) + 1)) :=
      (complexMin n).d 0 1 ⟨coeffForm f, hf⟩
    have h2' : ‖D -
        formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) (((0 : ℕ) : ℤ) + 1)
          ⟨extDeriv w, continuous_extDeriv hw1⟩‖ < ε := h2
    have := norm_sub_le D (D -
        formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) (((0 : ℕ) : ℤ) + 1)
          ⟨extDeriv w, continuous_extDeriv hw1⟩)
    rw [sub_sub_cancel] at this
    change _ < ‖D‖ + ε
    linarith
  · refine norm_le_of_sq_le (by have := (hN_pos N).le; positivity) (norm_nonneg _)
      ((sq_norm_sub_smoothL2_le_pMin hγ N hw1 hsupp).trans (le_of_eq ?_))
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring

omit [NeZero n] in
/-- `‖DF(x)‖ ≤ Σⱼ Σₜ |∂ⱼ Fₜ(x)|` for a form field differentiable at `x`. -/
theorem norm_fderiv_le_sum_partialDeriv {F : FormField n} {x : Fin n → ℝ}
    (hF : DifferentiableAt ℝ F x) :
    ‖fderiv ℝ F x‖ ≤ ∑ j, ∑ t, |partialDeriv j (fun z => F z t) x| := by
  have hcomp : ∀ t v, fderiv ℝ F x v t = fderiv ℝ (fun z => F z t) x v := fun t v => by
    have h := (hasFDerivAt_pi'.1 hF.hasFDerivAt) t
    rw [h.fderiv]; rfl
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv : v = ∑ j, v j • (Pi.single j 1 : Fin n → ℝ) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [map_smul, norm_smul]
  have hj : ‖v j‖ ≤ ‖v‖ := norm_le_pi_norm v j
  have hsum : ‖fderiv ℝ F x (Pi.single j 1)‖ ≤ ∑ t, |partialDeriv j (fun z => F z t) x| := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun t => ?_
    rw [Real.norm_eq_abs, hcomp t]
    exact Finset.single_le_sum (f := fun t => |partialDeriv j (fun z => F z t) x|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ t)
  calc ‖v j‖ * ‖fderiv ℝ F x (Pi.single j 1)‖ ≤ ‖v‖ * ∑ t, |partialDeriv j (fun z => F z t) x| :=
        mul_le_mul hj hsum (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_comm _ _

omit [NeZero n] in
/-- `‖w - glue u‖² ≤ Σ_T Σₛ ∫_T (wₛ - (u_T)ₛ)²` (any element family). -/
theorem norm_sq_formL2_sub_glue_le (E : LocalElement n) (M : SimplicialMesh n)
    (hΩ : MeasurableSet M.domain) (k : ℕ) (w : contForms n) (u : E.Piecewise M k) :
    ‖formL2 hΩ M.isBounded_domain k w - E.glue M k u‖ ^ 2 ≤
      ∑ T ∈ M.simplices, ∑ s : formIdx n k, ∫ x in T.closedInterior,
        ((w : FormField n) x s.1 - E.extendPW M u T x s.1) ^ 2 := by
  have hc1 : ∀ T ∈ M.simplices, ∀ s : formIdx n k,
      Continuous (formComp (k := (k : ℤ)) (w : FormField n) s) :=
    fun _ _ s => continuous_formComp w.2 s
  have hc2 : ∀ T ∈ M.simplices, ∀ s : formIdx n k,
      Continuous (formComp (k := (k : ℤ)) (E.extendPW M u T) s) :=
    fun T hT s => continuous_formComp (E.contDiff_extendPW M u hT).continuous s
  have hc3 : ∀ T ∈ M.simplices, ∀ s : formIdx n k,
      Continuous fun x => formComp (k := (k : ℤ)) (w : FormField n) s x +
        (-1) * formComp (k := (k : ℤ)) (E.extendPW M u T) s x :=
    fun T hT s => (hc1 T hT s).add (continuous_const.mul (hc2 T hT s))
  have e : formL2 hΩ M.isBounded_domain k w - E.glue M k u =
      pieceL2 M M.domain (fun T s x => formComp (k := (k : ℤ)) (w : FormField n) s x +
        (-1) * formComp (k := (k : ℤ)) (E.extendPW M u T) s x) hc3 := by
    rw [pieceL2_add M M.domain (v := fun _ s x => formComp (k := (k : ℤ)) (w : FormField n) s x)
      (w := fun T s x => (-1) * formComp (k := (k : ℤ)) (E.extendPW M u T) s x) hc1
      (fun T hT s => continuous_const.mul (hc2 T hT s)),
      pieceL2_smul M M.domain (-1) hc2, ← pieceL2_formComp_eq_formL2 M hΩ k w,
      LocalElement.glue_apply, neg_one_smul, sub_eq_add_neg]
  rw [e]
  refine (norm_sq_pieceL2_le M M.domain _ hc3).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun s _ => ?_
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [formComp]; ring

end H1Lemmas

/-! ### The `H¹` approximation: the interpolation error of the smoothed field -/

namespace Poly

variable (S : PolySeq)

omit [NeZero n] in
/-- **The interpolation error of the smoothed field in terms of a gradient** (the second
ingredient of the `H¹` approximation): if the partial derivatives of the smoothed coefficients
are the smoothed fields of `L²` fields `g s` (the commutation of the smoother with the gradient,
`hcomm`), then `‖R y - Π_h R y‖² ≲ h_N² Σₛ ‖g s‖²`, through the pointwise interpolation error
`h_N sup_T ‖D (R y)‖`, Jensen's inequality for the mollifier, and bounded overlap. -/
theorem sq_norm_formL2_sub_smoothedInterp_le {N k : ℕ} {B D : ℝ} (hB : DofBound S n k B)
    (hB0 : 0 ≤ B) (hD : CoeffBound S n k D) (hD0 : 0 ≤ D) {γ : ℝ}
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p) (hγ1 : γ ≤ 1)
    (y : L2F ℝ (mesh n N).domain (formIdx n k))
    (g : formIdx n k → L2F ℝ (mesh n N).domain (formIdx n ((1 : ℕ) : ℤ)))
    (hcomm : ∀ s : formIdx n k, ∀ x ∈ closure (mesh n N).domain, ∀ j : Fin n,
      partialDeriv j (smoothExt (mesh n N).domain p ((y s : L2 ℝ (mesh n N).domain) :
        (Fin n → ℝ) → ℝ)) x =
        (smoothForm p (isOpen_mesh_domain n N).measurableSet (1 : ℕ) (g s) : FormField n) x {j}) :
    ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
        (Submodule.inclusion c1Forms_le_contForms
          (smoothForm p (isOpen_mesh_domain n N).measurableSet k y)) -
      (polyElement n S).smoothedInterp (mesh n N) p (isOpen_mesh_domain n N).measurableSet k y‖ ^ 2
      ≤ 2 ^ n * (1 + B * Module.finrank ℝ (S.space n k) * D) ^ 2 * (2 ^ (k + 1)) ^ 2 * n ^ 2 * 2 ^ n *
        (32 / γ) ^ n * ((6 ^ n * n.factorial : ℕ) : ℝ) * hN N ^ 2 * ∑ s, ‖g s‖ ^ 2 := by
  classical
  set h := hN N
  have hh : 0 < h := hN_pos N
  have hγ0 : 0 < γ := hp.gamma_pos
  set F : c1Forms n := smoothForm p (isOpen_mesh_domain n N).measurableSet k y
  have hFc1 : ContDiff ℝ 1 (F : FormField n) := mem_c1Forms.1 F.2
  set u := (polyElement n S).globalInterp (mesh n N) k (Submodule.inclusion c1Forms_le_contForms F)
  have hQ := (polyElement n S).smoothedInterp_natCast (mesh n N) p (isOpen_mesh_domain n N).measurableSet k y
  set Mρ := 1 / volume.real (Metric.closedBall (0 : Fin n → ℝ) p.bump.rIn)
  have hMρ : Mρ = (32 / (γ * h)) ^ n := by
    simp only [Mρ]
    rw [hp.rIn_eq, volume_real_closedBall_zero (by positivity)]
    rw [one_div, ← inv_pow]
    congr 1
    simp only [h]
    field_simp
    ring
  have hMρ0 : 0 ≤ Mρ := by rw [hMρ]; positivity
  set P := (Module.finrank ℝ (S.space n k) : ℝ)
  set Ci := 1 + B * P * D
  have hCi : 0 ≤ Ci := by positivity
  -- the local masses of the gradients
  set L : formIdx n k → Affine.Simplex ℝ (Fin n → ℝ) n → ℝ := fun s T => locMass (g s) T
  have hL0 : ∀ s T, 0 ≤ L s T := fun s T => locMass_nonneg _ _
  -- the derivative bound on a simplex
  have hder : ∀ T ∈ (mesh n N).simplices, ∀ x ∈ T.closedInterior,
      ‖iteratedFDeriv ℝ (0 + 1) (F : FormField n) x‖ ≤
        2 ^ (k + 1) * n * ∑ s, √(Mρ * L s T) := by
    intro T hT x hx
    have hxc : x ∈ closure (mesh n N).domain := (mesh n N).closedInterior_subset_closure hT hx
    rw [zero_add, norm_iteratedFDeriv_one]
    refine (norm_fderiv_le_sum_partialDeriv ((hFc1.differentiable one_ne_zero) x)).trans ?_
    have hterm : ∀ j : Fin n, ∀ s : formIdx n k,
        |partialDeriv j (fun z => (F : FormField n) z s.1) x| ≤ 2 ^ (k + 1) * √(Mρ * L s T) := by
      intro j s
      have hsc : ContDiff ℝ ∞ (smoothExt (mesh n N).domain p ((y s : L2 ℝ (mesh n N).domain) : (Fin n → ℝ) → ℝ)) :=
        contDiff_smoothExt ((memLp_indicator (isOpen_mesh_domain n N).measurableSet _).locallyIntegrable (by norm_num))
      have hF : (fun z => (F : FormField n) z s.1) = fun z => p.factor ^ (k : ℤ) *
          smoothExt (mesh n N).domain p ((y s : L2 ℝ (mesh n N).domain) : (Fin n → ℝ) → ℝ) z := by
        funext z
        change formExt (smoothCoeff p k y) s.1 z = _
        rw [formExt_val]; rfl
      rw [hF]
      have hpd : partialDeriv j (fun z => p.factor ^ (k : ℤ) *
          smoothExt (mesh n N).domain p ((y s : L2 ℝ (mesh n N).domain) : (Fin n → ℝ) → ℝ) z) x =
          p.factor ^ (k : ℤ) * partialDeriv j
            (smoothExt (mesh n N).domain p ((y s : L2 ℝ (mesh n N).domain) : (Fin n → ℝ) → ℝ)) x := by
        simp only [partialDeriv]
        rw [fderiv_const_mul ((hsc.differentiable (by simp)) x)]
        rfl
      rw [hpd, hcomm s x hxc j, abs_mul, zpow_natCast, abs_of_pos (pow_pos p.factor_pos k)]
      have h1 := abs_smoothForm_le (isOpen_mesh_domain n N).measurableSet p 1 (g s) x {j}
      have hfac1 : p.factor ^ 1 ≤ 2 := by rw [pow_one]; exact hp.factor_le_two hγ1
      calc p.factor ^ k * |(smoothForm p (isOpen_mesh_domain n N).measurableSet (1 : ℕ) (g s) : FormField n) x {j}|
          ≤ 2 ^ k * (2 * √(Mρ * L s T)) := by
            refine mul_le_mul (hp.pow_factor_le hγ1 k) (h1.trans ?_) (abs_nonneg _) (by positivity)
            refine mul_le_mul hfac1 (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ hMρ0))
              (Real.sqrt_nonneg _) (by norm_num)
            refine Finset.sum_le_sum fun s' _ => ?_
            refine setIntegral_mono_set (integrable_sq_indicator _).integrableOn
              (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall fun t ht => ?_)
            have hxc' : x ∈ closure (cubeDomain n) := by rwa [← mesh_domain n N]
            have h1' := hp.norm_dil_sub_le hxc'
            have h2 : dist t (p.center + p.factor • (x - p.center)) ≤ γ * h / 32 := by
              have := Metric.mem_closedBall.1 ht; rwa [hp.rOut_eq] at this
            refine Metric.mem_cthickening_of_dist_le t x _ _ hx ?_
            calc dist t x ≤ dist t (p.center + p.factor • (x - p.center)) +
                  dist (p.center + p.factor • (x - p.center)) x := dist_triangle _ _ _
              _ ≤ γ * h / 32 + γ * h / 4 := add_le_add h2 (by rw [dist_eq_norm]; exact h1')
              _ ≤ 2 * h := by nlinarith
        _ = 2 ^ (k + 1) * √(Mρ * L s T) := by ring
    calc ∑ j, ∑ t, |partialDeriv j (fun z => (F : FormField n) z t) x|
        = ∑ j, ∑ s : formIdx n k, |partialDeriv j (fun z => (F : FormField n) z s.1) x| := by
          refine Finset.sum_congr rfl fun j _ => sum_eq_sum_formIdx fun t ht => ?_
          have : (fun z => (F : FormField n) z t) = fun _ => 0 := by
            funext z; exact isDeg_smoothForm p (isOpen_mesh_domain n N).measurableSet k y z t ht
          rw [this]; simp [partialDeriv]
      _ ≤ ∑ _j : Fin n, ∑ s : formIdx n k, 2 ^ (k + 1) * √(Mρ * L s T) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun s _ => hterm j s
      _ = 2 ^ (k + 1) * n * ∑ s, √(Mρ * L s T) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← Finset.mul_sum]; ring
  -- the local `L²` error on a simplex
  have hloc : ∀ T ∈ (mesh n N).simplices, ∑ s : formIdx n k, ∫ x in T.closedInterior,
      ((F : FormField n) x s.1 - (polyElement n S).extendPW (mesh n N) (u : (polyElement n S).Piecewise (mesh n N) k)
        T x s.1) ^ 2 ≤
      2 ^ n * Ci ^ 2 * (2 ^ (k + 1)) ^ 2 * n ^ 2 * 2 ^ n * (32 / γ) ^ n * h ^ 2 * ∑ s, L s T := by
    intro T hT
    set MT := 2 ^ (k + 1) * n * ∑ s, √(Mρ * L s T)
    have hMT0 : 0 ≤ MT := by positivity
    have hpt : ∀ x ∈ T.closedInterior, ∀ t : Finset (Fin n),
        |(F : FormField n) x t - (polyElement n S).extendPW (mesh n N)
          (u : (polyElement n S).Piecewise (mesh n N) k) T x t| ≤ Ci * (h ^ (0 + 1) * MT) := by
      intro x hx t
      rw [(polyElement n S).extendPW_of_mem (mesh n N) _ hT]
      exact abs_sub_globalInterp_le S (polySpace_zero_le_space S k) hB hB0 hD ⟨T, hT⟩
        (s := 0) (hFc1.of_le le_rfl) (isDeg_smoothForm p (isOpen_mesh_domain n N).measurableSet k y) (hder T hT) hx t
    obtain ⟨m, σ, hmσ⟩ := mem_mesh_simplices.1 hT
    have hcont : ∀ s : formIdx n k, Continuous fun x => ((F : FormField n) x s.1 -
        (polyElement n S).extendPW (mesh n N) (u : (polyElement n S).Piecewise (mesh n N) k) T x s.1) ^ 2 :=
      fun s => (((continuous_apply s.1).comp hFc1.continuous).sub ((continuous_apply s.1).comp
        ((polyElement n S).contDiff_extendPW (mesh n N) _ hT).continuous)).pow 2
    have hs1 : ∀ s : formIdx n k, ∫ x in T.closedInterior, ((F : FormField n) x s.1 -
        (polyElement n S).extendPW (mesh n N) (u : (polyElement n S).Piecewise (mesh n N) k) T x s.1) ^ 2 ≤
        h ^ n * (Ci * (h ^ (0 + 1) * MT)) ^ 2 := by
      intro s
      have := integral_cubeSimplex_le m σ (hcont s) (fun x hx => by
        rw [hmσ] at hx
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hpt x hx s.1) 2) (fun x => sq_nonneg _)
      rwa [hmσ] at this
    have hCS : (∑ s : formIdx n k, √(Mρ * L s T)) ^ 2 ≤ 2 ^ n * ∑ s, Mρ * L s T := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (formIdx n k)))
        (f := fun s => √(Mρ * L s T))
      refine this.trans ?_
      rw [Finset.card_univ]
      refine mul_le_mul (card_formIdx_le _) (le_of_eq (Finset.sum_congr rfl fun s _ => ?_))
        (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      exact Real.sq_sqrt (mul_nonneg hMρ0 (hL0 s T))
    calc ∑ s : formIdx n k, ∫ x in T.closedInterior, ((F : FormField n) x s.1 -
          (polyElement n S).extendPW (mesh n N) (u : (polyElement n S).Piecewise (mesh n N) k) T x s.1) ^ 2
        ≤ ∑ _s : formIdx n k, h ^ n * (Ci * (h ^ (0 + 1) * MT)) ^ 2 :=
          Finset.sum_le_sum fun s _ => hs1 s
      _ = Fintype.card (formIdx n k) * (h ^ n * (Ci * (h ^ (0 + 1) * MT)) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ 2 ^ n * (h ^ n * (Ci * (h ^ (0 + 1) * MT)) ^ 2) :=
          mul_le_mul_of_nonneg_right (card_formIdx_le _) (by positivity)
      _ = 2 ^ n * Ci ^ 2 * (2 ^ (k + 1)) ^ 2 * n ^ 2 * h ^ 2 * h ^ n *
            (∑ s : formIdx n k, √(Mρ * L s T)) ^ 2 := by
          simp only [MT]; ring
      _ ≤ 2 ^ n * Ci ^ 2 * (2 ^ (k + 1)) ^ 2 * n ^ 2 * h ^ 2 * h ^ n *
            (2 ^ n * ∑ s, Mρ * L s T) := by gcongr
      _ = 2 ^ n * Ci ^ 2 * (2 ^ (k + 1)) ^ 2 * n ^ 2 * 2 ^ n * (h ^ n * Mρ) * h ^ 2 * ∑ s, L s T := by
          rw [← Finset.mul_sum]; ring
      _ = 2 ^ n * Ci ^ 2 * (2 ^ (k + 1)) ^ 2 * n ^ 2 * 2 ^ n * (32 / γ) ^ n * h ^ 2 * ∑ s, L s T := by
          rw [hMρ, ← mul_pow, show h * (32 / (γ * h)) = 32 / γ by field_simp]
  -- assembly over the simplices
  rw [hQ]
  refine (norm_sq_formL2_sub_glue_le (polyElement n S) (mesh n N) (isOpen_mesh_domain n N).measurableSet k _ _).trans ?_
  set K' := 2 ^ n * Ci ^ 2 * (2 ^ (k + 1)) ^ 2 * n ^ 2 * 2 ^ n * (32 / γ) ^ n * h ^ 2
  have hK' : 0 ≤ K' := by positivity
  calc ∑ T ∈ (mesh n N).simplices, ∑ s : formIdx n k, ∫ x in T.closedInterior,
        (((Submodule.inclusion c1Forms_le_contForms F : contForms n) : FormField n) x s.1 -
          (polyElement n S).extendPW (mesh n N) (u : (polyElement n S).Piecewise (mesh n N) k) T x s.1) ^ 2
      ≤ ∑ T ∈ (mesh n N).simplices, K' * ∑ s, L s T := Finset.sum_le_sum fun T hT => hloc T hT
    _ = K' * ∑ s, ∑ T ∈ (mesh n N).simplices, L s T := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ K' * ∑ s, ((6 ^ n * n.factorial : ℕ) : ℝ) * ‖g s‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => sum_locMass_le N (g s)) hK'
    _ = _ := by rw [← Finset.mul_sum]; simp only [K', Ci, P]; ring

end Poly

/-! ### The commutation of the smoother with the gradient -/

omit [NeZero n] in
/-- The smoothed coefficient of a `0`-form is the smoothed scalar. -/
theorem smoothForm_zero_apply_empty {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (p : SmoothingParam (Fin n → ℝ)) (f : L2 ℝ Ω) :
    (fun y => (smoothForm p hΩ ((0 : ℕ) : ℤ) (coeffForm f) : FormField n) y ∅) =
      smoothExt Ω p (f : (Fin n → ℝ) → ℝ) := by
  funext y
  rw [smoothForm_apply, formExt_of_card _ (by simp)]
  simp [smoothCoeff, coeffForm_apply]

omit [NeZero n] in
/-- **The smoother commutes with the gradient, maximal family**: for `f` in the domain of the
maximal gradient and `x ∈ cl Ω`, `∂ⱼ (R f)(x) = (R (∇ f))ⱼ(x)` (the `1`-form smoother, with
its factor `c`). -/
theorem partialDeriv_smoothExt_eq_of_maximal {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω)
    {x₀ : Fin n → ℝ} {s₀ : ℝ} (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ Ω)
    {p : SmoothingParam (Fin n → ℝ)} (hp : p.IsMaximal x₀ s₀) (f : L2 ℝ Ω)
    (hf : coeffForm f ∈ (((deRham ℝ n).maximalComplex hΩo).d 0 1).domain)
    {x : Fin n → ℝ} (hx : x ∈ closure Ω) (j : Fin n) :
    partialDeriv j (smoothExt Ω p (f : (Fin n → ℝ) → ℝ)) x =
      (smoothForm p hΩo.measurableSet (1 : ℕ)
        (((deRham ℝ n).maximalComplex hΩo).d 0 1 ⟨coeffForm f, hf⟩) : FormField n) x {j} := by
  have hd : ((deRham ℝ n).maximalComplex hΩo).d 0 1 = (extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal Ω :=
    deRham_maximalComplex_d hΩo 0
  have hval := LinearPMap.apply_eq_of_eq' hd ⟨coeffForm f, hf⟩
  have h := extDeriv_smoothForm_of_maximal p hΩo.measurableSet hΩo hstar hp 0
    ⟨coeffForm f, hd ▸ hf⟩ hx
  have h2 := congrFun h {j}
  rw [extDeriv_apply_singleton, smoothForm_zero_apply_empty] at h2
  rw [h2, hval]
  rfl

omit [NeZero n] in
/-- **The smoother commutes with the gradient, minimal family**: for `f` in the domain of the
minimal gradient (`H¹₀`), `∂ⱼ (R f) = (R (∇ f))ⱼ` everywhere. -/
theorem partialDeriv_smoothExt_eq_of_minimal {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω)
    (p : SmoothingParam (Fin n → ℝ)) (f : L2 ℝ Ω)
    (hf : coeffForm f ∈ (((deRham ℝ n).minimalComplex hΩo).d 0 1).domain)
    (x : Fin n → ℝ) (j : Fin n) :
    partialDeriv j (smoothExt Ω p (f : (Fin n → ℝ) → ℝ)) x =
      (smoothForm p hΩo.measurableSet (1 : ℕ)
        (((deRham ℝ n).minimalComplex hΩo).d 0 1 ⟨coeffForm f, hf⟩) : FormField n) x {j} := by
  have hd : ((deRham ℝ n).minimalComplex hΩo).d 0 1 = (extDerivOp ℝ n ((0 : ℕ) : ℤ)).minimal Ω :=
    deRham_minimalComplex_d hΩo 0
  have hval := LinearPMap.apply_eq_of_eq' hd ⟨coeffForm f, hf⟩
  have h := extDeriv_smoothForm_of_minimal p hΩo.measurableSet hΩo 0 ⟨coeffForm f, hd ▸ hf⟩ x
  have h2 := congrFun h {j}
  rw [extDeriv_apply_singleton, smoothForm_zero_apply_empty] at h2
  rw [h2, hval]
  rfl

/-! ### The `H¹` approximation on the mesh domain -/

omit [NeZero n] in
/-- `‖v‖ ≤ Σᵢ ‖vᵢ‖` in `L²(Ω; ℝ^ι)`. -/
theorem L2F.norm_le_sum_norm {Ω : Set (Fin n → ℝ)} {ι : Type*} [Fintype ι] (v : L2F ℝ Ω ι) :
    ‖v‖ ≤ ∑ i, ‖v i‖ := by
  have h : ‖v‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _
  exact le_of_pow_le_pow_left₀ two_ne_zero (Finset.sum_nonneg fun _ _ => norm_nonneg _) h

omit [NeZero n] in
theorem sqrt_sum_sq_le_sum {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    √(∑ i, a i ^ 2) ≤ ∑ i, a i := by
  rw [Real.sqrt_le_left (Finset.sum_nonneg fun i _ => ha i)]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => ha i

omit [NeZero n] in
/-- The smoothed form restricted to `Ω`: its coefficients are `cᵏ R(yₛ)`. -/
theorem formL2_smoothForm_apply {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (p : SmoothingParam (Fin n → ℝ)) (k : ℕ)
    (y : L2F ℝ Ω (formIdx n k)) (s : formIdx n k) :
    formL2 hΩ hb k (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ k y)) s =
      p.factor ^ k • smoothL2 p hΩ (y s) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_formL2 hΩ hb k (Submodule.inclusion c1Forms_le_contForms
    (smoothForm p hΩ k y)) s, Lp.coeFn_smul (p.factor ^ k) (smoothL2 p hΩ (y s)),
    coeFn_smoothL2 hΩ (y s)] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
  change formExt (smoothCoeff p k y) s.1 x = _
  rw [formExt_val]
  simp [smoothCoeff, zpow_natCast]

variable (n) in
/-- The constant of the `H¹` approximation of degree `k` of the sequence `S` at smoothing scale
`γ`: `γ √(n 2ⁿ) + 2ᵏ √K₂` (`Poly.sq_norm_formL2_sub_smoothedInterp_le`). -/
def h1Const (S : PolySeq) (k : ℕ) (γ : ℝ) : ℝ :=
  γ * √(n * 2 ^ n) + 2 ^ k * √(2 ^ n * (1 + dofConst n S k * Module.finrank ℝ (S.space n k) *
    coeffConst n S k) ^ 2 * (2 ^ (k + 1)) ^ 2 * n ^ 2 * 2 ^ n * (32 / γ) ^ n *
      ((6 ^ n * n.factorial : ℕ) : ℝ))

omit [NeZero n] in
theorem h1Const_nonneg (S : PolySeq) (k : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) : 0 ≤ h1Const n S k γ := by
  unfold h1Const; positivity

omit [NeZero n] in
/-- **`H¹` approximation by the higher-order spaces, maximal family, on the mesh domain**: for
`y ∈ L²(Ω; Λᵏ)` whose coefficients lie in the domain of the maximal gradient, the field
`v = c⁻ᵏ Q_N y ∈ Vₕᵏ` (`Q_N` the smoothed interpolant of the parameters `pMax γ`) satisfies
`‖y - v‖ ≤ K h_N Σₛ ‖∇ yₛ‖`, `K = h1Const` independent of `N`. -/
theorem exists_mem_V_near_grad_pMax (S : PolySeq) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (N k : ℕ) (y : L2F ℝ (mesh n N).domain (formIdx n k))
    (hy : ∀ s, coeffForm (y s) ∈
      (((deRham ℝ n).maximalComplex (isOpen_mesh_domain n N)).d 0 1).domain) :
    ∃ v ∈ (polyElement n S).V (mesh n N) k, ‖y - v‖ ≤ h1Const n S k γ * hN N *
      ∑ s, ‖((deRham ℝ n).maximalComplex (isOpen_mesh_domain n N)).d 0 1 ⟨coeffForm (y s), hy s⟩‖ := by
  set hΩo := isOpen_mesh_domain n N
  set hΩ := hΩo.measurableSet
  set p := pMax (n := n) γ hγ hγ1 N
  have hp := pMax_isMaximal (n := n) (γ := γ) (hγ := hγ) (hγ1 := hγ1) N
  have hpa := pMax_isAdm (n := n) (γ := γ) (hγ := hγ) (hγ1 := hγ1) N
  set g : formIdx n k → L2F ℝ (mesh n N).domain (formIdx n ((1 : ℕ) : ℤ)) := fun s =>
    ((deRham ℝ n).maximalComplex hΩo).d 0 1 ⟨coeffForm (y s), hy s⟩
  set h := hN N
  have hh : 0 < h := hN_pos N
  -- Term A on the mesh domain
  have hTA : ∀ s, ‖y s - smoothL2 p hΩ (y s)‖ ≤ γ * h * √(n * 2 ^ n) * ‖g s‖ := by
    have key : ∀ (Θ : Set (Fin n → ℝ)) (_ : Θ = cubeDomain n) (hΘo : IsOpen Θ) (f : L2 ℝ Θ)
        (hf : coeffForm f ∈ (((deRham ℝ n).maximalComplex hΘo).d 0 1).domain),
        ‖f - smoothL2 p hΘo.measurableSet f‖ ≤
          γ * h * √(n * 2 ^ n) * ‖((deRham ℝ n).maximalComplex hΘo).d 0 1 ⟨coeffForm f, hf⟩‖ := by
      rintro Θ rfl hΘo f hf
      exact norm_sub_smoothL2_le_pMax hγ hγ1 N f hf
    exact fun s => key _ (mesh_domain n N) hΩo (y s) (hy s)
  -- Term B
  have hTB := Poly.sq_norm_formL2_sub_smoothedInterp_le S (dofBound_dofConst S k)
    (dofConst_nonneg S k) (coeffBound_coeffConst S k) (coeffConst_nonneg S k) hpa hγ1 y g
    fun s x hx j => partialDeriv_smoothExt_eq_of_maximal hΩo (starBall_mesh n N) hp (y s) (hy s)
      hx j
  set K₂ := 2 ^ n * (1 + dofConst n S k * Module.finrank ℝ (S.space n k) *
    coeffConst n S k) ^ 2 * (2 ^ (k + 1)) ^ 2 * n ^ 2 * 2 ^ n * (32 / γ) ^ n *
      ((6 ^ n * n.factorial : ℕ) : ℝ)
  have hK₂ : 0 ≤ K₂ := by
    have := dofConst_nonneg (n := n) S k; have := coeffConst_nonneg (n := n) S k; positivity
  set Fl := formL2 hΩ (mesh n N).isBounded_domain k
    (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ k y))
  set Q := (polyElement n S).smoothedInterp (mesh n N) p hΩ k y
  have hTB' : ‖Fl - Q‖ ≤ √K₂ * h * ∑ s, ‖g s‖ := by
    have h1 : ‖Fl - Q‖ ≤ √(K₂ * h ^ 2 * ∑ s, ‖g s‖ ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg (Fl - Q))]
      exact Real.sqrt_le_sqrt (by simpa only [K₂] using hTB)
    refine h1.trans ?_
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hK₂, Real.sqrt_sq hh.le]
    gcongr
    exact sqrt_sum_sq_le_sum _ fun s => norm_nonneg _
  have hc0 : 0 < p.factor := p.factor_pos
  have hcinv : (p.factor ^ k)⁻¹ ≤ 2 ^ k := by
    rw [inv_le_iff_one_le_mul₀ (pow_pos hc0 k), ← mul_pow]
    exact one_le_pow₀ (by linarith [p.half_le_factor])
  refine ⟨(p.factor ^ k)⁻¹ • Q, Submodule.smul_mem _ _
    ((polyElement n S).smoothedInterp_mem_V (mesh n N) p hΩ k y), ?_⟩
  have e : y - (p.factor ^ k)⁻¹ • Q = (y - (p.factor ^ k)⁻¹ • Fl) + (p.factor ^ k)⁻¹ • (Fl - Q) := by
    rw [smul_sub]; abel
  have hA : ‖y - (p.factor ^ k)⁻¹ • Fl‖ ≤ γ * h * √(n * 2 ^ n) * ∑ s, ‖g s‖ := by
    refine (L2F.norm_le_sum_norm _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have : (y - (p.factor ^ k)⁻¹ • Fl) s = y s - smoothL2 p hΩ (y s) := by
      rw [PiLp.sub_apply, PiLp.smul_apply, formL2_smoothForm_apply, smul_smul,
        inv_mul_cancel₀ (pow_pos hc0 k).ne', one_smul]
    rw [this]
    exact hTA s
  rw [e]
  calc ‖(y - (p.factor ^ k)⁻¹ • Fl) + (p.factor ^ k)⁻¹ • (Fl - Q)‖
      ≤ ‖y - (p.factor ^ k)⁻¹ • Fl‖ + ‖(p.factor ^ k)⁻¹ • (Fl - Q)‖ := norm_add_le _ _
    _ ≤ γ * h * √(n * 2 ^ n) * ∑ s, ‖g s‖ + 2 ^ k * (√K₂ * h * ∑ s, ‖g s‖) := by
        refine add_le_add hA ?_
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (pow_pos hc0 k).le)]
        exact mul_le_mul hcinv hTB' (norm_nonneg _) (by positivity)
    _ = h1Const n S k γ * h * ∑ s, ‖g s‖ := by simp only [h1Const, K₂]; ring

omit [NeZero n] in
/-- **`H¹` approximation by the higher-order spaces with vanishing boundary DOFs, on the mesh
domain**: for `y` whose coefficients lie in the domain of the minimal gradient (their extensions
by zero are in `H¹(ℝⁿ)`), `v = c⁻ᵏ Q̊_N y ∈ V̊ₕᵏ` (parameters `pMin γ`) satisfies
`‖y - v‖ ≤ K h_N Σₛ ‖∇ yₛ‖`. -/
theorem exists_mem_V₀_near_grad_pMin (S : PolySeq) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (N k : ℕ) (y : L2F ℝ (mesh n N).domain (formIdx n k))
    (hy : ∀ s, coeffForm (y s) ∈
      (((deRham ℝ n).minimalComplex (isOpen_mesh_domain n N)).d 0 1).domain) :
    ∃ v ∈ (polyElement n S).V₀ (mesh n N) k, ‖y - v‖ ≤ h1Const n S k γ * hN N *
      ∑ s, ‖((deRham ℝ n).minimalComplex (isOpen_mesh_domain n N)).d 0 1 ⟨coeffForm (y s), hy s⟩‖ := by
  set hΩo := isOpen_mesh_domain n N
  set hΩ := hΩo.measurableSet
  set p := pMin (n := n) γ hγ N
  have hp := pMin_isMinimal (n := n) (γ := γ) (hγ := hγ) N
  have hpa := pMin_isAdm (n := n) (γ := γ) (hγ := hγ) N
  set g : formIdx n k → L2F ℝ (mesh n N).domain (formIdx n ((1 : ℕ) : ℤ)) := fun s =>
    ((deRham ℝ n).minimalComplex hΩo).d 0 1 ⟨coeffForm (y s), hy s⟩
  set h := hN N
  have hh : 0 < h := hN_pos N
  have hTA : ∀ s, ‖y s - smoothL2 p hΩ (y s)‖ ≤ γ * h * √(n * 2 ^ n) * ‖g s‖ := by
    have key : ∀ (Θ : Set (Fin n → ℝ)) (_ : Θ = cubeDomain n) (hΘo : IsOpen Θ) (f : L2 ℝ Θ)
        (hf : coeffForm f ∈ (((deRham ℝ n).minimalComplex hΘo).d 0 1).domain),
        ‖f - smoothL2 p hΘo.measurableSet f‖ ≤
          γ * h * √(n * 2 ^ n) * ‖((deRham ℝ n).minimalComplex hΘo).d 0 1 ⟨coeffForm f, hf⟩‖ := by
      rintro Θ rfl hΘo f hf
      exact norm_sub_smoothL2_le_pMin hγ N f hf
    exact fun s => key _ (mesh_domain n N) hΩo (y s) (hy s)
  have hTB := Poly.sq_norm_formL2_sub_smoothedInterp_le S (dofBound_dofConst S k)
    (dofConst_nonneg S k) (coeffBound_coeffConst S k) (coeffConst_nonneg S k) hpa hγ1 y g
    fun s x _ j => partialDeriv_smoothExt_eq_of_minimal hΩo p (y s) (hy s) x j
  set K₂ := 2 ^ n * (1 + dofConst n S k * Module.finrank ℝ (S.space n k) *
    coeffConst n S k) ^ 2 * (2 ^ (k + 1)) ^ 2 * n ^ 2 * 2 ^ n * (32 / γ) ^ n *
      ((6 ^ n * n.factorial : ℕ) : ℝ)
  have hK₂ : 0 ≤ K₂ := by
    have := dofConst_nonneg (n := n) S k; have := coeffConst_nonneg (n := n) S k; positivity
  set Fl := formL2 hΩ (mesh n N).isBounded_domain k
    (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ k y))
  set Q := (polyElement n S).smoothedInterp (mesh n N) p hΩ k y
  have hTB' : ‖Fl - Q‖ ≤ √K₂ * h * ∑ s, ‖g s‖ := by
    have h1 : ‖Fl - Q‖ ≤ √(K₂ * h ^ 2 * ∑ s, ‖g s‖ ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg (Fl - Q))]
      exact Real.sqrt_le_sqrt (by simpa only [K₂] using hTB)
    refine h1.trans ?_
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hK₂, Real.sqrt_sq hh.le]
    gcongr
    exact sqrt_sum_sq_le_sum _ fun s => norm_nonneg _
  have hc0 : 0 < p.factor := p.factor_pos
  have hcinv : (p.factor ^ k)⁻¹ ≤ 2 ^ k := by
    rw [inv_le_iff_one_le_mul₀ (pow_pos hc0 k), ← mul_pow]
    exact one_le_pow₀ (by linarith [p.half_le_factor])
  refine ⟨(p.factor ^ k)⁻¹ • Q, Submodule.smul_mem _ _
    ((polyElement n S).smoothedInterp_mem_V₀ (mesh n N) p hΩo
      (mesh_domain n N ▸ isBounded_cubeDomain n) (starBall_mesh n N) hp k y), ?_⟩
  have e : y - (p.factor ^ k)⁻¹ • Q = (y - (p.factor ^ k)⁻¹ • Fl) + (p.factor ^ k)⁻¹ • (Fl - Q) := by
    rw [smul_sub]; abel
  have hA : ‖y - (p.factor ^ k)⁻¹ • Fl‖ ≤ γ * h * √(n * 2 ^ n) * ∑ s, ‖g s‖ := by
    refine (L2F.norm_le_sum_norm _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have : (y - (p.factor ^ k)⁻¹ • Fl) s = y s - smoothL2 p hΩ (y s) := by
      rw [PiLp.sub_apply, PiLp.smul_apply, formL2_smoothForm_apply, smul_smul,
        inv_mul_cancel₀ (pow_pos hc0 k).ne', one_smul]
    rw [this]
    exact hTA s
  rw [e]
  calc ‖(y - (p.factor ^ k)⁻¹ • Fl) + (p.factor ^ k)⁻¹ • (Fl - Q)‖
      ≤ ‖y - (p.factor ^ k)⁻¹ • Fl‖ + ‖(p.factor ^ k)⁻¹ • (Fl - Q)‖ := norm_add_le _ _
    _ ≤ γ * h * √(n * 2 ^ n) * ∑ s, ‖g s‖ + 2 ^ k * (√K₂ * h * ∑ s, ‖g s‖) := by
        refine add_le_add hA ?_
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (pow_pos hc0 k).le)]
        exact mul_le_mul hcinv hTB' (norm_nonneg _) (by positivity)
    _ = h1Const n S k γ * h * ∑ s, ‖g s‖ := by simp only [h1Const, K₂]; ring

/-! ### The `H¹` approximation of the smoothed projections on the cube -/

/-- **`H¹` approximation by the higher-order spaces on the cube**: for `y ∈ L²(Q; Λᵏ)` whose
coefficients lie in the domain of the maximal gradient (`H¹(Q)`), some `v ∈ Vₕᵏ` satisfies
`‖y - v‖ ≤ K h_N Σₛ ‖∇ yₛ‖` with `K = h1Const n S k γ` independent of `N` (any `γ ∈ (0, 1]`). -/
theorem exists_mem_poly_near_grad (S : PolySeq) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N k : ℕ)
    (y : L2F ℝ (cubeDomain n) (formIdx n k))
    (hy : ∀ s, coeffForm (y s) ∈ ((complex n).d 0 1).domain) :
    ∃ v ∈ (poly n S N).V k, ‖y - v‖ ≤ h1Const n S k γ * meshSize N *
      ∑ s, ‖(complex n).d 0 1 ⟨coeffForm (y s), hy s⟩‖ := by
  rw [← hN_eq_meshSize]
  exact (deRham ℝ n).maximalSubcomplexOfEq_induction (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n) (S.subcomplex (mesh n N) (isOpen_mesh_domain n N))
    (fun Θ hΘ S' => ∀ y : L2F ℝ Θ (formIdx n k),
      ∀ hy : (∀ s, coeffForm (y s) ∈ (((deRham ℝ n).maximalComplex hΘ).d 0 1).domain),
      ∃ v ∈ S'.V k, ‖y - asForm n v‖ ≤ h1Const n S k γ * hN N *
        ∑ s, ‖((deRham ℝ n).maximalComplex hΘ).d 0 1 ⟨coeffForm (y s), hy s⟩‖)
    (fun y hy => exists_mem_V_near_grad_pMax S hγ hγ1 N k y hy) y hy

/-- **`H¹` approximation by the higher-order spaces with vanishing boundary DOFs**: for `y` whose
coefficients lie in the domain of the minimal gradient (`H¹₀(Q)`), some `v ∈ V̊ₕᵏ` satisfies
`‖y - v‖ ≤ K h_N Σₛ ‖∇ yₛ‖`. -/
theorem exists_mem_polyMin_near_grad (S : PolySeq) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (N k : ℕ) (y : L2F ℝ (cubeDomain n) (formIdx n k))
    (hy : ∀ s, coeffForm (y s) ∈ ((complexMin n).d 0 1).domain) :
    ∃ v ∈ (polyMin n S N).V k, ‖y - v‖ ≤ h1Const n S k γ * meshSize N *
      ∑ s, ‖(complexMin n).d 0 1 ⟨coeffForm (y s), hy s⟩‖ := by
  rw [← hN_eq_meshSize]
  exact (deRham ℝ n).minimalSubcomplexOfEq_induction (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n)
    (S.subcomplexMin (mesh n N) (isOpen_mesh_domain n N) (center n) (strictStar_mesh n N))
    (fun Θ hΘ S' => ∀ y : L2F ℝ Θ (formIdx n k),
      ∀ hy : (∀ s, coeffForm (y s) ∈ (((deRham ℝ n).minimalComplex hΘ).d 0 1).domain),
      ∃ v ∈ S'.V k, ‖y - asForm n v‖ ≤ h1Const n S k γ * hN N *
        ∑ s, ‖((deRham ℝ n).minimalComplex hΘ).d 0 1 ⟨coeffForm (y s), hy s⟩‖)
    (fun y hy => exists_mem_V₀_near_grad_pMin S hγ hγ1 N k y hy) y hy

/-- `‖y - π y‖ ≤ (1 + 2C) ‖y - v‖` for a cochain projection bounded by `2C` and `v ∈ Vₕ`. -/
theorem norm_sub_π_le_of_mem {𝕜 : Type*} [RCLike 𝕜] {V : ℤ → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, CompleteSpace (V i)]
    {H : HilbertComplex 𝕜 (ComplexShape.up ℤ) V} {S' : H.Subcomplex} (π : S'.CochainProjection)
    {C : ℝ} {i : ℤ} (hπ : ∀ x, ‖π.π i x‖ ≤ 2 * C * ‖x‖) {y v : V i} (hv : v ∈ S'.V i) :
    ‖y - π.π i y‖ ≤ (1 + 2 * C) * ‖y - v‖ := by
  have e : y - π.π i y = (y - v) - π.π i (y - v) := by
    rw [map_sub, π.proj i v hv]; abel
  rw [e]
  calc ‖(y - v) - π.π i (y - v)‖ ≤ ‖y - v‖ + ‖π.π i (y - v)‖ := norm_sub_le _ _
    _ ≤ ‖y - v‖ + 2 * C * ‖y - v‖ := add_le_add le_rfl (hπ _)
    _ = (1 + 2 * C) * ‖y - v‖ := by ring

/-- **`H¹` approximation of the smoothed projections** (the estimate needed by the BGG
discretization): under the smoothing estimates of `S`, for `y ∈ L²(Q; Λᵏ)` whose coefficients
lie in `H¹(Q)` (the domain of the maximal gradient),
`‖y - π_N y‖ ≤ (1 + 2C) K h_N Σₛ ‖∇ yₛ‖`, `K = h1Const n S k 1`, independent of `N`. The proof
compares `y` with `c⁻ᵏ Q_N y`: mollification at scale `h_N` (`‖f - R f‖ ≲ h ‖∇f‖`,
`norm_sub_smoothL2_le_pMax`, from the fundamental theorem of calculus along segments and a
change of variables), the local interpolation error of the smoothed field
(`Poly.sq_norm_formL2_sub_smoothedInterp_le`), and the uniform bound of `π_N`. -/
theorem PolySmoothingEstimates.norm_sub_proj_le_grad {S : PolySeq}
    {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : PolySmoothingEstimates n S p C) (N k : ℕ)
    (y : L2F ℝ (cubeDomain n) (formIdx n k))
    (hy : ∀ s, coeffForm (y s) ∈ ((complex n).d 0 1).domain) :
    ‖y - (hE.proj N).π k y‖ ≤ (1 + 2 * C) * h1Const n S k 1 * meshSize N *
      ∑ s, ‖(complex n).d 0 1 ⟨coeffForm (y s), hy s⟩‖ := by
  obtain ⟨v, hv, hyv⟩ := exists_mem_poly_near_grad S one_pos le_rfl N k y hy
  refine (norm_sub_π_le_of_mem (hE.proj N) (hE.norm_proj_le N k) hv).trans ?_
  have := hE.two_mul_nonneg
  calc (1 + 2 * C) * ‖y - v‖ ≤ (1 + 2 * C) * (h1Const n S k 1 * meshSize N *
        ∑ s, ‖(complex n).d 0 1 ⟨coeffForm (y s), hy s⟩‖) :=
        mul_le_mul_of_nonneg_left hyv (by linarith)
    _ = _ := by ring

/-- **`H¹₀` approximation of the smoothed projections with vanishing boundary DOFs**: for `y`
whose coefficients lie in `H¹₀(Q)` (extend by zero to `H¹(ℝⁿ)`),
`‖y - π̊_N y‖ ≤ (1 + 2C) K h_N Σₛ ‖∇ yₛ‖`. -/
theorem PolySmoothingEstimatesMin.norm_sub_proj_le_grad {S : PolySeq}
    {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : PolySmoothingEstimatesMin n S p C)
    (N k : ℕ) (y : L2F ℝ (cubeDomain n) (formIdx n k))
    (hy : ∀ s, coeffForm (y s) ∈ ((complexMin n).d 0 1).domain) :
    ‖y - (hE.proj N).π k y‖ ≤ (1 + 2 * C) * h1Const n S k 1 * meshSize N *
      ∑ s, ‖(complexMin n).d 0 1 ⟨coeffForm (y s), hy s⟩‖ := by
  obtain ⟨v, hv, hyv⟩ := exists_mem_polyMin_near_grad S one_pos le_rfl N k y hy
  refine (norm_sub_π_le_of_mem (hE.proj N) (hE.norm_proj_le N k) hv).trans ?_
  have := hE.two_mul_nonneg
  calc (1 + 2 * C) * ‖y - v‖ ≤ (1 + 2 * C) * (h1Const n S k 1 * meshSize N *
        ∑ s, ‖(complexMin n).d 0 1 ⟨coeffForm (y s), hy s⟩‖) :=
        mul_le_mul_of_nonneg_left hyv (by linarith)
    _ = _ := by ring

/-- **The rows of Tables 5.1/6.1 with one smoother, with the `H¹₀` approximation**: the
projections `π̊_N` of the top row (`PolySeq.lowestOrder`) and the bottom row
(`PolySeq.lagrangeP2`) on `(0, ½)³`, built from the same smoothed fields, are uniformly bounded
in `L²` and every graph norm and satisfy `‖y - π̊_N y‖ ≤ K_k h_N Σₛ ‖∇ yₛ‖` for `y` with `H¹₀(Q)`
coefficients. -/
theorem tableRows_H1 :
    ∃ (p : ℕ → SmoothingParam (Fin 3 → ℝ)) (C : ℝ)
      (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
      (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C),
      (∀ N i x, ‖(hT.proj N).π i x‖ ≤ 2 * C * ‖x‖) ∧
      (∀ N i j, (hT.proj N).IsGraphBounded i j (2 * C)) ∧
      (∀ N i x, ‖(hB.proj N).π i x‖ ≤ 2 * C * ‖x‖) ∧
      (∀ N i j, (hB.proj N).IsGraphBounded i j (2 * C)) ∧
      (∀ (N k : ℕ) (y : L2F ℝ (cubeDomain 3) (formIdx 3 k))
        (hy : ∀ s, coeffForm (y s) ∈ ((complexMin 3).d 0 1).domain),
        ‖y - (hT.proj N).π k y‖ ≤ (1 + 2 * C) * h1Const 3 PolySeq.lowestOrder k 1 * meshSize N *
          ∑ s, ‖(complexMin 3).d 0 1 ⟨coeffForm (y s), hy s⟩‖) ∧
      ∀ (N k : ℕ) (y : L2F ℝ (cubeDomain 3) (formIdx 3 k))
        (hy : ∀ s, coeffForm (y s) ∈ ((complexMin 3).d 0 1).domain),
        ‖y - (hB.proj N).π k y‖ ≤ (1 + 2 * C) * h1Const 3 PolySeq.lagrangeP2 k 1 * meshSize N *
          ∑ s, ‖(complexMin 3).d 0 1 ⟨coeffForm (y s), hy s⟩‖ := by
  obtain ⟨p, C, hT, hB, h1, h2, h3, h4, -, -⟩ := tableRows_uniform_cochainProjection
  exact ⟨p, C, hT, hB, h1, h2, h3, h4, hT.norm_sub_proj_le_grad, hB.norm_sub_proj_le_grad⟩

end Feec.Models.Cube.FEM
