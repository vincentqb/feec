module

public import Feec.Models.Cube.PolyFiniteElementConvergence

/-!
# Rates of convergence of the higher-order finite element methods on the cube

DOCSTRING
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff

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

/-- `S` has order `h^{s+1}` if `s + 1 ≤ r_k` in every degree `k ≤ n` (both families). -/
theorem polyOrder_of_le_deg {S : PolySeq} {s : ℕ} (h : ∀ k ≤ n, s + 1 ≤ S.deg k) :
    PolyOrder n S s := by
  intro k
  by_cases hk : k ≤ n
  · exact Poly.polySpace_le_space S (h k hk)
  · rw [polySpace_eq_bot_of_lt (by omega)]; exact bot_le

/-- `S` has order `h^{s+1}` if in every degree `k ≤ n` either the full family `P_{r_k}Λᵏ` is used
with `s ≤ r_k`, or `s + 1 ≤ r_k`. -/
theorem polyOrder_of_full {S : PolySeq} {s : ℕ}
    (h : ∀ k ≤ n, (S.kind k = .full ∧ s ≤ S.deg k) ∨ s + 1 ≤ S.deg k) : PolyOrder n S s := by
  intro k
  by_cases hk : k ≤ n
  · rcases h k hk with ⟨hf, hs⟩ | hs
    · exact Poly.polySpace_le_space_of_full S hf hs
    · exact Poly.polySpace_le_space S hs
  · rw [polySpace_eq_bot_of_lt (by omega)]; exact bot_le

/-- The constant trimmed sequence `P_r⁻Λ` has order `h^r`. -/
theorem polyOrder_trimmed {r : ℕ} (hr : 1 ≤ r) : PolyOrder n (PolySeq.trimmed r hr) (r - 1) :=
  polyOrder_of_le_deg fun k _ => by
    change r - 1 + 1 ≤ r
    omega

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
`IsCsForm`. -/
def IsCsFormMin (s : ℕ) (j : ℤ) (L : ℝ) (x : L2F ℝ (cubeDomain n) (formIdx n j)) : Prop :=
  j < 0 ∨ ∃ k : ℕ, (k : ℤ) = j ∧ ∃ w : FormField n,
    ∃ hw : ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w, (∀ y, IsDeg k (w y)) ∧
    (∀ y ∉ cubeDomain n, w y = 0) ∧
    (∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L) ∧
    (∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L) ∧
    x = formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) j ⟨w, hw.continuous⟩

/-- **Every `C^{s+2}` form is `IsCsForm s`** for some bound `L ≥ 0` (the hypotheses of the rate
theorems are satisfiable). -/
theorem exists_isCsForm (s : ℕ) {k : ℕ} {w : FormField n}
    (hw : ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w) (hdeg : ∀ y, IsDeg k (w y)) :
    ∃ L, 0 ≤ L ∧ IsCsForm s (k : ℤ) L
      (formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
        ⟨w, hw.continuous⟩) := by
  obtain ⟨L, hL0, hL⟩ := exists_bound_iteratedFDeriv (m := s + 1)
    (hw.of_le (by exact_mod_cast Nat.le_succ (s + 1)))
  have hw' : ContDiff ℝ (((s + 1 : ℕ) : WithTop ℕ∞) + 1) w := by exact_mod_cast hw
  have hdw : ContDiff ℝ ((s + 1 : ℕ) : WithTop ℕ∞) (extDeriv w) := contDiff_extDeriv hw'
  obtain ⟨L', hL'0, hL'⟩ := exists_bound_iteratedFDeriv (m := s + 1) hdw
  exact ⟨max L L', le_max_of_le_left hL0, Or.inr ⟨k, rfl, w, hw, hdeg,
    fun y hy => (hL y hy).trans (le_max_left _ _),
    fun y hy => (hL' y hy).trans (le_max_right _ _), rfl⟩⟩

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
theorem IsCsForm.exists_mem_poly_le {S : PolySeq} {s : ℕ} (hS : PolyOrder n S s) {j : ℤ}
    {L : ℝ} {x : L2F ℝ (cubeDomain n) (formIdx n j)} (hx : IsCsForm s j L x) (hL0 : 0 ≤ L)
    (N : ℕ) :
    ∃ v, ∃ hv : v ∈ (poly n S N).V j, ‖x - v‖ ≤ polyInterpBound n S j * L * meshSize N ^ (s + 1) ∧
      ∀ j' (hxj : x ∈ ((complex n).d j j').domain),
        ‖(complex n).d j j' ⟨x - v, Submodule.sub_mem _ hxj ((poly n S N).le_domain j j' hv)⟩‖ ≤
          polyInterpBound n S j * L * meshSize N ^ (s + 1) := by
  have hh := pow_nonneg (meshSize_pos N).le (s + 1)
  have hB0 := mul_nonneg (mul_nonneg (polyInterpBound_nonneg (n := n) S j) hL0) hh
  rcases hx with hj | ⟨k, rfl, w, hw, hdeg, hL, hL', rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = Int.negSucc k := ⟨(-j - 1).toNat, by omega⟩
    have := LocalElement.subsingleton_L2F_negSucc (cubeDomain n) (n := n) k
    refine ⟨0, Submodule.zero_mem _, ?_, fun j' hxj => ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hB0
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := FEM.exists_mem_poly_le S N k s (hS k) (hS (k + 1)) hw hdeg hL hL'
  obtain ⟨hdom, hval⟩ := formL2_mem_domain k
    (hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1))) hdeg
  have hA0 := mul_nonneg (polyInterpConst_nonneg (n := n) S k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (polyInterpConst_nonneg (n := n) S (k + 1)) (mul_nonneg hh hL0)
  have e : polyInterpBound n S k * L * meshSize N ^ (s + 1) =
      polyInterpConst n S k * (meshSize N ^ (s + 1) * L) +
        polyInterpConst n S (k + 1) * (meshSize N ^ (s + 1) * L) := by
    simp only [polyInterpBound, Int.toNat_natCast]; ring
  refine ⟨v, hv, ?_, fun j' hxj => ?_⟩
  · rw [e]; linarith
  by_cases hj : (k : ℤ) + 1 = j'
  · subst hj
    have e' : (complex n).d k (k + 1)
        ⟨_ - v, Submodule.sub_mem _ hxj ((poly n S N).le_domain k (k + 1) hv)⟩ =
        (complex n).d k (k + 1) ⟨_, hdom⟩ - (complex n).d k (k + 1) ⟨v, hdv⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [e', hval, e]
    linarith
  · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]
    exact hB0

/-- **Graph-norm distance of a smooth form to the higher-order space**:
`dist_V(σ, Vₕʲ) ≤ 2 B_j L h_N^{s+1}`. -/
theorem IsCsForm.infDist_domainSub_poly_le {S : PolySeq} {s : ℕ} (hS : PolyOrder n S s) {j : ℤ}
    {L : ℝ} {σ : (complex n).domainSpace j} (hσ : IsCsForm s j L ((complex n).domainIncl j σ))
    (hL0 : 0 ≤ L) (N : ℕ) :
    Metric.infDist σ ((poly n S N).domainSub j) ≤
      2 * (polyInterpBound n S j * L * meshSize N ^ (s + 1)) := by
  obtain ⟨v, hv, h1, h2⟩ := hσ.exists_mem_poly_le hS hL0 N
  refine (Subcomplex.infDist_domainSub_le (S := poly n S N)
    (rfl : (ComplexShape.up ℤ).Rel j (j + 1)) σ hv).trans ?_
  have e : (complex n).d j (j + 1) ((complex n).domainCoord j (j + 1) σ) -
      (complex n).d j (j + 1) ⟨v, (poly n S N).le_domain j (j + 1) hv⟩ =
      (complex n).d j (j + 1) ⟨(complex n).domainIncl j σ - v,
        Submodule.sub_mem _ ((complex n).domainCoord j (j + 1) σ).2
          ((poly n S N).le_domain j (j + 1) hv)⟩ := by
    rw [← LinearPMap.map_sub]; rfl
  rw [e, two_mul]
  exact add_le_add h1 (h2 (j + 1) ((complex n).domainCoord j (j + 1) σ).2)

/-- **Degreewise interpolation error of order `s + 1` with vanishing boundary DOFs** in `H̊Λ(Q)`. -/
theorem IsCsFormMin.exists_mem_polyMin_le {S : PolySeq} {s : ℕ} (hS : PolyOrder n S s) {j : ℤ}
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
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = Int.negSucc k := ⟨(-j - 1).toNat, by omega⟩
    have := LocalElement.subsingleton_L2F_negSucc (cubeDomain n) (n := n) k
    refine ⟨0, Submodule.zero_mem _, ?_, fun j' hxj => ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hB0
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ :=
    FEM.exists_mem_polyMin_le S N k s (hS k) (hS (k + 1)) hw hdeg hsupp hL hL'
  have hA0 := mul_nonneg (polyInterpConst_nonneg (n := n) S k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (polyInterpConst_nonneg (n := n) S (k + 1)) (mul_nonneg hh hL0)
  have e : polyInterpBound n S k * L * meshSize N ^ (s + 1) =
      polyInterpConst n S k * (meshSize N ^ (s + 1) * L) +
        polyInterpConst n S (k + 1) * (meshSize N ^ (s + 1) * L) := by
    simp only [polyInterpBound, Int.toNat_natCast]; ring
  refine ⟨v, hv, ?_, fun j' hxj => ?_⟩
  · rw [e]; linarith
  by_cases hj : (k : ℤ) + 1 = j'
  · subst hj
    have e' : (complexMin n).d k (k + 1)
        ⟨_ - v, Submodule.sub_mem _ hxj ((polyMin n S N).le_domain k (k + 1) hv)⟩ =
        (complexMin n).d k (k + 1) ⟨_, hxj⟩ - (complexMin n).d k (k + 1) ⟨v, hdv⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [e', complexMin_d_formL2 k (hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1))) hdeg
      ⟨_, hxj⟩ rfl, e]
    linarith
  · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]
    exact hB0

/-- **Graph-norm distance of a smooth form vanishing outside `Q` to `V̊ₕʲ`**:
`dist_V(σ, V̊ₕʲ) ≤ 2 B_j L h_N^{s+1}`. -/
theorem IsCsFormMin.infDist_domainSub_polyMin_le {S : PolySeq} {s : ℕ} (hS : PolyOrder n S s)
    {j : ℤ} {L : ℝ} {σ : (complexMin n).domainSpace j}
    (hσ : IsCsFormMin s j L ((complexMin n).domainIncl j σ)) (hL0 : 0 ≤ L) (N : ℕ) :
    Metric.infDist σ ((polyMin n S N).domainSub j) ≤
      2 * (polyInterpBound n S j * L * meshSize N ^ (s + 1)) := by
  obtain ⟨v, hv, h1, h2⟩ := hσ.exists_mem_polyMin_le hS hL0 N
  refine (Subcomplex.infDist_domainSub_le (S := polyMin n S N)
    (rfl : (ComplexShape.up ℤ).Rel j (j + 1)) σ hv).trans ?_
  have e : (complexMin n).d j (j + 1) ((complexMin n).domainCoord j (j + 1) σ) -
      (complexMin n).d j (j + 1) ⟨v, (polyMin n S N).le_domain j (j + 1) hv⟩ =
      (complexMin n).d j (j + 1) ⟨(complexMin n).domainIncl j σ - v,
        Submodule.sub_mem _ ((complexMin n).domainCoord j (j + 1) σ).2
          ((polyMin n S N).le_domain j (j + 1) hv)⟩ := by
    rw [← LinearPMap.map_sub]; rfl
  rw [e, two_mul]
  exact add_le_add h1 (h2 (j + 1) ((complexMin n).domainCoord j (j + 1) σ).2)

/-! ### Rates for the mixed Hodge Laplacian -/

/-- **Convergence of order `h^{s+1}` of the mixed method for smooth solutions** ([AFW2010],
Thm 3.9; [Arnold2018], Ch. 7), for a sequence of order `s` under its smoothing estimates: if
`σ`, `u`, `P_𝔅 u` and the harmonic part `p` are `IsCsForm s` with bound `L`, the error is
`≤ C' K h_N^{s+1}` with `K = 2 (1 + 2C)(B_i + B_j) L` (the harmonic term through
`CochainProjection.infDist_harmonicW_le`). -/
theorem PolySmoothingEstimates.norm_sub_le_meshSize_pow {S : PolySeq}
    {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : PolySmoothingEstimates n S p C) {s : ℕ}
    (hS : PolyOrder n S s) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j}
    (hs : (complex n).IsMixedSolution i j k f σ u q) {L : ℝ} (hL0 : 0 ≤ L)
    (hσ : IsCsForm s i L ((complex n).domainIncl i σ))
    (hu : IsCsForm s j L ((complex n).domainIncl j u))
    (hB : IsCsForm s j L ((complex n).domainIncl j
      ((complex n).boundaryPart j ((complex n).domainIncl j u))))
    (hq : IsCsForm s j L (q : L2F ℝ (cubeDomain n) (formIdx n j))) (N : ℕ) :
    ‖σ - (poly n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).fst‖ +
        ‖u - (poly n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (poly n S N) hij hjk f).snd.snd :
            (poly n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
        (2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L)) *
          meshSize N ^ (s + 1) := by
  have hC := hE.two_mul_nonneg
  have hh := pow_nonneg (meshSize_pos N).le (s + 1)
  have hBi := polyInterpBound_nonneg (n := n) S i
  have hBj := polyInterpBound_nonneg (n := n) S j
  have hiL := mul_nonneg (mul_nonneg hBi hL0) hh
  have hjL := mul_nonneg (mul_nonneg hBj hL0) hh
  have hK : 2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
      meshSize N ^ (s + 1) =
      2 * ((1 + 2 * C) * (polyInterpBound n S i * L * meshSize N ^ (s + 1))) +
        2 * ((1 + 2 * C) * (polyInterpBound n S j * L * meshSize N ^ (s + 1))) := by ring
  have hi : 2 * (polyInterpBound n S i * L * meshSize N ^ (s + 1)) ≤
      2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
        meshSize N ^ (s + 1) := by
    rw [hK]; nlinarith
  have hj : 2 * (polyInterpBound n S j * L * meshSize N ^ (s + 1)) ≤
      2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
        meshSize N ^ (s + 1) := by
    rw [hK]; nlinarith
  have hq' : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j))
      ((poly n S N).harmonicW j) ≤
      2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
        meshSize N ^ (s + 1) := by
    refine ((hE.proj N).infDist_harmonicW_le hjk hC (hE.isGraphBounded_proj N j k) q.2).trans ?_
    have h := IsCsForm.infDist_domainSub_poly_le hS
      (σ := cyclesToDomainSpace ((complex n).harmonic_le_cycles j q.2)) hq hL0 N
    rw [hK]
    have : 0 ≤ 1 + 2 * C := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h this]
  exact hE.norm_sub_le_of_infDist_le hij hjk hs N
    ((hσ.infDist_domainSub_poly_le hS hL0 N).trans hi)
    ((hu.infDist_domainSub_poly_le hS hL0 N).trans hj) hq'
    ((hB.infDist_domainSub_poly_le hS hL0 N).trans hj)

/-- **Convergence of order `h^{s+1}` of the mixed method with vanishing traces for smooth
solutions**, for a sequence of order `s` under its smoothing estimates (`H̊Λ(Q)`, data vanishing
outside `Q`). -/
theorem PolySmoothingEstimatesMin.norm_sub_le_meshSize_pow {S : PolySeq}
    {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : PolySmoothingEstimatesMin n S p C)
    {s : ℕ} (hS : PolyOrder n S s) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j}
    (hs : (complexMin n).IsMixedSolution i j k f σ u q) {L : ℝ} (hL0 : 0 ≤ L)
    (hσ : IsCsFormMin s i L ((complexMin n).domainIncl i σ))
    (hu : IsCsFormMin s j L ((complexMin n).domainIncl j u))
    (hB : IsCsFormMin s j L ((complexMin n).domainIncl j
      ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))))
    (hq : IsCsFormMin s j L (q : L2F ℝ (cubeDomain n) (formIdx n j))) (N : ℕ) :
    ‖σ - (polyMin n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).fst‖ +
        ‖u - (polyMin n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (polyMin n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (polyMin n S N) hij hjk f).snd.snd :
            (polyMin n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
        (2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L)) *
          meshSize N ^ (s + 1) := by
  have hC := hE.two_mul_nonneg
  have hh := pow_nonneg (meshSize_pos N).le (s + 1)
  have hBi := polyInterpBound_nonneg (n := n) S i
  have hBj := polyInterpBound_nonneg (n := n) S j
  have hiL := mul_nonneg (mul_nonneg hBi hL0) hh
  have hjL := mul_nonneg (mul_nonneg hBj hL0) hh
  have hK : 2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
      meshSize N ^ (s + 1) =
      2 * ((1 + 2 * C) * (polyInterpBound n S i * L * meshSize N ^ (s + 1))) +
        2 * ((1 + 2 * C) * (polyInterpBound n S j * L * meshSize N ^ (s + 1))) := by ring
  have hi : 2 * (polyInterpBound n S i * L * meshSize N ^ (s + 1)) ≤
      2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
        meshSize N ^ (s + 1) := by
    rw [hK]; nlinarith
  have hj : 2 * (polyInterpBound n S j * L * meshSize N ^ (s + 1)) ≤
      2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
        meshSize N ^ (s + 1) := by
    rw [hK]; nlinarith
  have hq' : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j))
      ((polyMin n S N).harmonicW j) ≤
      2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j) * L) *
        meshSize N ^ (s + 1) := by
    refine ((hE.proj N).infDist_harmonicW_le hjk hC (hE.isGraphBounded_proj N j k) q.2).trans ?_
    have h := IsCsFormMin.infDist_domainSub_polyMin_le hS
      (σ := cyclesToDomainSpace ((complexMin n).harmonic_le_cycles j q.2)) hq hL0 N
    rw [hK]
    have : 0 ≤ 1 + 2 * C := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h this]
  exact hE.norm_sub_le_of_infDist_le hij hjk hs N
    ((hσ.infDist_domainSub_polyMin_le hS hL0 N).trans hi)
    ((hu.infDist_domainSub_polyMin_le hS hL0 N).trans hj) hq'
    ((hB.infDist_domainSub_polyMin_le hS hL0 N).trans hj)

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method on the cube**, with no
hypothesis beyond the data ([AFW2010], Thm 3.9; [Arnold2018], Ch. 7): for an admissible sequence
of order `s` (`PolyOrder`, e.g. `s + 1 ≤ r_k` in every degree) and a solution `(σ, u, q)` of the
mixed problem whose components, the boundary part of `u` and `q` are `C^{s+2}` with
`(s+1)`-st derivatives bounded by `L`, the error of the discrete mixed solution on the
level-`(N + 1)` mesh is `≤ K L h_N^{s+1}`, with `K` independent of `N` and of the solution. -/
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
      K * L * meshSize N ^ (s + 1) := by
  obtain ⟨p, C, hE⟩ := polySmoothingEstimates_exists (n := n) S
  refine ⟨(1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
    (2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j))),
    fun hs L hL0 hσ hu hB hq N => ?_⟩
  refine (hE.norm_sub_le_meshSize_pow hS hij hjk hs hL0 hσ hu hB hq N).trans_eq ?_
  ring

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method with vanishing traces on
the cube**, with no hypothesis beyond the data (components vanishing outside `Q`). -/
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
      K * L * meshSize N ^ (s + 1) := by
  obtain ⟨p, C, hE⟩ := polySmoothingEstimatesMin_exists (n := n) S
  refine ⟨(1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
    (2 * ((1 + 2 * C) * (polyInterpBound n S i + polyInterpBound n S j))),
    fun hs L hL0 hσ hu hB hq N => ?_⟩
  refine (hE.norm_sub_le_meshSize_pow hS hij hjk hs hL0 hσ hu hB hq N).trans_eq ?_
  ring

/-- **`O(h)` convergence of every higher-order mixed method for `C²` solutions** (the case
`s = 0` of `mixed_rate_poly`; every admissible sequence has order `0`). -/
theorem mixed_rate_poly_C2 (S : PolySeq) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j},
    (complex n).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    IsCsForm 0 i L ((complex n).domainIncl i σ) →
    IsCsForm 0 j L ((complex n).domainIncl j u) →
    IsCsForm 0 j L ((complex n).domainIncl j
      ((complex n).boundaryPart j ((complex n).domainIncl j u))) →
    IsCsForm 0 j L (q : L2F ℝ (cubeDomain n) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (poly n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).fst‖ +
        ‖u - (poly n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (poly n S N) hij hjk f).snd.snd :
            (poly n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * L * meshSize N := by
  obtain ⟨K, hK⟩ := mixed_rate_poly (n := n) S (polyOrder_zero S) hij hjk
  exact ⟨K, fun hs L hL0 hσ hu hB hq N => (hK hs hL0 hσ hu hB hq N).trans_eq (by ring)⟩

/-! ### Rates for the semi-discrete Hodge wave equation -/

/-- **Graph-norm rate in the total space of a window** for a sequence of order `s`: if every
component of `ζ ∈ Γ(𝐝)` is `IsCsForm s` with bound `L`, some point of the window of `Vₕ` is
within `(m + m²) (Σᵢ B_{a+i}) L h_N^{s+1}` of `ζ`. -/
theorem exists_mem_window_poly_le {S : PolySeq} {s : ℕ} (hS : PolyOrder n S s) (a : ℤ) (m : ℕ)
    (ζ : ((complex n).window a m).totalD.GraphSpace) {L : ℝ} (hL0 : 0 ≤ L)
    (hζ : ∀ i : Fin m, IsCsForm s (a + i) L (((complex n).window a m).totalD.graphFst ζ i))
    (N : ℕ) :
    ∃ w ∈ ((poly n S N).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * (∑ i : Fin m, polyInterpBound n S (a + i)) * L *
        meshSize N ^ (s + 1) := by
  obtain ⟨x, rfl, -, -⟩ := ((complex n).window a m).totalD.exists_toGraphSpace_eq ζ
  simp only [LinearPMap.graphFst_toGraphSpace] at hζ
  have hh := pow_nonneg (meshSize_pos N).le (s + 1)
  have hle : ∀ i : Fin m, polyInterpBound n S (a + i) * L * meshSize N ^ (s + 1) ≤
      (∑ i : Fin m, polyInterpBound n S (a + i)) * L * meshSize N ^ (s + 1) := fun i =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun i : Fin m => polyInterpBound n S (a + i))
        (fun _ _ => polyInterpBound_nonneg _ _) (Finset.mem_univ i)) hL0) hh
  obtain ⟨w, hw, hlt⟩ := Subcomplex.exists_mem_graphSub_le ((poly n S N).window a m) x
    (ε := (∑ i : Fin m, polyInterpBound n S (a + i)) * L * meshSize N ^ (s + 1)) fun i => by
      obtain ⟨v, hv, h1, h2⟩ := (hζ i).exists_mem_poly_le hS hL0 N
      exact ⟨v, hv, h1.trans (hle i), fun j hx => (h2 (a + j) hx).trans (hle i)⟩
  refine ⟨w, hw, hlt.trans (le_of_eq ?_)⟩
  rw [Fintype.card_fin]; ring

/-- **Convergence of order `h^{s+1}` of the semi-discrete Hodge wave equation** for the
higher-order complexes ([QuennevilleBelair2015], Thm 4.14; [Arnold2018], Ch. 7), on every window
of `HΛ(Q)`: for a weak solution `ξ` in `C¹([t₀, t₁]; Γ(𝐝))` whose values and time derivatives
have `IsCsForm s` components with bound `L`, and the semi-discrete solutions `ξₕ` started at the
elliptic projection,
`‖ξ(t) - ξₕ(t)‖ ≤ A (1 + (t - t₀))² (m + m²) (Σᵢ B_{a+i}) L h_N^{s+1}` with `A` independent of `N`
(`Feec.HilbertComplex.Subcomplex.norm_sub_le_of_approx`). -/
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
  ((poly n S N).window a m).norm_sub_le_of_approx hξ (hξh N) (h0 N) (fun τ hτ =>
    ⟨exists_mem_window_poly_le hS a m (ξ τ) hL0 (fun i => (hreg τ hτ i).1) N,
      exists_mem_window_poly_le hS a m (ξ' τ) hL0 (fun i => (hreg τ hτ i).2) N⟩) ht

/-- **Graph-norm rate in the total space of a window of `H̊Λ(Q)`** for a sequence of order `s`. -/
theorem exists_mem_windowMin_poly_le {S : PolySeq} {s : ℕ} (hS : PolyOrder n S s) (a : ℤ)
    (m : ℕ) (ζ : ((complexMin n).window a m).totalD.GraphSpace) {L : ℝ} (hL0 : 0 ≤ L)
    (hζ : ∀ i : Fin m,
      IsCsFormMin s (a + i) L (((complexMin n).window a m).totalD.graphFst ζ i))
    (N : ℕ) :
    ∃ w ∈ ((polyMin n S N).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * (∑ i : Fin m, polyInterpBound n S (a + i)) * L *
        meshSize N ^ (s + 1) := by
  obtain ⟨x, rfl, -, -⟩ := ((complexMin n).window a m).totalD.exists_toGraphSpace_eq ζ
  simp only [LinearPMap.graphFst_toGraphSpace] at hζ
  have hh := pow_nonneg (meshSize_pos N).le (s + 1)
  have hle : ∀ i : Fin m, polyInterpBound n S (a + i) * L * meshSize N ^ (s + 1) ≤
      (∑ i : Fin m, polyInterpBound n S (a + i)) * L * meshSize N ^ (s + 1) := fun i =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun i : Fin m => polyInterpBound n S (a + i))
        (fun _ _ => polyInterpBound_nonneg _ _) (Finset.mem_univ i)) hL0) hh
  obtain ⟨w, hw, hlt⟩ := Subcomplex.exists_mem_graphSub_le ((polyMin n S N).window a m) x
    (ε := (∑ i : Fin m, polyInterpBound n S (a + i)) * L * meshSize N ^ (s + 1)) fun i => by
      obtain ⟨v, hv, h1, h2⟩ := (hζ i).exists_mem_polyMin_le hS hL0 N
      exact ⟨v, hv, h1.trans (hle i), fun j hx => (h2 (a + j) hx).trans (hle i)⟩
  refine ⟨w, hw, hlt.trans (le_of_eq ?_)⟩
  rw [Fintype.card_fin]; ring

/-- **Convergence of order `h^{s+1}` of the semi-discrete Hodge wave equation with vanishing
traces** for the higher-order complexes, on every window of `H̊Λ(Q)` (components vanishing
outside `Q`). -/
theorem norm_sub_le_windowMin_poly_smooth {S : PolySeq} {s : ℕ} (hS : PolyOrder n S s) (a : ℤ)
    (m : ℕ) {t₀ t₁ : ℝ} {ξ ξ' : ℝ → ((complexMin n).window a m).totalD.GraphSpace}
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
    ⟨exists_mem_windowMin_poly_le hS a m (ξ τ) hL0 (fun i => (hreg τ hτ i).1) N,
      exists_mem_windowMin_poly_le hS a m (ξ' τ) hL0 (fun i => (hreg τ hτ i).2) N⟩) ht

end Feec.Models.Cube.FEM
