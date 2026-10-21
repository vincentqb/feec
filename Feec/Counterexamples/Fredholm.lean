module

public import Feec.Counterexamples.Ell2
public import Feec.HilbertComplex.Compactness
public import Feec.HilbertComplex.Short
public import Feec.ForMathlib.LinearPMap.Bounded
public import Mathlib.Analysis.PSeries

/-!
# Fredholm Hilbert complexes need not have closed range

Thesis §4.2 claims that "a Fredholm Hilbert complex is always closed", with Fredholm meaning
that every space of harmonic forms `ℌⁱ = 𝔷ⁱ ∩ (𝔅ⁱ)ᗮ` is finite-dimensional. This is false. Let
`A = diag(1/(n+1))` on `ℓ²(ℕ, 𝕜)`: bounded, injective, compact, with dense non-closed range.

* `Fredholm.complex`: the short complex `ℓ² --A--> ℓ² → 0` (`ShortHilbertComplex.ofOp`). Every
  `ℌⁱ` vanishes (`Fredholm.harmonic_eq_bot`), but `𝔅¹ = R(A)` is not closed
  (`Fredholm.not_closedRangeAt_one`), so the complex is not exact at `1` although `ℌ¹ = 0`, and
  it fails the compactness property at `0` and `1`. Headline: `fredholm_not_closedRange`.
* `Fredholm.periodic`: the infinite complex `ℓ² --A--> ℓ² --0--> ℓ² --A--> ⋯` on
  `ComplexShape.up ℕ`, with the same conclusions at every index (`periodic_not_closedRange`).

The correct statements are "finite-dimensional cohomology ⇒ closed range"
(`Feec.HilbertComplex.closedRangeAt_of_finiteDimensional_cohomology`) and "compactness ⇒ closed
range and finite-dimensional harmonic forms"
(`Feec.HilbertComplex.HasCompactPropertyAt.closed_and_fredholm`).

The compactness property itself holds on infinite-dimensional spaces:
`ℓ² --A⁻¹--> ℓ² → 0`, `A⁻¹ = diag(n+1)` (`Fredholm.invComplex`), has it at every index
(`hasCompactProperty_infiniteDimensional`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.2 (the refuted sentence and the compactness property)
* [J. Brüning, M. Lesch, *Hilbert complexes*][BruningLesch1992] (Fredholm complexes:
  finite-dimensional cohomology)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 4

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate
open LinearPMap Filter Topology

@[expose] public noncomputable section

namespace Feec.Counterexamples

namespace Fredholm

open Ell2 (L2)

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The diagonal operator `A = diag(1/(n+1))` -/

theorem norm_natCast_add_one (n : ℕ) : ‖(n : 𝕜) + 1‖ = (n : ℝ) + 1 := by
  rw [show (n : 𝕜) + 1 = ((n + 1 : ℕ) : 𝕜) by push_cast; rfl, RCLike.norm_natCast]
  push_cast; rfl

theorem natCast_add_one_ne_zero (n : ℕ) : (n : 𝕜) + 1 ≠ 0 := fun h => by
  have := norm_natCast_add_one (𝕜 := 𝕜) n
  rw [h, norm_zero] at this
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- `|a/(n+1)| ≤ |a|`. -/
theorem norm_div_succ_le (a : 𝕜) (n : ℕ) : ‖a / ((n : 𝕜) + 1)‖ ≤ ‖a‖ := by
  rw [norm_div, norm_natCast_add_one]
  exact div_le_self (norm_nonneg _) (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])

variable (𝕜) in
/-- `diag(1/(n+1))` on `ℓ²`, as a linear map. -/
def diagₗ : L2 𝕜 →ₗ[𝕜] L2 𝕜 where
  toFun x := ⟨fun n => x n / ((n : 𝕜) + 1), (lp.memℓp x).mono' fun n => norm_div_succ_le _ n⟩
  map_add' x y := lp.ext <| funext fun n => by simp only [lp.coeFn_add, Pi.add_apply, add_div]
  map_smul' c x := lp.ext <| funext fun n => by simp [mul_div_assoc]

variable (𝕜) in
/-- `A = diag(1/(n+1)) : ℓ² → ℓ²`: bounded, injective, compact, with dense non-closed range. -/
def diag : L2 𝕜 →L[𝕜] L2 𝕜 :=
  (diagₗ 𝕜).mkContinuous 1 fun x => by
    rw [one_mul]; exact lp.norm_mono two_ne_zero fun n => norm_div_succ_le _ n

/-- `(A x)_n = x_n / (n+1)`. -/
theorem diag_apply (x : L2 𝕜) (n : ℕ) : diag 𝕜 x n = x n / ((n : 𝕜) + 1) := rfl

theorem norm_diag_apply_le (x : L2 𝕜) : ‖diag 𝕜 x‖ ≤ ‖x‖ :=
  lp.norm_mono two_ne_zero fun n => norm_div_succ_le _ n

theorem diag_injective : Function.Injective (diag 𝕜) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine lp.ext <| funext fun n => ?_
  have := congrArg (fun y : L2 𝕜 => y n) hx
  simp only [diag_apply] at this
  simpa [div_eq_zero_iff, natCast_add_one_ne_zero] using this

/-- `A e_n = e_n / (n+1)`. -/
theorem diag_single (n : ℕ) :
    diag 𝕜 (lp.single 2 n 1) = lp.single 2 n (1 / ((n : 𝕜) + 1)) := by
  refine lp.ext <| funext fun m => ?_
  rw [diag_apply]
  by_cases h : m = n
  · subst h; simp
  · simp [lp.single_apply, Pi.single_eq_of_ne h]

/-- `‖e_n‖ = 1`. -/
theorem norm_single (n : ℕ) : ‖(lp.single 2 n 1 : L2 𝕜)‖ = 1 := by
  rw [lp.norm_single (by norm_num), norm_one]

/-- `‖A e_n‖ = 1/(n+1)`. -/
theorem norm_diag_single (n : ℕ) : ‖diag 𝕜 (lp.single 2 n 1)‖ = 1 / ((n : ℝ) + 1) := by
  rw [diag_single, lp.norm_single (by norm_num), norm_div, norm_one, norm_natCast_add_one]

/-- `R(A)` is dense: anything orthogonal to every `A e_n` vanishes. -/
theorem eq_zero_of_inner_diag_single {y : L2 𝕜} (hy : ∀ n, ⟪diag 𝕜 (lp.single 2 n 1), y⟫_𝕜 = 0) :
    y = 0 := by
  refine lp.ext (funext fun n => ?_)
  have := hy n
  rw [diag_single, lp.inner_single_left] at this
  simpa [natCast_add_one_ne_zero] using this

/-- `R(A)ᗮ = 0`. -/
theorem orthogonal_range_diag : (LinearMap.range (diag 𝕜 : L2 𝕜 →ₗ[𝕜] L2 𝕜))ᗮ = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  exact (Submodule.mem_bot 𝕜).2 (eq_zero_of_inner_diag_single fun n =>
    (Submodule.mem_orthogonal _ _).1 hy _ ⟨_, rfl⟩)

/-- `A` is symmetric (its weights are real). -/
theorem inner_diag_left (a b : L2 𝕜) : ⟪diag 𝕜 a, b⟫_𝕜 = ⟪a, diag 𝕜 b⟫_𝕜 := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1; funext n
  have hc : conj ((n : 𝕜) + 1) = (n : 𝕜) + 1 := by simp
  simp only [diag_apply, RCLike.inner_apply, map_div₀, hc]
  ring

/-- The sequence `(1/(n+1))ₙ ∈ ℓ²`. -/
def harm : L2 𝕜 :=
  ⟨fun n => 1 / ((n : 𝕜) + 1), (memℓp_gen_iff (by norm_num : (0:ℝ) < (2 : ENNReal).toReal)).2 (by
    have h : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
      simpa [Nat.cast_add, Nat.cast_one] using h
    refine h.congr fun n => ?_
    rw [ENNReal.toReal_ofNat, norm_div, norm_one, norm_natCast_add_one, Real.rpow_two, div_pow,
      one_pow])⟩

theorem harm_apply (n : ℕ) : (harm : L2 𝕜) n = 1 / ((n : 𝕜) + 1) := rfl

/-- `(1/(n+1))ₙ ∉ R(A)`: its preimage would be the constant sequence `1`. -/
theorem harm_not_mem_range : (harm : L2 𝕜) ∉ LinearMap.range (diag 𝕜 : L2 𝕜 →ₗ[𝕜] L2 𝕜) := by
  rintro ⟨f, hf⟩
  have h1 : ∀ n, f n = 1 := fun n => by
    have := congrArg (fun y : L2 𝕜 => y n) hf
    change f n / ((n : 𝕜) + 1) = 1 / ((n : 𝕜) + 1) at this
    exact (div_left_inj' (natCast_add_one_ne_zero n)).1 this
  have hs := (lp.memℓp f).summable (by norm_num : (0:ℝ) < (2 : ENNReal).toReal)
  have ht := hs.tendsto_atTop_zero
  simp only [h1, norm_one, Real.one_rpow] at ht
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)

/-- `R(A)` is not closed (it is dense and proper). -/
theorem not_isClosed_range_diag :
    ¬ IsClosed (LinearMap.range (diag 𝕜 : L2 𝕜 →ₗ[𝕜] L2 𝕜) : Set (L2 𝕜)) := fun h => by
  have htop : LinearMap.range (diag 𝕜 : L2 𝕜 →ₗ[𝕜] L2 𝕜) = ⊤ := by
    have hcl := Submodule.orthogonal_orthogonal_eq_closure
      (K := LinearMap.range (diag 𝕜 : L2 𝕜 →ₗ[𝕜] L2 𝕜))
    rw [IsClosed.submodule_topologicalClosure_eq h, orthogonal_range_diag,
      Submodule.bot_orthogonal_eq_top] at hcl
    exact hcl.symm
  exact harm_not_mem_range (htop ▸ Submodule.mem_top)

/-! ### Compactness of `A` -/

/-- The unit vectors `e_n` of `ℓ²` are orthonormal. -/
theorem orthonormal_single : Orthonormal 𝕜 (fun n : ℕ => (lp.single 2 n (1 : 𝕜) : L2 𝕜)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [lp.inner_single_left, lp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- `ℓ²` is infinite-dimensional. -/
theorem not_finiteDimensional_L2 : ¬ FiniteDimensional 𝕜 (L2 𝕜) := fun _ =>
  Module.Finite.not_linearIndependent_of_infinite _ (orthonormal_single (𝕜 := 𝕜)).linearIndependent

variable (𝕜) in
/-- Truncation `A_N = Σ_{n<N} (1/(n+1)) ⟨e_n, ·⟩ e_n` of `A` (finite rank). -/
def diagTrunc (N : ℕ) : L2 𝕜 →L[𝕜] L2 𝕜 :=
  ∑ n ∈ Finset.range N, (1 / ((n : 𝕜) + 1)) •
    (ContinuousLinearMap.toSpanSingleton 𝕜 (lp.single 2 n (1 : 𝕜) : L2 𝕜)).comp
      (innerSL 𝕜 (lp.single 2 n (1 : 𝕜) : L2 𝕜))

theorem diagTrunc_apply (N : ℕ) (x : L2 𝕜) (m : ℕ) :
    diagTrunc 𝕜 N x m = if m < N then x m / ((m : 𝕜) + 1) else 0 := by
  simp only [diagTrunc, FunLike.coe_sum, lp.coeFn_sum, Finset.sum_apply,
    FunLike.coe_smul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply, lp.coeFn_smul, Pi.smul_apply,
    lp.inner_single_left, lp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single m]
    · simp [div_eq_inv_mul]
    · intro b _ hb; simp [Pi.single_eq_of_ne hb.symm]
    · intro hm; exact absurd (Finset.mem_range.2 h) hm
  · refine Finset.sum_eq_zero fun b hb => ?_
    have : m ≠ b := fun e => h (e ▸ Finset.mem_range.1 hb)
    simp [Pi.single_eq_of_ne this]

theorem isCompactOperator_diagTrunc (N : ℕ) : IsCompactOperator (diagTrunc 𝕜 N) := by
  unfold diagTrunc
  refine Finset.sum_induction _ (fun T : L2 𝕜 →L[𝕜] L2 𝕜 => IsCompactOperator T)
    (fun S T hS hT => by rw [FunLike.coe_add]; exact hS.add hT)
    (by rw [FunLike.coe_zero]; exact isCompactOperator_zero) fun n _ => ?_
  rw [FunLike.coe_smul]
  have h1 : IsCompactOperator (innerSL 𝕜 (lp.single 2 n (1 : 𝕜) : L2 𝕜)) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  exact (h1.clm_comp (ContinuousLinearMap.toSpanSingleton 𝕜 (lp.single 2 n (1 : 𝕜) : L2 𝕜))).smul
    (1 / ((n : 𝕜) + 1))

/-- `‖A - A_N‖ ≤ 1/(N+1)`. -/
theorem norm_sub_diagTrunc_le (N : ℕ) (x : L2 𝕜) :
    ‖(diag 𝕜 - diagTrunc 𝕜 N) x‖ ≤ 1 / ((N : ℝ) + 1) * ‖x‖ := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  calc ‖(diag 𝕜 - diagTrunc 𝕜 N) x‖ ≤ ‖((1 / ((N : ℝ) + 1) : ℝ) : 𝕜) • x‖ := by
        refine lp.norm_mono two_ne_zero fun m => ?_
        rw [_root_.sub_apply, lp.coeFn_sub, Pi.sub_apply, diag_apply,
          diagTrunc_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul,
          RCLike.norm_ofReal, abs_of_pos (by positivity)]
        split_ifs with h
        · simp only [sub_self, norm_zero]; positivity
        · rw [sub_zero, norm_div, norm_natCast_add_one, mul_comm, div_eq_mul_inv, one_div]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact inv_anti₀ hN (by exact_mod_cast Nat.add_le_add_right (not_lt.1 h) 1)
    _ = 1 / ((N : ℝ) + 1) * ‖x‖ := by
        rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (by positivity)]

/-- `A = diag(1/(n+1))` is a compact operator (norm limit of the `A_N`). -/
theorem isCompactOperator_diag : IsCompactOperator (diag 𝕜) := by
  refine isCompactOperator_of_tendsto (l := atTop) (F := diagTrunc 𝕜) ?_
    (Eventually.of_forall isCompactOperator_diagTrunc)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [norm_sub_rev]
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_sub_diagTrunc_le N)

/-! ### The short complex `ℓ² --A--> ℓ² → 0` -/

variable (𝕜) in
/-- `A` as an everywhere-defined unbounded operator. -/
abbrev diagPMap : L2 𝕜 →ₗ.[𝕜] L2 𝕜 := (diag 𝕜 : L2 𝕜 →ₗ[𝕜] L2 𝕜).toPMap ⊤

theorem dense_diagPMap_domain : Dense ((diagPMap 𝕜).domain : Set (L2 𝕜)) := by
  simp [dense_univ]

theorem mem_ker_toPMap_top_iff {f : L2 𝕜 →ₗ[𝕜] L2 𝕜} {x : L2 𝕜} :
    x ∈ (f.toPMap ⊤).ker ↔ f x = 0 :=
  ⟨fun hx => by
    obtain ⟨y, rfl, hy⟩ := (LinearPMap.mem_ker_iff).1 hx
    exact hy,
   fun hx => (LinearPMap.mem_ker_iff).2 ⟨⟨x, Submodule.mem_top⟩, rfl, hx⟩⟩

theorem range_toPMap_top (f : L2 𝕜 →ₗ[𝕜] L2 𝕜) :
    LinearMap.range (f.toPMap ⊤).toFun = LinearMap.range f := by
  ext y
  exact ⟨fun ⟨x, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨⟨x, Submodule.mem_top⟩, hx⟩⟩

variable (𝕜) in
/-- The short complex `ℓ² --A--> ℓ² → 0` on `ComplexShape.fin3`. -/
def complex : HilbertComplex 𝕜 ComplexShape.fin3 (ShortHilbertComplex.W3 (L2 𝕜) (L2 𝕜) PUnit) :=
  (ShortHilbertComplex.ofOp (diagPMap 𝕜) dense_diagPMap_domain
    (diag 𝕜).isClosed_toPMap_top).toHilbertComplex

theorem complex_d01 : (complex 𝕜).d 0 1 = diagPMap 𝕜 := rfl

/-- `𝔷⁰ = N(A) = 0`. -/
theorem cycles_zero : (complex 𝕜).cycles 0 = ⊥ := by
  rw [(complex 𝕜).cycles_eq (show ComplexShape.fin3.Rel 0 1 from rfl), complex_d01, eq_bot_iff]
  intro x hx
  exact (Submodule.mem_bot 𝕜).2 (diag_injective ((mem_ker_toPMap_top_iff.1 hx).trans
    (_root_.map_zero _).symm))

/-- `𝔅¹ = R(A)`. -/
theorem boundaries_one :
    (complex 𝕜).boundaries 1 = LinearMap.range (diag 𝕜 : L2 𝕜 →ₗ[𝕜] L2 𝕜) := by
  rw [(complex 𝕜).boundaries_eq (show ComplexShape.fin3.Rel 0 1 from rfl), complex_d01]
  exact range_toPMap_top _

theorem harmonic_zero : (complex 𝕜).harmonic 0 = ⊥ :=
  eq_bot_iff.2 (cycles_zero (𝕜 := 𝕜) ▸ (complex 𝕜).harmonic_le_cycles 0)

theorem harmonic_one : (complex 𝕜).harmonic 1 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h := ((complex 𝕜).mem_harmonic_iff.1 hx).2
  rw [boundaries_one] at h
  change x ∈ (⊥ : Submodule 𝕜 (L2 𝕜))
  rw [← orthogonal_range_diag]
  exact h

theorem harmonic_two : (complex 𝕜).harmonic 2 = ⊥ := by
  rw [eq_bot_iff]
  intro x _
  exact (Submodule.mem_bot 𝕜).2 (Subsingleton.elim (α := PUnit) _ _)

/-- **Every harmonic space vanishes**: `ℌ⁰ = N(A) = 0`, `ℌ¹ ⊆ R(A)ᗮ = 0`, `W² = 0`. -/
theorem harmonic_eq_bot (i : Fin 3) : (complex 𝕜).harmonic i = ⊥ := by
  fin_cases i
  exacts [harmonic_zero, harmonic_one, harmonic_two]

theorem finiteDimensional_harmonic (i : Fin 3) : FiniteDimensional 𝕜 ((complex 𝕜).harmonic i) := by
  rw [harmonic_eq_bot]; infer_instance

/-- `𝔅¹ = R(A)` is not closed. -/
theorem not_closedRangeAt_one : ¬ (complex 𝕜).ClosedRangeAt 1 := by
  rw [HilbertComplex.ClosedRangeAt, boundaries_one]
  exact not_isClosed_range_diag

/-! ### The periodic complex `ℓ² --A--> ℓ² --0--> ℓ² --A--> ⋯` -/

variable (𝕜) in
/-- The differentials of the periodic complex: `A` from even degrees, `0` from odd ones. -/
def periodicD (k : ℕ) : L2 𝕜 →ₗ.[𝕜] L2 𝕜 := if Even k then diagPMap 𝕜 else 0

theorem periodicD_domain (k : ℕ) : (periodicD 𝕜 k).domain = ⊤ := by
  unfold periodicD; split_ifs <;> rfl

theorem periodicD_of_even {k : ℕ} (hk : Even k) : periodicD 𝕜 k = diagPMap 𝕜 := by
  simp [periodicD, hk]

theorem periodicD_of_odd {k : ℕ} (hk : Odd k) : periodicD 𝕜 k = 0 := by
  simp [periodicD, Nat.not_even_iff_odd.2 hk]

theorem periodicD_closed (k : ℕ) : (periodicD 𝕜 k).IsClosed := by
  unfold periodicD; split_ifs
  · exact (diag 𝕜).isClosed_toPMap_top
  · exact LinearPMap.isClosed_zero

theorem periodicD_mapsTo (k : ℕ) (x : (periodicD 𝕜 k).domain) :
    (periodicD 𝕜 k x : L2 𝕜) ∈ (periodicD 𝕜 (k + 1)).domain := by
  rw [periodicD_domain]; trivial

theorem periodicD_comp (k : ℕ) (x : (periodicD 𝕜 k).domain) :
    periodicD 𝕜 (k + 1) ⟨periodicD 𝕜 k x, periodicD_mapsTo k x⟩ = 0 := by
  rcases Nat.even_or_odd k with hk | hk
  · exact apply_eq_zero_of_eq_zero (periodicD_of_odd hk.add_one) _
  · have h0 : periodicD 𝕜 k = 0 := periodicD_of_odd hk
    have hx : (periodicD 𝕜 k x : L2 𝕜) = 0 := apply_eq_zero_of_eq_zero h0 x
    have e : (⟨periodicD 𝕜 k x, periodicD_mapsTo k x⟩ :
        (periodicD 𝕜 (k + 1)).domain) = 0 := Subtype.ext hx
    rw [e, LinearPMap.map_zero]

variable (𝕜) in
/-- The periodic complex `ℓ² --A--> ℓ² --0--> ℓ² --A--> ⋯` on `ComplexShape.up ℕ`. -/
def periodic : HilbertComplex 𝕜 (ComplexShape.up ℕ) (fun _ : ℕ => L2 𝕜) :=
  HilbertComplex.ofSucc (periodicD 𝕜) (fun k => by rw [periodicD_domain]; exact dense_univ)
    periodicD_closed periodicD_mapsTo periodicD_comp

theorem periodic_d_succ (k : ℕ) : (periodic 𝕜).d k (k + 1) = periodicD 𝕜 k :=
  show HilbertComplex.ofSuccD (periodicD 𝕜) k (k + 1) = _ from HilbertComplex.ofSuccD_succ _ k

/-- In even degrees, `𝔷ᵏ = N(A) = 0`. -/
theorem periodic_cycles_of_even {k : ℕ} (hk : Even k) : (periodic 𝕜).cycles k = ⊥ := by
  rw [(periodic 𝕜).cycles_eq (show (ComplexShape.up ℕ).Rel k (k + 1) from rfl), periodic_d_succ,
    periodicD_of_even hk, eq_bot_iff]
  intro x hx
  exact (Submodule.mem_bot 𝕜).2 (diag_injective ((mem_ker_toPMap_top_iff.1 hx).trans
    (_root_.map_zero _).symm))

/-- In odd degrees, `𝔅ᵏ⁺¹ = R(A)` for `k` even. -/
theorem periodic_boundaries_of_even {k : ℕ} (hk : Even k) :
    (periodic 𝕜).boundaries (k + 1) = LinearMap.range (diag 𝕜 : L2 𝕜 →ₗ[𝕜] L2 𝕜) := by
  rw [(periodic 𝕜).boundaries_eq (show (ComplexShape.up ℕ).Rel k (k + 1) from rfl),
    periodic_d_succ, periodicD_of_even hk, range_toPMap_top]

/-- **Every harmonic space of the periodic complex vanishes.** -/
theorem periodic_harmonic_eq_bot (k : ℕ) : (periodic 𝕜).harmonic k = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rcases Nat.even_or_odd k with hk | ⟨j, rfl⟩
  · exact periodic_cycles_of_even (𝕜 := 𝕜) hk ▸ (periodic 𝕜).harmonic_le_cycles k hx
  · have h := ((periodic 𝕜).mem_harmonic_iff.1 hx).2
    rw [periodic_boundaries_of_even ⟨j, two_mul j⟩, orthogonal_range_diag] at h
    exact h

/-- `𝔅ᵏ⁺¹ = R(A)` is not closed for every even `k`. -/
theorem periodic_not_closedRangeAt {k : ℕ} (hk : Even k) :
    ¬ (periodic 𝕜).ClosedRangeAt (k + 1) := by
  rw [HilbertComplex.ClosedRangeAt, periodic_boundaries_of_even hk]
  exact not_isClosed_range_diag

/-! ### The compactness property on an infinite-dimensional space -/

theorem ker_diagPMap : (diagPMap 𝕜).ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  exact (Submodule.mem_bot 𝕜).2 (diag_injective ((mem_ker_toPMap_top_iff.1 hx).trans
    (_root_.map_zero _).symm))

variable (𝕜) in
/-- The unbounded operator `A⁻¹ = diag(n+1)` on `ℓ²`, with domain `R(A)`. -/
def invDiag : L2 𝕜 →ₗ.[𝕜] L2 𝕜 := (diagPMap 𝕜).inverse

theorem invDiag_domain : (invDiag 𝕜).domain = LinearMap.range (diag 𝕜 : L2 𝕜 →ₗ[𝕜] L2 𝕜) := by
  rw [invDiag, inverse_domain, range_toPMap_top]

theorem invDiag_isClosed : (invDiag 𝕜).IsClosed :=
  (inverse_closed_iff ker_diagPMap).2 (diag 𝕜).isClosed_toPMap_top

/-- `A (A⁻¹ u) = u`. -/
theorem diag_invDiag (u : (invDiag 𝕜).domain) : diag 𝕜 (invDiag 𝕜 u) = u := by
  have h : ((u : L2 𝕜), invDiag 𝕜 u) ∈ (diagPMap 𝕜).inverse.graph := (invDiag 𝕜).mem_graph u
  rw [inverse_graph ker_diagPMap] at h
  obtain ⟨⟨a, b⟩, hab, he⟩ := h
  obtain ⟨y, hy1, hy2⟩ := (mem_graph_iff _).1 hab
  simp only [LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, Prod.swap_prod_mk,
    Prod.mk.injEq] at he
  dsimp only at hy1 hy2
  rw [← he.1, ← he.2, ← hy2, ← hy1]; rfl

/-- `A⁻¹ (A v) = v`. -/
theorem invDiag_diag (v : L2 𝕜) (h : diag 𝕜 v ∈ (invDiag 𝕜).domain) :
    invDiag 𝕜 ⟨diag 𝕜 v, h⟩ = v :=
  diag_injective (diag_invDiag _)

theorem dense_invDiag_domain : Dense ((invDiag 𝕜).domain : Set (L2 𝕜)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    invDiag_domain, orthogonal_range_diag]

/-- `A⁻¹` is self-adjoint. -/
theorem adjoint_invDiag : (invDiag 𝕜)† = invDiag 𝕜 := by
  have hD := dense_invDiag_domain (𝕜 := 𝕜)
  have hsymm : (invDiag 𝕜).IsFormalAdjoint (invDiag 𝕜) := fun p q => by
    rw [← diag_invDiag p, ← diag_invDiag q, inner_diag_left]
  have hle : invDiag 𝕜 ≤ (invDiag 𝕜)† := hsymm.le_adjoint hD
  refine (LinearPMap.eq_of_le_of_domain_eq hle ?_).symm
  refine le_antisymm hle.1 fun y hy => ?_
  set z := (invDiag 𝕜)† ⟨y, hy⟩
  have hz : y = diag 𝕜 z := by
    refine ext_inner_right 𝕜 fun w => ?_
    have hw : diag 𝕜 w ∈ (invDiag 𝕜).domain := (invDiag_domain (𝕜 := 𝕜)) ▸ ⟨w, rfl⟩
    have := LinearPMap.adjoint_isFormalAdjoint hD ⟨y, hy⟩ ⟨diag 𝕜 w, hw⟩
    rw [invDiag_diag] at this
    change ⟪z, diag 𝕜 w⟫_𝕜 = ⟪y, w⟫_𝕜 at this
    rw [inner_diag_left]
    exact this.symm
  rw [invDiag_domain, hz]
  exact ⟨z, rfl⟩

/-- The `A⁻¹`-graph unit ball lies in the compact set `cl A(B̄(0,1))`. -/
theorem mem_closure_image_diag {u : (invDiag 𝕜).domain} (hu : ‖invDiag 𝕜 u‖ ≤ 1) :
    (u : L2 𝕜) ∈ closure (diag 𝕜 '' Metric.closedBall 0 1) :=
  subset_closure ⟨invDiag 𝕜 u, mem_closedBall_zero_iff.2 hu, diag_invDiag u⟩

variable (𝕜) in
/-- The short complex `ℓ² --A⁻¹--> ℓ² → 0`, `A⁻¹ = diag(n+1)` (the model of `d` with compact
resolvent). -/
def invComplex :
    HilbertComplex 𝕜 ComplexShape.fin3 (ShortHilbertComplex.W3 (L2 𝕜) (L2 𝕜) PUnit) :=
  (ShortHilbertComplex.ofOp (invDiag 𝕜) dense_invDiag_domain invDiag_isClosed).toHilbertComplex

/-- `ℓ² --A⁻¹--> ℓ² → 0` has the compactness property at every index. -/
theorem invComplex_hasCompactProperty : (invComplex 𝕜).HasCompactProperty := by
  have hK := isCompactOperator_diag.isCompact_closure_image_closedBall
    (f := (diag 𝕜 : L2 𝕜 →ₗ[𝕜] L2 𝕜)) 1
  intro i
  fin_cases i
  · refine ((invComplex 𝕜).hasCompactPropertyAt_iff_of_not_rel_of_rel
      (fun h hh => by fin_cases h <;> simp_all [ComplexShape.fin3])
      (show ComplexShape.fin3.Rel 0 1 from rfl)).2 ⟨_, hK, fun x hx _ h2 => ?_⟩
    exact mem_closure_image_diag (u := ⟨x, hx⟩) h2
  · refine ((invComplex 𝕜).hasCompactPropertyAt_iff_of_rel
      (show ComplexShape.fin3.Rel 0 1 from rfl) (show ComplexShape.fin3.Rel 1 2 from rfl)).2
      ⟨_, hK, fun x _ hx' _ _ h3 => ?_⟩
    change x ∈ ((invDiag 𝕜)†).domain at hx'
    have hx : x ∈ (invDiag 𝕜).domain := adjoint_invDiag (𝕜 := 𝕜) ▸ hx'
    refine mem_closure_image_diag (u := ⟨x, hx⟩) ?_
    have e : (invDiag 𝕜)† ⟨x, hx'⟩ = invDiag 𝕜 ⟨x, hx⟩ := by
      have key : ∀ T : L2 𝕜 →ₗ.[𝕜] L2 𝕜, T = invDiag 𝕜 → ∀ (h : x ∈ T.domain),
          T ⟨x, h⟩ = invDiag 𝕜 ⟨x, hx⟩ := by
        rintro _ rfl h; rfl
      exact key _ adjoint_invDiag hx'
    change ‖(invDiag 𝕜)† ⟨x, hx'⟩‖ ≤ 1 at h3
    rwa [e] at h3
  · have : FiniteDimensional 𝕜 (ShortHilbertComplex.W3 (L2 𝕜) (L2 𝕜) PUnit 2) :=
      inferInstanceAs (FiniteDimensional 𝕜 PUnit)
    exact (invComplex 𝕜).hasCompactPropertyAt_of_finiteDimensional 2

end Fredholm

open Fredholm
open Ell2 (L2)

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **A Fredholm Hilbert complex need not have closed range.** The short complex
`ℓ² --A--> ℓ² → 0`, `A = diag(1/(n+1))` on `ℓ²(ℕ, 𝕜)`, of closed densely defined (indeed
bounded) operators has `ℌⁱ = 0` at every index, so it is Fredholm in the thesis' sense, but
`𝔅¹ = R(A)` is not closed; hence `𝔅¹ ≠ 𝔷¹` although `ℌ¹ = 0`, and the compactness property fails
at `0` and `1`. [QuennevilleBelair2015], §4.2 (refuted) -/
theorem fredholm_not_closedRange :
    (∀ i, (complex 𝕜).harmonic i = ⊥) ∧ (∀ i, FiniteDimensional 𝕜 ((complex 𝕜).harmonic i)) ∧
      ¬ (complex 𝕜).ClosedRangeAt 1 ∧ (complex 𝕜).boundaries 1 ≠ (complex 𝕜).cycles 1 ∧
      ¬ (complex 𝕜).HasCompactPropertyAt 0 ∧ ¬ (complex 𝕜).HasCompactPropertyAt 1 :=
  ⟨harmonic_eq_bot, finiteDimensional_harmonic, not_closedRangeAt_one,
    (complex 𝕜).boundaries_ne_cycles_of_not_closedRangeAt not_closedRangeAt_one,
    fun h => not_closedRangeAt_one
      (h.closedRangeAt_of_rel (show ComplexShape.fin3.Rel 0 1 from rfl)),
    fun h => not_closedRangeAt_one h.closedRangeAt⟩

/-- "Every Fredholm Hilbert complex has closed range" is false, already for short complexes on
`ℓ²(ℕ, 𝕜)`. [QuennevilleBelair2015], §4.2 (refuted) -/
theorem not_forall_closedRangeAt_of_finiteDimensional_harmonic :
    ¬ ∀ H : HilbertComplex 𝕜 ComplexShape.fin3 (ShortHilbertComplex.W3 (L2 𝕜) (L2 𝕜) PUnit),
      (∀ i, FiniteDimensional 𝕜 (H.harmonic i)) → ∀ i, H.ClosedRangeAt i :=
  fun h => not_closedRangeAt_one (h _ finiteDimensional_harmonic 1)

/-- **Periodic form**: `ℓ² --A--> ℓ² --0--> ℓ² --A--> ⋯` on `ComplexShape.up ℕ` has `ℌᵏ = 0`
for every `k`, but `𝔅ᵏ⁺¹ = R(A)` is not closed for every even `k`, so the complex is not exact
there. [QuennevilleBelair2015], §4.2 (refuted) -/
theorem periodic_not_closedRange :
    (∀ k, (periodic 𝕜).harmonic k = ⊥) ∧
      ∀ k, Even k → ¬ (periodic 𝕜).ClosedRangeAt (k + 1) ∧
        (periodic 𝕜).boundaries (k + 1) ≠ (periodic 𝕜).cycles (k + 1) :=
  ⟨periodic_harmonic_eq_bot, fun _ hk => ⟨periodic_not_closedRangeAt hk,
    (periodic 𝕜).boundaries_ne_cycles_of_not_closedRangeAt (periodic_not_closedRangeAt hk)⟩⟩

/-- **The compactness property on an infinite-dimensional space.** On `ℓ²(ℕ, 𝕜)`, which is
infinite-dimensional, the short complex `ℓ² --A⁻¹--> ℓ² → 0` with `A⁻¹ = diag(n+1)` (compact
resolvent: the model of `d` on a compact manifold) has the compactness property at every index.
[QuennevilleBelair2015], §4.2 -/
theorem hasCompactProperty_infiniteDimensional :
    ¬ FiniteDimensional 𝕜 (L2 𝕜) ∧ (invComplex 𝕜).HasCompactProperty :=
  ⟨not_finiteDimensional_L2, invComplex_hasCompactProperty⟩

end Feec.Counterexamples
