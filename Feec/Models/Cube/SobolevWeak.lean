module

public import Feec.Models.Cube.Sobolev
public import Feec.ForMathlib.Calculus.Partial
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Sobolev spaces of integer order and weak derivatives on the cube

Weak derivatives of the forms of `Hᵐ(Q; Λᵏ)`, `Q = (0, ½)ⁿ`, the spaces `Hᵐ(𝕋ⁿ)` and `Hᵐ_J(Q; Λᵏ)`
by weak derivatives, and a Bernstein inequality for the Fourier truncations.

## Main results

* `hasWeakDerivs_of_mem_sobolevQ`: the forms of `Hᵐ(Q)` have weak derivatives up to order `m`.
* `memSob_nat_iff`: `Hᵐ(𝕋ⁿ)` is the space of forms with weak derivatives up to order `m`.
* `mem_sobolevPar_add_one_iff`, `mem_sobolevPar_two_iff`: the parity classes by weak derivatives.
* `weakHmNormSq_le_parNorm_sq`, `parNorm_sq_le_weakHmNormSq`: the equivalence of the norms.
* `sum_norm_iteratedFDeriv_truncQ_sq_le`: the Bernstein inequality for the Fourier truncations.

## References

* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011]
* [L. C. Evans, *Partial Differential Equations*][Evans2010]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate Topology ContDiff
open Set MeasureTheory Filter Finset

@[expose] public noncomputable section

namespace Feec.Models.Cube.Sobolev

open Feec.Models.Cube.DeRhamIdent Geometry
open Feec.Domain (formIdx L2F L2 toL2F extDerivOp IsTest)
open Feec.Fourier.Exterior (Form)
open Feec.Fourier.Torus (freq bandN finite_bandN norm_freq_sq)
open UnitAddTorus Feec.Fourier.TorusWeak

/-- The normalised Haar measure on `ℝ/ℤ`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The local Haar measure on `ℝ/ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {n : ℕ}

/-! ### Exponential sums on `ℝⁿ` -/

section ExpSum

/-- The phase `y ↦ 2πi m·y` of the character of frequency `m`, a real-linear form. -/
def phaseCLM (m : Fin n → ℤ) : (Fin n → ℝ) →L[ℝ] ℂ :=
  ∑ i, (2 * Real.pi * Complex.I * m i : ℂ) •
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ))

theorem phaseCLM_apply (m : Fin n → ℤ) (y : Fin n → ℝ) :
    phaseCLM m y = ∑ i, 2 * Real.pi * Complex.I * m i * (y i : ℂ) := by
  simp [phaseCLM, smul_eq_mul]

theorem phaseCLM_single (m : Fin n → ℤ) (j : Fin n) :
    phaseCLM m (Pi.single j 1) = 2 * Real.pi * Complex.I * m j := by
  rw [phaseCLM_apply, Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
  simp

/-- The character `e_m(y) = exp(2πi m·y)` on `ℝⁿ`. -/
def expChar (m : Fin n → ℤ) (y : Fin n → ℝ) : ℂ := Complex.exp (phaseCLM m y)

theorem expChar_eq_mFourier (m : Fin n → ℤ) (y : Fin n → ℝ) :
    expChar m y = mFourier m (proj y) := by
  rw [expChar, mFourier_proj, phaseCLM_apply, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem hasFDerivAt_expChar (m : Fin n → ℤ) (y : Fin n → ℝ) :
    HasFDerivAt (expChar m) (expChar m y • phaseCLM m) y :=
  (phaseCLM m).hasFDerivAt.cexp

/-- The exponential sum `Σ_{m ∈ S} c_m e_m(y)`. -/
def expSum (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) (y : Fin n → ℝ) : ℂ :=
  ∑ m ∈ S, c m * expChar m y

theorem contDiff_expChar (m : Fin n → ℤ) : ContDiff ℝ ∞ (expChar m) :=
  Complex.contDiff_exp.comp (phaseCLM m).contDiff

theorem contDiff_expSum (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) :
    ContDiff ℝ ∞ (expSum S c) :=
  ContDiff.sum fun m _ => contDiff_const.mul (contDiff_expChar m)

theorem contDiff_re_expSum (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) :
    ContDiff ℝ ∞ (fun y => (expSum S c y).re) :=
  Complex.reCLM.contDiff.comp (contDiff_expSum S c)

theorem hasFDerivAt_expSum (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) (y : Fin n → ℝ) :
    HasFDerivAt (expSum S c) (∑ m ∈ S, (c m * expChar m y) • phaseCLM m) y := by
  have h := HasFDerivAt.fun_sum (u := S) (A := fun m y => c m * expChar m y)
    (A' := fun m => (c m * expChar m y) • phaseCLM m) (x := y) fun m _ => by
      have := (hasFDerivAt_expChar m y).const_mul (c m)
      simpa [smul_smul] using this
  exact h

theorem partialDeriv_expSum (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) (j : Fin n) :
    partialDeriv j (expSum S c) =
      expSum S (fun m => 2 * Real.pi * Complex.I * m j * c m) := by
  funext y
  rw [(hasFDerivAt_expSum S c y).partialDeriv_eq, FunLike.coe_sum, Finset.sum_apply, expSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_apply, phaseCLM_single, smul_eq_mul]
  ring

theorem partialDeriv_re_expSum (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) (j : Fin n) :
    partialDeriv j (fun y => (expSum S c y).re) =
      fun y => (expSum S (fun m => 2 * Real.pi * Complex.I * m j * c m) y).re := by
  funext y
  rw [partialDeriv, fderiv_re_comp ((contDiff_expSum S c).differentiable (by simp) y),
    ← partialDeriv, partialDeriv_expSum]

/-- The symbol `∏_{j ∈ l} 2πi m_j` of the iterated partial derivative along the list `l`. -/
def symb (l : List (Fin n)) (m : Fin n → ℤ) : ℂ :=
  (l.map fun j => 2 * Real.pi * Complex.I * (m j : ℂ)).prod

@[simp] theorem symb_nil (m : Fin n → ℤ) : symb [] m = 1 := rfl

theorem symb_cons (j : Fin n) (l : List (Fin n)) (m : Fin n → ℤ) :
    symb (j :: l) m = 2 * Real.pi * Complex.I * m j * symb l m := by
  simp [symb]

theorem norm_symb_sq (l : List (Fin n)) (m : Fin n → ℤ) :
    ‖symb l m‖ ^ 2 = (l.map fun j => (2 * Real.pi * m j) ^ 2).prod := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [symb_cons, norm_mul, mul_pow, ih, List.map_cons, List.prod_cons]
    congr 1
    rw [show (2 * Real.pi * Complex.I * m j : ℂ) = ((2 * Real.pi * m j : ℝ) : ℂ) * Complex.I by
      push_cast; ring, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]

section IterPartial

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The iterated partial derivative `∂^{[j₁, …, j_p]} f = ∂_{j₁} ⋯ ∂_{j_p} f` along a word. -/
def iterPartial : List (Fin n) → ((Fin n → ℝ) → F) → (Fin n → ℝ) → F
  | [], f => f
  | j :: l, f => partialDeriv j (iterPartial l f)

@[simp] theorem iterPartial_nil (f : (Fin n → ℝ) → F) : iterPartial [] f = f := rfl

theorem iterPartial_cons (j : Fin n) (l : List (Fin n)) (f : (Fin n → ℝ) → F) :
    iterPartial (j :: l) f = partialDeriv j (iterPartial l f) := rfl

theorem iterPartial_eq_foldr (l : List (Fin n)) (f : (Fin n → ℝ) → F) :
    iterPartial l f = l.foldr (fun j g => partialDeriv j g) f := by
  induction l with
  | nil => rfl
  | cons j l ih => rw [iterPartial_cons, ih]; rfl

theorem iterPartial_append (l₁ l₂ : List (Fin n)) (f : (Fin n → ℝ) → F) :
    iterPartial (l₁ ++ l₂) f = iterPartial l₁ (iterPartial l₂ f) := by
  induction l₁ with
  | nil => rfl
  | cons j l ih => rw [List.cons_append, iterPartial_cons, iterPartial_cons, ih]

theorem contDiff_iterPartial {f : (Fin n → ℝ) → F} (hf : ContDiff ℝ ∞ f) (l : List (Fin n)) :
    ContDiff ℝ ∞ (iterPartial l f) := by
  induction l with
  | nil => exact hf
  | cons j l ih => exact ih.partialDeriv (by simp) j

theorem iterPartial_clm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (T : F →L[ℝ] G)
    {f : (Fin n → ℝ) → F} (hf : ContDiff ℝ ∞ f) (l : List (Fin n)) :
    iterPartial l (fun y => T (f y)) = fun y => T (iterPartial l f y) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    funext y
    rw [iterPartial_cons, ih, iterPartial_cons]
    exact T.partialDeriv_comp ((contDiff_iterPartial hf l).differentiable (by simp) y) j

theorem iterPartial_eqOn {O : Set (Fin n → ℝ)} (hO : IsOpen O) {f g : (Fin n → ℝ) → F}
    (h : EqOn f g O) (l : List (Fin n)) : EqOn (iterPartial l f) (iterPartial l g) O := by
  induction l with
  | nil => exact h
  | cons j l ih =>
    intro y hy
    rw [iterPartial_cons, iterPartial_cons]
    exact Filter.EventuallyEq.partialDeriv_eq
      (Filter.eventuallyEq_of_mem (hO.mem_nhds hy) ih) j

end IterPartial

theorem iterPartial_re_expSum (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (l : List (Fin n)) :
    iterPartial l (fun y => (expSum S c y).re) =
      fun y => (expSum S (fun m => symb l m * c m) y).re := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [iterPartial_cons, ih, partialDeriv_re_expSum]
    funext y
    congr 2
    funext m
    rw [symb_cons]; ring

theorem symb_reverse (l : List (Fin n)) (m : Fin n → ℤ) : symb l.reverse m = symb l m := by
  simp only [symb, List.map_reverse, List.prod_reverse]

theorem norm_sq_eq_integral_sq' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ x, ((f : α → ℝ) x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]

theorem integral_re_expSum_sq_le (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) :
    ∫ y in Q (Fin n), ((expSum S c y).re) ^ 2 ≤ ∑ m ∈ S, ‖c m‖ ^ 2 := by
  set G : C(UnitAddTorus (Fin n), ℂ) := ∑ m ∈ S, c m • mFourier m
  have hG : ∀ y, G (proj y) = expSum S c y := fun y => by
    simp [G, expSum, expChar_eq_mFourier, ContinuousMap.coe_sum, Finset.sum_apply, smul_eq_mul]
  have hc : Continuous fun y => (G (proj y)).re := by
    simp_rw [hG]; exact (contDiff_re_expSum S c).continuous
  have hF : MemLp (fun y => (G (proj y)).re) 2 (volume.restrict (Q (Fin n))) :=
    Feec.Domain.memLp_of_continuous measurableSet_Q isBounded_Qn hc
  have h1 := norm_toLp_re_le G hF
  have h2 : ‖hF.toLp (fun y => (G (proj y)).re)‖ ^ 2 =
      ∫ y in Q (Fin n), ((expSum S c y).re) ^ 2 := by
    rw [norm_sq_eq_integral_sq']
    refine integral_congr_ae ?_
    filter_upwards [hF.coeFn_toLp] with y hy
    rw [hy, hG]
  have h3 : G.toLp 2 (volume : Measure (UnitAddTorus (Fin n))) ℂ =
      ∑ m ∈ S, c m • mFourierLp 2 m := by
    simp [G, map_sum, map_smul]
  have h4 : ‖G.toLp 2 (volume : Measure (UnitAddTorus (Fin n))) ℂ‖ ^ 2 = ∑ m ∈ S, ‖c m‖ ^ 2 := by
    rw [h3, @norm_sq_eq_re_inner ℂ, orthonormal_mFourier.inner_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [RCLike.conj_mul]
    norm_cast
  rw [← h2, ← h4]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

end ExpSum

/-! ### Iterated derivatives, partial derivatives and their norms -/

section IterDeriv

theorem iterPartial_zero (l : List (Fin n)) : iterPartial l (fun _ => (0 : ℝ)) = fun _ => 0 := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [iterPartial_cons, ih]
    funext y
    simp [partialDeriv]

theorem norm_le_sum_apply_single {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin p => Fin n → ℝ) F) :
    ‖A‖ ≤ ∑ r : Fin p → Fin n, ‖A (fun l => Pi.single (r l) 1)‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    fun v => ?_
  have hv : v = fun l => ∑ j, v l j • (Pi.single j 1 : Fin n → ℝ) := by
    funext l; funext i; simp [Finset.sum_apply, Pi.single_apply]
  have e : A v = ∑ r : Fin p → Fin n, (∏ l, v l (r l)) • A (fun l => Pi.single (r l) 1) := by
    conv_lhs => rw [hv]
    rw [A.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact A.map_smul_univ (fun l => v l (r l)) (fun l => Pi.single (r l) 1)
  rw [e, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_smul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_prod]
  gcongr with l
  exact norm_le_pi_norm (v l) (r l)

theorem norm_le_sum_proj {ι : Type*} [Fintype ι] {p : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin p => Fin n → ℝ) (ι → ℝ)) :
    ‖A‖ ≤ ∑ s, ‖(ContinuousLinearMap.proj s : (ι → ℝ) →L[ℝ] ℝ).compContinuousMultilinearMap A‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun s => ?_
  set P : ι → ContinuousMultilinearMap ℝ (fun _ : Fin p => Fin n → ℝ) ℝ := fun s =>
    (ContinuousLinearMap.proj s : (ι → ℝ) →L[ℝ] ℝ).compContinuousMultilinearMap A
  have h := (P s).le_opNorm v
  have h2 : ‖P s‖ ≤ ∑ s, ‖P s‖ :=
    Finset.single_le_sum (f := fun s => ‖P s‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  calc ‖A v s‖ = ‖P s v‖ := rfl
    _ ≤ _ := h
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 (by positivity)

theorem norm_iteratedFDeriv_le_sum_iterPartial {ι : Type*} [Fintype ι]
    {w : (Fin n → ℝ) → ι → ℝ} (hw : ContDiff ℝ ∞ w) (p : ℕ) (y : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ p w y‖ ≤
      ∑ s, ∑ r : Fin p → Fin n, |iterPartial (List.ofFn r) (fun z => w z s) y| := by
  refine (norm_le_sum_proj _).trans (Finset.sum_le_sum fun s _ => ?_)
  have hs : ContDiff ℝ ∞ (fun z => w z s) := (contDiff_pi.1 hw) s
  have e := (ContinuousLinearMap.proj s : (ι → ℝ) →L[ℝ] ℝ).iteratedFDeriv_comp_left
    (hw.contDiffAt (x := y)) (i := p) (by exact_mod_cast le_top)
  have e' : iteratedFDeriv ℝ p (fun z => w z s) y =
      (ContinuousLinearMap.proj s : (ι → ℝ) →L[ℝ] ℝ).compContinuousMultilinearMap
        (iteratedFDeriv ℝ p w y) := e
  rw [← e']
  refine (norm_le_sum_apply_single _).trans (le_of_eq (Finset.sum_congr rfl fun r _ => ?_))
  rw [iteratedFDeriv_apply_single_eq_foldr hs (by exact_mod_cast le_top), iterPartial_eq_foldr,
    Real.norm_eq_abs]

theorem sum_norm_symb_sq (p : ℕ) (m : Fin n → ℤ) :
    ∑ r : Fin p → Fin n, ‖symb (List.ofFn r) m‖ ^ 2 = (‖freq m‖ ^ 2) ^ p := by
  simp_rw [norm_symb_sq, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
  rw [← Fintype.prod_sum (fun (_ : Fin p) (j : Fin n) => (2 * Real.pi * m j) ^ 2),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_freq_sq, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end IterDeriv

/-! ### The Bernstein inequality for the Fourier truncations -/

section Bernstein

variable {k : ℕ}

theorem integrable_sq_of_continuous {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) :
    Integrable (fun y => f y ^ 2) (volume.restrict (Q (Fin n))) :=
  (Feec.Domain.memLp_of_continuous measurableSet_Q isBounded_Qn hf).integrable_sq

theorem trigLift_eq_re_expSum (x : Seq n k) (S : Finset (Fin n → ℤ)) (t : formIdx n (k : ℤ)) :
    trigLift k x S t = fun y => (expSum S (fun m => cf x m t) y).re := by
  funext y
  simp only [trigLift, trigPoly, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, expSum, expChar_eq_mFourier, repr_physF]

/-- The Fourier truncation `Re Σ_{|m|_∞ ≤ M} x(m) e_m` of `x` as a smooth form field on `ℝⁿ`. -/
def truncField (k : ℕ) (x : Seq n k) (M : ℕ) : (Fin n → ℝ) → Finset (Fin n) → ℝ :=
  fun y s => Feec.Domain.formExt
    (fun t : formIdx n (k : ℤ) => trigLift k (trunc M k x) (bandS M) t y) s

theorem truncField_val (x : Seq n k) (M : ℕ) (y : Fin n → ℝ) (t : formIdx n (k : ℤ)) :
    truncField k x M y t.1 = trigLift k (trunc M k x) (bandS M) t y :=
  Feec.Domain.formExt_val _ t

theorem truncField_of_ne (x : Seq n k) (M : ℕ) (y : Fin n → ℝ) {s : Finset (Fin n)}
    (hs : #s ≠ k) : truncField k x M y s = 0 := by
  have hs' : ¬((#s : ℤ) = k) := fun h => hs (by exact_mod_cast h)
  simp only [truncField, Feec.Domain.formExt, hs', dite_false]

theorem contDiff_truncField (x : Seq n k) (M : ℕ) : ContDiff ℝ ∞ (truncField k x M) := by
  refine contDiff_pi.2 fun s => ?_
  by_cases hs : (#s : ℤ) = k
  · have : (fun y => truncField k x M y s) = trigLift k (trunc M k x) (bandS M) ⟨s, hs⟩ := by
      funext y; exact truncField_val x M y ⟨s, hs⟩
    rw [this]; exact contDiff_trigLift k _ _ _
  · have : (fun y => truncField k x M y s) = fun _ => 0 := by
      funext y; exact truncField_of_ne x M y (fun h => hs (by exact_mod_cast h))
    rw [this]; exact contDiff_const

theorem Jinvf_trunc_eq_toL2F (x : Seq n k) (M : ℕ) :
    Jinvf k (trunc M k x) = toL2F (memLp_trigLift k (trunc M k x) (bandS M)) :=
  Jinvf_eq_toL2F fun _ hm => trunc_eq_zero_of_notMem x hm

theorem truncField_comp_eq (x : Seq n k) (M : ℕ) (t : formIdx n (k : ℤ)) :
    (fun y => truncField k x M y t.1) =
      fun y => (expSum (bandS M) (fun m => cf (trunc M k x) m t) y).re := by
  funext y
  rw [truncField_val, trigLift_eq_re_expSum]

theorem integral_iterPartial_truncField_sq_le (x : Seq n k) (M : ℕ) (l : List (Fin n))
    (t : formIdx n (k : ℤ)) :
    ∫ y in Q (Fin n), (iterPartial l (fun z => truncField k x M z t.1) y) ^ 2 ≤
      ∑ m ∈ bandS M, ‖symb l m‖ ^ 2 * ‖cf (trunc M k x) m t‖ ^ 2 := by
  rw [truncField_comp_eq, iterPartial_re_expSum]
  refine (integral_re_expSum_sq_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [norm_mul, mul_pow]

theorem integral_norm_iteratedFDeriv_truncField_sq_le (x : Seq n k) (M p : ℕ) :
    ∫ y in Q (Fin n), ‖iteratedFDeriv ℝ p (truncField k x M) y‖ ^ 2 ≤
      2 ^ n * n ^ p * sobSum p (trunc M k x) := by
  set w := truncField k x M
  have hw := contDiff_truncField x M
  have hws : ∀ s, ContDiff ℝ ∞ (fun z => w z s) := fun s => (contDiff_pi.1 hw) s
  set a : Finset (Fin n) → (Fin p → Fin n) → (Fin n → ℝ) → ℝ :=
    fun s r y => iterPartial (List.ofFn r) (fun z => w z s) y
  have ha : ∀ s r, Continuous (a s r) := fun s r =>
    (contDiff_iterPartial (hws s) (List.ofFn r)).continuous
  have hcard : (Fintype.card (Finset (Fin n) × (Fin p → Fin n)) : ℝ) = 2 ^ n * n ^ p := by
    simp [Fintype.card_prod, Fintype.card_finset]
  have hpt : ∀ y, ‖iteratedFDeriv ℝ p w y‖ ^ 2 ≤
      2 ^ n * n ^ p * ∑ s, ∑ r, (a s r y) ^ 2 := by
    intro y
    have h1 := norm_iteratedFDeriv_le_sum_iterPartial hw p y
    have h2 : (∑ s, ∑ r : Fin p → Fin n, |a s r y|) ^ 2 ≤
        2 ^ n * n ^ p * ∑ s, ∑ r, (a s r y) ^ 2 := by
      rw [← Finset.sum_product', ← Finset.sum_product', ← hcard]
      refine (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun q : Finset (Fin n) × (Fin p → Fin n) => |a q.1 q.2 y|)).trans ?_
      simp [sq_abs, Finset.card_univ]
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hint : ∀ s r, Integrable (fun y => (a s r y) ^ 2) (volume.restrict (Q (Fin n))) :=
    fun s r => integrable_sq_of_continuous (ha s r)
  have hD : Continuous fun y => ‖iteratedFDeriv ℝ p w y‖ :=
    (hw.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  have h1 : ∫ y in Q (Fin n), ‖iteratedFDeriv ℝ p w y‖ ^ 2 ≤
      2 ^ n * n ^ p * ∑ s, ∑ r, ∫ y in Q (Fin n), (a s r y) ^ 2 := by
    refine (integral_mono (integrable_sq_of_continuous hD)
      ((integrable_finsetSum _ fun s _ => integrable_finsetSum _ fun r _ => hint s r).const_mul _)
      hpt).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_finsetSum _ fun s _ => integrable_finsetSum _ fun r _ =>
      hint s r]
    congr 1
    exact Finset.sum_congr rfl fun s _ => integral_finsetSum _ fun r _ => hint s r
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have h0 : ∀ s, #s ≠ k → ∑ r : Fin p → Fin n, ∫ y in Q (Fin n), (a s r y) ^ 2 = 0 := by
    intro s hs
    refine Finset.sum_eq_zero fun r _ => ?_
    have : (fun z => w z s) = fun _ => 0 := funext fun z => truncField_of_ne x M z hs
    simp [a, this, iterPartial_zero]
  rw [Feec.Domain.sum_eq_sum_formIdx h0]
  set c := fun (m : Fin n → ℤ) (t : formIdx n (k : ℤ)) => cf (trunc M k x) m t
  calc ∑ t : formIdx n (k : ℤ), ∑ r : Fin p → Fin n, ∫ y in Q (Fin n), (a t.1 r y) ^ 2
      ≤ ∑ t : formIdx n (k : ℤ), ∑ r : Fin p → Fin n, ∑ m ∈ bandS M,
          ‖symb (List.ofFn r) m‖ ^ 2 * ‖c m t‖ ^ 2 :=
        Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun r _ =>
          integral_iterPartial_truncField_sq_le x M _ t
    _ = ∑ t : formIdx n (k : ℤ), ∑ m ∈ bandS M, ∑ r : Fin p → Fin n,
          ‖symb (List.ofFn r) m‖ ^ 2 * ‖c m t‖ ^ 2 :=
        Finset.sum_congr rfl fun t _ => Finset.sum_comm
    _ = ∑ m ∈ bandS M, ∑ t : formIdx n (k : ℤ), ∑ r : Fin p → Fin n,
          ‖symb (List.ofFn r) m‖ ^ 2 * ‖c m t‖ ^ 2 := Finset.sum_comm
    _ = ∑ m ∈ bandS M, (‖freq m‖ ^ 2) ^ p * ‖cf (trunc M k x) m‖ ^ 2 := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [norm_cf_sq_eq_sum k, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← sum_norm_symb_sq p m, Finset.sum_mul]
    _ ≤ ∑ m ∈ bandS M, weight (p : ℝ) m * ‖cf (trunc M k x) m‖ ^ 2 := by
        refine Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        rw [weight, Real.rpow_natCast]
        exact pow_le_pow_left₀ (sq_nonneg _) (by linarith) p
    _ ≤ sobSum p (trunc M k x) :=
        Summable.sum_le_tsum _ (fun m _ => mul_nonneg (weight_nonneg _ _) (sq_nonneg _))
          (memSob_trunc (p : ℝ) M x)

/-- **Bernstein inequality**: for `x ∈ Hˢ(𝕋ⁿ)` and an integer order `p ≥ s`, the truncation
`u_M = (x_M)|_Q` satisfies `‖Dᵖ u_M‖²_{L²(Q)} ≤ 2ⁿ nᵖ (1 + n (2πM)²)^{p - s} ‖x‖²_{Hˢ(𝕋ⁿ)}`. -/
theorem sum_norm_iteratedFDeriv_truncQ_sq_le {s : ℝ} {p : ℕ} (hsp : s ≤ p) {x : Seq n k}
    (hx : MemSob s x) (M : ℕ) :
    ∫ y in Q (Fin n), ‖iteratedFDeriv ℝ p (truncField k x M) y‖ ^ 2 ≤
      2 ^ n * n ^ p * ((1 + n * (2 * Real.pi * M) ^ 2) ^ ((p : ℝ) - s) * sobSum s x) :=
  (integral_norm_iteratedFDeriv_truncField_sq_le x M p).trans
    (mul_le_mul_of_nonneg_left (sobSum_trunc_le hsp hx M) (by positivity))

end Bernstein

/-! ### Weak derivatives of every order -/

section Weak

variable {Ω : Set (Fin n → ℝ)}

theorem isTest_iterPartial {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : (Fin n → ℝ) → F} (hφ : IsTest Ω φ) (l : List (Fin n)) :
    IsTest Ω (iterPartial l φ) := by
  induction l with
  | nil => exact hφ
  | cons j l ih => exact ih.fderiv_apply (Pi.single j 1)

/-- `v = ∂^l f` weakly on `Ω` along the word `l` ([Brezis2011], §9.1; [Evans2010], §5.2.1). -/
def HasWeakDeriv (Ω : Set (Fin n → ℝ)) (l : List (Fin n)) (f v : L2 ℝ Ω) : Prop :=
  ∀ φ : (Fin n → ℝ) → ℝ, IsTest Ω φ →
    ∫ x in Ω, (f : (Fin n → ℝ) → ℝ) x * iterPartial l φ x =
      (-1) ^ l.length * ∫ x in Ω, (v : (Fin n → ℝ) → ℝ) x * φ x

/-- Every coefficient of `u` has weak derivatives in `L²(Ω)` along every word of length `≤ m`. -/
def HasWeakDerivs (Ω : Set (Fin n → ℝ)) (m : ℕ) {k : ℤ} (u : L2F ℝ Ω (formIdx n k)) : Prop :=
  ∀ t : formIdx n k, ∀ l : List (Fin n), l.length ≤ m → ∃ v : L2 ℝ Ω, HasWeakDeriv Ω l (u t) v

theorem HasWeakDeriv.unique (hΩ : IsOpen Ω) {l : List (Fin n)} {f v v' : L2 ℝ Ω}
    (h : HasWeakDeriv Ω l f v) (h' : HasWeakDeriv Ω l f v') : v = v' := by
  refine sub_eq_zero.1 (Feec.Domain.L2.eq_zero_of_forall_integral hΩ (v - v') fun g hg => ?_)
  have e1 := h g hg
  have e2 := h' g hg
  have hpow : ((-1 : ℝ) ^ l.length) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hint : ∀ w : L2 ℝ Ω, Integrable (fun x => (w : (Fin n → ℝ) → ℝ) x * g x)
      (volume.restrict Ω) := fun w => by
    have := Feec.Domain.inner_toL2 w hg
    exact (L2.integrable_inner (𝕜 := ℝ) w (Feec.Domain.toL2 hg)).congr (by
      filter_upwards [Feec.Domain.coeFn_toL2 hg] with x hx
      simp [hx, mul_comm])
  have e3 : ∫ x in Ω, (v : (Fin n → ℝ) → ℝ) x * g x = ∫ x in Ω, (v' : (Fin n → ℝ) → ℝ) x * g x :=
    mul_left_cancel₀ hpow (e1.symm.trans e2)
  calc ∫ x in Ω, starRingEnd ℝ (((v - v' : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) x) * ((g x : ℝ) : ℝ)
      = ∫ x in Ω, ((v : (Fin n → ℝ) → ℝ) x * g x - (v' : (Fin n → ℝ) → ℝ) x * g x) :=
        integral_congr_ae (by
          filter_upwards [Lp.coeFn_sub v v'] with x hx
          rw [hx, Pi.sub_apply]
          simp only [conj_trivial]
          ring)
    _ = (∫ x in Ω, (v : (Fin n → ℝ) → ℝ) x * g x) - ∫ x in Ω, (v' : (Fin n → ℝ) → ℝ) x * g x :=
        integral_sub (hint v) (hint v')
    _ = 0 := by rw [e3, sub_self]

theorem integral_mul_iterPartial {g : (Fin n → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    {φ : (Fin n → ℝ) → ℝ} (hφ : IsTest Ω φ) (l : List (Fin n)) :
    ∫ x in Ω, g x * iterPartial l φ x =
      (-1) ^ l.length * ∫ x in Ω, iterPartial l.reverse g x * φ x := by
  have hΩ1 : ∀ (ψ : (Fin n → ℝ) → ℝ), IsTest Ω ψ → ∀ F : (Fin n → ℝ) → ℝ,
      ∫ x in Ω, F x * ψ x = ∫ x, F x * ψ x := fun ψ hψ F =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hψ.eq_zero_of_notMem hx, mul_zero]
  rw [hΩ1 _ (isTest_iterPartial hφ l), hΩ1 _ hφ]
  induction l generalizing g with
  | nil => simp
  | cons j l ih =>
    have h1 := integral_partialDeriv_mul_eq_neg (f := iterPartial l φ) (g := g)
      ((contDiff_iterPartial hφ.contDiff l).of_le (by exact_mod_cast le_top))
      (isTest_iterPartial hφ l).hasCompactSupport (hg.of_le (by exact_mod_cast le_top)) j
    have e1 : ∫ x, g x * iterPartial (j :: l) φ x = ∫ x, partialDeriv j (iterPartial l φ) x * g x :=
      integral_congr_ae (Eventually.of_forall fun x => by
        simp only [iterPartial_cons]; ring)
    have e2 : ∫ x, iterPartial l φ x * partialDeriv j g x =
        ∫ x, partialDeriv j g x * iterPartial l φ x :=
      integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    rw [e1, h1, e2, ih (hg.partialDeriv (by simp) j), List.reverse_cons, iterPartial_append,
      List.length_cons, pow_succ]
    simp only [iterPartial_cons, iterPartial_nil]
    ring

theorem hasWeakDeriv_of_tendsto {l : List (Fin n)} {fM vM : ℕ → L2 ℝ Ω} {f v : L2 ℝ Ω}
    (hf : Tendsto fM atTop (𝓝 f)) (hv : Tendsto vM atTop (𝓝 v))
    (h : ∀ M, HasWeakDeriv Ω l (fM M) (vM M)) : HasWeakDeriv Ω l f v := by
  intro φ hφ
  have hψ := isTest_iterPartial hφ l
  have key : ∀ (w : L2 ℝ Ω) {ψ : (Fin n → ℝ) → ℝ} (hψ : IsTest Ω ψ),
      ∫ x in Ω, (w : (Fin n → ℝ) → ℝ) x * ψ x = ⟪w, Feec.Domain.toL2 hψ⟫_ℝ := fun w ψ hψ => by
    rw [Feec.Domain.inner_toL2]
    simp
  have h1 : Tendsto (fun M => ∫ x in Ω, (fM M : (Fin n → ℝ) → ℝ) x * iterPartial l φ x) atTop
      (𝓝 (∫ x in Ω, (f : (Fin n → ℝ) → ℝ) x * iterPartial l φ x)) := by
    simp_rw [key _ hψ]
    exact hf.inner tendsto_const_nhds
  have h2 : Tendsto (fun M => (-1) ^ l.length * ∫ x in Ω, (vM M : (Fin n → ℝ) → ℝ) x * φ x)
      atTop (𝓝 ((-1) ^ l.length * ∫ x in Ω, (v : (Fin n → ℝ) → ℝ) x * φ x)) := by
    simp_rw [key _ hφ]
    exact (hv.inner tendsto_const_nhds).const_mul _
  exact tendsto_nhds_unique h1 (h2.congr fun M => (h M φ hφ).symm)

end Weak

/-! ### `Hᵐ(Q)` of the Fourier definition has weak derivatives up to order `m` -/

section Forward

variable {k : ℕ}

theorem norm_symb_sq_le (l : List (Fin n)) (m : Fin n → ℤ) :
    ‖symb l m‖ ^ 2 ≤ weight l.length m := by
  rw [norm_symb_sq, weight, Real.rpow_natCast]
  have h1 : ∀ j, (2 * Real.pi * m j) ^ 2 ≤ 1 + ‖freq m‖ ^ 2 := fun j => by
    have : (2 * Real.pi * m j) ^ 2 ≤ ‖freq m‖ ^ 2 := by
      rw [norm_freq_sq, mul_pow]
      exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun i => ((m i : ℝ)) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)) (by positivity)
    linarith
  induction l with
  | nil => simp
  | cons j l ih =>
    have hp : 0 ≤ (l.map fun j => (2 * Real.pi * m j) ^ 2).prod := by
      rw [← norm_symb_sq]; positivity
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    calc (2 * Real.pi * m j) ^ 2 * (l.map fun j => (2 * Real.pi * m j) ^ 2).prod
        ≤ (1 + ‖freq m‖ ^ 2) * (1 + ‖freq m‖ ^ 2) ^ l.length :=
          mul_le_mul (h1 j) ih hp (by positivity)
      _ = _ := mul_comm _ _

open scoped Classical in
/-- The symbol multiplier `x ↦ (symb_l(m) x(m))_m` of `∂^l` (`0` if the result is not in `ℓ²`). -/
def mulSeq (l : List (Fin n)) (x : Seq n k) : Seq n k :=
  if h : Summable fun m => ‖symb l m • cf x m‖ ^ 2 then
    (memLp_of_summable h).toLp fun m => symb l m • cf x m
  else 0

theorem summable_symb_smul {s : ℝ} {x : Seq n k} (hx : MemSob s x) {l : List (Fin n)}
    (hl : (l.length : ℝ) ≤ s) : Summable fun m => ‖symb l m • cf x m‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun m => ?_) hx
  rw [norm_smul, mul_pow]
  exact mul_le_mul_of_nonneg_right ((norm_symb_sq_le l m).trans (weight_mono hl m)) (sq_nonneg _)

theorem cf_mulSeq {s : ℝ} {x : Seq n k} (hx : MemSob s x) {l : List (Fin n)}
    (hl : (l.length : ℝ) ≤ s) (m : Fin n → ℤ) : cf (mulSeq l x) m = symb l m • cf x m := by
  have h := summable_symb_smul hx hl
  simp only [mulSeq, h, dite_true]
  change ((memLp_of_summable h).toLp fun m => symb l m • cf x m :
    (Fin n → ℤ) → Form ℂ (Fin n) k) m = _
  rw [MemLp.coeFn_toLp_count]

theorem norm_mulSeq_sq_le {s : ℝ} {x : Seq n k} (hx : MemSob s x) {l : List (Fin n)}
    (hl : (l.length : ℝ) ≤ s) : ‖mulSeq l x‖ ^ 2 ≤ sobSum s x := by
  rw [norm_sq_eq_tsum]
  refine Summable.tsum_le_tsum (fun m => ?_) ?_ hx
  · rw [cf_mulSeq hx hl, norm_smul, mul_pow]
    exact mul_le_mul_of_nonneg_right ((norm_symb_sq_le l m).trans (weight_mono hl m))
      (sq_nonneg _)
  · simpa [cf_mulSeq hx hl] using summable_symb_smul hx hl

theorem hasWeakDeriv_Jinvf_trunc {s : ℝ} {x : Seq n k} (hx : MemSob s x) {l : List (Fin n)}
    (hl : (l.length : ℝ) ≤ s) (M : ℕ) (t : formIdx n (k : ℤ)) :
    HasWeakDeriv (Q (Fin n)) l (Jinvf k (trunc M k x) t) (Jinvf k (trunc M k (mulSeq l x)) t) := by
  intro φ hφ
  set c := fun m => cf (trunc M k x) m t
  have hc' : (fun m => cf (trunc M k (mulSeq l x)) m t) = fun m => symb l m * c m := by
    classical
    funext m
    simp only [c, cf_trunc]
    split_ifs
    · rw [cf_mulSeq hx hl]; rfl
    · simp
  have h1 : ∫ y in Q (Fin n), ((Jinvf k (trunc M k x) t : L2 ℝ (Q (Fin n))) :
      (Fin n → ℝ) → ℝ) y * iterPartial l φ y =
      ∫ y in Q (Fin n), (expSum (bandS M) c y).re * iterPartial l φ y := by
    refine integral_congr_ae ?_
    rw [Jinvf_trunc_eq_toL2F]
    filter_upwards [(memLp_trigLift k (trunc M k x) (bandS M) t).coeFn_toLp] with y hy
    change ((memLp_trigLift k (trunc M k x) (bandS M) t).toLp _ : (Fin n → ℝ) → ℝ) y * _ = _
    rw [hy, trigLift_eq_re_expSum]
  have h2 : ∫ y in Q (Fin n), ((Jinvf k (trunc M k (mulSeq l x)) t : L2 ℝ (Q (Fin n))) :
      (Fin n → ℝ) → ℝ) y * φ y =
      ∫ y in Q (Fin n), (expSum (bandS M) (fun m => symb l m * c m) y).re * φ y := by
    refine integral_congr_ae ?_
    rw [Jinvf_trunc_eq_toL2F]
    filter_upwards [(memLp_trigLift k (trunc M k (mulSeq l x)) (bandS M) t).coeFn_toLp] with y hy
    change ((memLp_trigLift k (trunc M k (mulSeq l x)) (bandS M) t).toLp _ :
      (Fin n → ℝ) → ℝ) y * _ = _
    rw [hy, trigLift_eq_re_expSum, hc']
  rw [h1, h2, integral_mul_iterPartial (contDiff_re_expSum _ _) hφ l, iterPartial_re_expSum]
  simp_rw [symb_reverse]

theorem hasWeakDeriv_of_memSob {s : ℝ} {x : Seq n k} (hx : MemSob s x) {l : List (Fin n)}
    (hl : (l.length : ℝ) ≤ s) (t : formIdx n (k : ℤ)) :
    HasWeakDeriv (Q (Fin n)) l (Jinvf k x t) (Jinvf k (mulSeq l x) t) := by
  have hc : Continuous fun y : Seq n k => (Jinvf k y t : L2 ℝ (Q (Fin n))) :=
    (PiLp.continuous_apply 2 _ t).comp (Jinvf k).continuous
  exact hasWeakDeriv_of_tendsto ((hc.tendsto x).comp (tendsto_trunc k x))
    ((hc.tendsto _).comp (tendsto_trunc k _)) fun M => hasWeakDeriv_Jinvf_trunc hx hl M t

/-- **The forms of `Hᵐ(Q; Λᵏ)` have weak derivatives**: every `u ∈ Hᵐ(Q; Λᵏ)`, `m ∈ ℕ`, has weak
derivatives in `L²(Q)` up to order `m`. -/
theorem hasWeakDerivs_of_mem_sobolevQ {m : ℕ} {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    (hu : u ∈ sobolevQ n k m) : HasWeakDerivs (Q (Fin n)) m u := by
  obtain ⟨x, hx, rfl⟩ := hu
  exact fun t l hl => ⟨_, hasWeakDeriv_of_memSob hx (by exact_mod_cast hl) t⟩

end Forward

/-! ### Weak derivatives on the torus and the integer Sobolev spaces `Hᵐ(𝕋ⁿ)` -/

section Torus

variable {k : ℕ}

theorem isSmooth_partialT {φ : UnitAddTorus (Fin n) → ℂ} (hφ : IsSmooth φ) (j : Fin n) :
    IsSmooth (partialT j φ) := by
  unfold IsSmooth
  have e : partialT j φ ∘ proj = fun y => fderiv ℝ (φ ∘ proj) y (Pi.single j 1) :=
    funext fun y => partialT_proj (hφ.contDiff_one.differentiable one_ne_zero) j y
  rw [e]
  exact ((show ContDiff ℝ ∞ (φ ∘ proj) from hφ).fderiv_right (m := ∞) (by simp)).clm_apply
    contDiff_const

/-- Iterated partial derivatives on `𝕋ⁿ` along a word, `∂^{[j₁,…,j_p]} = ∂_{j₁} ⋯ ∂_{j_p}`. -/
def iterPartialT : List (Fin n) → (UnitAddTorus (Fin n) → ℂ) → UnitAddTorus (Fin n) → ℂ
  | [], φ => φ
  | j :: l, φ => partialT j (iterPartialT l φ)

theorem isSmooth_iterPartialT {φ : UnitAddTorus (Fin n) → ℂ} (hφ : IsSmooth φ)
    (l : List (Fin n)) : IsSmooth (iterPartialT l φ) := by
  induction l with
  | nil => exact hφ
  | cons j l ih => exact isSmooth_partialT ih j

theorem mFourierCoeff_iterPartialT {φ : UnitAddTorus (Fin n) → ℂ} (hφ : IsSmooth φ)
    (l : List (Fin n)) (m : Fin n → ℤ) :
    mFourierCoeff (iterPartialT l φ) m = symb l m * mFourierCoeff φ m := by
  induction l with
  | nil => simp [iterPartialT]
  | cons j l ih =>
    change mFourierCoeff (partialT j (iterPartialT l φ)) m = _
    rw [mFourierCoeff_partialT (isSmooth_iterPartialT hφ l).contDiff_one, ih, symb_cons]
    ring

theorem iterPartialT_mFourier (l : List (Fin n)) (m : Fin n → ℤ) :
    iterPartialT l (mFourier m) = fun x => symb l m * mFourier m x := by
  induction l with
  | nil => funext x; simp [iterPartialT]
  | cons j l ih =>
    funext x
    change partialT j (iterPartialT l (mFourier m)) x = _
    rw [ih]
    have h : partialT j (fun x => symb l m * mFourier m x) x =
        symb l m * partialT j (mFourier m) x := by
      have h1 := partialT_mul (φ := fun _ => symb l m) (ψ := mFourier m) (differentiable_const _)
        ((isSmooth_mFourier m).contDiff_one.differentiable one_ne_zero) j x
      have h0 : partialT j (fun _ : UnitAddTorus (Fin n) => symb l m) x = 0 := by
        unfold partialT; simp
      rw [h1, h0, zero_mul, zero_add]
    rw [h, partialT_mFourier, symb_cons]
    ring

theorem symb_neg (l : List (Fin n)) (m : Fin n → ℤ) :
    symb l (-m) = (-1) ^ l.length * symb l m := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [symb_cons, symb_cons, ih, List.length_cons, pow_succ]
    simp only [Pi.neg_apply, Int.cast_neg]
    ring

/-- **`v = ∂^l f` weakly on `𝕋ⁿ`**: `∫ f ∂^l φ = (-1)^{|l|} ∫ v φ` for every smooth `φ`. -/
def HasWeakDerivT (l : List (Fin n)) (f v : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin n)))) :
    Prop :=
  ∀ φ : UnitAddTorus (Fin n) → ℂ, IsSmooth φ →
    ∫ x, f x * iterPartialT l φ x = (-1) ^ l.length * ∫ x, v x * φ x

/-- **Weak derivatives up to order `m` in `L²(𝕋ⁿ)`**. -/
def HasWeakDerivsT (m : ℕ) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin n)))) : Prop :=
  ∀ l : List (Fin n), l.length ≤ m → ∃ v, HasWeakDerivT l f v

theorem mFourierCoeff_physF (x : Seq n k) (t : formIdx n (k : ℤ)) (m : Fin n → ℤ) :
    mFourierCoeff (physF k x t : UnitAddTorus (Fin n) → ℂ) m = cf x m t := by
  rw [← mFourierBasis_repr, repr_physF]

theorem hasWeakDerivT_physF {s : ℝ} {x : Seq n k} (hx : MemSob s x) {l : List (Fin n)}
    (hl : (l.length : ℝ) ≤ s) (t : formIdx n (k : ℤ)) :
    HasWeakDerivT l (physF k x t) (physF k (mulSeq l x) t) := by
  intro φ hφ
  have h1 := hasSum_pairing (physF k x t) (isSmooth_iterPartialT hφ l).continuous
  have h2 := hasSum_pairing (physF k (mulSeq l x) t) hφ.continuous
  rw [← h1.tsum_eq, ← h2.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [mFourierCoeff_iterPartialT hφ, symb_neg, mFourierCoeff_physF, mFourierCoeff_physF,
    cf_mulSeq hx hl]
  change _ = _ * (_ * (symb l m * cf x m t))
  ring

theorem HasWeakDerivT.mFourierCoeff_eq {l : List (Fin n)}
    {f v : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin n)))} (h : HasWeakDerivT l f v)
    (m : Fin n → ℤ) : mFourierCoeff (v : UnitAddTorus (Fin n) → ℂ) m =
      symb l m * mFourierCoeff (f : UnitAddTorus (Fin n) → ℂ) m := by
  have e := h _ (isSmooth_mFourier (-m))
  rw [iterPartialT_mFourier] at e
  have e1 : ∫ x, (f : UnitAddTorus (Fin n) → ℂ) x * (symb l (-m) * mFourier (-m) x) =
      symb l (-m) * mFourierCoeff (f : UnitAddTorus (Fin n) → ℂ) m := by
    rw [mFourierCoeff, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul]; ring
  have e2 : ∫ x, (v : UnitAddTorus (Fin n) → ℂ) x * mFourier (-m) x =
      mFourierCoeff (v : UnitAddTorus (Fin n) → ℂ) m := by
    rw [mFourierCoeff]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul]; ring
  rw [e1, e2, symb_neg] at e
  have hne : ((-1 : ℂ) ^ l.length) ≠ 0 := pow_ne_zero _ (by norm_num)
  refine mul_left_cancel₀ hne ?_
  rw [← e]
  ring

theorem weight_mul_le_pure (x : Seq n k) (m : ℕ) (q : Fin n → ℤ) :
    weight ((m + 1 : ℕ) : ℝ) q * ‖cf x q‖ ^ 2 ≤ (n + 1 : ℝ) ^ m *
      (‖cf x q‖ ^ 2 + ∑ j, ∑ t : formIdx n (k : ℤ),
        ((2 * Real.pi * q j) ^ 2) ^ (m + 1) * ‖cf x q t‖ ^ 2) := by
  set a : Option (Fin n) → ℝ := fun i => i.elim 1 fun j => (2 * Real.pi * q j) ^ 2
  have ha : ∀ i ∈ (Finset.univ : Finset (Option (Fin n))), 0 ≤ a i := fun i _ => by
    cases i <;> simp [a, sq_nonneg]
  have hpm := pow_sum_le_card_mul_sum_pow ha m
  have hS : ∑ i, a i = 1 + ‖freq q‖ ^ 2 := by
    rw [Fintype.sum_option, norm_freq_sq, Finset.mul_sum]
    simp only [a, Option.elim]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hS' : ∑ i, a i ^ (m + 1) = 1 + ∑ j, ((2 * Real.pi * q j) ^ 2) ^ (m + 1) := by
    rw [Fintype.sum_option]; simp [a]
  rw [hS, hS', Finset.card_univ, Fintype.card_option, Fintype.card_fin] at hpm
  rw [weight, Real.rpow_natCast]
  calc (1 + ‖freq q‖ ^ 2) ^ (m + 1) * ‖cf x q‖ ^ 2
      ≤ ((n + 1 : ℕ) : ℝ) ^ m * (1 + ∑ j, ((2 * Real.pi * q j) ^ 2) ^ (m + 1)) *
        ‖cf x q‖ ^ 2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hpm) (sq_nonneg _)
    _ = _ := by
      push_cast
      rw [mul_assoc, add_mul, one_mul, Finset.sum_mul]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [norm_cf_sq_eq_sum k, Finset.mul_sum]

theorem sobSum_le (x : Seq n k) {m : ℕ}
    (v : Fin n → formIdx n (k : ℤ) → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin n))))
    (hv : ∀ j t, HasWeakDerivT (List.replicate (m + 1) j) (physF k x t) (v j t)) :
    sobSum ((m + 1 : ℕ) : ℝ) x ≤ (n + 1 : ℝ) ^ m * (‖x‖ ^ 2 + ∑ j, ∑ t, ‖v j t‖ ^ 2) := by
  have hpure : ∀ j t, HasSum (fun q : Fin n → ℤ =>
      ((2 * Real.pi * q j) ^ 2) ^ (m + 1) * ‖cf x q t‖ ^ 2) (‖v j t‖ ^ 2) := by
    intro j t
    have h := hasSum_sq_mFourierCoeff (v j t)
    rw [← Feec.Models.Cube.Geometry.norm_sq_eq_integral] at h
    have e : (fun q => ‖mFourierCoeff (v j t : UnitAddTorus (Fin n) → ℂ) q‖ ^ 2) = fun q =>
        ((2 * Real.pi * q j) ^ 2) ^ (m + 1) * ‖cf x q t‖ ^ 2 := by
      funext q
      rw [(hv j t).mFourierCoeff_eq, mFourierCoeff_physF, norm_mul, mul_pow, norm_symb_sq]
      simp
    rwa [e] at h
  have hx : HasSum (fun q => ‖cf x q‖ ^ 2) (‖x‖ ^ 2) := by
    rw [norm_sq_eq_tsum]; exact (summable_norm_sq x).hasSum
  have hb := (hx.add (hasSum_sum (s := Finset.univ) fun j _ =>
    hasSum_sum (s := Finset.univ) fun t _ => hpure j t)).mul_left ((n + 1 : ℝ) ^ m)
  have hs : Summable fun q => weight ((m + 1 : ℕ) : ℝ) q * ‖cf x q‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun q => mul_nonneg (weight_nonneg _ _) (sq_nonneg _))
      (weight_mul_le_pure x m) hb.summable
  exact (hs.tsum_le_tsum (weight_mul_le_pure x m) hb.summable).trans_eq hb.tsum_eq

/-- **The integer Sobolev spaces of the torus are the spaces of weak derivatives**: `x ∈ Hᵐ(𝕋ⁿ)`
iff the components of `physF k x` have weak derivatives up to order `m` in `L²(𝕋ⁿ)`. -/
theorem memSob_nat_iff (x : Seq n k) (m : ℕ) :
    MemSob m x ↔ ∀ t, HasWeakDerivsT m (physF k x t) := by
  constructor
  · intro hx t l hl
    exact ⟨_, hasWeakDerivT_physF hx (by exact_mod_cast hl) t⟩
  · intro h
    rcases m with _ | m
    · rw [Nat.cast_zero]; exact memSob_zero x
    -- the pure derivatives `∂_j^{m+1}` of every component
    have hpure : ∀ (j : Fin n) (t : formIdx n (k : ℤ)), Summable fun q : Fin n → ℤ =>
        ((2 * Real.pi * q j) ^ 2) ^ (m + 1) * ‖cf x q t‖ ^ 2 := by
      intro j t
      obtain ⟨v, hv⟩ := h t (List.replicate (m + 1) j) (by simp)
      refine ((hasSum_sq_mFourierCoeff v).summable).congr fun q => ?_
      rw [hv.mFourierCoeff_eq, mFourierCoeff_physF, norm_mul, mul_pow, norm_symb_sq]
      simp
    exact Summable.of_nonneg_of_le (fun q => mul_nonneg (weight_nonneg _ _) (sq_nonneg _))
      (weight_mul_le_pure x m) (((summable_norm_sq x).add
        (summable_sum fun j _ => summable_sum fun t _ => hpure j t)).mul_left _)

theorem mem_sobolevPar_nat_iff (J : Finset (Fin n)) (m : ℕ)
    (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    u ∈ sobolevPar J k m ↔ ∀ t, HasWeakDerivsT m (physF k (JfJ J k u) t) := by
  rw [mem_sobolevPar]
  exact memSob_nat_iff _ m

end Torus

/-! ### The `Hᵐ` norm by weak derivatives -/

section Norm

variable {k : ℕ}

open scoped Classical in
/-- The squared `Hᵐ` norm `Σ_t Σ_{|r| ≤ m} ‖∂^r u_t‖²` by weak derivatives along words `r`. -/
def weakHmNormSq (Ω : Set (Fin n → ℝ)) (m : ℕ) {k' : ℤ} (u : L2F ℝ Ω (formIdx n k')) : ℝ :=
  ∑ t : formIdx n k', ∑ p ∈ Finset.range (m + 1), ∑ r : Fin p → Fin n,
    if h : ∃ v, HasWeakDeriv Ω (List.ofFn r) (u t) v then ‖h.choose‖ ^ 2 else 0

theorem weakHmNormSq_le_qNorm_sq {m : ℕ} {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    (hu : u ∈ sobolevQ n k m) :
    weakHmNormSq (Q (Fin n)) m u ≤ (∑ p ∈ Finset.range (m + 1), (n : ℝ) ^ p) * qNorm k m u ^ 2 := by
  classical
  have hC : 0 ≤ ∑ p ∈ Finset.range (m + 1), (n : ℝ) ^ p := Finset.sum_nonneg fun _ _ => by
    positivity
  have key : ∀ x : Seq n k, MemSob m x → Jinvf k x = u →
      √(weakHmNormSq (Q (Fin n)) m u) ≤ √(∑ p ∈ Finset.range (m + 1), (n : ℝ) ^ p) *
        √(sobSum m x) := by
    intro x hx hxu
    rw [← Real.sqrt_mul hC]
    refine Real.sqrt_le_sqrt ?_
    have hterm : ∀ t : formIdx n (k : ℤ), ∀ p ∈ Finset.range (m + 1), ∀ r : Fin p → Fin n,
        (if h : ∃ v, HasWeakDeriv (Q (Fin n)) (List.ofFn r) (u t) v then ‖h.choose‖ ^ 2 else 0) =
          ‖(Jinvf k (mulSeq (List.ofFn r) x)) t‖ ^ 2 := by
      intro t p hp r
      have hl : ((List.ofFn r).length : ℝ) ≤ m := by
        rw [List.length_ofFn]; exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
      have hw := hasWeakDeriv_of_memSob hx hl t
      rw [hxu] at hw
      have hex : ∃ v, HasWeakDeriv (Q (Fin n)) (List.ofFn r) (u t) v := ⟨_, hw⟩
      rw [dite_eq_left_of_eq_true (eq_true hex), hex.choose_spec.unique isOpen_Q hw]
    have hcomp : ∀ y : Seq n k, ∑ t : formIdx n (k : ℤ), ‖(Jinvf k y) t‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      intro y
      rw [← PiLp.norm_sq_eq_of_L2]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_Jinvf_le k y) 2
    calc weakHmNormSq (Q (Fin n)) m u
        = ∑ t : formIdx n (k : ℤ), ∑ p ∈ Finset.range (m + 1), ∑ r : Fin p → Fin n,
            ‖(Jinvf k (mulSeq (List.ofFn r) x)) t‖ ^ 2 :=
          Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun p hp =>
            Finset.sum_congr rfl fun r _ => hterm t p hp r
      _ = ∑ p ∈ Finset.range (m + 1), ∑ r : Fin p → Fin n, ∑ t : formIdx n (k : ℤ),
            ‖(Jinvf k (mulSeq (List.ofFn r) x)) t‖ ^ 2 := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ ≤ ∑ p ∈ Finset.range (m + 1), ∑ _r : Fin p → Fin n, sobSum m x := by
          refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun r _ => (hcomp _).trans ?_
          refine norm_mulSeq_sq_le hx ?_
          rw [List.length_ofFn]; exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
      _ = (∑ p ∈ Finset.range (m + 1), (n : ℝ) ^ p) * sobSum m x := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have h := le_mul_qNorm hu (Real.sqrt_nonneg _) key
  have h0 := Real.sqrt_nonneg (weakHmNormSq (Q (Fin n)) m u)
  have hw0 : 0 ≤ weakHmNormSq (Q (Fin n)) m u := Finset.sum_nonneg fun t _ =>
    Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun r _ => by split_ifs <;> positivity
  calc weakHmNormSq (Q (Fin n)) m u = (√(weakHmNormSq (Q (Fin n)) m u)) ^ 2 :=
        (Real.sq_sqrt hw0).symm
    _ ≤ (√(∑ p ∈ Finset.range (m + 1), (n : ℝ) ^ p) * qNorm k m u) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hC]

end Norm

/-! ### `H²` in the parity classes: the compatibility conditions -/

section ParityTwo

variable {k : ℕ}

theorem realParJ_mulSeq_single {J : Finset (Fin n)} {x : Seq n k} (hJ : RealParJ J k x)
    {s : ℝ} (hx : MemSob s x) (hs : 1 ≤ s) (j : Fin n) :
    RealParJ (symmDiff J {j}) k (mulSeq [j] x) := by
  have hl : (([j] : List (Fin n)).length : ℝ) ≤ s := by simpa using hs
  refine ⟨fun m t => ?_, fun i m t => ?_⟩
  · change cf (mulSeq [j] x) (-m) t = conj (cf (mulSeq [j] x) m t)
    rw [cf_mulSeq hx hl, cf_mulSeq hx hl]
    change symb [j] (-m) * cf x (-m) t = conj (symb [j] m * cf x m t)
    rw [show cf x (-m) t = conj (cf x m t) from hJ.1 m t, map_mul]
    simp only [symb, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Pi.neg_apply, Int.cast_neg, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
      map_intCast]
    ring
  · change cf (mulSeq [j] x) (Fourier.Torus.flipAt i m) t = _ * cf (mulSeq [j] x) m t
    rw [cf_mulSeq hx hl, cf_mulSeq hx hl]
    change symb [j] (Fourier.Torus.flipAt i m) * cf x (Fourier.Torus.flipAt i m) t =
      _ * (symb [j] m * cf x m t)
    rw [show cf x (Fourier.Torus.flipAt i m) t = _ from hJ.2 i m t]
    simp only [symb, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Fourier.Torus.flipAt_apply, DeRham.mixedSign, Finset.mem_symmDiff, Finset.mem_singleton]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i ∈ J <;> simp [hi] <;> ring
    · have : ¬ (j = i) := fun h => hij h.symm
      simp [hij, this]
      ring_nf

theorem mem_sobolevPar_two_compat (J : Finset (Fin n))
    {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))} (hu : u ∈ sobolevPar J k 2) :
    (∀ t : formIdx n (k : ℤ),
      zeroF (u t) ∈ (dPart (Q (Fin n)) (symmDiff J t.1) ((0 : ℕ) : ℤ)).domain) ∧
    ∀ j : Fin n, ∃ w : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)),
      w ∈ sobolevPar (symmDiff J {j}) k 1 ∧ (∀ t, HasWeakDeriv (Q (Fin n)) [j] (u t) (w t)) ∧
      ∀ t : formIdx n (k : ℤ),
        zeroF (w t) ∈ (dPart (Q (Fin n)) (symmDiff (symmDiff J {j}) t.1) ((0 : ℕ) : ℤ)).domain := by
  have hx : MemSob 2 (JfJ J k u) := (mem_sobolevPar J k).1 hu
  refine ⟨(mem_sobolevPar_one_iff J k).1 (sobolevPar_anti J k (by norm_num) hu), fun j => ?_⟩
  have hl : (([j] : List (Fin n)).length : ℝ) ≤ 2 := by norm_num
  set y := mulSeq [j] (JfJ J k u)
  have hy : RealParJ (symmDiff J {j}) k y :=
    realParJ_mulSeq_single (JfJ_realParJ J k u) hx (by norm_num) j
  have hy1 : MemSob 1 y := by
    refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (weight_nonneg _ _) (sq_nonneg _))
      (fun m => ?_) hx
    rw [cf_mulSeq hx hl, norm_smul, mul_pow, show (2 : ℝ) = 1 + 1 by norm_num, weight_add,
      mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (weight_nonneg _ _)
    exact mul_le_mul_of_nonneg_right ((norm_symb_sq_le _ m).trans (by simp)) (sq_nonneg _)
  have hw : Jinvf k y ∈ sobolevPar (symmDiff J {j}) k 1 := by
    rw [mem_sobolevPar, JfJ_Jinvf hy]; exact hy1
  refine ⟨Jinvf k y, hw, fun t => ?_, (mem_sobolevPar_one_iff _ k).1 hw⟩
  have h := hasWeakDeriv_of_memSob hx hl t
  rwa [Jinvf_JfJ] at h

end ParityTwo

/-! ### The recursion of the weak `Hᵐ` norm -/

section WeakSucc

variable {Ω : Set (Fin n → ℝ)}

theorem hasWeakDeriv_nil_self (f : L2 ℝ Ω) : HasWeakDeriv Ω [] f f := fun φ _ => by simp

theorem hasWeakDeriv_cons_iff {j : Fin n} {f g : L2 ℝ Ω}
    (hg : HasWeakDeriv Ω [j] f g) (l : List (Fin n)) (v : L2 ℝ Ω) :
    HasWeakDeriv Ω (j :: l) f v ↔ HasWeakDeriv Ω l g v := by
  have e : ∀ φ, IsTest Ω φ → ∫ x in Ω, (f : (Fin n → ℝ) → ℝ) x * iterPartial (j :: l) φ x =
      -∫ x in Ω, (g : (Fin n → ℝ) → ℝ) x * iterPartial l φ x := fun φ hφ => by
    rw [show iterPartial (j :: l) φ = iterPartial [j] (iterPartial l φ) from rfl,
      hg _ (isTest_iterPartial hφ l)]
    simp
  refine forall₂_congr fun φ hφ => ?_
  rw [e φ hφ, List.length_cons, pow_succ]
  constructor <;> intro h <;> linear_combination -h

open scoped Classical in
theorem dite_hasWeakDeriv_nil (hΩ : IsOpen Ω) (f : L2 ℝ Ω) :
    (if h : ∃ v, HasWeakDeriv Ω [] f v then ‖h.choose‖ ^ 2 else 0) = ‖f‖ ^ 2 := by
  have hex : ∃ v, HasWeakDeriv Ω [] f v := ⟨f, hasWeakDeriv_nil_self f⟩
  rw [dite_eq_left hex, hex.choose_spec.unique hΩ (hasWeakDeriv_nil_self f)]

open scoped Classical in
theorem dite_hasWeakDeriv_cons (hΩ : IsOpen Ω) {j : Fin n} {f g : L2 ℝ Ω}
    (hg : HasWeakDeriv Ω [j] f g) (l : List (Fin n)) :
    (if h : ∃ v, HasWeakDeriv Ω (j :: l) f v then ‖h.choose‖ ^ 2 else 0) =
      (if h : ∃ v, HasWeakDeriv Ω l g v then ‖h.choose‖ ^ 2 else 0) := by
  have e : (∃ v, HasWeakDeriv Ω (j :: l) f v) ↔ ∃ v, HasWeakDeriv Ω l g v :=
    exists_congr fun v => hasWeakDeriv_cons_iff hg l v
  by_cases h : ∃ v, HasWeakDeriv Ω l g v
  · rw [dite_eq_left (e.2 h), dite_eq_left h,
      (e.2 h).choose_spec.unique hΩ ((hasWeakDeriv_cons_iff hg l _).2 h.choose_spec)]
  · rw [dite_eq_right (mt e.1 h), dite_eq_right h]

theorem weakHmNormSq_zero (hΩ : IsOpen Ω) {k' : ℤ} (u : L2F ℝ Ω (formIdx n k')) :
    weakHmNormSq Ω 0 u = ‖u‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  unfold weakHmNormSq
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_range_one, Fintype.sum_unique, List.ofFn_zero]
  convert dite_hasWeakDeriv_nil hΩ (u t)

theorem weakHmNormSq_mono {m m' : ℕ} (h : m ≤ m') {k' : ℤ} (u : L2F ℝ Ω (formIdx n k')) :
    weakHmNormSq Ω m u ≤ weakHmNormSq Ω m' u := by
  classical
  unfold weakHmNormSq
  refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 (by omega)) fun p _ _ => Finset.sum_nonneg fun r _ => ?_
  split_ifs <;> positivity

theorem weakHmNormSq_succ (hΩ : IsOpen Ω) {m : ℕ} {k' : ℤ} {u : L2F ℝ Ω (formIdx n k')}
    {w : Fin n → L2F ℝ Ω (formIdx n k')} (hw : ∀ j t, HasWeakDeriv Ω [j] (u t) (w j t)) :
    weakHmNormSq Ω (m + 1) u = ‖u‖ ^ 2 + ∑ j, weakHmNormSq Ω m (w j) := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  unfold weakHmNormSq
  have ht : ∀ t : formIdx n k', ∑ p ∈ Finset.range (m + 1 + 1), ∑ r : Fin p → Fin n,
      (if h : ∃ v, HasWeakDeriv Ω (List.ofFn r) (u t) v then ‖h.choose‖ ^ 2 else 0) =
      ‖u t‖ ^ 2 + ∑ j, ∑ p ∈ Finset.range (m + 1), ∑ r : Fin p → Fin n,
        (if h : ∃ v, HasWeakDeriv Ω (List.ofFn r) (w j t) v then ‖h.choose‖ ^ 2 else 0) := by
    intro t
    rw [Finset.sum_range_succ', add_comm, Finset.sum_comm]
    congr 1
    · rw [Fintype.sum_unique, List.ofFn_zero]
      convert dite_hasWeakDeriv_nil hΩ (u t)
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [← (Fin.consEquiv fun _ : Fin (p + 1) => Fin n).sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun r _ => ?_
      simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
      exact dite_hasWeakDeriv_cons hΩ (hw j t) _
  rw [Finset.sum_congr rfl fun t _ => ht t, Finset.sum_add_distrib, Finset.sum_comm]

end WeakSucc

/-! ### The parity classes of every integer order, intrinsically on `Q` -/

section ParitySucc

variable {k : ℕ}

theorem norm_cf_mulSeq_single_sq {x : Seq n k} (hx1 : MemSob 1 x) (j : Fin n) (q : Fin n → ℤ) :
    ‖cf (mulSeq [j] x) q‖ ^ 2 = (2 * Real.pi * q j) ^ 2 * ‖cf x q‖ ^ 2 := by
  rw [cf_mulSeq hx1 (by simp), norm_smul, mul_pow, norm_symb_sq]
  simp

theorem weight_add_one_mul {x : Seq n k} (hx1 : MemSob 1 x) (s : ℝ) (q : Fin n → ℤ) :
    weight (s + 1) q * ‖cf x q‖ ^ 2 =
      weight s q * ‖cf x q‖ ^ 2 + ∑ j, weight s q * ‖cf (mulSeq [j] x) q‖ ^ 2 := by
  simp_rw [norm_cf_mulSeq_single_sq hx1]
  rw [weight_add, weight_one, norm_freq_sq, Finset.mul_sum]
  have : ∀ j : Fin n, weight s q * ((2 * Real.pi * q j) ^ 2 * ‖cf x q‖ ^ 2) =
      weight s q * (2 * Real.pi) ^ 2 * ‖cf x q‖ ^ 2 * (q j : ℝ) ^ 2 := fun j => by ring
  simp_rw [this, ← Finset.mul_sum]
  ring

theorem memSob_add_one_iff {x : Seq n k} (hx1 : MemSob 1 x) (s : ℝ) :
    MemSob (s + 1) x ↔ MemSob s x ∧ ∀ j, MemSob s (mulSeq [j] x) := by
  constructor
  · intro h
    refine ⟨h.mono (by linarith), fun j => ?_⟩
    refine Summable.of_nonneg_of_le (fun q => mul_nonneg (weight_nonneg _ _) (sq_nonneg _))
      (fun q => ?_) h
    rw [weight_add_one_mul hx1]
    have h1 := Finset.single_le_sum (f := fun j => weight s q * ‖cf (mulSeq [j] x) q‖ ^ 2)
      (fun _ _ => mul_nonneg (weight_nonneg _ _) (sq_nonneg _)) (Finset.mem_univ j)
    have h2 := mul_nonneg (weight_nonneg s q) (sq_nonneg ‖cf x q‖)
    linarith
  · rintro ⟨hs, hj⟩
    exact ((show Summable _ from hs).add (summable_sum fun j _ => hj j)).congr fun q =>
      (weight_add_one_mul hx1 s q).symm

theorem sobSum_add_one {x : Seq n k} (hx1 : MemSob 1 x) {s : ℝ} (h : MemSob (s + 1) x) :
    sobSum (s + 1) x = sobSum s x + ∑ j, sobSum s (mulSeq [j] x) := by
  obtain ⟨hs, hj⟩ := (memSob_add_one_iff hx1 s).1 h
  unfold sobSum
  simp_rw [weight_add_one_mul hx1 s]
  rw [Summable.tsum_add hs (summable_sum fun j _ => hj j),
    Summable.tsum_finsetSum fun j _ => hj j]

theorem memSob_nat_add_one_iff {x : Seq n k} (hx1 : MemSob 1 x) (m : ℕ) :
    MemSob ((m : ℝ) + 1) x ↔ ∀ j, MemSob m (mulSeq [j] x) := by
  refine ⟨fun h => ((memSob_add_one_iff hx1 m).1 h).2, fun h => ?_⟩
  have key : ∀ r : ℕ, r ≤ m → MemSob ((r : ℝ) + 1) x := by
    intro r
    induction r with
    | zero => intro _; simpa using hx1
    | succ r ih =>
      intro hr
      have := (memSob_add_one_iff hx1 ((r : ℝ) + 1)).2 ⟨ih (by omega),
        fun j => (h j).mono (by exact_mod_cast hr)⟩
      push_cast
      exact this
  exact key m le_rfl

theorem mulSeq_eq_of_hasWeakDeriv {J : Finset (Fin n)} {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    (hu : u ∈ sobolevPar J k 1) {j : Fin n} {w : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    (hw : ∀ t, HasWeakDeriv (Q (Fin n)) [j] (u t) (w t)) :
    w = Jinvf k (mulSeq [j] (JfJ J k u)) ∧
      JfJ (symmDiff J {j}) k w = mulSeq [j] (JfJ J k u) := by
  have hx1 : MemSob 1 (JfJ J k u) := hu
  have e : w = Jinvf k (mulSeq [j] (JfJ J k u)) := PiLp.ext fun t => by
    have h := hasWeakDeriv_of_memSob hx1 (l := [j]) (by simp) t
    rw [Jinvf_JfJ] at h
    exact (hw t).unique isOpen_Q h
  refine ⟨e, ?_⟩
  rw [e, JfJ_Jinvf (realParJ_mulSeq_single (JfJ_realParJ J k u) hx1 le_rfl j)]

/-- **The parity classes of every integer order on `Q`**: `u ∈ H^{m+1}_J(Q)` iff `u ∈ H¹_J(Q)` and
every weak derivative `∂_j u` exists and lies in `Hᵐ_{J ∆ {j}}(Q)`. -/
theorem mem_sobolevPar_add_one_iff (J : Finset (Fin n)) (m : ℕ)
    (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    u ∈ sobolevPar J k ((m : ℝ) + 1) ↔ u ∈ sobolevPar J k 1 ∧ ∀ j : Fin n,
      ∃ w ∈ sobolevPar (symmDiff J {j}) k m, ∀ t, HasWeakDeriv (Q (Fin n)) [j] (u t) (w t) := by
  constructor
  · intro hu
    have hx : MemSob ((m : ℝ) + 1) (JfJ J k u) := hu
    have hu1 : u ∈ sobolevPar J k 1 :=
      sobolevPar_anti J k (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) hu
    have hx1 : MemSob 1 (JfJ J k u) := hu1
    refine ⟨hu1, fun j => ⟨Jinvf k (mulSeq [j] (JfJ J k u)), ?_, fun t => ?_⟩⟩
    · rw [mem_sobolevPar, JfJ_Jinvf (realParJ_mulSeq_single (JfJ_realParJ J k u) hx1 le_rfl j)]
      exact (memSob_nat_add_one_iff hx1 m).1 hx j
    · have h := hasWeakDeriv_of_memSob hx1 (l := [j]) (by simp) t
      rwa [Jinvf_JfJ] at h
  · rintro ⟨hu1, hw⟩
    refine (memSob_nat_add_one_iff hu1 m).2 fun j => ?_
    obtain ⟨w, hwm, hwd⟩ := hw j
    rw [← (mulSeq_eq_of_hasWeakDeriv hu1 hwd).2]
    exact hwm

/-- **`H²` in the parity classes**: `u ∈ H²_J(Q)` iff each `u_t` and `∂_j u_t` lies in `H¹(Q)`
with vanishing traces on the faces normal to `J ∆ t` and `(J ∆ {j}) ∆ t`. -/
theorem mem_sobolevPar_two_iff (J : Finset (Fin n)) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    u ∈ sobolevPar J k 2 ↔ (∀ t : formIdx n (k : ℤ),
      zeroF (u t) ∈ (dPart (Q (Fin n)) (symmDiff J t.1) ((0 : ℕ) : ℤ)).domain) ∧
    ∀ j : Fin n, ∃ w : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)),
      w ∈ sobolevPar (symmDiff J {j}) k 1 ∧ (∀ t, HasWeakDeriv (Q (Fin n)) [j] (u t) (w t)) ∧
      ∀ t : formIdx n (k : ℤ),
        zeroF (w t) ∈ (dPart (Q (Fin n)) (symmDiff (symmDiff J {j}) t.1) ((0 : ℕ) : ℤ)).domain := by
  refine ⟨mem_sobolevPar_two_compat J, fun ⟨h1, hw⟩ => ?_⟩
  have h := (mem_sobolevPar_add_one_iff J 1 u).2 ⟨(mem_sobolevPar_one_iff J k).2 h1, fun j => by
    obtain ⟨w, hw1, hd, -⟩ := hw j
    exact ⟨w, by simpa using hw1, hd⟩⟩
  rwa [show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num] at h

theorem parNorm_add_one_sq (J : Finset (Fin n)) {m : ℕ}
    {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))} (hu : u ∈ sobolevPar J k ((m : ℝ) + 1))
    {w : Fin n → L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    (hw : ∀ j t, HasWeakDeriv (Q (Fin n)) [j] (u t) (w j t)) :
    parNorm J k ((m : ℝ) + 1) u ^ 2 =
      parNorm J k m u ^ 2 + ∑ j, parNorm (symmDiff J {j}) k m (w j) ^ 2 := by
  have hu1 : u ∈ sobolevPar J k 1 :=
    sobolevPar_anti J k (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) hu
  have e : ∀ j, JfJ (symmDiff J {j}) k (w j) = mulSeq [j] (JfJ J k u) := fun j =>
    (mulSeq_eq_of_hasWeakDeriv hu1 (hw j)).2
  simp only [parNorm_sq, e, sobSum_add_one (hu1 : MemSob 1 _) hu, mul_add, Finset.mul_sum]

/-- **Norm comparison on the parity classes, `≤`**: for `u ∈ Hᵐ_J(Q)`,
`Σ_t Σ_{|r| ≤ m} ‖∂^r u_t‖²_{L²(Q)} ≤ ‖u‖²_{m,J}`. -/
theorem weakHmNormSq_le_parNorm_sq (J : Finset (Fin n)) (m : ℕ)
    {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))} (hu : u ∈ sobolevPar J k m) :
    weakHmNormSq (Q (Fin n)) m u ≤ parNorm J k m u ^ 2 := by
  induction m generalizing J u with
  | zero => rw [weakHmNormSq_zero isOpen_Q, Nat.cast_zero, parNorm_zero]
  | succ m ih =>
    rw [Nat.cast_succ] at hu ⊢
    obtain ⟨-, hw⟩ := (mem_sobolevPar_add_one_iff J m u).1 hu
    choose w hwm hwd using hw
    rw [weakHmNormSq_succ isOpen_Q hwd, parNorm_add_one_sq J hu hwd]
    have h0 : ‖u‖ ^ 2 ≤ parNorm J k m u ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_parNorm J k (Nat.cast_nonneg m)
        (sobolevPar_anti J k (by linarith) hu)) 2
    exact add_le_add h0 (Finset.sum_le_sum fun j _ => ih _ (hwm j))

/-- **Norm comparison on the parity classes, `≥`**: for `u ∈ Hᵐ_J(Q)`,
`‖u‖²_{m,J} ≤ 2ᵐ Σ_t Σ_{|r| ≤ m} ‖∂^r u_t‖²_{L²(Q)}`. -/
theorem parNorm_sq_le_weakHmNormSq (J : Finset (Fin n)) (m : ℕ)
    {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))} (hu : u ∈ sobolevPar J k m) :
    parNorm J k m u ^ 2 ≤ 2 ^ m * weakHmNormSq (Q (Fin n)) m u := by
  induction m generalizing J u with
  | zero => rw [weakHmNormSq_zero isOpen_Q, Nat.cast_zero, parNorm_zero, pow_zero, one_mul]
  | succ m ih =>
    rw [Nat.cast_succ] at hu ⊢
    obtain ⟨-, hw⟩ := (mem_sobolevPar_add_one_iff J m u).1 hu
    choose w hwm hwd using hw
    rw [parNorm_add_one_sq J hu hwd]
    have hsucc := weakHmNormSq_succ (m := m) isOpen_Q hwd
    have h1 := ih J (sobolevPar_anti J k (by linarith) hu)
    have h2 : ∑ j, parNorm (symmDiff J {j}) k m (w j) ^ 2 ≤
        2 ^ m * ∑ j, weakHmNormSq (Q (Fin n)) m (w j) := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun j _ => ih _ (hwm j)
    have h3 := weakHmNormSq_mono (Ω := Q (Fin n)) (m' := m + 1) (Nat.le_succ m) u
    have h5 : (0 : ℝ) ≤ 2 ^ m := by positivity
    have h6 : ∑ j, weakHmNormSq (Q (Fin n)) m (w j) ≤ weakHmNormSq (Q (Fin n)) (m + 1) u := by
      rw [hsucc]; linarith [sq_nonneg ‖u‖]
    calc parNorm J k (↑m) u ^ 2 + ∑ j, parNorm (symmDiff J {j}) k (↑m) (w j) ^ 2
        ≤ 2 ^ m * weakHmNormSq (Q (Fin n)) m u +
          2 ^ m * ∑ j, weakHmNormSq (Q (Fin n)) m (w j) := add_le_add h1 h2
      _ ≤ 2 ^ m * weakHmNormSq (Q (Fin n)) (m + 1) u +
          2 ^ m * weakHmNormSq (Q (Fin n)) (m + 1) u :=
          add_le_add (mul_le_mul_of_nonneg_left h3 h5) (mul_le_mul_of_nonneg_left h6 h5)
      _ = _ := by ring

end ParitySucc
end Feec.Models.Cube.Sobolev
