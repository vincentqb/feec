module

public import Feec.Models.Cube.Sobolev
public import Feec.ForMathlib.Calculus.Partial
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Sobolev spaces of integer order and weak derivatives on the cube

(Module docstring written at the end.)
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

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Fourier.TorusWeak`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The local Haar measure on `ℝ/ℤ` is an additive Haar measure. -/
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

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

/-- `∂ⱼ Σ c_m e_m = Σ (2πi m_j) c_m e_m`. -/
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

/-- **Iterated partial derivatives** along a list of directions:
`∂^{[j₁, …, j_p]} f = ∂_{j₁} ⋯ ∂_{j_p} f`. -/
def iterPartial : List (Fin n) → ((Fin n → ℝ) → ℝ) → (Fin n → ℝ) → ℝ
  | [], f => f
  | j :: l, f => partialDeriv j (iterPartial l f)

@[simp] theorem iterPartial_nil (f : (Fin n → ℝ) → ℝ) : iterPartial [] f = f := rfl

theorem iterPartial_cons (j : Fin n) (l : List (Fin n)) (f : (Fin n → ℝ) → ℝ) :
    iterPartial (j :: l) f = partialDeriv j (iterPartial l f) := rfl

theorem iterPartial_append (l₁ l₂ : List (Fin n)) (f : (Fin n → ℝ) → ℝ) :
    iterPartial (l₁ ++ l₂) f = iterPartial l₁ (iterPartial l₂ f) := by
  induction l₁ with
  | nil => rfl
  | cons j l ih => rw [List.cons_append, iterPartial_cons, iterPartial_cons, ih]

theorem contDiff_iterPartial {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (l : List (Fin n)) :
    ContDiff ℝ ∞ (iterPartial l f) := by
  induction l with
  | nil => exact hf
  | cons j l ih => exact ih.partialDeriv (by simp) j

/-- **Derivatives of real exponential sums**: `∂^l Re (Σ c_m e_m) = Re (Σ symb_l(m) c_m e_m)`. -/
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

/-- **Parseval on `Q` for exponential sums**: `‖Re Σ c_m e_m‖²_{L²(Q)} ≤ Σ |c_m|²` (the
restriction to `Q ⊆ 𝕋ⁿ` of the real part is a contraction, and the characters are orthonormal on
`𝕋ⁿ`). -/
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

/-- **Iterated Fréchet derivatives on coordinate vectors are iterated partial derivatives**:
`Dᵖ f(y)(e_{r₀}, …, e_{r_{p-1}}) = ∂_{r₀} ⋯ ∂_{r_{p-1}} f(y)`. -/
theorem iteratedFDeriv_single_eq_iterPartial {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∀ (p : ℕ) (r : Fin p → Fin n) (y : Fin n → ℝ),
      iteratedFDeriv ℝ p f y (fun l => Pi.single (r l) 1) = iterPartial (List.ofFn r) f y
  | 0, r, y => by simp
  | p + 1, r, y => by
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ, iterPartial_cons]
    have ih : iterPartial (List.ofFn fun i => r i.succ) f =
        fun z => iteratedFDeriv ℝ p f z (fun l => Pi.single (r l.succ) 1) :=
      funext fun z => (iteratedFDeriv_single_eq_iterPartial hf p (fun i => r i.succ) z).symm
    rw [ih, partialDeriv, fderiv_continuousMultilinear_apply_const_apply
      (hf.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _) y)]
    rfl

/-- **A multilinear map on `(ℝⁿ, sup)` is bounded by its values on coordinate vectors**:
`‖A‖ ≤ Σ_r ‖A(e_{r₀}, …, e_{r_{p-1}})‖`. -/
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

/-- **A multilinear map into a sup-normed product is bounded by its components**. -/
theorem norm_le_sum_proj {ι : Type*} [Fintype ι] {p : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin p => Fin n → ℝ) (ι → ℝ)) :
    ‖A‖ ≤ ∑ s, ‖(ContinuousLinearMap.proj s : (ι → ℝ) →L[ℝ] ℝ).compContinuousMultilinearMap A‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun s => ?_
  have h := ((ContinuousLinearMap.proj s : (ι → ℝ) →L[ℝ] ℝ).compContinuousMultilinearMap A).le_opNorm v
  have h2 : ‖(ContinuousLinearMap.proj s : (ι → ℝ) →L[ℝ] ℝ).compContinuousMultilinearMap A‖ ≤
      ∑ s, ‖(ContinuousLinearMap.proj s : (ι → ℝ) →L[ℝ] ℝ).compContinuousMultilinearMap A‖ :=
    Finset.single_le_sum (f := fun s => ‖(ContinuousLinearMap.proj s : (ι → ℝ) →L[ℝ] ℝ).compContinuousMultilinearMap A‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  calc ‖A v s‖ = ‖(ContinuousLinearMap.proj s : (ι → ℝ) →L[ℝ] ℝ).compContinuousMultilinearMap A v‖ := rfl
    _ ≤ _ := h
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 (by positivity)

/-- **The norm of the iterated derivative of a smooth form field by partial derivatives**:
`‖Dᵖ w(y)‖ ≤ Σ_s Σ_r |∂^r w_s(y)|`. -/
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
  rw [iteratedFDeriv_single_eq_iterPartial hs, Real.norm_eq_abs]

/-- `Σ_r |symb_r(m)|² = |2πm|^{2p}` over the words `r` of length `p`. -/
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

theorem sum_eq_sum_formIdx' {f : Finset (Fin n) → ℝ} (hf : ∀ s, #s ≠ k → f s = 0) :
    ∑ s, f s = ∑ s : formIdx n k, f s.1 := by
  have h0 : ∑ s : {s : Finset (Fin n) // ¬ ((#s : ℤ) = (k : ℤ))}, f s = 0 :=
    Finset.sum_eq_zero fun s _ => hf s.1 (fun h => s.2 (by rw [h]))
  rw [← Fintype.sum_subtype_add_sum_subtype (fun s : Finset (Fin n) => (#s : ℤ) = (k : ℤ)) f, h0,
    add_zero]

theorem integrable_sq_of_continuous {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) :
    Integrable (fun y => f y ^ 2) (volume.restrict (Q (Fin n))) :=
  (Feec.Domain.memLp_of_continuous measurableSet_Q isBounded_Qn hf).integrable_sq

/-- The restriction of a trigonometric polynomial is the real part of an exponential sum. -/
theorem trigLift_eq_re_expSum (x : Seq n k) (S : Finset (Fin n → ℤ)) (t : formIdx n (k : ℤ)) :
    trigLift k x S t = fun y => (expSum S (fun m => cf x m (idx k t)) y).re := by
  funext y
  simp only [trigLift, trigPoly, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, expSum, expChar_eq_mFourier, repr_physF]

/-- **The Fourier truncation as a smooth form field on `ℝⁿ`**: the real trigonometric polynomial
`(x_M)ₜ = Re Σ_{|m|_∞ ≤ M} x(m)ₜ e_m` in the components `#t = k`, `0` in the others. Its
restriction to `Q` is `Jinvf k (trunc M k x)` (`Jinvf_trunc_eq_truncField`). -/
def truncField (k : ℕ) (x : Seq n k) (M : ℕ) : (Fin n → ℝ) → Finset (Fin n) → ℝ :=
  fun y s => Feec.Domain.formExt (fun t : formIdx n (k : ℤ) => trigLift k (trunc M k x) (bandS M) t y) s

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

/-- The components of the truncation field are real exponential sums. -/
theorem truncField_comp_eq (x : Seq n k) (M : ℕ) (t : formIdx n (k : ℤ)) :
    (fun y => truncField k x M y t.1) =
      fun y => (expSum (bandS M) (fun m => cf (trunc M k x) m (idx k t)) y).re := by
  funext y
  rw [truncField_val, trigLift_eq_re_expSum]

/-- The iterated partial derivatives of the truncation field, in `L²(Q)`, by Parseval. -/
theorem integral_iterPartial_truncField_sq_le (x : Seq n k) (M : ℕ) (l : List (Fin n))
    (t : formIdx n (k : ℤ)) :
    ∫ y in Q (Fin n), (iterPartial l (fun z => truncField k x M z t.1) y) ^ 2 ≤
      ∑ m ∈ bandS M, ‖symb l m‖ ^ 2 * ‖cf (trunc M k x) m (idx k t)‖ ^ 2 := by
  rw [truncField_comp_eq, iterPartial_re_expSum]
  refine (integral_re_expSum_sq_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [norm_mul, mul_pow]

/-- **Bernstein inequality for the Fourier truncations**, in the iterated Fréchet derivative:
`∫_Q ‖Dᵖ (x_M)‖² ≤ 2ⁿ nᵖ ‖x_M‖²_{Hᵖ(𝕋ⁿ)}` (sup norms on `ℝⁿ` and on the fibre `Λ`). -/
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
      refine (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun q : Finset (Fin n) × (Fin p → Fin n) => |a q.1 q.2 y|)).trans ?_
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
  rw [sum_eq_sum_formIdx' h0]
  set c := fun (m : Fin n → ℤ) (t : formIdx n (k : ℤ)) => cf (trunc M k x) m (idx k t)
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

/-- **Bernstein inequality** (`sum_norm_iteratedFDeriv_truncQ_sq_le`): for `x ∈ Hˢ(𝕋ⁿ)` and an
integer order `p ≥ s`, the truncation `u_M = (x_M)|_Q` satisfies
`‖Dᵖ u_M‖²_{L²(Q)} ≤ 2ⁿ nᵖ (1 + n (2πM)²)^{p - s} ‖x‖²_{Hˢ(𝕋ⁿ)}`. This generalizes
`grad_Jinvf_sum_le` and `grad_truncQ_le` (`p = 1`) to every order. -/
theorem sum_norm_iteratedFDeriv_truncQ_sq_le {s : ℝ} {p : ℕ} (hsp : s ≤ p) {x : Seq n k}
    (hx : MemSob s x) (M : ℕ) :
    ∫ y in Q (Fin n), ‖iteratedFDeriv ℝ p (truncField k x M) y‖ ^ 2 ≤
      2 ^ n * n ^ p * ((1 + n * (2 * Real.pi * M) ^ 2) ^ ((p : ℝ) - s) * sobSum s x) :=
  (integral_norm_iteratedFDeriv_truncField_sq_le x M p).trans
    (mul_le_mul_of_nonneg_left (sobSum_trunc_le hsp hx M) (by positivity))

/-- **Bernstein inequality in the parity classes**: for `u ∈ Hˢ_J(Q)` and `p ≥ s`, the
truncation `u_M = truncPar J k M u` (the restriction of `truncField k (JfJ J k u) M`) satisfies
`‖Dᵖ u_M‖²_{L²(Q)} ≤ 2ⁿ nᵖ (1 + n (2πM)²)^{p - s} 2ⁿ ‖u‖²_{s,J}`. -/
theorem sum_norm_iteratedFDeriv_truncPar_sq_le (J : Finset (Fin n)) {s : ℝ} {p : ℕ}
    (hsp : s ≤ p) {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))} (hu : u ∈ sobolevPar J k s)
    (M : ℕ) :
    ∫ y in Q (Fin n), ‖iteratedFDeriv ℝ p (truncField k (JfJ J k u) M) y‖ ^ 2 ≤
      2 ^ n * n ^ p * ((1 + n * (2 * Real.pi * M) ^ 2) ^ ((p : ℝ) - s) *
        (2 ^ n * parNorm J k s u ^ 2)) := by
  have h := sum_norm_iteratedFDeriv_truncQ_sq_le hsp ((mem_sobolevPar J k).1 hu) M
  rwa [show sobSum s (JfJ J k u) = 2 ^ n * parNorm J k s u ^ 2 by
    rw [parNorm_sq]; field_simp] at h

end Bernstein

end Feec.Models.Cube.Sobolev
