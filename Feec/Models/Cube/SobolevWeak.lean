module

public import Feec.Models.Cube.Sobolev
public import Feec.ForMathlib.Calculus.Partial
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Sobolev spaces of integer order and weak derivatives on the cube

The Sobolev spaces `Hˢ(Q; Λᵏ)`, `Hˢ_J(Q; Λᵏ)` of `Feec.Models.Cube.Sobolev` are defined on the
Fourier side of the torus `𝕋ⁿ = ℝⁿ/ℤⁿ` (restrictions to `Q = (0, ½)ⁿ`, parity extensions). For
`s = 1` they were identified with the weak-derivative spaces (`mem_sobolevQ_one_iff`,
`mem_sobolevPar_one_iff`). This file treats every integer order `m`, and proves the Bernstein
inequality used by the optimal finite element rates of `Feec.Models.Cube.SobolevRateHigh`.

## Weak derivatives

* `HasWeakDeriv Ω l f v`: `∫_Ω f ∂^l φ = (-1)^{|l|} ∫_Ω v φ` for every `φ ∈ C_c^∞(Ω)`, along a
  word `l = [j₁, …, j_p]` of directions (`iterPartial`; words of length `p` cover the
  multi-indices of order `p`, partial derivatives of test functions commuting).
  `HasWeakDerivs Ω m u`: every coefficient `u_t` has weak derivatives in `L²(Ω)` along every word
  of length `≤ m`. They are unique (`HasWeakDeriv.unique`), pass to `L²` limits
  (`hasWeakDeriv_of_tendsto`), and classical integration by parts of every order holds
  (`integral_mul_iterPartial`). `weakHmNorm`, `weakHmNormSq`: the norm `Σ_t Σ_{|r| ≤ m} ‖∂^r u_t‖²` over ordered words `r`
  (a mixed derivative of multi-index `α` is counted `|α|!/α!` times; equivalent, up to
  constants depending on `m`, to the norm over multi-indices).
* **Forward direction** (`hasWeakDerivs_of_mem_sobolevQ`): every `u ∈ Hᵐ(Q; Λᵏ)` has weak
  derivatives up to order `m` in `L²(Q)`; the derivative along `l` is the restriction of the
  Fourier multiplier `mulSeq l x` (`hasWeakDeriv_of_memSob`), the `L²` limit of the classical
  derivatives of the truncations (graph convergence, `hasWeakDeriv_Jinvf_trunc`), and
  `Σ_t Σ_{|r| ≤ m} ‖∂^r u_t‖² ≤ (Σ_{p ≤ m} nᵖ) ‖u‖²_{Hᵐ(Q)}` (`weakHmNormSq_le_qNorm_sq`,
  `weakHmNorm_le_qNorm`).
* **The torus** (`HasWeakDerivT`, `HasWeakDerivsT`, with `iterPartialT`, test functions the smooth
  functions of `𝕋ⁿ`): `x ∈ Hᵐ(𝕋ⁿ; Λᵏ)` iff every component of `physF k x` has weak derivatives up
  to order `m` in `L²(𝕋ⁿ)` (**`memSob_nat_iff`**; `⇐` by testing against the characters, the pure
  derivatives `∂_j^m` and the power-mean inequality). Hence **`mem_sobolevPar_nat_iff`**:
  `u ∈ Hᵐ_J(Q)` iff the parity extension `JfJ J k u` has weak derivatives up to order `m` in
  `L²(𝕋ⁿ)`.
* **The parity classes of every integer order, intrinsically on `Q`**
  (**`mem_sobolevPar_add_one_iff`**): `u ∈ H^{m+1}_J(Q; Λᵏ)` iff `u ∈ H¹_J(Q; Λᵏ)` and every first
  weak derivative `∂_j u` (in `L²(Q)`) lies in `Hᵐ_{J ∆ {j}}(Q; Λᵏ)` (`∂_j` flips the parity in
  `x_j`, `realParJ_mulSeq_single`; the weak derivative is the restriction of `∂_j (JfJ J k u)` by
  uniqueness, `mulSeq_eq_of_hasWeakDeriv`; `x ∈ H^{m+1}(𝕋ⁿ)` iff every `∂_j x ∈ Hᵐ(𝕋ⁿ)`,
  `memSob_nat_add_one_iff`). With `mem_sobolevPar_one_iff` this is the backward direction for the
  parity classes: weak derivatives on `Q` plus vanishing traces of the derivatives give `Hᵐ_J`.
  For `m = 2` (**`mem_sobolevPar_two_iff`**, `⇒` is `mem_sobolevPar_two_compat`): `u ∈ H²_J(Q)`
  iff `u_t ∈ H¹(Q)` with vanishing traces on the faces normal to `J ∆ t`, and every `∂_j u_t` is
  the coefficient of `w_j ∈ H¹_{J ∆ {j}}(Q)`, i.e. `∂_j u_t ∈ H¹(Q)` with vanishing traces on the
  faces normal to `(J ∆ {j}) ∆ t`; on the faces normal to `j` this is the **compatibility
  condition** `∂_j u_t = 0` for `j ∉ J ∆ t` (the odd-order normal derivatives of the even
  reflection).
* **Norms on the parity classes**: the recursion `‖u‖²_{m+1,J} = ‖u‖²_{m,J} + Σ_j ‖∂_j u‖²_{m,J∆{j}}`
  (`parNorm_add_one_sq`, from `sobSum_add_one`) and the recursion of the weak norm
  (`weakHmNormSq_succ`) give the equivalence
  `weakHmNormSq Q m u ≤ ‖u‖²_{m,J} ≤ 2ᵐ weakHmNormSq Q m u` on `Hᵐ_J(Q)`
  (`weakHmNormSq_le_parNorm_sq`, `parNorm_sq_le_weakHmNormSq`).

## The Bernstein inequality

The truncation `u_M = (x_M)|_Q` is the restriction of the smooth form `truncField k x M` (real
parts of the exponential sums `expSum`, `trigLift_eq_re_expSum`). Its iterated partial derivatives
are exponential sums with the symbols `symb l` (`iterPartial_re_expSum`), the iterated Fréchet
derivative on coordinate vectors is the iterated partial derivative
(`iteratedFDeriv_single_eq_iterPartial`), multilinear maps are bounded by their coordinate values
(`norm_le_sum_apply_single`, `norm_le_sum_proj`), and Parseval on `Q ⊆ 𝕋ⁿ`
(`integral_re_expSum_sq_le`) gives **`sum_norm_iteratedFDeriv_truncQ_sq_le`**:
`‖Dᵖ u_M‖²_{L²(Q)} ≤ 2ⁿ nᵖ (1 + n(2πM)²)^{p-s} ‖x‖²_{Hˢ(𝕋ⁿ)}` for `s ≤ p`, and its parity version
`sum_norm_iteratedFDeriv_truncPar_sq_le` (`‖x‖² = 2ⁿ ‖u‖²_{s,J}`). This generalizes
`grad_Jinvf_sum_le`, `grad_truncQ_le` (`p = 1`) to every order.

## A power witness

`powWitness a = Σ_{c ≠ 0} |c|^{-a} cos(2π c y₀)` (`a > ½`; `a = 1` is `logWitness`) lies in
`Hˢ_∅(Q) ⊆ Hˢ(Q)` for `s < a - ½` (`powWitness_mem_sobolevPar`, `powWitness_mem_sobolevQ`), not in
`H^{a-1/2}_∅(Q)` (`powWitness_not_mem_sobolevPar`), and is nonzero (`powWitness_ne_zero`).

## What is not formalized

* **The backward direction on `Q` without boundary conditions**: `HasWeakDerivs Q m u →
  u ∈ sobolevQ n k m` (with the reverse norm inequality) for `m ≥ 2`. It needs an `Hᵐ` extension
  operator from `Q` to a period cell, e.g. the reflection of [Hestenes1941] with `m + 1`
  coefficients across each face, applied face by face and periodized, together with the
  approximation of `Hᵐ(Q)` functions by functions smooth up to the boundary (the matching
  conditions of the reflection only remove the boundary terms for test functions vanishing to
  order `m` on the face). For `m = 1` the even reflection suffices (`mem_sobolevQ_one_iff`).
  Consequently the planned `mem_sobolevQ_nat_iff` is proved only as `⇒`
  (`hasWeakDerivs_of_mem_sobolevQ`), and the planned norm equivalence `qNorm_nat_sq_equiv` only as
  `weakHmNormSq_le_qNorm_sq`. In the parity classes both directions and both norm inequalities are
  proved (above).

No hypothesis is assumed.

## References

* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.1 (weak derivatives, `W^{m,p}`), §9.2 (extension)
* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.2 (weak derivatives), §5.4
  (extensions)
* [M. R. Hestenes, *Extension of the Range of a Differentiable Function*][Hestenes1941]
  (higher-order reflection)

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
  set P : ι → ContinuousMultilinearMap ℝ (fun _ : Fin p => Fin n → ℝ) ℝ := fun s =>
    (ContinuousLinearMap.proj s : (ι → ℝ) →L[ℝ] ℝ).compContinuousMultilinearMap A
  have h := (P s).le_opNorm v
  have h2 : ‖P s‖ ≤ ∑ s, ‖P s‖ :=
    Finset.single_le_sum (f := fun s => ‖P s‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  calc ‖A v s‖ = ‖P s v‖ := rfl
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

/-! ### A power witness: `Hˢ` data outside `H^{a - 1/2}` -/

section PowWitness

variable [NeZero n]

open scoped Classical in
/-- **The coefficients of the power series** `Σ_{c ≠ 0} |c|^{-a} e^{2πi c y₀}`: `|c|^{-a}` at the
frequencies `±c e₀`, `c ≠ 0` (for `a = 1` the logarithmic series `logCoeff`). -/
def powCoeff (a : ℝ) (m : Fin n → ℤ) : Form ℂ (Fin n) 0 :=
  WithLp.toLp 2 fun _ => if OnAxis m ∧ m 0 ≠ 0 then ((|(m 0 : ℝ)| ^ (-a) : ℝ) : ℂ) else 0

open scoped Classical in
theorem norm_powCoeff_sq (a : ℝ) (m : Fin n → ℤ) :
    ‖powCoeff a m‖ ^ 2 = if OnAxis m ∧ m 0 ≠ 0 then (|(m 0 : ℝ)| ^ (-a)) ^ 2 else 0 := by
  rw [norm_form_zero_sq]
  change ‖(if OnAxis m ∧ m 0 ≠ 0 then ((|(m 0 : ℝ)| ^ (-a) : ℝ) : ℂ) else 0)‖ ^ 2 = _
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · simp

/-- The weighted squares of the power series on the axis. -/
def powTerm (a s : ℝ) (c : ℤ) : ℝ :=
  weight s (axis (n := n) c) * ‖powCoeff a (axis (n := n) c)‖ ^ 2

theorem powTerm_eq (a s : ℝ) (c : ℤ) :
    powTerm (n := n) a s c =
      if c = 0 then 0 else (1 + (2 * Real.pi * c) ^ 2) ^ s * (|(c : ℝ)| ^ (-a)) ^ 2 := by
  classical
  have hax : OnAxis (axis (n := n) c) := (onAxis_iff_mem_range _).2 ⟨c, rfl⟩
  have h0 : axis (n := n) c 0 = c := by simp [axis]
  rw [powTerm, norm_powCoeff_sq, weight, norm_freq_axis_sq, h0]
  by_cases hc : c = 0 <;> simp [hc, hax]

theorem summable_weight_powCoeff_iff (a s : ℝ) :
    Summable (fun m : Fin n → ℤ => weight s m * ‖powCoeff a m‖ ^ 2) ↔
      Summable (powTerm (n := n) a s) := by
  classical
  rw [← axis_injective.summable_iff (f := fun m : Fin n → ℤ => weight s m * ‖powCoeff a m‖ ^ 2)
    fun m hm => ?_]
  · rfl
  · have h : ¬ OnAxis m := fun h => hm ((onAxis_iff_mem_range m).1 h)
    rw [norm_powCoeff_sq]
    simp [show ¬ (OnAxis m ∧ m 0 ≠ 0) from fun h' => h h'.1]

theorem powTerm_nonneg (a s : ℝ) (c : ℤ) : 0 ≤ powTerm (n := n) a s c :=
  mul_nonneg (weight_nonneg s _) (sq_nonneg _)

theorem sq_rpow_neg_abs (a : ℝ) (c : ℤ) :
    (|(c : ℝ)| ^ (-a)) ^ 2 = |(c : ℝ)| ^ (-(2 * a)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 1; push_cast; ring

/-- **The power series is in `Hˢ` for `s < a - ½`**: `Σ_c (1 + 4π²c²)^s |c|^{-2a} < ∞`. -/
theorem summable_powTerm {a s : ℝ} (hs0 : 0 ≤ s) (hs : s < a - 1 / 2) :
    Summable (powTerm (n := n) a s) := by
  refine Summable.of_nonneg_of_le (powTerm_nonneg a s) (fun c => ?_)
    ((Real.summable_abs_int_rpow (b := 2 * a - 2 * s) (by linarith)).mul_left
      ((1 + (2 * Real.pi) ^ 2) ^ s))
  rw [powTerm_eq]
  split_ifs with hc
  · exact mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg _) _)
  · have hc1 : (1 : ℝ) ≤ |(c : ℝ)| := by
      have : (1 : ℤ) ≤ |c| := Int.one_le_abs hc
      exact_mod_cast this
    have hcpos : 0 < |(c : ℝ)| := by linarith
    have hb : 1 + (2 * Real.pi * c) ^ 2 ≤ (1 + (2 * Real.pi) ^ 2) * |(c : ℝ)| ^ 2 := by
      rw [sq_abs, mul_pow]
      have : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by rw [← sq_abs]; nlinarith
      nlinarith [sq_nonneg (2 * Real.pi)]
    have h1 := Real.rpow_le_rpow (by positivity) hb hs0
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (|(c : ℝ)|) 2,
      ← Real.rpow_mul (abs_nonneg _)] at h1
    rw [sq_rpow_neg_abs]
    calc (1 + (2 * Real.pi * c) ^ 2) ^ s * |(c : ℝ)| ^ (-(2 * a)) ≤
        ((1 + (2 * Real.pi) ^ 2) ^ s * |(c : ℝ)| ^ ((2 : ℕ) * s)) * |(c : ℝ)| ^ (-(2 * a)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (abs_nonneg _) _)
      _ = (1 + (2 * Real.pi) ^ 2) ^ s * |(c : ℝ)| ^ (-(2 * a - 2 * s)) := by
          rw [mul_assoc, ← Real.rpow_add hcpos]; push_cast; ring_nf

/-- **The power series is not in `H^{a - 1/2}`**: `Σ_c (1 + 4π²c²)^{a-1/2} |c|^{-2a}
≥ (2π)^{2a-1} Σ 1/|c| = ∞` (`a ≥ ½`). -/
theorem not_summable_powTerm {a : ℝ} (ha : 1 / 2 ≤ a) :
    ¬ Summable (powTerm (n := n) a (a - 1 / 2)) := by
  intro h
  have hle : ∀ c : ℤ, (2 * Real.pi) ^ (2 * a - 1) * (1 / |(c : ℝ) + 0| ^ (1 : ℝ)) ≤
      powTerm (n := n) a (a - 1 / 2) c := by
    intro c
    rw [powTerm_eq, add_zero, Real.rpow_one]
    split_ifs with hc
    · subst hc; simp
    · have hcpos : 0 < |(c : ℝ)| := abs_pos.2 (by exact_mod_cast hc)
      have hs : (2 * Real.pi * |(c : ℝ)|) ^ (2 * a - 1) ≤
          (1 + (2 * Real.pi * c) ^ 2) ^ (a - 1 / 2) := by
        have e : (2 * Real.pi * |(c : ℝ)|) ^ (2 * a - 1) =
            ((2 * Real.pi * |(c : ℝ)|) ^ 2) ^ (a - 1 / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
        rw [e]
        exact Real.rpow_le_rpow (by positivity) (by rw [mul_pow, sq_abs, mul_pow]; linarith)
          (by linarith)
      have e2 : (2 * Real.pi * |(c : ℝ)|) ^ (2 * a - 1) * (|(c : ℝ)| ^ (-a)) ^ 2 =
          (2 * Real.pi) ^ (2 * a - 1) * (1 / |(c : ℝ)|) := by
        rw [sq_rpow_neg_abs, Real.mul_rpow (by positivity) hcpos.le, mul_assoc,
          ← Real.rpow_add hcpos, one_div, ← Real.rpow_neg_one]
        congr 2; ring
      calc (2 * Real.pi) ^ (2 * a - 1) * (1 / |(c : ℝ)|) =
          (2 * Real.pi * |(c : ℝ)|) ^ (2 * a - 1) * (|(c : ℝ)| ^ (-a)) ^ 2 := e2.symm
        _ ≤ (1 + (2 * Real.pi * c) ^ 2) ^ (a - 1 / 2) * (|(c : ℝ)| ^ (-a)) ^ 2 :=
            mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have hpos : 0 < (2 * Real.pi) ^ (2 * a - 1) := Real.rpow_pos_of_pos (by positivity) _
  have h2 : Summable fun c : ℤ => (2 * Real.pi) ^ (2 * a - 1) * (1 / |(c : ℝ) + 0| ^ (1 : ℝ)) :=
    Summable.of_nonneg_of_le (fun c => by positivity) hle h
  have h3 : Summable fun c : ℤ => 1 / |(c : ℝ) + 0| ^ (1 : ℝ) :=
    (h2.mul_left ((2 * Real.pi) ^ (2 * a - 1))⁻¹).congr fun c => by
      rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  exact lt_irrefl _ ((Real.summable_one_div_int_add_rpow 0 1).1 h3)

theorem summable_norm_powCoeff_sq {a : ℝ} (ha : 1 / 2 < a) :
    Summable fun m : Fin n → ℤ => ‖powCoeff a m‖ ^ 2 := by
  have h := (summable_weight_powCoeff_iff (n := n) a 0).2 (summable_powTerm le_rfl (by linarith))
  simpa using h

/-- The coefficient sequence of the power series (`a > ½`). -/
def powSeq {a : ℝ} (ha : 1 / 2 < a) : Seq n 0 :=
  (memLp_of_summable (summable_norm_powCoeff_sq (n := n) ha)).toLp (powCoeff a)

theorem cf_powSeq {a : ℝ} (ha : 1 / 2 < a) (m : Fin n → ℤ) :
    cf (powSeq (n := n) ha) m = powCoeff a m := by
  change ((memLp_of_summable (summable_norm_powCoeff_sq (n := n) ha)).toLp (powCoeff a) :
    (Fin n → ℤ) → Form ℂ (Fin n) 0) m = _
  rw [MemLp.coeFn_toLp_count]

theorem memSob_powSeq_iff {a : ℝ} (ha : 1 / 2 < a) (s : ℝ) :
    MemSob s (powSeq (n := n) ha) ↔ Summable (powTerm (n := n) a s) := by
  rw [← summable_weight_powCoeff_iff]
  simp only [MemSob, cf_powSeq]

/-- The power series is real and even in every variable: the parity class `∅`. -/
theorem realParJ_powSeq {a : ℝ} (ha : 1 / 2 < a) :
    RealParJ (∅ : Finset (Fin n)) 0 (powSeq (n := n) ha) := by
  classical
  have key : ∀ m m' : Fin n → ℤ, (OnAxis m' ↔ OnAxis m) → |(m' 0 : ℝ)| = |(m 0 : ℝ)| →
      (m' 0 ≠ 0 ↔ m 0 ≠ 0) → powCoeff a m' = powCoeff a m := by
    intro m m' h1 h2 h3
    simp only [powCoeff, h2]
    congr 1
    funext _
    exact if_congr (and_congr h1 h3) rfl rfl
  refine ⟨fun m t => ?_, fun j m t => ?_⟩
  · change cf (powSeq ha) (-m) t = conj (cf (powSeq ha) m t)
    rw [cf_powSeq, cf_powSeq, key m (-m) (by
      simp only [OnAxis, Pi.neg_apply, neg_eq_zero]) (by simp) (by simp)]
    change _ = conj ((if OnAxis m ∧ m 0 ≠ 0 then ((|(m 0 : ℝ)| ^ (-a) : ℝ) : ℂ) else 0))
    change (if OnAxis m ∧ m 0 ≠ 0 then ((|(m 0 : ℝ)| ^ (-a) : ℝ) : ℂ) else 0) = _
    split_ifs <;> simp
  · change cf (powSeq ha) (DeRham.flipAt j m) t = _ * cf (powSeq ha) m t
    have ht : t.1 = ∅ := Finset.card_eq_zero.1 t.2
    have hf : ∀ b, DeRham.flipAt j m b = if b = j then -m b else m b := fun b => rfl
    rw [cf_powSeq, cf_powSeq, key m (DeRham.flipAt j m) (by
        simp only [OnAxis, hf]
        refine forall_congr' fun b => imp_congr_right fun _ => ?_
        split_ifs <;> simp)
      (by rw [hf]; split_ifs <;> simp) (by rw [hf]; split_ifs <;> simp)]
    simp [DeRham.mixedSign, DeRham.reflSign, ht]

/-- **The power witness** `u_a(y) = Σ_{c ≠ 0} |c|^{-a} cos(2π c y₀)` on `Q` (`a > ½`; for `a = 1`
the logarithmic witness `logWitness`). -/
def powWitness {a : ℝ} (ha : 1 / 2 < a) : L2F ℝ (Q (Fin n)) (formIdx n ((0 : ℕ) : ℤ)) :=
  Jinvf 0 (powSeq (n := n) ha)

theorem JfJ_powWitness {a : ℝ} (ha : 1 / 2 < a) :
    JfJ ∅ 0 (powWitness (n := n) ha) = powSeq ha := JfJ_Jinvf (realParJ_powSeq ha)

/-- **The power witness lies in `Hˢ_∅(Q)` (hence in `Hˢ(Q)`) for every `0 ≤ s < a - ½`**. -/
theorem powWitness_mem_sobolevPar {a s : ℝ} (ha : 1 / 2 < a) (hs0 : 0 ≤ s) (hs : s < a - 1 / 2) :
    powWitness (n := n) ha ∈ sobolevPar ∅ 0 s := by
  rw [mem_sobolevPar, JfJ_powWitness, memSob_powSeq_iff]
  exact summable_powTerm hs0 hs

theorem powWitness_mem_sobolevQ {a s : ℝ} (ha : 1 / 2 < a) (hs0 : 0 ≤ s) (hs : s < a - 1 / 2) :
    powWitness (n := n) ha ∈ sobolevQ n 0 s :=
  sobolevPar_le_sobolevQ ∅ s (powWitness_mem_sobolevPar ha hs0 hs)

/-- **The power witness is not in `H^{a - 1/2}_∅(Q)`**. -/
theorem powWitness_not_mem_sobolevPar {a : ℝ} (ha : 1 / 2 < a) :
    powWitness (n := n) ha ∉ sobolevPar ∅ 0 (a - 1 / 2) := by
  rw [mem_sobolevPar, JfJ_powWitness, memSob_powSeq_iff]
  exact not_summable_powTerm ha.le

theorem powWitness_ne_zero {a : ℝ} (ha : 1 / 2 < a) : powWitness (n := n) ha ≠ 0 := by
  classical
  intro h
  have h1 := JfJ_powWitness (n := n) ha
  rw [h, map_zero] at h1
  have h2 := congrArg (fun x : Seq n 0 => cf x (axis 1) t₀) h1
  simp only [cf_zero, cf_powSeq] at h2
  have hax : OnAxis (axis (n := n) 1) := (onAxis_iff_mem_range _).2 ⟨1, rfl⟩
  have h0 : axis (n := n) 1 0 = 1 := by simp [axis]
  change (0 : ℂ) = (if OnAxis (axis (n := n) 1) ∧ axis (n := n) 1 0 ≠ 0 then
    ((|(axis (n := n) 1 0 : ℝ)| ^ (-a) : ℝ) : ℂ) else 0) at h2
  simp [hax, h0] at h2

end PowWitness

/-! ### Weak derivatives of every order -/

section Weak

variable {Ω : Set (Fin n → ℝ)}

theorem isTest_iterPartial {φ : (Fin n → ℝ) → ℝ} (hφ : IsTest Ω φ) (l : List (Fin n)) :
    IsTest Ω (iterPartial l φ) := by
  induction l with
  | nil => exact hφ
  | cons j l ih => exact ih.fderiv_apply (Pi.single j 1)

/-- **`v` is the weak derivative `∂^l f`** of `f ∈ L²(Ω)` along the word `l = [j₁, …, j_p]`:
`∫_Ω f ∂_{j₁} ⋯ ∂_{j_p} φ = (-1)^p ∫_Ω v φ` for every `φ ∈ C_c^∞(Ω)` ([Brezis2011], §9.1;
[Evans2010], §5.2.1). Words of length `p` cover the multi-indices of order `p` (partial
derivatives of test functions commute). -/
def HasWeakDeriv (Ω : Set (Fin n → ℝ)) (l : List (Fin n)) (f v : L2 ℝ Ω) : Prop :=
  ∀ φ : (Fin n → ℝ) → ℝ, IsTest Ω φ →
    ∫ x in Ω, (f : (Fin n → ℝ) → ℝ) x * iterPartial l φ x =
      (-1) ^ l.length * ∫ x in Ω, (v : (Fin n → ℝ) → ℝ) x * φ x

/-- **Weak derivatives up to order `m`** (`HasWeakDerivs Ω m u`): every coefficient `u_t` of
`u ∈ L²(Ω; Λᵏ)` has weak derivatives `∂^l u_t ∈ L²(Ω)` along every word of length `≤ m`, i.e.
`u ∈ Hᵐ(Ω; Λᵏ)` in the sense of weak derivatives ([Brezis2011], §9.1). -/
def HasWeakDerivs (Ω : Set (Fin n → ℝ)) (m : ℕ) {k : ℤ} (u : L2F ℝ Ω (formIdx n k)) : Prop :=
  ∀ t : formIdx n k, ∀ l : List (Fin n), l.length ≤ m → ∃ v : L2 ℝ Ω, HasWeakDeriv Ω l (u t) v

/-- **Uniqueness of weak derivatives** (`Ω` open; the fundamental lemma
`Feec.Domain.L2.eq_zero_of_forall_integral`). -/
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

/-- **Classical integration by parts of every order**: for `g` smooth and `φ ∈ C_c^∞(Ω)`,
`∫_Ω g ∂^l φ = (-1)^{|l|} ∫_Ω (∂^{l^R} g) φ` (`l^R` the reversed word). -/
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

/-- **Weak derivatives pass to `L²` limits**: if `f_M → f`, `v_M → v` in `L²(Ω)` and
`v_M = ∂^l f_M` weakly, then `v = ∂^l f` weakly. -/
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
/-- **The symbol multiplier** `x ↦ (symb_l(m) x(m))_m`, the Fourier coefficients of `∂^l` (`0` if
the result is not in `ℓ²`). -/
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

/-- `‖∂^l x‖_{L²(𝕋ⁿ)}² ≤ ‖x‖²_{H^{|l|}(𝕋ⁿ)}`. -/
theorem norm_mulSeq_sq_le {s : ℝ} {x : Seq n k} (hx : MemSob s x) {l : List (Fin n)}
    (hl : (l.length : ℝ) ≤ s) : ‖mulSeq l x‖ ^ 2 ≤ sobSum s x := by
  rw [norm_sq_eq_tsum]
  refine Summable.tsum_le_tsum (fun m => ?_) ?_ hx
  · rw [cf_mulSeq hx hl, norm_smul, mul_pow]
    exact mul_le_mul_of_nonneg_right ((norm_symb_sq_le l m).trans (weight_mono hl m))
      (sq_nonneg _)
  · simpa [cf_mulSeq hx hl] using summable_symb_smul hx hl

/-- The weak derivatives of the truncations are the truncations of the multiplied sequence. -/
theorem hasWeakDeriv_Jinvf_trunc {s : ℝ} {x : Seq n k} (hx : MemSob s x) {l : List (Fin n)}
    (hl : (l.length : ℝ) ≤ s) (M : ℕ) (t : formIdx n (k : ℤ)) :
    HasWeakDeriv (Q (Fin n)) l (Jinvf k (trunc M k x) t) (Jinvf k (trunc M k (mulSeq l x)) t) := by
  intro φ hφ
  set c := fun m => cf (trunc M k x) m (idx k t)
  have hc' : (fun m => cf (trunc M k (mulSeq l x)) m (idx k t)) = fun m => symb l m * c m := by
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

/-- **The weak derivatives of `x|_Q`** for `x ∈ Hˢ(𝕋ⁿ)` and a word `l` with `|l| ≤ s`: the weak
derivative of `u_t = (x|_Q)_t` along `l` is `(Jinvf (mulSeq l x))_t`, the `L²(Q)` limit of the
classical derivatives of the truncations (graph convergence). -/
theorem hasWeakDeriv_of_memSob {s : ℝ} {x : Seq n k} (hx : MemSob s x) {l : List (Fin n)}
    (hl : (l.length : ℝ) ≤ s) (t : formIdx n (k : ℤ)) :
    HasWeakDeriv (Q (Fin n)) l (Jinvf k x t) (Jinvf k (mulSeq l x) t) := by
  have hc : Continuous fun y : Seq n k => (Jinvf k y t : L2 ℝ (Q (Fin n))) :=
    (PiLp.continuous_apply 2 _ t).comp (Jinvf k).continuous
  exact hasWeakDeriv_of_tendsto ((hc.tendsto x).comp (tendsto_trunc k x))
    ((hc.tendsto _).comp (tendsto_trunc k _)) fun M => hasWeakDeriv_Jinvf_trunc hx hl M t

/-- **Forward direction of the identification** (`hasWeakDerivs_of_mem_sobolevQ`): every
`u ∈ Hᵐ(Q; Λᵏ)` (restriction of an `Hᵐ(𝕋ⁿ)` form, `m ∈ ℕ`) has weak derivatives in `L²(Q)` up to
order `m` (`HasWeakDerivs (Q (Fin n)) m u`). -/
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

/-- `(∂^l φ)^(m) = symb_l(m) φ̂(m)`. -/
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
    mFourierCoeff (physF k x t : UnitAddTorus (Fin n) → ℂ) m = cf x m (idx k t) := by
  rw [← mFourierBasis_repr, repr_physF]

/-- **`Hᵐ(𝕋ⁿ)` has weak derivatives up to order `m`** (the multiplier `mulSeq`). -/
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
  change _ = _ * (_ * (symb l m * cf x m (idx k t)))
  ring

/-- Conversely, a weak derivative on `𝕋ⁿ` has the Fourier coefficients `symb_l(m) f̂(m)`. -/
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

/-- **The integer Sobolev spaces of the torus are the spaces of weak derivatives**:
`x ∈ Hᵐ(𝕋ⁿ; Λᵏ)` iff every component of the physical form `physF k x` has weak derivatives up
to order `m` in `L²(𝕋ⁿ)`. The direction `⇐` uses only the pure derivatives `∂_j^m` and the
power-mean inequality `(1 + |ξ|²)ᵐ ≤ (n + 1)^{m-1} (1 + Σ_j ξ_j^{2m})`. -/
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
        ((2 * Real.pi * q j) ^ 2) ^ (m + 1) * ‖cf x q (idx k t)‖ ^ 2 := by
      intro j t
      obtain ⟨v, hv⟩ := h t (List.replicate (m + 1) j) (by simp)
      refine ((hasSum_sq_mFourierCoeff v).summable).congr fun q => ?_
      rw [hv.mFourierCoeff_eq, mFourierCoeff_physF, norm_mul, mul_pow, norm_symb_sq]
      simp
    have hsum : Summable fun q : Fin n → ℤ =>
        (n + 1 : ℝ) ^ m * (‖cf x q‖ ^ 2 + ∑ j, ∑ t : formIdx n (k : ℤ),
          ((2 * Real.pi * q j) ^ 2) ^ (m + 1) * ‖cf x q (idx k t)‖ ^ 2) :=
      ((summable_norm_sq x).add
        (summable_sum fun j _ => summable_sum fun t _ => hpure j t)).mul_left _
    refine Summable.of_nonneg_of_le (fun q => mul_nonneg (weight_nonneg _ _) (sq_nonneg _))
      (fun q => ?_) hsum
    -- the power-mean inequality
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
    rw [weight, show ((m + 1 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
    calc (1 + ‖freq q‖ ^ 2) ^ (m + 1) * ‖cf x q‖ ^ 2
        ≤ ((n + 1 : ℕ) : ℝ) ^ m * (1 + ∑ j, ((2 * Real.pi * q j) ^ 2) ^ (m + 1)) *
          ‖cf x q‖ ^ 2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hpm) (sq_nonneg _)
      _ = (n + 1 : ℝ) ^ m * (‖cf x q‖ ^ 2 + ∑ j, ∑ t : formIdx n (k : ℤ),
          ((2 * Real.pi * q j) ^ 2) ^ (m + 1) * ‖cf x q (idx k t)‖ ^ 2) := by
        push_cast
        rw [mul_assoc, add_mul, one_mul, Finset.sum_mul]
        congr 2
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_cf_sq_eq_sum k, Finset.mul_sum]

/-- **`mem_sobolevPar_nat_iff`**: `u ∈ Hᵐ_J(Q; Λᵏ)` (`m ∈ ℕ`) iff every component of the parity
extension `JfJ J k u` (as a function on `𝕋ⁿ`, `physF k (JfJ J k u)`) has weak derivatives up to
order `m` in `L²(𝕋ⁿ)`. -/
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
/-- **The `Hᵐ` norm by weak derivatives** (squared):
`Σ_t Σ_{p ≤ m} Σ_{|r| = p} ‖∂^r u_t‖²_{L²(Ω)}` over the words `r` of length `≤ m` (a missing
weak derivative contributes `0`; on open `Ω` the weak derivatives are unique,
`HasWeakDeriv.unique`). The sum is over ordered words, so a mixed derivative of multi-index `α`
is counted `|α|!/α!` times; this is equivalent to the sum over multi-indices up to constants
depending only on `m`. -/
def weakHmNormSq (Ω : Set (Fin n → ℝ)) (m : ℕ) {k' : ℤ} (u : L2F ℝ Ω (formIdx n k')) : ℝ :=
  ∑ t : formIdx n k', ∑ p ∈ Finset.range (m + 1), ∑ r : Fin p → Fin n,
    if h : ∃ v, HasWeakDeriv Ω (List.ofFn r) (u t) v then ‖h.choose‖ ^ 2 else 0

/-- **The `Hᵐ` norm by weak derivatives**, `weakHmNorm Ω m u = (weakHmNormSq Ω m u)^{1/2}`. -/
def weakHmNorm (Ω : Set (Fin n → ℝ)) (m : ℕ) {k' : ℤ} (u : L2F ℝ Ω (formIdx n k')) : ℝ :=
  √(weakHmNormSq Ω m u)

/-- **Comparison of the norms** (the forward half of the planned `qNorm_nat_sq_equiv`, the direction
available without an extension operator): for `u ∈ Hᵐ(Q; Λᵏ)`,
`Σ_t Σ_{|r| ≤ m} ‖∂^r u_t‖² ≤ (Σ_{p ≤ m} nᵖ) ‖u‖²_{Hᵐ(Q)}`. -/
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

theorem weakHmNorm_le_qNorm {m : ℕ} {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    (hu : u ∈ sobolevQ n k m) :
    weakHmNorm (Q (Fin n)) m u ≤ √(∑ p ∈ Finset.range (m + 1), (n : ℝ) ^ p) * qNorm k m u := by
  rw [weakHmNorm, ← Real.sqrt_sq (qNorm_nonneg (k := k) m u), ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt (weakHmNormSq_le_qNorm_sq hu)

end Norm

/-! ### `H²` in the parity classes: the compatibility conditions -/

section ParityTwo

variable {k : ℕ}

/-- **The parity of a first derivative**: if `x` is real of the class `J`, the Fourier
coefficients `2πi m_j x(m)` of `∂_j x` are real of the class `J ∆ {j}` (`∂_j` flips the parity
in `x_j`). -/
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
  · change cf (mulSeq [j] x) (DeRham.flipAt i m) t = _ * cf (mulSeq [j] x) m t
    rw [cf_mulSeq hx hl, cf_mulSeq hx hl]
    change symb [j] (DeRham.flipAt i m) * cf x (DeRham.flipAt i m) t =
      _ * (symb [j] m * cf x m t)
    rw [show cf x (DeRham.flipAt i m) t = _ from hJ.2 i m t]
    simp only [symb, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      DeRham.flipAt, DeRham.mixedSign, Finset.mem_symmDiff, Finset.mem_singleton]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i ∈ J <;> simp [hi] <;> ring
    · have : ¬ (j = i) := fun h => hij h.symm
      simp [hij, this]
      ring_nf

/-- **`H²` in the parity classes, with the compatibility conditions** (one inclusion of the
`m = 2` characterization): for `u ∈ H²_J(Q; Λᵏ)`, every coefficient `u_t` lies in `H¹(Q)` with
vanishing trace on the faces normal to `J ∆ t` (`mem_sobolevPar_one_iff`), and every first weak
derivative `∂_j u_t` is the coefficient of a form `w_j ∈ H¹_{J ∆ {j}}(Q; Λᵏ)`: `∂_j u_t ∈ H¹(Q)`
with vanishing trace on the faces normal to `(J ∆ {j}) ∆ t`. For the faces normal to `j` this is
the **compatibility condition on the normal derivative**: `∂_j u_t = 0` on `{x_j ∈ {0, ½}}`
whenever `j ∉ J ∆ t` (the components without a Dirichlet condition there have a vanishing normal
derivative, the odd-order normal derivatives of the even reflection). -/
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

/-- The empty word: every `f` is its own weak derivative of order `0`. -/
theorem hasWeakDeriv_nil_self (f : L2 ℝ Ω) : HasWeakDeriv Ω [] f f := fun φ _ => by simp

/-- **Weak derivatives along `j :: l` from a first derivative**: if `g = ∂_j f` weakly, then
`v = ∂^{j :: l} f` weakly iff `v = ∂^l g` weakly (test with `∂^l φ`). -/
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
/-- The order-`0` term of `weakHmNormSq` is `‖f‖²`. -/
theorem dite_hasWeakDeriv_nil (hΩ : IsOpen Ω) (f : L2 ℝ Ω) :
    (if h : ∃ v, HasWeakDeriv Ω [] f v then ‖h.choose‖ ^ 2 else 0) = ‖f‖ ^ 2 := by
  have hex : ∃ v, HasWeakDeriv Ω [] f v := ⟨f, hasWeakDeriv_nil_self f⟩
  rw [dite_eq_left hex, hex.choose_spec.unique hΩ (hasWeakDeriv_nil_self f)]

open scoped Classical in
/-- The term of `weakHmNormSq` along `j :: l` for `f` is the term along `l` for `∂_j f`. -/
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

theorem weakHmNormSq_nonneg (m : ℕ) {k' : ℤ} (u : L2F ℝ Ω (formIdx n k')) :
    0 ≤ weakHmNormSq Ω m u := by
  classical
  exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun r _ => by
    split_ifs <;> positivity

/-- `weakHmNormSq Ω 0 u = ‖u‖²`. -/
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

/-- **The recursion of the weak `Hᵐ` norm**: if `w_j = ∂_j u` weakly (coefficientwise), then
`Σ_{|r| ≤ m+1} ‖∂^r u‖² = ‖u‖² + Σ_j Σ_{|r| ≤ m} ‖∂^r w_j‖²` (words `j :: r`). -/
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

/-- `⟨ξ⟩^{2(s+1)} |x(q)|² = ⟨ξ⟩^{2s} |x(q)|² + Σ_j ⟨ξ⟩^{2s} |(∂_j x)(q)|²`. -/
theorem weight_add_one_mul {x : Seq n k} (hx1 : MemSob 1 x) (s : ℝ) (q : Fin n → ℤ) :
    weight (s + 1) q * ‖cf x q‖ ^ 2 =
      weight s q * ‖cf x q‖ ^ 2 + ∑ j, weight s q * ‖cf (mulSeq [j] x) q‖ ^ 2 := by
  simp_rw [norm_cf_mulSeq_single_sq hx1]
  rw [weight_add, weight_one, norm_freq_sq, Finset.mul_sum]
  have : ∀ j : Fin n, weight s q * ((2 * Real.pi * q j) ^ 2 * ‖cf x q‖ ^ 2) =
      weight s q * (2 * Real.pi) ^ 2 * ‖cf x q‖ ^ 2 * (q j : ℝ) ^ 2 := fun j => by ring
  simp_rw [this, ← Finset.mul_sum]
  ring

/-- `x ∈ H^{s+1}(𝕋ⁿ)` iff `x ∈ Hˢ(𝕋ⁿ)` and every `∂_j x ∈ Hˢ(𝕋ⁿ)` (for `x ∈ H¹`). -/
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

/-- `‖x‖²_{s+1} = ‖x‖²_s + Σ_j ‖∂_j x‖²_s`. -/
theorem sobSum_add_one {x : Seq n k} (hx1 : MemSob 1 x) {s : ℝ} (h : MemSob (s + 1) x) :
    sobSum (s + 1) x = sobSum s x + ∑ j, sobSum s (mulSeq [j] x) := by
  obtain ⟨hs, hj⟩ := (memSob_add_one_iff hx1 s).1 h
  unfold sobSum
  simp_rw [weight_add_one_mul hx1 s]
  rw [Summable.tsum_add hs (summable_sum fun j _ => hj j),
    Summable.tsum_finsetSum fun j _ => hj j]

/-- `x ∈ H^{m+1}(𝕋ⁿ)` iff every `∂_j x ∈ Hᵐ(𝕋ⁿ)` (for `x ∈ H¹`, `m ∈ ℕ`; induction on the
order). -/
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

/-- **A weak first derivative on `Q` of `u ∈ H¹_J` is the restriction of `∂_j (JfJ J k u)`**
(uniqueness of weak derivatives), and its parity extension in the class `J ∆ {j}` is
`∂_j (JfJ J k u)` (`realParJ_mulSeq_single`). -/
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

/-- **The parity classes of every integer order on `Q`** (`mem_sobolevPar_add_one_iff`):
`u ∈ H^{m+1}_J(Q; Λᵏ)` iff `u ∈ H¹_J(Q; Λᵏ)` and, for every `j`, the weak derivative `∂_j u`
(coefficientwise in `L²(Q)`) exists and lies in `Hᵐ_{J ∆ {j}}(Q; Λᵏ)`. By induction on `m` (with
`mem_sobolevPar_one_iff`) this characterizes `Hᵐ_J(Q)` intrinsically on `Q`: weak derivatives up to
order `m` in `L²(Q)` with the vanishing traces of `∂^r u_t` (`|r| < m`) on the faces normal to
`(J ∆ r) ∆ t` (`r` read as the set of directions of odd multiplicity). -/
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

/-- **`H²` in the parity classes, the full characterization** (`mem_sobolevPar_two_iff`):
`u ∈ H²_J(Q; Λᵏ)` iff every `u_t ∈ H¹(Q)` has vanishing trace on the faces normal to `J ∆ t` and
every first weak derivative `∂_j u_t` is the coefficient of `w_j ∈ H¹_{J ∆ {j}}(Q; Λᵏ)`, i.e.
`∂_j u_t ∈ H¹(Q)` with vanishing trace on the faces normal to `(J ∆ {j}) ∆ t` (the compatibility
conditions on the normal derivatives). `⇒` is `mem_sobolevPar_two_compat`. -/
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

/-- **The recursion of the `H^{m+1}_J` norm**:
`‖u‖²_{m+1,J} = ‖u‖²_{m,J} + Σ_j ‖∂_j u‖²_{m,J∆{j}}`. -/
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

/-- **Norm comparison on the parity classes, `≥`** (the reverse inequality): for `u ∈ Hᵐ_J(Q)`,
`‖u‖²_{m,J} ≤ 2ᵐ Σ_t Σ_{|r| ≤ m} ‖∂^r u_t‖²_{L²(Q)}`. With `weakHmNormSq_le_parNorm_sq`, the
`Hᵐ_J` norm is equivalent to the weak `Hᵐ(Q)` norm, with constants depending only on `m`. -/
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
