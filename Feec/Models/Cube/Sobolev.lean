module

public import Feec.Models.Cube.DeRhamPartialIdent
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.PSeries

/-!
# Sobolev spaces on the cube `Q = (0, ½)ⁿ`

Fractional Sobolev spaces of `k`-forms on `Q = (0, ½)ⁿ` (`Geometry.Q (Fin n)`), for real `s`,
defined on the Fourier side of the period-`1` torus `𝕋ⁿ = ℝⁿ/ℤⁿ` (normalised Haar measure,
frequencies `ξ_m = 2πm`, `m ∈ ℤⁿ`, weight `⟨ξ_m⟩^{2s} = (1 + |2πm|²)^s`, `weight`). A coefficient
sequence `x ∈ ℓ²(ℤⁿ; Λᵏ)` (`Seq n k`) is in `Hˢ(𝕋ⁿ)` if `Σ_m ⟨ξ_m⟩^{2s} |x(m)|² < ∞` (`MemSob`,
`sobSum`); `x|_Q` is the restriction to `Q` of the real part of its inverse Fourier transform
(`Feec.Models.Cube.DeRhamIdent.Jinvf`).

* **Without boundary condition** (`sobolevQ n k s`, `qNorm`): the restrictions to `Q` of the
  forms of `Hˢ(𝕋ⁿ)`, with the quotient norm `‖u‖_{Hˢ(Q)} = inf {‖x‖_{Hˢ(𝕋ⁿ)} : x|_Q = u}`
  (the Fourier definition of fractional Sobolev spaces by restriction, with periodic extensions
  in place of extensions to `ℝⁿ`; for `s = 1` it is the space `H¹(Q)` of [Brezis2011], §9.1, by
  `mem_sobolevQ_one_iff` and `qNorm_one_sq_equiv`).
* **The parity classes** (`sobolevPar J k s`, `parNorm`): the forms whose parity extension in the
  class `J` (`Feec.Models.Cube.DeRhamIdent.JfJ`: odd in `x_j` for the components that vanish on
  the faces normal to `e_j`, i.e. the tangential components for `j ∈ J`, the normal ones for
  `j ∉ J`) lies in `Hˢ(𝕋ⁿ)`, `‖u‖²_{s,J} = 2⁻ⁿ Σ_m ⟨ξ_m⟩^{2s} |(JfJ u)(m)|²`. `J = ∅` is the
  absolute class (`Jf false`), `J = univ` the relative class (`Jf true`, vanishing tangential
  trace), the other `J` the partial boundary conditions of `HΛ_J(Q)`.

## Main results

* **`L²` and monotonicity**: `sobolevPar_zero`, **`parNorm_zero`**, `sobolevQ_zero`,
  **`qNorm_zero`** (`H⁰ = L²` isometrically; for `sobolevQ` through the contraction
  `norm_Jinvf_le` and the extension by zero `zeroExt`, the average of the `2ⁿ` parity extensions,
  orthogonal by `inner_JfJ_eq_zero`); `sobolevPar_anti`, `parNorm_mono`, `norm_le_parNorm`;
  `sobolevPar_le_sobolevQ`.
* **`H¹` is the weak-derivative space**: **`mem_sobolevPar_one_iff`** (`u ∈ H¹_J` iff every
  coefficient `u_t` lies in `D(d_{J ∆ t})`, i.e. is `H¹(Q)` with vanishing trace on the faces
  normal to `J ∆ t`) with the norm identity **`parNorm_one_sq`**
  (`‖u‖²_{1,J} = ‖u‖² + Σ_t ‖∇_{J ∆ t} u_t‖²`), and **`mem_sobolevQ_one_iff`** (`u ∈ H¹(Q)` iff
  every coefficient lies in `D(grad_max) = H¹(Q)`: forward by graph-norm convergence of the
  truncations, `coeff_mem_maximal_of_mem_sobolevQ_one`; backward by the even reflection of each
  coefficient), with equivalent norms, **`qNorm_one_sq_equiv`**:
  `‖u‖² + Σ_t ‖∇ u_t‖² ≤ ‖u‖²_{H¹(Q)} ≤ 2ⁿ (‖u‖² + Σ_t ‖∇ u_t‖²)`
  (`norm_sq_add_sum_grad_sq_le_qNorm`; `qNorm_one_sq_le` through the coefficientwise even
  extension `evenExt`, `sobSum_evenExt`).
* **Fourier truncation** `u_M` (frequencies `|m|_∞ ≤ M`, a real trigonometric polynomial
  restricted to `Q`; `truncPar` in the class `J`, `truncPar_mem`, and `Jinvf k (trunc M k x)` for
  an extension `x`):
  - `‖u - u_M‖ ≤ (2π(M + 1))^{-s} ‖u‖` (**`norm_sub_truncPar_le`**, **`norm_sub_Jinvf_trunc_le`**),
    in every weaker norm `‖u - u_M‖_t² ≤ (1 + (2π(M + 1))²)^{t - s} ‖u‖_s²`
    (`parNorm_sub_truncPar_sq_le`, `sobSum_sub_trunc_le`);
  - the inverse estimates `‖u_M‖_t² ≤ (1 + n(2πM)²)^{t - s} ‖u‖_s²` for `t ≥ s`
    (`parNorm_truncPar_sq_le`); for the gradient,
    `Σ_t ‖∇ (u_M)_t‖² ≤ (1 + n(2πM)²)^{1 - s} ‖x‖²_{Hˢ(𝕋ⁿ)}` for `s ≤ 1` (`grad_truncQ_le`, from
    `grad_Jinvf_sum_le`: `Σ_t ‖∇ (x|_Q)_t‖² ≤ ‖x‖²_{H¹(𝕋ⁿ)}` for trigonometric polynomials), and
    `‖u_M‖²_{1,J} ≤ (1 + n(2πM)²)^{1 - s} ‖u‖²_{s,J}` with `parNorm_one_sq` in the classes; the
    derivatives `Dᵐ`, `m ≥ 2`, enter only through the `Hᵐ` norm.

No hypothesis is assumed. Not formalized: the identification of `Hᵐ`, `m ≥ 2`, with the spaces of
`m` weak derivatives in `L²(Q)`, the Slobodeckij form of the fractional norms, and the equality
`Hˢ(Q) = Hˢ_∅(Q)` (with equivalent norms) for `s < 3/2`.

## References

* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.1 (the space `H¹`), §9.2 (extension by reflection)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4.3 (relative and absolute boundary conditions)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (the cube by the method of images)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate Topology
open Set MeasureTheory Filter Finset

@[expose] public noncomputable section

namespace Feec.Models.Cube.Sobolev

open Feec.Models.Cube.DeRhamIdent Geometry
open Feec.Domain (formIdx L2F L2 toL2F extDerivOp)
open Feec.Fourier.Exterior (Form)
open Feec.Fourier.Torus (freq bandN finite_bandN norm_freq_sq)

variable {n : ℕ}

/-! ### The Sobolev weight -/

/-- The Sobolev weight `⟨ξ_m⟩^{2s} = (1 + |2πm|²)^s` of the frequency `m ∈ ℤⁿ`. -/
def weight (s : ℝ) (m : Fin n → ℤ) : ℝ := (1 + ‖freq m‖ ^ 2) ^ s

theorem one_le_base (m : Fin n → ℤ) : 1 ≤ 1 + ‖freq m‖ ^ 2 := by
  have := sq_nonneg ‖freq m‖; linarith

theorem base_pos (m : Fin n → ℤ) : 0 < 1 + ‖freq m‖ ^ 2 :=
  lt_of_lt_of_le one_pos (one_le_base m)

theorem weight_pos (s : ℝ) (m : Fin n → ℤ) : 0 < weight s m :=
  Real.rpow_pos_of_pos (base_pos m) s

theorem weight_nonneg (s : ℝ) (m : Fin n → ℤ) : 0 ≤ weight s m := (weight_pos s m).le

@[simp] theorem weight_zero (m : Fin n → ℤ) : weight 0 m = 1 := Real.rpow_zero _

theorem weight_one (m : Fin n → ℤ) : weight 1 m = 1 + ‖freq m‖ ^ 2 := Real.rpow_one _

theorem weight_add (s t : ℝ) (m : Fin n → ℤ) : weight (s + t) m = weight s m * weight t m :=
  Real.rpow_add (base_pos m) s t

theorem weight_mono {s t : ℝ} (h : s ≤ t) (m : Fin n → ℤ) : weight s m ≤ weight t m :=
  Real.rpow_le_rpow_of_exponent_le (one_le_base m) h

/-- Inside the band `|m|_∞ ≤ M` the frequencies are at most `2π √n M`. -/
theorem norm_freq_sq_le_of_mem {M : ℕ} {m : Fin n → ℤ} (hm : m ∈ bandN M) :
    ‖freq m‖ ^ 2 ≤ n * (2 * Real.pi * M) ^ 2 := by
  rw [norm_freq_sq]
  have h : ∀ i, ((m i : ℝ)) ^ 2 ≤ (M : ℝ) ^ 2 := fun i => by
    have h2 : |(m i : ℝ)| ≤ M := by exact_mod_cast hm i
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  calc (2 * Real.pi) ^ 2 * ∑ i, ((m i : ℝ)) ^ 2 ≤ (2 * Real.pi) ^ 2 * ∑ _i : Fin n, (M : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i) (by positivity)
    _ = n * (2 * Real.pi * M) ^ 2 := by simp; ring

/-- **The weight inside the band**: `⟨ξ_m⟩^{2s} ≤ (1 + n (2πM)²)^s` for `s ≥ 0`. -/
theorem weight_le_of_mem {s : ℝ} (hs : 0 ≤ s) {M : ℕ} {m : Fin n → ℤ} (hm : m ∈ bandN M) :
    weight s m ≤ (1 + n * (2 * Real.pi * M) ^ 2) ^ s :=
  Real.rpow_le_rpow (base_pos m).le (by linarith [norm_freq_sq_le_of_mem hm]) hs

/-! ### Weighted sums of coefficient sequences -/

section Seq

variable {k : ℕ}

/-- The coefficient sequences of `k`-forms on `𝕋ⁿ`: `ℓ²(ℤⁿ; Λᵏ)`. -/
abbrev Seq (n k : ℕ) := Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))

/-- The value `x(m)` of a coefficient sequence at a frequency. -/
abbrev cf (x : Seq n k) (m : Fin n → ℤ) : Form ℂ (Fin n) k :=
  (x : (Fin n → ℤ) → Form ℂ (Fin n) k) m

theorem norm_sq_eq_tsum (x : Seq n k) : ‖x‖ ^ 2 = ∑' m, ‖cf x m‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    ((lp.equivLpCount ℂ (Fin n → ℤ) (Form ℂ (Fin n) k) 2).symm x)
  rw [LinearIsometryEquiv.norm_map] at h
  simp only [lp.equivLpCount_symm_apply, ENNReal.toReal_ofNat] at h
  simpa only [Real.rpow_two] using h

theorem summable_norm_sq (x : Seq n k) : Summable fun m => ‖cf x m‖ ^ 2 := by
  have h := (lp.memℓp_count (Fin n → ℤ) (Form ℂ (Fin n) k) 2 x).summable (by norm_num)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem cf_add (x y : Seq n k) (m : Fin n → ℤ) : cf (x + y) m = cf x m + cf y m :=
  Measure.ae_count_iff.1 (Lp.coeFn_add x y) m

theorem cf_sub (x y : Seq n k) (m : Fin n → ℤ) : cf (x - y) m = cf x m - cf y m :=
  Measure.ae_count_iff.1 (Lp.coeFn_sub x y) m

theorem cf_smul (c : ℂ) (x : Seq n k) (m : Fin n → ℤ) : cf (c • x) m = c • cf x m :=
  Measure.ae_count_iff.1 (Lp.coeFn_smul c x) m

theorem cf_zero (m : Fin n → ℤ) : cf (0 : Seq n k) m = 0 :=
  Measure.ae_count_iff.1 (Lp.coeFn_zero _ 2 _) m

/-- A function with summable squares is a coefficient sequence. -/
theorem memLp_of_summable {f : (Fin n → ℤ) → Form ℂ (Fin n) k}
    (hf : Summable fun m => ‖f m‖ ^ 2) : MemLp f 2 (Measure.count : Measure (Fin n → ℤ)) :=
  (memLp_count_iff (by norm_num)).2 (memℓp_gen (by simpa using hf))

/-- The weighted sum `Σ_m ⟨ξ_m⟩^{2s} |x(m)|²`. -/
def sobSum (s : ℝ) (x : Seq n k) : ℝ := ∑' m, weight s m * ‖cf x m‖ ^ 2

/-- `x ∈ Hˢ(𝕋ⁿ; Λᵏ)` on the Fourier side: `Σ_m ⟨ξ_m⟩^{2s} |x(m)|² < ∞`. -/
def MemSob (s : ℝ) (x : Seq n k) : Prop := Summable fun m => weight s m * ‖cf x m‖ ^ 2

theorem sobSum_nonneg (s : ℝ) (x : Seq n k) : 0 ≤ sobSum s x :=
  tsum_nonneg fun m => mul_nonneg (weight_nonneg s m) (sq_nonneg _)

theorem memSob_zero (x : Seq n k) : MemSob 0 x := by
  simpa [MemSob] using summable_norm_sq x

theorem sobSum_zero (x : Seq n k) : sobSum 0 x = ‖x‖ ^ 2 := by
  simp [sobSum, norm_sq_eq_tsum]

theorem MemSob.mono {s t : ℝ} (h : s ≤ t) {x : Seq n k} (hx : MemSob t x) : MemSob s x :=
  Summable.of_nonneg_of_le (fun m => mul_nonneg (weight_nonneg s m) (sq_nonneg _))
    (fun m => mul_le_mul_of_nonneg_right (weight_mono h m) (sq_nonneg _)) hx

theorem sobSum_mono {s t : ℝ} (h : s ≤ t) {x : Seq n k} (hx : MemSob t x) :
    sobSum s x ≤ sobSum t x :=
  Summable.tsum_le_tsum (fun m => mul_le_mul_of_nonneg_right (weight_mono h m) (sq_nonneg _))
    (hx.mono h) hx

theorem norm_add_sq_le (a b : Form ℂ (Fin n) k) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have := norm_add_le a b
  nlinarith [norm_nonneg (a + b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]

theorem MemSob.add {s : ℝ} {x y : Seq n k} (hx : MemSob s x) (hy : MemSob s y) :
    MemSob s (x + y) := by
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (weight_nonneg s m) (sq_nonneg _))
    (fun m => ?_) ((hx.mul_left 2).add (hy.mul_left 2))
  rw [cf_add]
  have := norm_add_sq_le (cf x m) (cf y m)
  have := weight_nonneg s m
  nlinarith

theorem MemSob.smul {s : ℝ} (c : ℂ) {x : Seq n k} (hx : MemSob s x) : MemSob s (c • x) := by
  refine (hx.mul_left (‖c‖ ^ 2)).congr fun m => ?_
  rw [cf_smul, norm_smul, mul_pow]; ring

theorem MemSob.real_smul {s : ℝ} (c : ℝ) {x : Seq n k} (hx : MemSob s x) : MemSob s (c • x) :=
  hx.smul (c : ℂ)

theorem memSob_zero_seq (s : ℝ) : MemSob s (0 : Seq n k) := by
  simp [MemSob, cf_zero]

theorem MemSob.neg {s : ℝ} {x : Seq n k} (hx : MemSob s x) : MemSob s (-x) := by
  simpa using hx.smul (-1)

theorem MemSob.sub {s : ℝ} {x y : Seq n k} (hx : MemSob s x) (hy : MemSob s y) :
    MemSob s (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem MemSob.sum {s : ℝ} {ι : Type*} (t : Finset ι) {x : ι → Seq n k}
    (hx : ∀ i ∈ t, MemSob s (x i)) : MemSob s (∑ i ∈ t, x i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using memSob_zero_seq (k := k) s
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (hx a (Finset.mem_insert_self a t)).add
      (ih fun i hi => hx i (Finset.mem_insert_of_mem hi))

/-- Finitely supported sequences have every Sobolev regularity. -/
theorem memSob_of_finite {s : ℝ} {x : Seq n k} (S : Finset (Fin n → ℤ))
    (hS : ∀ m ∉ S, cf x m = 0) : MemSob s x :=
  summable_of_ne_finset_zero (s := S) fun m hm => by simp [hS m hm]

end Seq

/-! ### Fourier truncation -/

section Trunc

variable {k : ℕ}

theorem rpow_le_rpow_of_nonpos {x y z : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hz : z ≤ 0) :
    x ^ z ≤ y ^ z := by
  have hx : 0 < x := hy.trans_le hyx
  have e : ∀ w : ℝ, 0 < w → w ^ z = (w⁻¹) ^ (-z) := fun w hw => by
    rw [Real.inv_rpow hw.le, ← Real.rpow_neg hw.le, neg_neg]
  rw [e x hx, e y hy]
  exact Real.rpow_le_rpow (inv_nonneg.2 hx.le) (inv_anti₀ hy hyx) (neg_nonneg.2 hz)

open scoped Classical in
theorem cf_trunc (M : ℕ) (x : Seq n k) (m : Fin n → ℤ) :
    cf (trunc M k x) m = if m ∈ bandN M then cf x m else 0 :=
  coeFn_trunc M k x m

theorem cf_trunc_of_mem {M : ℕ} (x : Seq n k) {m : Fin n → ℤ} (hm : m ∈ bandN M) :
    cf (trunc M k x) m = cf x m := by
  classical
  simp [cf_trunc, hm]

theorem cf_trunc_of_notMem {M : ℕ} (x : Seq n k) {m : Fin n → ℤ} (hm : m ∉ bandN M) :
    cf (trunc M k x) m = 0 := by
  classical
  simp [cf_trunc, hm]

theorem cf_sub_trunc_of_mem {M : ℕ} (x : Seq n k) {m : Fin n → ℤ} (hm : m ∈ bandN M) :
    cf (x - trunc M k x) m = 0 := by
  rw [cf_sub, cf_trunc_of_mem x hm, sub_self]

theorem cf_sub_trunc_of_notMem {M : ℕ} (x : Seq n k) {m : Fin n → ℤ} (hm : m ∉ bandN M) :
    cf (x - trunc M k x) m = cf x m := by
  rw [cf_sub, cf_trunc_of_notMem x hm, sub_zero]

theorem memSob_trunc (t : ℝ) (M : ℕ) (x : Seq n k) : MemSob t (trunc M k x) :=
  memSob_of_finite (bandS M) fun _ hm => trunc_eq_zero_of_notMem x hm

/-- **The truncation error in every weaker norm**: for `t ≤ s`,
`Σ ⟨ξ⟩^{2t} |x - x_M|² ≤ (1 + (2π(M+1))²)^{t-s} Σ ⟨ξ⟩^{2s} |x|²`. -/
theorem sobSum_sub_trunc_le {s t : ℝ} (hts : t ≤ s) {x : Seq n k} (hx : MemSob s x) (M : ℕ) :
    MemSob t (x - trunc M k x) ∧
      sobSum t (x - trunc M k x) ≤ (1 + (2 * Real.pi * (M + 1)) ^ 2) ^ (t - s) * sobSum s x := by
  set B : ℝ := (1 + (2 * Real.pi * (M + 1)) ^ 2) ^ (t - s)
  have hB : 0 ≤ B := by positivity
  have hle : ∀ m, weight t m * ‖cf (x - trunc M k x) m‖ ^ 2 ≤ B * (weight s m * ‖cf x m‖ ^ 2) := by
    intro m
    by_cases hm : m ∈ bandN M
    · rw [cf_sub_trunc_of_mem x hm, norm_zero, zero_pow two_ne_zero, mul_zero]
      exact mul_nonneg hB (mul_nonneg (weight_nonneg s m) (sq_nonneg _))
    · rw [cf_sub_trunc_of_notMem x hm]
      have hf : (2 * Real.pi * (M + 1)) ^ 2 ≤ ‖freq m‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity)
          (Feec.Fourier.Torus.two_pi_mul_add_one_le_norm_freq_of_notMem hm) 2
      have hw : weight t m ≤ B * weight s m := by
        have e : weight t m = weight (t - s) m * weight s m := by
          rw [← weight_add]; ring_nf
        rw [e]
        refine mul_le_mul_of_nonneg_right ?_ (weight_nonneg s m)
        exact rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      calc weight t m * ‖cf x m‖ ^ 2 ≤ (B * weight s m) * ‖cf x m‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hw (sq_nonneg _)
        _ = _ := by ring
  have hsum : MemSob t (x - trunc M k x) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (weight_nonneg t m) (sq_nonneg _)) hle
      (hx.mul_left B)
  refine ⟨hsum, ?_⟩
  calc sobSum t (x - trunc M k x) ≤ ∑' m, B * (weight s m * ‖cf x m‖ ^ 2) :=
        Summable.tsum_le_tsum hle hsum (hx.mul_left B)
    _ = B * sobSum s x := tsum_mul_left

/-- **The inverse estimate for the truncation**: for `s ≤ t`,
`Σ ⟨ξ⟩^{2t} |x_M|² ≤ (1 + n (2πM)²)^{t-s} Σ ⟨ξ⟩^{2s} |x|²`. -/
theorem sobSum_trunc_le {s t : ℝ} (hst : s ≤ t) {x : Seq n k} (hx : MemSob s x) (M : ℕ) :
    sobSum t (trunc M k x) ≤ (1 + n * (2 * Real.pi * M) ^ 2) ^ (t - s) * sobSum s x := by
  set A : ℝ := (1 + n * (2 * Real.pi * M) ^ 2) ^ (t - s)
  have hle : ∀ m, weight t m * ‖cf (trunc M k x) m‖ ^ 2 ≤ A * (weight s m * ‖cf x m‖ ^ 2) := by
    intro m
    by_cases hm : m ∈ bandN M
    · rw [cf_trunc_of_mem x hm]
      have hw : weight t m ≤ A * weight s m := by
        have e : weight t m = weight (t - s) m * weight s m := by
          rw [← weight_add]; ring_nf
        rw [e]
        exact mul_le_mul_of_nonneg_right (weight_le_of_mem (by linarith) hm) (weight_nonneg s m)
      calc weight t m * ‖cf x m‖ ^ 2 ≤ (A * weight s m) * ‖cf x m‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hw (sq_nonneg _)
        _ = _ := by ring
    · rw [cf_trunc_of_notMem x hm, norm_zero, zero_pow two_ne_zero, mul_zero]
      have : 0 ≤ A := by positivity
      exact mul_nonneg this (mul_nonneg (weight_nonneg s m) (sq_nonneg _))
  calc sobSum t (trunc M k x) ≤ ∑' m, A * (weight s m * ‖cf x m‖ ^ 2) :=
        Summable.tsum_le_tsum hle (memSob_trunc t M x) (hx.mul_left A)
    _ = A * sobSum s x := tsum_mul_left

/-- **The `L²` truncation error**: `‖x - x_M‖² ≤ (1 + (2π(M+1))²)^{-s} Σ ⟨ξ⟩^{2s} |x|²` for
`s ≥ 0`. -/
theorem norm_sub_trunc_sq_le {s : ℝ} (hs : 0 ≤ s) {x : Seq n k} (hx : MemSob s x) (M : ℕ) :
    ‖x - trunc M k x‖ ^ 2 ≤ (1 + (2 * Real.pi * (M + 1)) ^ 2) ^ (-s) * sobSum s x := by
  have h := (sobSum_sub_trunc_le hs hx M).2
  rwa [sobSum_zero, zero_sub] at h

end Trunc

/-! ### The restriction to `Q` is a contraction -/

section Contraction

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Fourier.TorusWeak`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem norm_reL_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : Lp ℂ 2 μ) :
    ‖RowWise.reL μ f‖ ≤ ‖f‖ :=
  Lp.norm_le_norm_of_ae_le (by
    filter_upwards [RowWise.coeFn_reL f] with x hx
    rw [hx, Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _)

theorem norm_resQ_le {d : Type*} [Fintype d]
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) : ‖resQ f‖ ≤ ‖f‖ := by
  change ‖(Lp.compMeasurePreservingₗᵢ ℂ Feec.Fourier.TorusWeak.proj measurePreserving_proj_Q)
    (LpToLpRestrictCLM (UnitAddTorus d) ℂ ℂ volume 2 (boxSet d) f)‖ ≤ ‖f‖
  rw [LinearIsometry.norm_map]
  exact norm_Lp_toLp_restrict_le _ f

theorem norm_piLp_le_of_le {ι : Type*} [Fintype ι] {E F : ι → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, SeminormedAddCommGroup (F i)]
    (G : PiLp 2 E) (H : PiLp 2 F) (h : ∀ i, ‖G i‖ ≤ ‖H i‖) : ‖G‖ ≤ ‖H‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (h i) 2)

/-- **Restriction to `Q` (real part) is a contraction**: `‖x|_Q‖_{L²(Q)} ≤ ‖x‖_{ℓ²}`. -/
theorem norm_Jinvf_le (k : ℕ) (x : Seq n k) : ‖Jinvf k x‖ ≤ ‖x‖ := by
  set F := (Fourier.Torus.fieldFourier (Fin n) (formIdx n (k : ℤ))).symm x
  change ‖Jinv (Fin n) (formIdx n (k : ℤ)) x‖ ≤ ‖x‖
  rw [Jinv_apply]
  calc ‖reF (Q (Fin n)) (formIdx n (k : ℤ)) (resQF F)‖ ≤ ‖resQF (P := formIdx n (k : ℤ)) F‖ :=
        norm_piLp_le_of_le _ _ fun p => by rw [reF_apply]; exact norm_reL_le _ _
    _ ≤ ‖F‖ := norm_piLp_le_of_le _ _ fun p => by rw [resQF_apply]; exact norm_resQ_le _
    _ = ‖x‖ := by rw [LinearIsometryEquiv.norm_map]

end Contraction

/-! ### The parity classes `Hˢ_J(Q; Λᵏ)` -/

section Parity

variable (J : Finset (Fin n)) (k : ℕ)

theorem norm_JfJ_sq (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    ‖JfJ J k u‖ ^ 2 = 2 ^ n * ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_JfJ, real_inner_self_eq_norm_sq]

/-- **The Sobolev space of the parity class `J`**: the `k`-forms `u` on `Q = (0, ½)ⁿ` whose
parity extension `JfJ J k u` (odd in `x_j` for the components vanishing on the faces normal to
`e_j`: tangential components for `j ∈ J`, normal ones for `j ∉ J`) lies in `Hˢ(𝕋ⁿ)`:
`Σ_m (1 + |2πm|²)^s |(JfJ u)(m)|² < ∞`. `J = ∅` is the absolute class (`Jf false`), `J = univ`
the relative class (`Jf true`, vanishing tangential trace). -/
def sobolevPar (s : ℝ) : Submodule ℝ (L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) where
  carrier := {u | MemSob s (JfJ J k u)}
  add_mem' {u v} hu hv := by
    change MemSob s (JfJ J k (u + v)); rw [map_add]; exact MemSob.add hu hv
  zero_mem' := by change MemSob s (JfJ J k 0); rw [map_zero]; exact memSob_zero_seq s
  smul_mem' c u hu := by
    change MemSob s (JfJ J k (c • u)); rw [map_smul]; exact MemSob.real_smul c hu

theorem mem_sobolevPar {s : ℝ} {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))} :
    u ∈ sobolevPar J k s ↔ MemSob s (JfJ J k u) := Iff.rfl

/-- The norm of `Hˢ_J(Q; Λᵏ)`: `‖u‖²_{s,J} = 2⁻ⁿ Σ_m (1 + |2πm|²)^s |(JfJ u)(m)|²` (the factor
`2⁻ⁿ` makes it the `L²(Q)` norm for `s = 0`). -/
def parNorm (s : ℝ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) : ℝ :=
  √((2 ^ n)⁻¹ * sobSum s (JfJ J k u))

theorem parNorm_nonneg (s : ℝ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    0 ≤ parNorm J k s u := Real.sqrt_nonneg _

theorem parNorm_sq (s : ℝ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    parNorm J k s u ^ 2 = (2 ^ n)⁻¹ * sobSum s (JfJ J k u) :=
  Real.sq_sqrt (mul_nonneg (by positivity) (sobSum_nonneg s _))

/-- **`H⁰_J = L²` isometrically.** -/
theorem sobolevPar_zero : sobolevPar J k 0 = ⊤ :=
  eq_top_iff.2 fun u _ => memSob_zero (JfJ J k u)

theorem parNorm_zero (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) : parNorm J k 0 u = ‖u‖ := by
  rw [parNorm, sobSum_zero, norm_JfJ_sq, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul,
    Real.sqrt_sq (norm_nonneg u)]

/-- **Monotonicity**: `Hᵗ_J ⊆ Hˢ_J` and `‖u‖_{s,J} ≤ ‖u‖_{t,J}` for `s ≤ t`. -/
theorem sobolevPar_anti {s t : ℝ} (h : s ≤ t) : sobolevPar J k t ≤ sobolevPar J k s :=
  fun _ hu => MemSob.mono h hu

theorem parNorm_mono {s t : ℝ} (h : s ≤ t) {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    (hu : u ∈ sobolevPar J k t) : parNorm J k s u ≤ parNorm J k t u :=
  Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (sobSum_mono h hu) (by positivity))

theorem norm_le_parNorm {s : ℝ} (hs : 0 ≤ s) {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    (hu : u ∈ sobolevPar J k s) : ‖u‖ ≤ parNorm J k s u := by
  rw [← parNorm_zero J k u]; exact parNorm_mono J k hs hu

/-- **The Fourier truncation in the parity class** `u_M = (x_M)|_Q`, `x = JfJ J k u`: the
restriction to `Q` of a real trigonometric polynomial of the class `J` (frequencies
`|m|_∞ ≤ M`), smooth on `cl Q`. -/
def truncPar (M : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)) :=
  Jinvf k (trunc M k (JfJ J k u))

theorem JfJ_truncPar (M : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    JfJ J k (truncPar J k M u) = trunc M k (JfJ J k u) :=
  JfJ_Jinvf (realParJ_trunc (JfJ_realParJ J k u) M)

theorem JfJ_sub_truncPar (M : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    JfJ J k (u - truncPar J k M u) = JfJ J k u - trunc M k (JfJ J k u) := by
  rw [map_sub, JfJ_truncPar]

/-- The truncation is in every Sobolev class. -/
theorem truncPar_mem (t : ℝ) (M : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    truncPar J k M u ∈ sobolevPar J k t := by
  rw [mem_sobolevPar, JfJ_truncPar]; exact memSob_trunc t M _

/-- **Truncation error in the parity class, in every weaker norm** (`t ≤ s`):
`‖u - u_M‖²_{t,J} ≤ (1 + (2π(M+1))²)^{t-s} ‖u‖²_{s,J}`. -/
theorem parNorm_sub_truncPar_sq_le {s t : ℝ} (hts : t ≤ s)
    {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))} (hu : u ∈ sobolevPar J k s) (M : ℕ) :
    parNorm J k t (u - truncPar J k M u) ^ 2 ≤
      (1 + (2 * Real.pi * (M + 1)) ^ 2) ^ (t - s) * parNorm J k s u ^ 2 := by
  rw [parNorm_sq, parNorm_sq, JfJ_sub_truncPar]
  have h := (sobSum_sub_trunc_le hts hu M).2
  calc (2 ^ n)⁻¹ * sobSum t (JfJ J k u - trunc M k (JfJ J k u)) ≤
      (2 ^ n)⁻¹ * ((1 + (2 * Real.pi * (M + 1)) ^ 2) ^ (t - s) * sobSum s (JfJ J k u)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- **Inverse estimate for the truncation in the parity class** (`s ≤ t`):
`‖u_M‖²_{t,J} ≤ (1 + n (2πM)²)^{t-s} ‖u‖²_{s,J}`. -/
theorem parNorm_truncPar_sq_le {s t : ℝ} (hst : s ≤ t)
    {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))} (hu : u ∈ sobolevPar J k s) (M : ℕ) :
    parNorm J k t (truncPar J k M u) ^ 2 ≤
      (1 + n * (2 * Real.pi * M) ^ 2) ^ (t - s) * parNorm J k s u ^ 2 := by
  rw [parNorm_sq, parNorm_sq, JfJ_truncPar]
  have h := sobSum_trunc_le hst hu M
  calc (2 ^ n)⁻¹ * sobSum t (trunc M k (JfJ J k u)) ≤
      (2 ^ n)⁻¹ * ((1 + n * (2 * Real.pi * M) ^ 2) ^ (t - s) * sobSum s (JfJ J k u)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

theorem rpow_neg_le_sq {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    (1 + a ^ 2) ^ (-s) ≤ (a ^ (-s)) ^ 2 := by
  have e : (a ^ (-s)) ^ 2 = (a ^ 2) ^ (-s) := by
    rw [← Real.rpow_natCast (a ^ (-s)) 2, ← Real.rpow_mul ha.le, ← Real.rpow_natCast a 2,
      ← Real.rpow_mul ha.le]
    ring_nf
  rw [e]
  exact rpow_le_rpow_of_nonpos (pow_pos ha 2) (by linarith) (neg_nonpos.2 hs)

/-- **The `L²` truncation error in the parity class**:
`‖u - u_M‖ ≤ (2π(M + 1))^{-s} ‖u‖_{s,J}` for `s ≥ 0`. -/
theorem norm_sub_truncPar_le {s : ℝ} (hs : 0 ≤ s) {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    (hu : u ∈ sobolevPar J k s) (M : ℕ) :
    ‖u - truncPar J k M u‖ ≤ (2 * Real.pi * (M + 1)) ^ (-s) * parNorm J k s u := by
  have h := parNorm_sub_truncPar_sq_le J k hs hu M
  rw [parNorm_zero, zero_sub] at h
  have ha : 0 < 2 * Real.pi * (M + 1) := by positivity
  have h2 := h.trans (mul_le_mul_of_nonneg_right (rpow_neg_le_sq ha hs) (sq_nonneg _))
  rw [← mul_pow] at h2
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by positivity) (parNorm_nonneg J k s u))).1 h2

end Parity

/-! ### `d_J` and the truncation; the coefficients as `0`-forms -/

section ParityH1

variable (J : Finset (Fin n)) (k : ℕ)

/-- The `0`-form with coefficient `f`. -/
def zeroF {Ω : Set (Fin n → ℝ)} (f : L2 ℝ Ω) : L2F ℝ Ω (formIdx n ((0 : ℕ) : ℤ)) :=
  WithLp.toLp 2 fun _ => f

/-- The index `∅` of `Λ⁰`. -/
def t₀ : {s : Finset (Fin n) // (#s : ℤ) = 0} := ⟨∅, by simp⟩

theorem eq_t₀ (t : {s : Finset (Fin n) // (#s : ℤ) = 0}) : t = t₀ :=
  Subtype.ext (Finset.card_eq_zero.1 (by exact_mod_cast t.2))

theorem norm_form_zero_sq (a : Form ℂ (Fin n) 0) : ‖a‖ ^ 2 = ‖a t₀‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_eq_single t₀ fun t ht => absurd (eq_t₀ t) ht]

theorem pcJ_symmDiff_empty (s : Finset (Fin n)) : pcJ (symmDiff J s) ∅ = pcJ J s := by
  funext j
  by_cases hJ : j ∈ J <;> by_cases hs : j ∈ s <;>
    simp [pcJ, DeRham.mixedSign, DeRham.reflSign, Finset.mem_symmDiff, hJ, hs]

/-- **The coefficients of the extension**: the extension of the coefficient `u_t` (a `0`-form,
class `J ∆ t`) is the `t`-component of the extension of `u` (class `J`). -/
theorem cf_JfJ_zeroF (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) (t : formIdx n (k : ℤ))
    (m : Fin n → ℤ) :
    cf (JfJ (symmDiff J t.1) 0 (zeroF (u t))) m t₀ = cf (JfJ J k u) m t := by
  rw [coeff_JfJ, coeff_JfJ]
  change ∫ y in Q (Fin n), _ * fold (pcJ (symmDiff J t.1) ∅) _ y = _
  rw [pcJ_symmDiff_empty]
  rfl

theorem norm_deRham_zero_sq (ξ : EuclideanSpace ℝ (Fin n)) (a : Form ℂ (Fin n) 0) :
    ‖(Feec.Fourier.Exterior.deRham (Fin n)).m 0 (0 + 1) ξ a‖ ^ 2 = ‖ξ‖ ^ 2 * ‖a‖ ^ 2 := by
  rw [Feec.Fourier.Exterior.norm_deRham_apply]
  have h := Feec.Fourier.Exterior.norm_koszulDeg_sq_add 0 ξ a
  have h0 : Feec.Fourier.Exterior.contr ξ (Feec.Fourier.Exterior.ext 0 a) = 0 := by
    ext s; exact Feec.Fourier.Exterior.contr_ext_eq_zero ξ 0 a (by omega)
  rw [h0, norm_zero, zero_pow two_ne_zero, add_zero] at h
  exact h

/-- **`H¹_J` for `0`-forms, forward**: `v ∈ D(d_J)` gives
`Σ_m |2πm|² |(JfJ v)(m)|² = 2ⁿ ‖d_J v‖²`. -/
theorem dPart_zero_spec {v : L2F ℝ (Q (Fin n)) (formIdx n ((0 : ℕ) : ℤ))}
    (hv : v ∈ (dPart (Q (Fin n)) J ((0 : ℕ) : ℤ)).domain) :
    Summable (fun m => ‖freq m‖ ^ 2 * ‖cf (JfJ J 0 v) m‖ ^ 2) ∧
      ∑' m, ‖freq m‖ ^ 2 * ‖cf (JfJ J 0 v) m‖ ^ 2 =
        2 ^ n * ‖dPart (Q (Fin n)) J ((0 : ℕ) : ℤ) ⟨v, hv⟩‖ ^ 2 := by
  have hc := coeff_d_dPart J 0 ⟨v, hv⟩
  have e : (fun m => ‖freq m‖ ^ 2 * ‖cf (JfJ J 0 v) m‖ ^ 2) =
      fun m => ‖cf (JfJ J (0 + 1) (dPart (Q (Fin n)) J ((0 : ℕ) : ℤ) ⟨v, hv⟩)) m‖ ^ 2 := by
    funext m
    rw [← norm_deRham_zero_sq]
    exact congrArg (fun z => ‖z‖ ^ 2) (hc m)
  rw [e]
  exact ⟨summable_norm_sq _, by rw [← norm_sq_eq_tsum, norm_JfJ_sq]⟩

/-- **`H¹_J` for `0`-forms, backward**: `Σ_m |2πm|² |(JfJ v)(m)|² < ∞` gives `v ∈ D(d_J)`. -/
theorem mem_dPart_zero_of_summable {v : L2F ℝ (Q (Fin n)) (formIdx n ((0 : ℕ) : ℤ))}
    (h : Summable fun m => ‖freq m‖ ^ 2 * ‖cf (JfJ J 0 v) m‖ ^ 2) :
    v ∈ (dPart (Q (Fin n)) J ((0 : ℕ) : ℤ)).domain := by
  set g : (Fin n → ℤ) → Form ℂ (Fin n) (0 + 1) := fun m =>
    (Feec.Fourier.Exterior.deRham (Fin n)).m 0 (0 + 1) (freq m) (cf (JfJ J 0 v) m)
  have hg : Summable fun m => ‖g m‖ ^ 2 := h.congr fun m => (norm_deRham_zero_sq _ _).symm
  set y : Seq n (0 + 1) := (memLp_of_summable hg).toLp g
  have hy : ∀ m, (Feec.Fourier.Exterior.deRham (Fin n)).m 0 (0 + 1) (freq m)
      (cf (JfJ J 0 v) m) = cf y m := fun m => by
    change g m = ((memLp_of_summable hg).toLp g : (Fin n → ℤ) → Form ℂ (Fin n) (0 + 1)) m
    rw [MemLp.coeFn_toLp_count]
  exact (mem_dPart_of_JfJ hy).1

theorem norm_cf_sq_eq_sum (x : Seq n k) (m : Fin n → ℤ) :
    ‖cf x m‖ ^ 2 = ∑ t : formIdx n (k : ℤ), ‖cf x m t‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]

theorem grad_term_eq (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) (t : formIdx n (k : ℤ))
    (m : Fin n → ℤ) :
    ‖freq m‖ ^ 2 * ‖cf (JfJ (symmDiff J t.1) 0 (zeroF (u t))) m‖ ^ 2 =
      ‖freq m‖ ^ 2 * ‖cf (JfJ J k u) m t‖ ^ 2 := by
  rw [norm_form_zero_sq, cf_JfJ_zeroF]

theorem summable_one_iff (x : Seq n k) :
    MemSob 1 x ↔ ∀ t : formIdx n (k : ℤ),
      Summable fun m => ‖freq m‖ ^ 2 * ‖cf x m t‖ ^ 2 := by
  have e : ∀ m, weight 1 m * ‖cf x m‖ ^ 2 =
      ‖cf x m‖ ^ 2 + ∑ t : formIdx n (k : ℤ), ‖freq m‖ ^ 2 * ‖cf x m t‖ ^ 2 := by
    intro m
    rw [weight_one, ← Finset.mul_sum, ← norm_cf_sq_eq_sum]; ring
  constructor
  · intro hx t
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hx
    rw [e m]
    have h1 := Finset.single_le_sum (f := fun t => ‖freq m‖ ^ 2 * ‖cf x m t‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ t)
    have h2 := sq_nonneg ‖cf x m‖
    linarith
  · intro h
    exact ((summable_norm_sq x).add (summable_sum fun t _ => h t)).congr fun m => (e m).symm

/-- **`H¹` of the parity class `J` is the space of `k`-forms whose coefficients `u_t` lie in
`H¹(Q)` with vanishing trace on the faces normal to `J ∆ t`** (i.e. whose parity extension has
`H¹` coefficients): `u ∈ H¹_J(Q; Λᵏ)` iff every `u_t ∈ D(d_{J ∆ t})` in degree `0`. -/
theorem mem_sobolevPar_one_iff {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))} :
    u ∈ sobolevPar J k 1 ↔ ∀ t : formIdx n (k : ℤ),
      zeroF (u t) ∈ (dPart (Q (Fin n)) (symmDiff J t.1) ((0 : ℕ) : ℤ)).domain := by
  rw [mem_sobolevPar, summable_one_iff]
  refine forall_congr' fun t => ⟨fun h => ?_, fun h => ?_⟩
  · refine mem_dPart_zero_of_summable _ ?_
    exact h.congr fun m => (grad_term_eq J k u t m).symm
  · exact (dPart_zero_spec _ h).1.congr fun m => grad_term_eq J k u t m

/-- **The `H¹_J` norm is the graph norm of the coefficients**:
`‖u‖²_{1,J} = ‖u‖² + Σ_t ‖∇_{J ∆ t} u_t‖²`. -/
theorem parNorm_one_sq {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))} (hu : u ∈ sobolevPar J k 1) :
    parNorm J k 1 u ^ 2 = ‖u‖ ^ 2 + ∑ t : formIdx n (k : ℤ),
      ‖dPart (Q (Fin n)) (symmDiff J t.1) ((0 : ℕ) : ℤ)
        ⟨zeroF (u t), (mem_sobolevPar_one_iff J k).1 hu t⟩‖ ^ 2 := by
  set x := JfJ J k u
  have hs := (summable_one_iff k x).1 hu
  have e : ∀ m, weight 1 m * ‖cf x m‖ ^ 2 =
      ‖cf x m‖ ^ 2 + ∑ t : formIdx n (k : ℤ), ‖freq m‖ ^ 2 * ‖cf x m t‖ ^ 2 := by
    intro m
    rw [weight_one, ← Finset.mul_sum, ← norm_cf_sq_eq_sum]; ring
  have hsum : sobSum 1 x = ‖x‖ ^ 2 + ∑ t : formIdx n (k : ℤ),
      ∑' m, ‖freq m‖ ^ 2 * ‖cf x m t‖ ^ 2 := by
    unfold sobSum
    simp_rw [e]
    rw [Summable.tsum_add (summable_norm_sq x) (summable_sum fun t _ => hs t),
      Summable.tsum_finsetSum fun t _ => hs t, ← norm_sq_eq_tsum]
  have ht : ∀ t : formIdx n (k : ℤ), ∑' m, ‖freq m‖ ^ 2 * ‖cf x m t‖ ^ 2 =
      2 ^ n * ‖dPart (Q (Fin n)) (symmDiff J t.1) ((0 : ℕ) : ℤ)
        ⟨zeroF (u t), (mem_sobolevPar_one_iff J k).1 hu t⟩‖ ^ 2 := by
    intro t
    rw [← (dPart_zero_spec _ ((mem_sobolevPar_one_iff J k).1 hu t)).2]
    exact tsum_congr fun m => (grad_term_eq J k u t m).symm
  rw [parNorm_sq, hsum, norm_JfJ_sq, Finset.sum_congr rfl fun t _ => ht t, ← Finset.mul_sum,
    ← mul_add, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

end ParityH1

/-! ### Orthogonality of the parity classes and the extension by zero -/

section ZeroExt

variable {k : ℕ}

theorem inner_eq_tsum (x y : Seq n k) : ⟪x, y⟫_ℂ = ∑' m, ⟪cf x m, cf y m⟫_ℂ := by
  set e := lp.equivLpCount ℂ (Fin n → ℤ) (Form ℂ (Fin n) k) 2
  rw [← e.symm.inner_map_map x y, lp.inner_eq_tsum]
  rfl

/-- **Different parity classes are orthogonal**: if `J ≠ J'`, `⟪JfJ J u, JfJ J' v⟫ = 0` (pair the
frequencies `m` and `flip_j m` for `j ∈ J ∆ J'`). -/
theorem inner_JfJ_eq_zero {J J' : Finset (Fin n)} (h : J ≠ J')
    (u v : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) : ⟪JfJ J k u, JfJ J' k v⟫_ℂ = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, ¬ (j ∈ J ↔ j ∈ J') := by
    by_contra hc; push Not at hc; exact h (Finset.ext hc)
  set x := JfJ J k u
  set y := JfJ J' k v
  have hx := (JfJ_realParJ J k u).2 j
  have hy := (JfJ_realParJ J' k v).2 j
  set F : (Fin n → ℤ) → ℂ := fun m => ⟪cf x m, cf y m⟫_ℂ
  have hF : ∀ m, F (Fourier.Torus.flipAt j m) = -F m := by
    intro m
    simp only [F, PiLp.inner_apply, RCLike.inner_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    change cf y (Fourier.Torus.flipAt j m) t * conj (cf x (Fourier.Torus.flipAt j m) t) =
      -(cf y m t * conj (cf x m t))
    rw [hx m t, hy m t]
    have hs : conj (DeRham.mixedSign J j * DeRham.reflSign j t.1) *
        (DeRham.mixedSign J' j * DeRham.reflSign j t.1) = -1 := by
      by_cases h1 : j ∈ J <;> by_cases h2 : j ∈ J' <;> by_cases h3 : j ∈ t.1 <;>
        simp_all [DeRham.mixedSign, DeRham.reflSign]
    rw [map_mul]
    linear_combination (cf y m t * conj (cf x m t)) * hs
  have e : (Fourier.Torus.flipAt_involutive j).toPerm _ = _ := rfl
  have hsum : ∑' m, F m = -∑' m, F m := by
    rw [← tsum_neg, ← (Function.Involutive.toPerm _ (Fourier.Torus.flipAt_involutive j)).tsum_eq]
    exact tsum_congr fun m => hF m
  rw [inner_eq_tsum]
  change ∑' m, F m = 0
  linear_combination hsum / 2

/-- **The extension by zero**, `2⁻ⁿ Σ_J JfJ J u`: the average of the parity extensions over all
`2ⁿ` classes vanishes off the box `(0, ½)ⁿ ⊂ 𝕋ⁿ`, restricts to `u` and has the norm of `u`. -/
def zeroExt (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) : Seq n k :=
  ((2 : ℝ) ^ n)⁻¹ • ∑ J : Finset (Fin n), JfJ J k u

theorem Jinvf_zeroExt (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) : Jinvf k (zeroExt u) = u := by
  rw [zeroExt, map_smul, map_sum]
  simp only [Jinvf_JfJ, Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_pow, Nat.cast_ofNat,
    inv_mul_cancel₀ (by positivity), one_smul]

theorem norm_zeroExt (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) : ‖zeroExt u‖ = ‖u‖ := by
  have hsq : ‖∑ J : Finset (Fin n), JfJ J k u‖ ^ 2 = (2 ^ n) ^ 2 * ‖u‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, sum_inner]
    simp_rw [inner_sum]
    have hd : ∀ J : Finset (Fin n), ∑ J' : Finset (Fin n), ⟪JfJ J k u, JfJ J' k u⟫_ℂ =
        ⟪JfJ J k u, JfJ J k u⟫_ℂ := fun J =>
      Finset.sum_eq_single J (fun J' _ hJ' => inner_JfJ_eq_zero (Ne.symm hJ') u u)
        (fun h => absurd (Finset.mem_univ J) h)
    simp_rw [hd, map_sum, ← @norm_sq_eq_re_inner ℂ, norm_JfJ_sq, Finset.sum_const,
      Finset.card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hn : ‖∑ J : Finset (Fin n), JfJ J k u‖ = 2 ^ n * ‖u‖ := by
    rw [← mul_pow] at hsq
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 hsq
  rw [zeroExt, norm_smul, hn, norm_inv, norm_pow, Real.norm_two, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

end ZeroExt

/-! ### The Sobolev spaces `Hˢ(Q; Λᵏ)` without boundary condition -/

section NoBC

variable (k : ℕ)

variable (n) in
/-- **The Sobolev space `Hˢ(Q; Λᵏ)`** of `Q = (0, ½)ⁿ`: the restrictions to `Q` (real parts) of
the `k`-forms of `Hˢ(𝕋ⁿ)` on the period-`1` torus, `{x|_Q : Σ_m (1 + |2πm|²)^s |x(m)|² < ∞}`
(the restriction definition of fractional Sobolev spaces, with periodic extensions in place of
extensions to `ℝⁿ`; for `s = 1` the space `H¹(Q)` of [Brezis2011], §9.1, `mem_sobolevQ_one_iff`). -/
def sobolevQ (s : ℝ) : Submodule ℝ (L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) where
  carrier := {u | ∃ x : Seq n k, MemSob s x ∧ Jinvf k x = u}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, hx.add hy, map_add _ _ _⟩
  zero_mem' := ⟨0, memSob_zero_seq s, map_zero _⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    exact ⟨c • x, hx.real_smul c, map_smul _ _ _⟩

/-- **The quotient norm** of `Hˢ(Q; Λᵏ)`: `‖u‖_{Hˢ(Q)} = inf {‖x‖_{Hˢ(𝕋ⁿ)} : x|_Q = u}`. -/
def qNorm (s : ℝ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) : ℝ :=
  sInf ((fun x => √(sobSum s x)) '' {x : Seq n k | MemSob s x ∧ Jinvf k x = u})

variable {k}

theorem qNorm_nonneg (s : ℝ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) : 0 ≤ qNorm k s u :=
  Real.sInf_nonneg (by rintro _ ⟨x, -, rfl⟩; exact Real.sqrt_nonneg _)

/-- Every extension bounds the quotient norm. -/
theorem qNorm_le {s : ℝ} {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))} {x : Seq n k}
    (hx : MemSob s x) (hxu : Jinvf k x = u) : qNorm k s u ≤ √(sobSum s x) :=
  csInf_le ⟨0, by rintro _ ⟨y, -, rfl⟩; exact Real.sqrt_nonneg _⟩ ⟨x, ⟨hx, hxu⟩, rfl⟩

/-- A lower bound for all extensions is a lower bound for the quotient norm. -/
theorem le_qNorm {s : ℝ} {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))} (hu : u ∈ sobolevQ n k s)
    {c : ℝ} (h : ∀ x : Seq n k, MemSob s x → Jinvf k x = u → c ≤ √(sobSum s x)) :
    c ≤ qNorm k s u := by
  obtain ⟨x, hx, hxu⟩ := hu
  exact le_csInf ⟨_, x, ⟨hx, hxu⟩, rfl⟩ (by rintro _ ⟨y, ⟨hy, hyu⟩, rfl⟩; exact h y hy hyu)

/-- **Passing an estimate valid for every extension to the quotient norm**: if
`a ≤ b ‖x‖_{Hˢ(𝕋ⁿ)}` for every extension `x` of `u` (`b ≥ 0`), then `a ≤ b ‖u‖_{Hˢ(Q)}`. -/
theorem le_mul_qNorm {s : ℝ} {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))} (hu : u ∈ sobolevQ n k s)
    {a b : ℝ} (hb : 0 ≤ b) (h : ∀ x : Seq n k, MemSob s x → Jinvf k x = u → a ≤ b * √(sobSum s x)) :
    a ≤ b * qNorm k s u := by
  rcases hb.eq_or_lt with rfl | hb
  · obtain ⟨x, hx, hxu⟩ := hu
    simpa using h x hx hxu
  · rw [← div_le_iff₀' hb]
    exact le_qNorm hu fun x hx hxu => (div_le_iff₀' hb).2 (h x hx hxu)

/-- **`H⁰(Q) = L²(Q)`**: every `L²` form is the restriction of an `L²(𝕋ⁿ)` form. -/
theorem sobolevQ_zero : sobolevQ n k 0 = ⊤ :=
  eq_top_iff.2 fun u _ => ⟨zeroExt u, memSob_zero _, Jinvf_zeroExt u⟩

/-- **`H⁰(Q) = L²(Q)` isometrically**: the quotient norm of `L²(𝕋ⁿ)` is the norm of `L²(Q)`
(restriction is a contraction, `norm_Jinvf_le`, and the extension by zero is isometric,
`norm_zeroExt`). -/
theorem qNorm_zero (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) : qNorm k 0 u = ‖u‖ := by
  refine le_antisymm ?_ ?_
  · refine (qNorm_le (memSob_zero (zeroExt u)) (Jinvf_zeroExt u)).trans (le_of_eq ?_)
    rw [sobSum_zero, Real.sqrt_sq (norm_nonneg _), norm_zeroExt]
  · refine le_qNorm (by rw [sobolevQ_zero]; exact Submodule.mem_top) fun x _ hxu => ?_
    rw [sobSum_zero, Real.sqrt_sq (norm_nonneg _), ← hxu]
    exact norm_Jinvf_le k x

/-- **The parity classes lie in `Hˢ(Q)`**: `Hˢ_J(Q) ⊆ Hˢ(Q)` with
`‖u‖_{Hˢ(Q)} ≤ 2^{n/2} ‖u‖_{s,J}`. -/
theorem sobolevPar_le_sobolevQ (J : Finset (Fin n)) (s : ℝ) :
    sobolevPar J k s ≤ sobolevQ n k s := fun u hu => ⟨JfJ J k u, hu, Jinvf_JfJ J k u⟩

/-- **The truncation error in `Hˢ(Q)`**: for every extension `x` of `u`,
`‖u - (x_M)|_Q‖ ≤ (2π(M + 1))^{-s} ‖x‖_{Hˢ(𝕋ⁿ)}` (`s ≥ 0`). -/
theorem norm_sub_Jinvf_trunc_le {s : ℝ} (hs : 0 ≤ s) {x : Seq n k} (hx : MemSob s x) (M : ℕ) :
    ‖Jinvf k x - Jinvf k (trunc M k x)‖ ≤ (2 * Real.pi * (M + 1)) ^ (-s) * √(sobSum s x) := by
  rw [← map_sub]
  refine (norm_Jinvf_le k _).trans ?_
  have h := norm_sub_trunc_sq_le hs hx M
  have ha : 0 < 2 * Real.pi * (M + 1) := by positivity
  have h2 := h.trans (mul_le_mul_of_nonneg_right (rpow_neg_le_sq ha hs) (sobSum_nonneg s x))
  rw [← Real.sq_sqrt (sobSum_nonneg s x), ← mul_pow] at h2
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).1 h2

end NoBC

/-! ### Gradients of the restrictions of trigonometric polynomials -/

section Gradient

open UnitAddTorus Feec.Fourier.TorusWeak

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Fourier.TorusWeak`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The local Haar measure on `ℝ/ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {k : ℕ}

/-- **Parseval**: `‖f‖²_{L²(𝕋ⁿ)} = Σ_m |f̂(m)|²`. -/
theorem norm_sq_eq_tsum_mFourierCoeff (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin n)))) :
    ‖f‖ ^ 2 = ∑' m, ‖mFourierCoeff f m‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (mFourierBasis.repr f)
  rw [LinearIsometryEquiv.norm_map] at h
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, mFourierBasis_repr] at h
  exact h

/-- The restriction to `Q` of the real part of a continuous function on `𝕋ⁿ` has `L²(Q)` norm at
most its `L²(𝕋ⁿ)` norm. -/
theorem norm_toLp_re_le (g : C(UnitAddTorus (Fin n), ℂ))
    (hF : MemLp (fun y => (g (proj y)).re) 2 (volume.restrict (Q (Fin n)))) :
    ‖hF.toLp (fun y => (g (proj y)).re)‖ ≤
      ‖g.toLp 2 (volume : Measure (UnitAddTorus (Fin n))) ℂ‖ := by
  have e : hF.toLp (fun y => (g (proj y)).re) =
      RowWise.reL _ (resQ (g.toLp 2 (volume : Measure (UnitAddTorus (Fin n))) ℂ)) := by
    refine Lp.ext ?_
    filter_upwards [hF.coeFn_toLp, RowWise.coeFn_reL (resQ (g.toLp 2 volume ℂ)),
      coeFn_resQ (g.toLp 2 (volume : Measure (UnitAddTorus (Fin n))) ℂ),
      ae_Q_of_ae_boxSet (ae_restrict_of_ae (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
        (μ := (volume : Measure (UnitAddTorus (Fin n)))) g))] with y h1 h2 h3 h4
    rw [h1, h2, h3, h4]
  rw [e]
  exact (norm_reL_le _ _).trans (norm_resQ_le _)

/-- The equivalence `Fin n ≃ {1-forms indices}`, `j ↦ {j}`. -/
def single1 : Fin n ≃ formIdx n (((0 : ℕ) : ℤ) + 1) :=
  Equiv.ofBijective (fun j => ⟨{j}, by simp⟩) ⟨fun i j h => by
    simpa using congrArg Subtype.val h, fun s => by
    obtain ⟨j, hj⟩ := Finset.card_eq_one.1 (by exact_mod_cast s.2)
    exact ⟨j, Subtype.ext hj.symm⟩⟩

/-- **The derivative of a real trigonometric polynomial**: for `x` supported in `S`,
`‖∂_j Re P_t‖²_{L²(Q)} ≤ Σ_m (2π m_j)² |x(m)_t|²`. -/
theorem norm_sq_fderiv_trigLift_le (x : Seq n k) {S : Finset (Fin n → ℤ)}
    (hS : ∀ m ∉ S, cf x m = 0) (t : formIdx n (k : ℤ)) (j : Fin n)
    (hF : MemLp (fun y => fderiv ℝ (trigLift k x S t) y (Pi.single j 1)) 2
      (volume.restrict (Q (Fin n)))) :
    ‖hF.toLp (fun y => fderiv ℝ (trigLift k x S t) y (Pi.single j 1))‖ ^ 2 ≤
      ∑' m, (2 * Real.pi * m j) ^ 2 * ‖cf x m t‖ ^ 2 := by
  set P := trigPoly (mFourierBasis.repr (physF k x t)) S
  have hPs := isSmooth_trigPoly (mFourierBasis.repr (physF k x t)) S
  set g : C(UnitAddTorus (Fin n), ℂ) := ⟨partialT j P, continuous_partialT hPs.contDiff_one j⟩
  have hfun : (fun y => fderiv ℝ (trigLift k x S t) y (Pi.single j 1)) =
      fun y => (g (proj y)).re := funext fun y => fderiv_trigLift k x S t j y
  have hF' : MemLp (fun y => (g (proj y)).re) 2 (volume.restrict (Q (Fin n))) := hfun ▸ hF
  have e1 : hF.toLp (fun y => fderiv ℝ (trigLift k x S t) y (Pi.single j 1)) =
      hF'.toLp (fun y => (g (proj y)).re) := by
    congr 1
  rw [e1]
  have h1 := norm_toLp_re_le g hF'
  have hS' : ∀ m ∉ S, mFourierBasis.repr (physF k x t) m = 0 := fun m hm => by
    have h0 := hS m hm
    simp only [cf] at h0
    rw [repr_physF, h0]; rfl
  have hP : physF k x t = P.toLp 2 volume ℂ := by
    rw [← ofCoeff_eq_toLp S hS', ofCoeff, LinearIsometryEquiv.symm_apply_apply]
  have hcoef : ∀ m, mFourierCoeff (g.toLp 2 (volume : Measure (UnitAddTorus (Fin n))) ℂ) m =
      2 * Real.pi * Complex.I * m j * cf x m t := by
    intro m
    rw [mFourierCoeff_toLp]
    change mFourierCoeff (partialT j P) m = _
    rw [mFourierCoeff_partialT hPs.contDiff_one, ← mFourierCoeff_toLp, ← hP,
      ← mFourierBasis_repr, repr_physF]
  have h2 : ‖g.toLp 2 (volume : Measure (UnitAddTorus (Fin n))) ℂ‖ ^ 2 =
      ∑' m, (2 * Real.pi * m j) ^ 2 * ‖cf x m t‖ ^ 2 := by
    rw [norm_sq_eq_tsum_mFourierCoeff]
    refine tsum_congr fun m => ?_
    rw [hcoef, norm_mul, mul_pow]
    congr 1
    rw [show (2 * Real.pi * Complex.I * m j : ℂ) = ((2 * Real.pi * m j : ℝ) : ℂ) * Complex.I by
      push_cast; ring, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
  rw [← h2]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- **Restrictions of trigonometric polynomials are in `H¹(Q)`, with the torus bound**: for `x`
supported in a finite set, every coefficient `(x|_Q)_t` lies in `D(grad_max)` and
`‖∇ (x|_Q)_t‖² ≤ Σ_m |2πm|² |x(m)_t|²`. -/
theorem grad_Jinvf_of_finite (x : Seq n k) {S : Finset (Fin n → ℤ)}
    (hS : ∀ m ∉ S, cf x m = 0) (t : formIdx n (k : ℤ)) :
    ∃ h : zeroF (Jinvf k x t) ∈ ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))).domain,
      ‖(extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n)) ⟨_, h⟩‖ ^ 2 ≤
        ∑' m, ‖freq m‖ ^ 2 * ‖cf x m t‖ ^ 2 := by
  set ψ : formIdx n ((0 : ℕ) : ℤ) → (Fin n → ℝ) → ℝ := fun _ => trigLift k x S t
  have hψs : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (ψ s) := fun _ => contDiff_trigLift k x S t
  have hw : ∀ s, MemLp (ψ s) 2 (volume.restrict (Q (Fin n))) := fun _ => memLp_trigLift k x S t
  have hdw : ∀ t', MemLp ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).apply ψ t') 2
      (volume.restrict (Q (Fin n))) := fun t' =>
    Feec.Domain.memLp_of_continuous measurableSet_Q isBounded_Qn
      ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).continuous_apply (Feec.Domain.extDerivOp_isOrderLE _)
        (fun s => (hψs s).of_le (by exact_mod_cast le_top)) t')
  obtain ⟨hmem, hd⟩ := Feec.Domain.extDerivOp_smooth_mem_maximal_domain isOpen_Q
    (fun s => (hψs s).of_le (by exact_mod_cast le_top)) hw hdw
  have hJ : Jinvf k x = toL2F (memLp_trigLift k x S) := Jinvf_eq_toL2F hS
  have hz : zeroF (Jinvf k x t) = toL2F hw := by rw [hJ]; rfl
  refine ⟨hz ▸ hmem, ?_⟩
  have hval : (extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n)) ⟨_, hz ▸ hmem⟩ = toL2F hdw := by
    rw [← hd]; congr 2
  rw [hval, PiLp.norm_sq_eq_of_L2, ← (single1 (n := n)).sum_comp]
  have hcomp : ∀ j : Fin n, ‖(toL2F hdw) (single1 j)‖ ^ 2 ≤
      ∑' m, (2 * Real.pi * m j) ^ 2 * ‖cf x m t‖ ^ 2 := by
    intro j
    have hfj : (extDerivOp ℝ n ((0 : ℕ) : ℤ)).apply ψ (single1 j) =
        fun y => fderiv ℝ (trigLift k x S t) y (Pi.single j 1) := by
      funext y
      exact Feec.Domain.extDerivOp_zero_apply (𝕜 := ℝ) ψ j y
    have hF : MemLp (fun y => fderiv ℝ (trigLift k x S t) y (Pi.single j 1)) 2
        (volume.restrict (Q (Fin n))) := hfj ▸ hdw (single1 j)
    have e : (toL2F hdw) (single1 j) = hF.toLp _ := by
      change (hdw (single1 j)).toLp _ = _
      congr 1
    rw [e]
    exact norm_sq_fderiv_trigLift_le x hS t j hF
  have hsum : ∀ j : Fin n, Summable fun m => (2 * Real.pi * m j) ^ 2 * ‖cf x m t‖ ^ 2 :=
    fun j => summable_of_ne_finset_zero (s := S) fun m hm => by simp [hS m hm]
  refine (Finset.sum_le_sum fun j _ => hcomp j).trans (le_of_eq ?_)
  rw [← Summable.tsum_finsetSum fun j _ => hsum j]
  refine tsum_congr fun m => ?_
  rw [← Finset.sum_mul, norm_freq_sq, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Gradient

/-! ### `H¹(Q)` and the gradient of the truncations -/

section H1Q

variable {k : ℕ}

/-- `Σ_t Σ_m |2πm|² |x(m)_t|² ≤ Σ_m ⟨ξ⟩² |x(m)|²` for finitely supported `x`. -/
theorem sum_tsum_freq_le (x : Seq n k) {S : Finset (Fin n → ℤ)} (hS : ∀ m ∉ S, cf x m = 0) :
    ∑ t : formIdx n (k : ℤ), ∑' m, ‖freq m‖ ^ 2 * ‖cf x m t‖ ^ 2 ≤ sobSum 1 x := by
  have hsum : ∀ t : formIdx n (k : ℤ),
      Summable fun m => ‖freq m‖ ^ 2 * ‖cf x m t‖ ^ 2 := fun t =>
    summable_of_ne_finset_zero (s := S) fun m hm => by
      have h0 := hS m hm
      simp only [cf] at h0
      simp [cf, h0]
  rw [← Summable.tsum_finsetSum fun t _ => hsum t]
  refine Summable.tsum_le_tsum (fun m => ?_) (summable_sum fun t _ => hsum t)
    (memSob_of_finite S hS)
  rw [← Finset.mul_sum, ← norm_cf_sq_eq_sum, weight_one]
  exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

/-- **The gradients of the coefficients of a restricted trigonometric polynomial**: for `x`
supported in a finite set, every `(x|_Q)_t ∈ H¹(Q)` and `Σ_t ‖∇ (x|_Q)_t‖² ≤ ‖x‖²_{H¹(𝕋ⁿ)}`. -/
theorem grad_Jinvf_sum_le (x : Seq n k) {S : Finset (Fin n → ℤ)} (hS : ∀ m ∉ S, cf x m = 0) :
    ∃ h : ∀ t : formIdx n (k : ℤ),
        zeroF (Jinvf k x t) ∈ ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))).domain,
      ∑ t, ‖(extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n)) ⟨_, h t⟩‖ ^ 2 ≤ sobSum 1 x := by
  refine ⟨fun t => (grad_Jinvf_of_finite x hS t).1, ?_⟩
  refine (Finset.sum_le_sum fun t _ => (grad_Jinvf_of_finite x hS t).2).trans ?_
  exact sum_tsum_freq_le x hS

/-- **The gradient of the truncation, for `Hˢ(Q)` data** (`0 ≤ s ≤ 1`): for an extension `x` of
`u` with `‖x‖_{Hˢ(𝕋ⁿ)} < ∞`, the coefficients of `u_M = (x_M)|_Q` lie in `H¹(Q)` and
`Σ_t ‖∇ (u_M)_t‖² ≤ (1 + n (2πM)²)^{1-s} ‖x‖²_{Hˢ(𝕋ⁿ)}`. -/
theorem grad_truncQ_le {s : ℝ} (hs1 : s ≤ 1) {x : Seq n k} (hx : MemSob s x) (M : ℕ) :
    ∃ h : ∀ t : formIdx n (k : ℤ), zeroF (Jinvf k (trunc M k x) t) ∈
        ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))).domain,
      ∑ t, ‖(extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n)) ⟨_, h t⟩‖ ^ 2 ≤
        (1 + n * (2 * Real.pi * M) ^ 2) ^ (1 - s) * sobSum s x := by
  obtain ⟨h, hle⟩ := grad_Jinvf_sum_le (trunc M k x) (S := bandS M)
    fun _ hm => trunc_eq_zero_of_notMem x hm
  exact ⟨h, hle.trans (sobSum_trunc_le hs1 hx M)⟩

/-- **The truncations converge in `Hᵗ`**: `‖x - x_N‖_{Hᵗ(𝕋ⁿ)} → 0`. -/
theorem tendsto_sobSum_sub_trunc {t : ℝ} {x : Seq n k} (hx : MemSob t x) :
    Tendsto (fun N => sobSum t (x - trunc N k x)) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun N m => weight t m * ‖cf (x - trunc N k x) m‖ ^ 2) (g := fun _ => (0 : ℝ))
    (bound := fun m => weight t m * ‖cf x m‖ ^ 2) hx (fun m => ?_) (Eventually.of_forall
      fun N m => ?_)
  · simpa [sobSum] using h
  · obtain ⟨N₀, hN₀⟩ := Feec.Fourier.Torus.exists_mem_bandN m
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N₀] with N hN
    rw [cf_sub_trunc_of_mem x (Feec.Fourier.Torus.bandN_mono hN hN₀)]; simp
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weight_nonneg t m) (sq_nonneg _))]
    by_cases hm : m ∈ bandN N
    · rw [cf_sub_trunc_of_mem x hm, norm_zero, zero_pow two_ne_zero, mul_zero]
      exact mul_nonneg (weight_nonneg t m) (sq_nonneg _)
    · rw [cf_sub_trunc_of_notMem x hm]

theorem sobSum_sub_trunc_anti {t : ℝ} {x : Seq n k} (hx : MemSob t x) {a b : ℕ} (hab : a ≤ b) :
    sobSum t (x - trunc b k x) ≤ sobSum t (x - trunc a k x) := by
  have hle : ∀ m, weight t m * ‖cf (x - trunc b k x) m‖ ^ 2 ≤
      weight t m * ‖cf (x - trunc a k x) m‖ ^ 2 := by
    intro m
    by_cases hm : m ∈ bandN b
    · rw [cf_sub_trunc_of_mem x hm, norm_zero, zero_pow two_ne_zero, mul_zero]
      exact mul_nonneg (weight_nonneg t m) (sq_nonneg _)
    · have ha : m ∉ bandN a := fun h => hm (Feec.Fourier.Torus.bandN_mono hab h)
      rw [cf_sub_trunc_of_notMem x hm, cf_sub_trunc_of_notMem x ha]
  have h1 := (sobSum_sub_trunc_le le_rfl hx b).1
  have h2 := (sobSum_sub_trunc_le le_rfl hx a).1
  exact Summable.tsum_le_tsum hle h1 h2

theorem sobSum_sub_le (s : ℝ) {x y : Seq n k} (hx : MemSob s x) (hy : MemSob s y) :
    sobSum s (x - y) ≤ 2 * sobSum s x + 2 * sobSum s y := by
  have hle : ∀ m, weight s m * ‖cf (x - y) m‖ ^ 2 ≤
      2 * (weight s m * ‖cf x m‖ ^ 2) + 2 * (weight s m * ‖cf y m‖ ^ 2) := by
    intro m
    rw [cf_sub, sub_eq_add_neg]
    have := norm_add_sq_le (cf x m) (-cf y m)
    rw [norm_neg] at this
    have := weight_nonneg s m
    nlinarith
  calc sobSum s (x - y) ≤ ∑' m, (2 * (weight s m * ‖cf x m‖ ^ 2) +
        2 * (weight s m * ‖cf y m‖ ^ 2)) :=
        Summable.tsum_le_tsum hle (hx.sub hy) ((hx.mul_left 2).add (hy.mul_left 2))
    _ = 2 * sobSum s x + 2 * sobSum s y := by
        rw [Summable.tsum_add (hx.mul_left 2) (hy.mul_left 2), tsum_mul_left, tsum_mul_left]; rfl

theorem zeroF_sub {Ω : Set (Fin n → ℝ)} (f g : L2 ℝ Ω) : zeroF (f - g) = zeroF f - zeroF g := rfl

theorem continuous_zeroF {Ω : Set (Fin n → ℝ)} : Continuous (zeroF (n := n) (Ω := Ω)) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_id)

/-- **The gradients of the truncations converge**: for `‖x‖_{H¹(𝕋ⁿ)} < ∞`, every coefficient of
`x|_Q` lies in `D(grad_max) = H¹(Q)` and `∇ (x_N|_Q)_t → ∇ (x|_Q)_t` in `L²(Q)` (the
truncations are Cauchy in the graph norm, and `grad_max` is closed). -/
theorem exists_tendsto_grad_trunc {x : Seq n k} (hx : MemSob 1 x) (t : formIdx n (k : ℤ)) :
    ∃ h : zeroF (Jinvf k x t) ∈ ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))).domain,
      Tendsto (fun N => (extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))
        ⟨_, (grad_Jinvf_of_finite (trunc N k x)
          (fun _ hm => trunc_eq_zero_of_notMem x hm) t).1⟩) atTop
        (𝓝 ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n)) ⟨_, h⟩)) := by
  set D := (extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))
  have hfin : ∀ N, ∀ m ∉ bandS (n := n) N, cf (trunc N k x) m = 0 := fun N _ hm =>
    trunc_eq_zero_of_notMem x hm
  have hmem : ∀ N, zeroF (Jinvf k (trunc N k x) t) ∈ D.domain := fun N =>
    (grad_Jinvf_of_finite (trunc N k x) (hfin N) t).1
  set v : ℕ → D.domain := fun N => ⟨_, hmem N⟩
  -- the differences
  have hdiff : ∀ a b, dist (D (v a)) (D (v b)) ≤
      √(2 * sobSum 1 (x - trunc a k x) + 2 * sobSum 1 (x - trunc b k x)) := by
    intro a b
    set y := trunc a k x - trunc b k x
    have hy : ∀ m ∉ bandS (n := n) (max a b), cf y m = 0 := by
      intro m hm
      have hm' : m ∉ bandN (d := Fin n) (max a b) := fun h => hm ((Set.Finite.mem_toFinset _).2 h)
      rw [cf_sub, cf_trunc_of_notMem x (fun h => hm' (Feec.Fourier.Torus.bandN_mono
          (le_max_left a b) h)),
        cf_trunc_of_notMem x (fun h => hm' (Feec.Fourier.Torus.bandN_mono (le_max_right a b) h)),
        sub_zero]
    obtain ⟨hy1, hy2⟩ := grad_Jinvf_of_finite y hy t
    have e : D (v a) - D (v b) = D ⟨_, hy1⟩ := by
      rw [← LinearPMap.map_sub]
      congr 1
      refine Subtype.ext ?_
      change zeroF _ - zeroF _ = zeroF _
      rw [← zeroF_sub, ← PiLp.sub_apply, ← map_sub]
    rw [dist_eq_norm, e]
    have hb : y = (x - trunc b k x) - (x - trunc a k x) := by simp only [y]; abel
    have h3 : ∑' m, ‖freq m‖ ^ 2 * ‖cf y m t‖ ^ 2 ≤ sobSum 1 y := by
      refine le_trans ?_ (sum_tsum_freq_le y hy)
      exact Finset.single_le_sum (f := fun t => ∑' m, ‖freq m‖ ^ 2 * ‖cf y m t‖ ^ 2)
        (fun _ _ => tsum_nonneg fun m => by positivity) (Finset.mem_univ t)
    have h4 : sobSum 1 y ≤ 2 * sobSum 1 (x - trunc b k x) + 2 * sobSum 1 (x - trunc a k x) := by
      rw [hb]
      exact sobSum_sub_le 1 (sobSum_sub_trunc_le le_rfl hx b).1 (sobSum_sub_trunc_le le_rfl hx a).1
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hcauchy : CauchySeq fun N => D (v N) := by
    refine cauchySeq_of_le_tendsto_0 (fun N => √(4 * sobSum 1 (x - trunc N k x)))
      (fun a b N ha hb => (hdiff a b).trans (Real.sqrt_le_sqrt ?_)) ?_
    · have := sobSum_sub_trunc_anti hx ha
      have := sobSum_sub_trunc_anti hx hb
      linarith
    · have h := ((tendsto_sobSum_sub_trunc hx).const_mul 4).sqrt
      simpa using h
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim : Tendsto (fun N => (((v N : D.domain) : L2F ℝ (Q (Fin n)) (formIdx n ((0 : ℕ) : ℤ))),
      D (v N))) atTop (𝓝 (zeroF (Jinvf k x t), G)) := by
    refine Tendsto.prodMk_nhds ?_ hG
    have hc : Continuous fun z : Seq n k => zeroF (Jinvf k z t) :=
      continuous_zeroF.comp ((PiLp.continuous_apply 2 _ t).comp (Jinvf k).continuous)
    exact (hc.tendsto x).comp (tendsto_trunc k x)
  have hg := ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).isClosed_maximal isOpen_Q).mem_of_tendsto hlim
    (Eventually.of_forall fun N => LinearPMap.mem_graph D (v N))
  obtain ⟨w, hw, hGw⟩ := (LinearPMap.mem_graph_iff _).1 hg
  have hw' : (w : L2F ℝ (Q (Fin n)) (formIdx n ((0 : ℕ) : ℤ))) = zeroF (Jinvf k x t) := hw
  have hGw' : D w = G := hGw
  refine ⟨hw' ▸ w.2, ?_⟩
  have e : (⟨_, hw' ▸ w.2⟩ : D.domain) = w := Subtype.ext hw'.symm
  rw [e, hGw']
  exact hG

/-- **`H¹(Q)` restrictions have `H¹(Q)` coefficients**: if `u = x|_Q` with
`‖x‖_{H¹(𝕋ⁿ)} < ∞`, then every coefficient `u_t` lies in `D(grad_max) = H¹(Q)`. -/
theorem coeff_mem_maximal_of_mem_sobolevQ_one {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    (hu : u ∈ sobolevQ n k 1) (t : formIdx n (k : ℤ)) :
    zeroF (u t) ∈ ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))).domain := by
  obtain ⟨x, hx, rfl⟩ := hu
  exact (exists_tendsto_grad_trunc hx t).1

/-- The `k`-form with the single coefficient `u_t` (the other coefficients vanish). -/
def singleCoeff (t : formIdx n (k : ℤ)) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)) :=
  WithLp.toLp 2 (Pi.single t (u t))

theorem sum_singleCoeff (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    ∑ t, singleCoeff t u = u := by
  refine PiLp.ext fun t' => ?_
  rw [WithLp.ofLp_sum]
  simp [singleCoeff, Pi.single_apply]

/-- **`H¹(Q)` is the space of forms with `H¹(Q)` coefficients** (the weak-derivative space):
`u ∈ H¹(Q; Λᵏ)` iff every coefficient `u_t` lies in `D(grad_max)`. The forward direction is
`coeff_mem_maximal_of_mem_sobolevQ_one`; conversely each `u_t dx_t` is the restriction of its
even reflection, the parity extension of the class `J = t` (`mem_sobolevPar_one_iff`). -/
theorem mem_sobolevQ_one_iff {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))} :
    u ∈ sobolevQ n k 1 ↔ ∀ t : formIdx n (k : ℤ),
      zeroF (u t) ∈ ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))).domain := by
  refine ⟨fun hu t => coeff_mem_maximal_of_mem_sobolevQ_one hu t, fun h => ?_⟩
  have hpar : ∀ t : formIdx n (k : ℤ), singleCoeff t u ∈ sobolevPar t.1 k 1 := by
    intro t
    refine (mem_sobolevPar_one_iff t.1 k).2 fun t' => ?_
    by_cases ht : t' = t
    · subst ht
      rw [symmDiff_self, Finset.bot_eq_empty, dPart_empty isOpen_Q]
      simpa [singleCoeff] using h t'
    · have : singleCoeff t u t' = 0 := by simp [singleCoeff, ht]
      rw [this, show zeroF (0 : L2 ℝ (Q (Fin n))) = 0 from rfl]
      exact Submodule.zero_mem _
  rw [← sum_singleCoeff u]
  exact Submodule.sum_mem _ fun t _ => sobolevPar_le_sobolevQ t.1 1 (hpar t)

/-- `Λ⁰` has a single index. -/
theorem card_formIdx_zero : Fintype.card (formIdx n 0) = 1 :=
  Fintype.card_eq_one_iff.2 ⟨⟨∅, by simp⟩, fun s =>
    Subtype.ext (Finset.card_eq_zero.1 (by exact_mod_cast s.2))⟩

/-- The `0`-form with coefficient `f` has the norm of `f`. -/
theorem norm_zeroF {Ω : Set (Fin n → ℝ)} (f : L2 ℝ Ω) : ‖zeroF (n := n) f‖ = ‖f‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [zeroF, card_formIdx_zero]

theorem cf_sum {ι : Type*} (s : Finset ι) (y : ι → Seq n k) (m : Fin n → ℤ) :
    cf (∑ i ∈ s, y i) m = ∑ i ∈ s, cf (y i) m := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, cf_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cf_add, ih]

/-- Equal partial maps agree on common points of their domains. -/
theorem pmap_apply_eq_of_eq {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] {f g : E →ₗ.[ℝ] F} (h : f = g) (x : E) (hf : x ∈ f.domain)
    (hg : x ∈ g.domain) : f ⟨x, hf⟩ = g ⟨x, hg⟩ := by
  subst h; rfl

/-- **The coefficientwise even extension** of `u` to `𝕋ⁿ`: the sum over `t` of the parity
extensions of `u_t dx_t` in the class `J = t`, so that every coefficient `u_t` is extended evenly
in all variables (`cf_evenExt_apply`). -/
noncomputable def evenExt (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) : Seq n k :=
  ∑ t : formIdx n (k : ℤ), JfJ t.1 k (singleCoeff t u)

theorem Jinvf_evenExt (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) : Jinvf k (evenExt u) = u := by
  rw [evenExt, map_sum]
  simp_rw [Jinvf_JfJ]
  exact sum_singleCoeff u

/-- The `t`-component of `evenExt u` is the even extension of the coefficient `u_t`. -/
theorem cf_evenExt_apply (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) (m : Fin n → ℤ)
    (t' : formIdx n (k : ℤ)) :
    cf (evenExt u) m t' = cf (JfJ ∅ 0 (zeroF (u t'))) m t₀ := by
  rw [evenExt, cf_sum]
  rw [show (∑ t : formIdx n (k : ℤ), cf (JfJ t.1 k (singleCoeff t u)) m) t' =
      ∑ t : formIdx n (k : ℤ), cf (JfJ t.1 k (singleCoeff t u)) m t' by
    simp]
  rw [Finset.sum_eq_single t']
  · rw [← cf_JfJ_zeroF, symmDiff_self, Finset.bot_eq_empty]
    simp [singleCoeff]
  · intro t _ ht
    rw [← cf_JfJ_zeroF]
    have : singleCoeff t u t' = 0 := by simp [singleCoeff, Ne.symm ht]
    rw [this, show zeroF (0 : L2 ℝ (Q (Fin n))) = 0 from rfl, map_zero, cf_zero]
    rfl
  · intro h; exact absurd (Finset.mem_univ t') h

/-- **The `H¹(𝕋ⁿ)` norm of an even extension**: for `v ∈ H¹(Q)` (a `0`-form),
`‖JfJ ∅ v‖²_{H¹(𝕋ⁿ)} = 2ⁿ (‖v‖² + ‖∇ v‖²)`. -/
theorem sobSum_JfJ_empty {v : L2F ℝ (Q (Fin n)) (formIdx n ((0 : ℕ) : ℤ))}
    (hv : v ∈ ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))).domain) :
    Summable (fun m => weight 1 m * ‖cf (JfJ ∅ 0 v) m‖ ^ 2) ∧
      ∑' m, weight 1 m * ‖cf (JfJ ∅ 0 v) m‖ ^ 2 =
        2 ^ n * (‖v‖ ^ 2 + ‖(extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n)) ⟨v, hv⟩‖ ^ 2) := by
  have hv' : v ∈ (dPart (Q (Fin n)) (∅ : Finset (Fin n)) ((0 : ℕ) : ℤ)).domain := by
    rw [dPart_empty isOpen_Q]; exact hv
  obtain ⟨hs, he⟩ := dPart_zero_spec ∅ hv'
  have e : (fun m => weight 1 m * ‖cf (JfJ ∅ 0 v) m‖ ^ 2) =
      fun m => ‖cf (JfJ ∅ 0 v) m‖ ^ 2 + ‖freq m‖ ^ 2 * ‖cf (JfJ ∅ 0 v) m‖ ^ 2 := by
    funext m; rw [weight_one]; ring
  rw [e]
  refine ⟨(summable_norm_sq _).add hs, ?_⟩
  rw [Summable.tsum_add (summable_norm_sq _) hs, ← norm_sq_eq_tsum, he, norm_JfJ_sq,
    pmap_apply_eq_of_eq (dPart_empty isOpen_Q _) v hv' hv]
  ring

/-- **The `H¹(𝕋ⁿ)` norm of the coefficientwise even extension**: if every `u_t ∈ H¹(Q)`, then
`‖evenExt u‖²_{H¹(𝕋ⁿ)} = 2ⁿ (‖u‖² + Σ_t ‖∇ u_t‖²)`. -/
theorem sobSum_evenExt {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    (h : ∀ t, zeroF (u t) ∈ ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))).domain) :
    MemSob 1 (evenExt u) ∧ sobSum 1 (evenExt u) =
      2 ^ n * (‖u‖ ^ 2 + ∑ t, ‖(extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))
        ⟨zeroF (u t), h t⟩‖ ^ 2) := by
  have e : ∀ m, weight 1 m * ‖cf (evenExt u) m‖ ^ 2 =
      ∑ t : formIdx n (k : ℤ), weight 1 m * ‖cf (JfJ ∅ 0 (zeroF (u t))) m‖ ^ 2 := by
    intro m
    rw [norm_cf_sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [cf_evenExt_apply, norm_form_zero_sq]
  have hs : ∀ t : formIdx n (k : ℤ), Summable fun m =>
      weight 1 m * ‖cf (JfJ ∅ 0 (zeroF (u t))) m‖ ^ 2 := fun t => (sobSum_JfJ_empty (h t)).1
  refine ⟨(summable_sum fun t _ => hs t).congr fun m => (e m).symm, ?_⟩
  unfold sobSum
  simp_rw [e]
  rw [Summable.tsum_finsetSum fun t _ => hs t]
  rw [Finset.sum_congr rfl fun t _ => (sobSum_JfJ_empty (h t)).2]
  simp_rw [norm_zeroF]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, PiLp.norm_sq_eq_of_L2]

/-- `‖x‖²_{H¹(𝕋ⁿ)} = ‖x‖² + Σ_t Σ_m |2πm|² |x(m)_t|²`. -/
theorem sobSum_one_eq {x : Seq n k} (hx : MemSob 1 x) :
    sobSum 1 x = ‖x‖ ^ 2 + ∑ t : formIdx n (k : ℤ),
      ∑' m, ‖freq m‖ ^ 2 * ‖cf x m t‖ ^ 2 := by
  have hs := (summable_one_iff (k := k) x).1 hx
  have e : ∀ m, weight 1 m * ‖cf x m‖ ^ 2 =
      ‖cf x m‖ ^ 2 + ∑ t : formIdx n (k : ℤ), ‖freq m‖ ^ 2 * ‖cf x m t‖ ^ 2 := by
    intro m
    rw [weight_one, ← Finset.mul_sum, ← norm_cf_sq_eq_sum]; ring
  unfold sobSum
  simp_rw [e]
  rw [Summable.tsum_add (summable_norm_sq x) (summable_sum fun t _ => hs t),
    Summable.tsum_finsetSum fun t _ => hs t, ← norm_sq_eq_tsum]

/-- **Restriction is a contraction `H¹(𝕋ⁿ) → H¹(Q)`**:
`‖x|_Q‖² + Σ_t ‖∇ (x|_Q)_t‖² ≤ ‖x‖²_{H¹(𝕋ⁿ)}` (by the trigonometric case,
`grad_Jinvf_of_finite`, and the graph-norm convergence of the truncations). -/
theorem norm_sq_add_sum_grad_sq_le_sobSum {x : Seq n k} (hx : MemSob 1 x) :
    ‖Jinvf k x‖ ^ 2 + ∑ t, ‖(extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))
      ⟨zeroF (Jinvf k x t), (exists_tendsto_grad_trunc hx t).1⟩‖ ^ 2 ≤ sobSum 1 x := by
  have hfin : ∀ N, ∀ m ∉ bandS (n := n) N, cf (trunc N k x) m = 0 := fun N _ hm =>
    trunc_eq_zero_of_notMem x hm
  have hf : Tendsto (fun N => ‖Jinvf k (trunc N k x)‖ ^ 2 + ∑ t,
      ‖(extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))
        ⟨_, (grad_Jinvf_of_finite (trunc N k x) (hfin N) t).1⟩‖ ^ 2) atTop
      (𝓝 (‖Jinvf k x‖ ^ 2 + ∑ t, ‖(extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))
        ⟨zeroF (Jinvf k x t), (exists_tendsto_grad_trunc hx t).1⟩‖ ^ 2)) := by
    refine Tendsto.add ?_ (tendsto_finsetSum _ fun t _ => ?_)
    · exact ((((Jinvf k).continuous.tendsto x).comp (tendsto_trunc k x)).norm).pow 2
    · exact ((exists_tendsto_grad_trunc hx t).2.norm).pow 2
  refine le_of_tendsto' hf fun N => ?_
  have h1 : ‖Jinvf k (trunc N k x)‖ ^ 2 ≤ ‖trunc N k x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_Jinvf_le k _) 2
  have h2 : ∑ t, ‖(extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))
        ⟨_, (grad_Jinvf_of_finite (trunc N k x) (hfin N) t).1⟩‖ ^ 2 ≤
      ∑ t : formIdx n (k : ℤ), ∑' m, ‖freq m‖ ^ 2 * ‖cf (trunc N k x) m t‖ ^ 2 :=
    Finset.sum_le_sum fun t _ => (grad_Jinvf_of_finite (trunc N k x) (hfin N) t).2
  have h3 := sobSum_one_eq (memSob_trunc 1 N x)
  have h4 : sobSum 1 (trunc N k x) ≤ sobSum 1 x := by
    simpa using sobSum_trunc_le le_rfl hx N
  linarith

/-- **The `H¹(Q)` graph norm is bounded by the quotient norm**:
`‖u‖² + Σ_t ‖∇ u_t‖² ≤ ‖u‖²_{H¹(Q)}`. -/
theorem norm_sq_add_sum_grad_sq_le_qNorm {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    (hu : u ∈ sobolevQ n k 1) :
    ‖u‖ ^ 2 + ∑ t, ‖(extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))
      ⟨zeroF (u t), coeff_mem_maximal_of_mem_sobolevQ_one hu t⟩‖ ^ 2 ≤ qNorm k 1 u ^ 2 := by
  have hA : 0 ≤ ‖u‖ ^ 2 + ∑ t, ‖(extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))
      ⟨zeroF (u t), coeff_mem_maximal_of_mem_sobolevQ_one hu t⟩‖ ^ 2 := by positivity
  rw [← Real.sq_sqrt hA]
  refine pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_qNorm hu fun x hx hxu => ?_) 2
  subst hxu
  exact Real.sqrt_le_sqrt (norm_sq_add_sum_grad_sq_le_sobSum hx)

/-- **The quotient norm is bounded by the `H¹(Q)` graph norm**: if every coefficient `u_t` lies
in `H¹(Q)`, then `‖u‖²_{H¹(Q)} ≤ 2ⁿ (‖u‖² + Σ_t ‖∇ u_t‖²)` (extend every coefficient evenly,
`sobSum_evenExt`). -/
theorem qNorm_one_sq_le {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    (h : ∀ t, zeroF (u t) ∈ ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))).domain) :
    qNorm k 1 u ^ 2 ≤ 2 ^ n * (‖u‖ ^ 2 + ∑ t, ‖(extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))
      ⟨zeroF (u t), h t⟩‖ ^ 2) := by
  obtain ⟨hm, he⟩ := sobSum_evenExt h
  rw [← he, ← Real.sq_sqrt (sobSum_nonneg 1 _)]
  exact pow_le_pow_left₀ (qNorm_nonneg 1 u) (qNorm_le hm (Jinvf_evenExt u)) 2

/-- **The norm of `H¹(Q)` is equivalent to the graph norm of the coefficients**:
`‖u‖² + Σ_t ‖∇ u_t‖² ≤ ‖u‖²_{H¹(Q)} ≤ 2ⁿ (‖u‖² + Σ_t ‖∇ u_t‖²)` for `u ∈ H¹(Q)`. -/
theorem qNorm_one_sq_equiv {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    (hu : u ∈ sobolevQ n k 1) :
    ‖u‖ ^ 2 + ∑ t, ‖(extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))
        ⟨zeroF (u t), coeff_mem_maximal_of_mem_sobolevQ_one hu t⟩‖ ^ 2 ≤ qNorm k 1 u ^ 2 ∧
      qNorm k 1 u ^ 2 ≤ 2 ^ n * (‖u‖ ^ 2 + ∑ t, ‖(extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal
        (Q (Fin n)) ⟨zeroF (u t), coeff_mem_maximal_of_mem_sobolevQ_one hu t⟩‖ ^ 2) :=
  ⟨norm_sq_add_sum_grad_sq_le_qNorm hu, qNorm_one_sq_le _⟩

end H1Q

/-! ### Axis frequencies and the coefficients `1/|c|` of the logarithmic series -/

section Witness

variable [NeZero n]

/-- The frequencies `c e₀` on the first axis. -/
def axis (c : ℤ) : Fin n → ℤ := Pi.single 0 c

theorem axis_injective : Function.Injective (axis (n := n)) := fun a b h => by
  simpa [axis] using congrFun h 0

/-- `m` lies on the first axis. -/
def OnAxis (m : Fin n → ℤ) : Prop := ∀ j, j ≠ 0 → m j = 0

theorem onAxis_iff_mem_range (m : Fin n → ℤ) : OnAxis m ↔ m ∈ Set.range (axis (n := n)) := by
  constructor
  · intro h
    refine ⟨m 0, funext fun j => ?_⟩
    by_cases hj : j = 0
    · subst hj; simp [axis]
    · simp [axis, hj, h j hj]
  · rintro ⟨c, rfl⟩ j hj
    simp [axis, hj]

theorem norm_freq_axis_sq (c : ℤ) : ‖freq (axis (n := n) c)‖ ^ 2 = (2 * Real.pi * c) ^ 2 := by
  rw [norm_freq_sq, Fintype.sum_eq_single 0 fun j hj => by simp [axis, hj]]
  simp [axis]; ring

open scoped Classical in
/-- **The coefficients of the logarithmic series**: `1/|c|` at the frequencies `±c e₀`, `c ≠ 0`
(the function `Σ_{c ≠ 0} e^{2πi c y₀}/|c| = -2 log |2 sin π y₀|`). -/
def logCoeff (m : Fin n → ℤ) : Form ℂ (Fin n) 0 :=
  WithLp.toLp 2 fun _ => if OnAxis m ∧ m 0 ≠ 0 then (((|(m 0 : ℝ)|)⁻¹ : ℝ) : ℂ) else 0

open scoped Classical in
theorem norm_logCoeff_sq (m : Fin n → ℤ) :
    ‖logCoeff m‖ ^ 2 = if OnAxis m ∧ m 0 ≠ 0 then ((|(m 0 : ℝ)|)⁻¹) ^ 2 else 0 := by
  rw [norm_form_zero_sq]
  change ‖(if OnAxis m ∧ m 0 ≠ 0 then (((|(m 0 : ℝ)|)⁻¹ : ℝ) : ℂ) else 0)‖ ^ 2 = _
  split_ifs <;> simp

/-- The weighted squares on the axis. -/
def axisTerm (s : ℝ) (c : ℤ) : ℝ := weight s (axis (n := n) c) * ‖logCoeff (axis (n := n) c)‖ ^ 2

theorem axisTerm_eq (s : ℝ) (c : ℤ) :
    axisTerm (n := n) s c =
      if c = 0 then 0 else (1 + (2 * Real.pi * c) ^ 2) ^ s * ((|(c : ℝ)|)⁻¹) ^ 2 := by
  classical
  have hax : OnAxis (axis (n := n) c) := (onAxis_iff_mem_range _).2 ⟨c, rfl⟩
  have h0 : axis (n := n) c 0 = c := by simp [axis]
  rw [axisTerm, norm_logCoeff_sq, weight, norm_freq_axis_sq, h0]
  by_cases hc : c = 0 <;> simp [hc, hax]

theorem summable_weight_logCoeff_iff (s : ℝ) :
    Summable (fun m : Fin n → ℤ => weight s m * ‖logCoeff m‖ ^ 2) ↔
      Summable (axisTerm (n := n) s) := by
  classical
  rw [← axis_injective.summable_iff (f := fun m : Fin n → ℤ => weight s m * ‖logCoeff m‖ ^ 2)
    fun m hm => ?_]
  · rfl
  · have h : ¬ OnAxis m := fun h => hm ((onAxis_iff_mem_range m).1 h)
    rw [norm_logCoeff_sq]
    simp [show ¬ (OnAxis m ∧ m 0 ≠ 0) from fun h' => h h'.1]

theorem axisTerm_nonneg (s : ℝ) (c : ℤ) : 0 ≤ axisTerm (n := n) s c :=
  mul_nonneg (weight_nonneg s _) (sq_nonneg _)

/-- **The logarithmic series is in `Hˢ` for `s < ½`**: `Σ_c (1 + 4π²c²)^s c⁻² < ∞`. -/
theorem summable_axisTerm {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 2) :
    Summable (axisTerm (n := n) s) := by
  refine Summable.of_nonneg_of_le (axisTerm_nonneg s) (fun c => ?_)
    ((Real.summable_abs_int_rpow (b := 2 - 2 * s) (by linarith)).mul_left
      ((1 + (2 * Real.pi) ^ 2) ^ s))
  rw [axisTerm_eq]
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
    have e : ((|(c : ℝ)|)⁻¹) ^ 2 = |(c : ℝ)| ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, inv_pow]
    rw [e]
    calc (1 + (2 * Real.pi * c) ^ 2) ^ s * |(c : ℝ)| ^ (-(2 : ℝ)) ≤
        ((1 + (2 * Real.pi) ^ 2) ^ s * |(c : ℝ)| ^ ((2 : ℕ) * s)) * |(c : ℝ)| ^ (-(2 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (abs_nonneg _) _)
      _ = (1 + (2 * Real.pi) ^ 2) ^ s * |(c : ℝ)| ^ (-(2 - 2 * s)) := by
          rw [mul_assoc, ← Real.rpow_add hcpos]; push_cast; ring_nf

/-- **The logarithmic series is not in `H^{1/2}`**: `Σ_c (1 + 4π²c²)^{1/2} c⁻² ≥ 2π Σ 1/|c| = ∞`. -/
theorem not_summable_axisTerm_half : ¬ Summable (axisTerm (n := n) (1 / 2)) := by
  intro h
  have hle : ∀ c : ℤ,
      2 * Real.pi * (1 / |(c : ℝ) + 0| ^ (1 : ℝ)) ≤ axisTerm (n := n) (1 / 2) c := by
    intro c
    rw [axisTerm_eq, add_zero, Real.rpow_one]
    split_ifs with hc
    · subst hc; simp
    · have hcpos : 0 < |(c : ℝ)| := abs_pos.2 (by exact_mod_cast hc)
      have hs : 2 * Real.pi * |(c : ℝ)| ≤ (1 + (2 * Real.pi * c) ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        refine Real.le_sqrt_of_sq_le ?_
        rw [mul_pow, sq_abs, mul_pow]; nlinarith
      calc 2 * Real.pi * (1 / |(c : ℝ)|) = (2 * Real.pi * |(c : ℝ)|) * ((|(c : ℝ)|)⁻¹) ^ 2 := by
            field_simp
        _ ≤ (1 + (2 * Real.pi * c) ^ 2) ^ (1 / 2 : ℝ) * ((|(c : ℝ)|)⁻¹) ^ 2 :=
            mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have h2 : Summable fun c : ℤ => 2 * Real.pi * (1 / |(c : ℝ) + 0| ^ (1 : ℝ)) :=
    Summable.of_nonneg_of_le (fun c => by positivity) hle h
  have h3 : Summable fun c : ℤ => 1 / |(c : ℝ) + 0| ^ (1 : ℝ) :=
    (h2.mul_left (2 * Real.pi)⁻¹).congr fun c => by
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  exact lt_irrefl _ ((Real.summable_one_div_int_add_rpow 0 1).1 h3)

theorem summable_norm_logCoeff_sq : Summable fun m : Fin n → ℤ => ‖logCoeff m‖ ^ 2 := by
  have h := (summable_weight_logCoeff_iff (n := n) 0).2 (summable_axisTerm le_rfl (by norm_num))
  simpa using h

end Witness

end Feec.Models.Cube.Sobolev
