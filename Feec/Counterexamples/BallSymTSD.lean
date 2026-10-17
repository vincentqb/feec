module

public import Feec.Ch4.BoundedSymExt
public import Feec.Ch4.BoundedInterior
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Prop 4.19 with the boundary conditions as printed fails on the unit ball

Moved from `Feec.Ch4.BoundedSymDual` (whose names are deprecated aliases); the headline results
are `tsd_not_propagates`, `not_propagates` and `tsdSk_not_propagates`. The construction still
uses the complex `Feec.BoundedSym.symComplexD` of `Feec.Ch4.BoundedSymExt`.

`Feec.Ch4.BoundedSymExt` builds the complex (4.16) with the boundary conditions of the data space
printed in Prop 4.19 ([QuennevilleBelair2015, §4.11]), `symComplexD`:
`H²(Ω) --grad grad--> H(curl, S) --curl--> L²(T)` (no boundary conditions), whose adjoints are
`div div` on `H̊(div div, S)` and `sym curl` on `H̊(sym curl, T)`, so
`D(L) = H² × (H(curl, S) ∩ H̊(div div, S)) × H̊(sym curl, T)`. For
`K = {0} × L²(TSD) × L²(TSD)` it shows, on every bounded domain, that the projection and density
hypotheses of Theorem 4.4 fail and that `L` maps `D(L) ∩ K` into `K`, and it leaves the conclusion
(TSD propagation) open. This file decides the
conclusion on one domain: on the Euclidean unit ball `B = {x₀² + x₁² + x₂² < 1}` (`ball3`; `R3`
carries the sup norm, so `B` is not `Metric.ball 0 1`) **TSD does not propagate**.

## The counterexample

* **Datum** `x₀ = (0, E₀, 0)`, `E₀ = e₃ uᵀ + u e₃ᵀ`, `u = e₃ × x = (-x₁, x₀, 0)`
  (`eF`, `E0`, `x0`): a linear field, symmetric, trace-free, divergence-free, with
  `xᵀ E₀ x = 0` and the constant curl `curl E₀ = diag(-1, -1, 2)` (`curlM_eF`).
* **`E₀ ∈ H̊(div div, S)`** (`E0_mem_divdivD`). With the radial cutoffs `χ_n(x) = η_n(|x|²)`
  (`chi`, built from `Real.smoothTransition`), `div div (χ_n E₀) = E₀ : ∇²χ_n + 2 ∇χ_n · div E₀`
  vanishes identically, since `∇²χ_n = 4 η_n'' x xᵀ + 2 η_n' I`, `tr E₀ = 0`, `xᵀ E₀ x = 0`
  (`divdivF_chi_eF`); and `χ_n E₀ → E₀` in `L²` (`tendsto_testFieldS_psiN`). So
  `x₀ ∈ D(L) ∩ K` (`x0_mem_domL`, `x0_mem_Kc`).
* **Test vector** `N = (0, 0, curl Q)` (`Nvec`), `Q = sym ∇v` (`qExp = symF gExp`),
  `v = (1 - |x|²)(-x₁x₂, x₀x₂, 0)` (`vF`). `v ∈ H̊¹(B)` in the sense needed: `∇(χ_n v) → ∇v` in
  `L²`, because `(1 - s) η_n'(s)` stays bounded (`abs_mul_deriv_eta_le`, `tendsto_pd_chi_vF`).
  Hence `⟪C, Q⟫ = ⟪C, ∇v⟫ = 0` for every `C ∈ L²(TSD)` (`sum_integral_mul_qExp_eq_zero`), and for
  `y = (0, E, B) ∈ D(L) ∩ K`, `⟪y, N⟫ = ⟪B, curl Q⟫ = ⟪sym curl B, Q⟫ = 0`, as
  `sym curl B ∈ L²(TSD)` (Lemma 3.5, `symComplexD_adjoint_d1_mem_TSDS`): `N ⊥ D(L) ∩ K`
  (`inner_Nvec_eq_zero`).
* **The pairing** `⟪-L x₀, N⟫ = ⟪curl E₀, curl Q⟫ = 3 ∫_B (1 - 2x₀² - 2x₁² - 3x₂²)`
  (`inner_negL_x0`, `inner_curlE0_curlQ`, `sum_Mc_curlM_qExp`), bounded by
  `3 ∫_B (1 - 2|x|²) = -(3/5) |B| < 0` via the radial moment `∫_B |x|² = (3/5) |B|`
  (`integral_rho_ball3`, from `MeasureTheory.integral_fun_norm_addHaar`) (`inner_negL_x0_lt`;
  the exact value `-(6/5) |B|` is not needed).
* **Criterion** (`not_propagate_of_inner`, any Hilbert complex): if `N ⊥ D(L) ∩ K` and
  `⟪-L x₀, N⟫ ≠ 0`, every strong solution from `x₀` leaves `K` on every `[0, T]`, `T > 0`.

## Main results

* **`tsd_not_propagates`**, **`not_propagates`**,
  `tsdSk_not_propagates`: the
  TSD datum `x₀ ∈ D(L) ∩ K` has, on every `[0, T]`, `T > 0`, a unique strong solution (Stone's
  theorem), and it leaves `K = {0} × L²(TSD) × L²(TSD)`; `x₀` also lies in the variant
  `{0} × (L²(TSD) ∩ ker d0*) × L²(TSD)` of `Feec.Ch4.BoundedSymExt`.
* `negL_x0_not_mem_closure`: `-L x₀ ∉ closure (D(L) ∩ K)`. `L` maps `D(L) ∩ K` into `K`, but not
  into the closure of `D(L) ∩ K`; the defect is in the magnetic slot:
* `curlE0_not_mem_closure`: `curl E₀ = diag(-1, -1, 2) ∈ L²(TSD)` is not in the closure of
  `L²(TSD) ∩ H̊(sym curl, T)`, so that intersection is not dense in `L²(TSD)` on `B`.
* `x0_not_mem_Kmax`: `x₀ ∉ K*`, so the maximal form `symComplexD_prop_4_19_max` is a strict
  restriction of the data of Prop 4.19 on `B`.

## Correction

[QuennevilleBelair2015, §4.11, Prop 4.19], read with its printed data space
`H² × (H(curl, S) ∩ H̊(div div, S)) × H̊(sym curl, T)` and `K = {0} × L²(TSD) × L²(TSD)`: the
conclusion is false on the unit ball of `ℝ³`. With the placement of the boundary conditions used
in the proof (`symComplexB`) it is false on every bounded domain (`Feec.Ch4.BoundedSym`), so on the
unit ball the conclusion of Prop 4.19 fails with either placement. Prop 4.19 itself is an
implication whose projection and density hypotheses already fail on bounded domains
(`Feec.Ch4.BoundedSymExt`), so what is refuted here is its conclusion (TSD propagation for every
TSD datum of the printed data space), not the implication.

## Scope

* Only the unit ball centred at `0` is treated. The same construction applies to every ball
  `{|x - c| < R}` (with `u = e₃ × (x - c)` and `v = (R² - |x - c|²)(…)`); this is not
  formalized. The construction needs explicit fields in `H̊(div div, S)` that do not vanish near
  `∂Ω`; the radial cutoffs provide them because `B` is rotation-invariant about the axis `e₃` of
  `E₀`. Whether the conclusion fails on every bounded domain is not decided.
* Not decided either: whether `K* ≠ {0}` on `B`, and whether the constant magnetic field
  `(0, 0, diag(1, -1, 0))` is orthogonal to `D(L) ∩ K` (the open sub-questions of
  `Feec.Ch4.BoundedSymExt`); here the obstruction is `curl Q`, not a constant.
* The box parity model of `Feec.Ch4.Box*` is not used.

## References

* [QuennevilleBelair2015], §3.4 (Lemma 3.5), §4.11 ((4.16)–(4.18), Prop 4.19)
* [ArnoldHu2021] (the `grad grad`–`curl`–`div` complex)
* [Brezis2011] (weak derivatives, `H̊¹`)
* [Pazy1983], §1.10 (Stone's theorem, behind `Feec.HilbertComplex2.waveGroup`)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal ContDiff Matrix LinearPMap
open MeasureTheory Set Filter Topology

namespace Feec.Counterexamples.BallSymTSD

open Feec.BoundedDomain Feec.BoundedSym Feec.HilbertComplex2 Feec.Constraints

/-! ## The unit ball and the radial cutoffs -/

/-- `|x|² = x₀² + x₁² + x₂²`. -/
def rho (x : R3) : ℝ := x 0 * x 0 + x 1 * x 1 + x 2 * x 2

theorem differentiable_rho : Differentiable ℝ rho := by
  unfold rho; fun_prop

theorem contDiff_rho : ContDiff ℝ ∞ rho := by
  unfold rho; fun_prop

/-- `∂_k |x|² = 2 x_k`. -/
theorem pd_rho (k : Fin 3) (x : R3) : BoundedDomain.pd k rho x = 2 * x k := by
  have h := fun a : Fin 3 => (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) a x).mul
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) a x)
  have h' : HasFDerivAt rho _ x := ((h 0).add (h 1)).add (h 2)
  rw [pd_of_hasFDerivAt h']
  fin_cases k <;> simp <;> ring

/-- Chain rule: `∂_k η(|x|²) = 2 η'(|x|²) x_k`. -/
theorem pd_comp_rho {η : ℝ → ℝ} (hη : Differentiable ℝ η) (k : Fin 3) (x : R3) :
    BoundedDomain.pd k (fun y => η (rho y)) x = deriv η (rho x) * (2 * x k) := by
  have h1 := fun a : Fin 3 => (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) a x).mul
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) a x)
  have hr : HasFDerivAt rho _ x := ((h1 0).add (h1 1)).add (h1 2)
  have h : HasFDerivAt (fun y => η (rho y)) _ x := (hη (rho x)).hasDerivAt.comp_hasFDerivAt x hr
  rw [pd_of_hasFDerivAt h, smul_apply, ← pd_of_hasFDerivAt hr, pd_rho,
    smul_eq_mul]

theorem continuous_rho : Continuous rho := differentiable_rho.continuous

theorem rho_nonneg (x : R3) : 0 ≤ rho x := by
  unfold rho; nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1), mul_self_nonneg (x 2)]

theorem sq_le_rho (x : R3) (i : Fin 3) : x i * x i ≤ rho x := by
  unfold rho
  fin_cases i <;> simp <;> nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1),
    mul_self_nonneg (x 2)]

theorem abs_le_one_of_rho_le {x : R3} (hx : rho x ≤ 1) (i : Fin 3) : |x i| ≤ 1 := by
  have := sq_le_rho x i
  exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

theorem norm_le_one_of_rho_le {x : R3} (hx : rho x ≤ 1) : ‖x‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
    rw [Real.norm_eq_abs]; exact abs_le_one_of_rho_le hx i

/-- The Euclidean unit ball `{|x| < 1}` (`R3` carries the sup norm, so this is not
`Metric.ball 0 1`). -/
def ball3 : Set R3 := {x | rho x < 1}

theorem isOpen_ball3 : IsOpen ball3 := isOpen_lt continuous_rho continuous_const

theorem isBounded_ball3 : Bornology.IsBounded ball3 :=
  (Metric.isBounded_closedBall (x := (0 : R3)) (r := 1)).subset fun x hx => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_one_of_rho_le (le_of_lt hx)

theorem zero_mem_ball3 : (0 : R3) ∈ ball3 := by
  show rho 0 < 1
  simp [rho]

theorem ball3_nonempty : ball3.Nonempty := ⟨0, zero_mem_ball3⟩

/-- The radial profile `η_n(s) = χ((n + 2)(1 - s) - 1)`: `1` for `s ≤ 1 - 2/(n + 2)`, `0` for
`s ≥ 1 - 1/(n + 2)` (`χ = Real.smoothTransition`). -/
def eta (n : ℕ) (s : ℝ) : ℝ := Real.smoothTransition (((n : ℝ) + 2) * (1 - s) - 1)

/-- The radial cutoff `χ_n(x) = η_n(|x|²)`. -/
def chi (n : ℕ) (x : R3) : ℝ := eta n (rho x)

theorem contDiff_eta (n : ℕ) : ContDiff ℝ ∞ (eta n) :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem differentiable_eta (n : ℕ) : Differentiable ℝ (eta n) :=
  (contDiff_eta n).differentiable (by simp)

theorem differentiable_deriv_eta (n : ℕ) : Differentiable ℝ (deriv (eta n)) :=
  (contDiff_infty_iff_deriv.1 (contDiff_eta n)).2.differentiable (by simp)

theorem deriv_eta (n : ℕ) (s : ℝ) :
    deriv (eta n) s = -((n : ℝ) + 2) * dχ (((n : ℝ) + 2) * (1 - s) - 1) := by
  have hi : HasDerivAt (fun s : ℝ => ((n : ℝ) + 2) * (1 - s) - 1) (((n : ℝ) + 2) * (-1)) s := by
    have := ((hasDerivAt_id s).const_sub 1).const_mul ((n : ℝ) + 2)
    simpa using this.sub_const 1
  have h := (hasDerivAt_χ (((n : ℝ) + 2) * (1 - s) - 1)).comp s hi
  rw [show eta n = Real.smoothTransition ∘ fun s : ℝ => ((n : ℝ) + 2) * (1 - s) - 1 from rfl,
    h.deriv]
  ring

theorem two_le_mul (n : ℕ) : (2 : ℝ) ≤ (n : ℝ) + 2 := by
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem eta_eq_one {n : ℕ} {s : ℝ} (h : 2 ≤ ((n : ℝ) + 2) * (1 - s)) : eta n s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem eta_eq_zero {n : ℕ} {s : ℝ} (h : ((n : ℝ) + 2) * (1 - s) ≤ 1) : eta n s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem deriv_eta_eq_zero {n : ℕ} {s : ℝ} (h : 2 ≤ ((n : ℝ) + 2) * (1 - s)) :
    deriv (eta n) s = 0 := by
  rw [deriv_eta, dχ_eq_zero_of_one_le (by linarith), mul_zero]

theorem eta_nonneg (n : ℕ) (s : ℝ) : 0 ≤ eta n s := Real.smoothTransition.nonneg _

theorem eta_le_one (n : ℕ) (s : ℝ) : eta n s ≤ 1 := Real.smoothTransition.le_one _

/-- **The cutoff gradient is `O(1/(1 - s))`**: `|(1 - s) η_n'(s)| ≤ 2 D`, `D` a bound of `|χ'|`. -/
theorem abs_mul_deriv_eta_le {D : ℝ} (hD : ∀ s, |dχ s| ≤ D) (n : ℕ) (s : ℝ) :
    |(1 - s) * deriv (eta n) s| ≤ 2 * D := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  rw [deriv_eta]
  set t := ((n : ℝ) + 2) * (1 - s) - 1
  by_cases h0 : t ≤ 0
  · rw [dχ_eq_zero_of_nonpos h0]; simp; positivity
  by_cases h1 : 1 ≤ t
  · rw [dχ_eq_zero_of_one_le h1]; simp; positivity
  rw [not_le] at h0 h1
  have e : (1 - s) * (-((n : ℝ) + 2) * dχ t) = -(((n : ℝ) + 2) * (1 - s)) * dχ t := by ring
  rw [e, abs_mul, abs_neg, abs_of_pos (by linarith)]
  have := hD t
  nlinarith [abs_nonneg (dχ t)]

theorem contDiff_chi (n : ℕ) : ContDiff ℝ ∞ (chi n) := (contDiff_eta n).comp contDiff_rho

theorem differentiable_chi (n : ℕ) : Differentiable ℝ (chi n) :=
  (contDiff_chi n).differentiable (by simp)

/-- `χ_n ∈ C_c^∞(B)`. -/
theorem isTest_chi (n : ℕ) : IsTest ball3 (chi n) := by
  set c : ℝ := 1 - 1 / ((n : ℝ) + 2)
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by linarith [two_le_mul n]
  have hc1 : c < 1 := by simp only [c]; have := one_div_pos.2 hpos; linarith
  have hK : IsCompact {x : R3 | rho x ≤ c} :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_rho continuous_const)
      ((Metric.isBounded_closedBall (x := (0 : R3)) (r := 1)).subset fun x hx => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_le_one_of_rho_le (le_trans hx hc1.le))
  have hz : ∀ x, ¬ rho x ≤ c → chi n x = 0 := fun x hx => by
    rw [not_le] at hx
    refine eta_eq_zero ?_
    have : (1 : ℝ) - rho x < 1 / ((n : ℝ) + 2) := by simp only [c] at hx; linarith
    have h2 := (lt_div_iff₀ hpos).1 this
    nlinarith
  refine ⟨contDiff_chi n, HasCompactSupport.intro hK fun x hx => hz x hx, ?_⟩
  refine (closure_minimal (fun x hx => ?_) (isClosed_le continuous_rho continuous_const)).trans
    fun x (hx : rho x ≤ c) => (show rho x < 1 from lt_of_le_of_lt hx hc1)
  by_contra h
  exact hx (hz x h)

theorem pd_chi (n : ℕ) (k : Fin 3) (x : R3) :
    BoundedDomain.pd k (chi n) x = deriv (eta n) (rho x) * (2 * x k) :=
  pd_comp_rho (differentiable_eta n) k x

/-- On `B`, eventually `η_n = 1` and `η_n' = 0` near `|x|²`. -/
theorem eventually_eta_eq_one {x : R3} (hx : x ∈ ball3) :
    ∀ᶠ n : ℕ in atTop, eta n (rho x) = 1 ∧ deriv (eta n) (rho x) = 0 := by
  have hx' : 0 < 1 - rho x := by have : rho x < 1 := hx; linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / (1 - rho x))
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have h : 2 ≤ ((n : ℝ) + 2) * (1 - rho x) := by
    have h1 : 2 / (1 - rho x) ≤ (n : ℝ) + 2 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have := (div_le_iff₀ hx').1 h1
    linarith
  exact ⟨eta_eq_one h, deriv_eta_eq_zero h⟩

theorem tendsto_chi {x : R3} (hx : x ∈ ball3) : Tendsto (fun n => chi n x) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' ((eventually_eta_eq_one hx).mono fun _ h => h.1.symm)

/-! ## Bounded pointwise convergence gives `L²` convergence -/

/-- On a set of finite measure, uniformly bounded pointwise convergence of `L²` functions implies
convergence in `L²(Ω)` (dominated convergence for `∫ |F_n - f|²`). -/
theorem tendsto_toLp_of_bound {Ω : Set R3} (hΩm : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    {F : ℕ → R3 → ℝ} {f : R3 → ℝ} (hF : ∀ n, MemLp (F n) 2 (volume.restrict Ω))
    (hf : MemLp f 2 (volume.restrict Ω)) {C : ℝ} (hC : ∀ n, ∀ x ∈ Ω, |F n x - f x| ≤ C)
    (hlim : ∀ x ∈ Ω, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 (hf.toLp f)) := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.2 hfin
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have key : ∀ n, ‖(hF n).toLp (F n) - hf.toLp f‖ ^ 2 =
      ∫ x, (F n x - f x) ^ 2 ∂volume.restrict Ω := by
    intro n
    rw [← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [((hF n).sub hf).coeFn_toLp] with x hx
    rw [hx, Real.inner_apply, Pi.sub_apply, sq]
  have hint : Tendsto (fun n => ∫ x, (F n x - f x) ^ 2 ∂volume.restrict Ω) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict Ω)
      (F := fun n x => (F n x - f x) ^ 2) (f := fun _ => (0 : ℝ)) (fun _ => C ^ 2)
      (fun n => ((hF n).aestronglyMeasurable.sub hf.aestronglyMeasurable).pow 2)
      (integrable_const _)
      (fun n => ae_restrict_of_forall_mem hΩm fun x hx => by
        rw [Real.norm_eq_abs, abs_pow, sq_abs]
        have := hC n x hx
        nlinarith [abs_nonneg (F n x - f x), sq_abs (F n x - f x)])
      (ae_restrict_of_forall_mem hΩm fun x hx => by
        have := ((hlim x hx).sub (tendsto_const_nhds (x := f x))).pow 2
        simpa using this)
    simpa using h
  have h2 : Tendsto (fun n => Real.sqrt (‖(hF n).toLp (F n) - hf.toLp f‖ ^ 2)) atTop
      (𝓝 (Real.sqrt 0)) := (Real.continuous_sqrt.tendsto 0).comp (by simpa only [key] using hint)
  simpa [Real.sqrt_sq (norm_nonneg _)] using h2

/-! ## Linear fields -/

/-- The linear function `x ↦ c · x`. -/
def linF (c : Fin 3 → ℝ) (x : R3) : ℝ := c 0 * x 0 + c 1 * x 1 + c 2 * x 2

theorem contDiff_linF (c : Fin 3 → ℝ) : ContDiff ℝ ∞ (linF c) := by
  unfold linF; fun_prop

theorem differentiable_linF (c : Fin 3 → ℝ) : Differentiable ℝ (linF c) :=
  (contDiff_linF c).differentiable (by simp)

theorem pd_linF (c : Fin 3 → ℝ) (k : Fin 3) (x : R3) : BoundedDomain.pd k (linF c) x = c k := by
  have h := fun a : Fin 3 =>
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) a x).const_mul (c a)
  have h' : HasFDerivAt (linF c) _ x := ((h 0).add (h 1)).add (h 2)
  rw [pd_of_hasFDerivAt h']
  fin_cases k <;> simp

/-- Coefficients of the electric datum `E₀ = e₃ uᵀ + u e₃ᵀ`, `u = e₃ × x = (-x₁, x₀, 0)`:
`E₀_{02} = E₀_{20} = -x₁`, `E₀_{12} = E₀_{21} = x₀`, all other entries `0`. -/
def ecoef (ij : Ix) (m : Fin 3) : ℝ :=
  if (ij = (0, 2) ∨ ij = (2, 0)) ∧ m = 1 then -1
  else if (ij = (1, 2) ∨ ij = (2, 1)) ∧ m = 0 then 1 else 0

/-- The electric datum `E₀ = e₃ uᵀ + u e₃ᵀ`, `u = e₃ × x`. -/
def eF (ij : Ix) : R3 → ℝ := linF (ecoef ij)

theorem eF_symm (i j : Fin 3) : eF (i, j) = eF (j, i) := by
  funext x
  fin_cases i <;> fin_cases j <;> simp [eF, ecoef, linF]

theorem eF_trace (x : R3) : ∑ i, eF (i, i) x = 0 := by
  simp [eF, ecoef, linF, Fin.sum_univ_three]

/-- `E₀` is divergence-free: `Σ_j ∂_j E₀_{ij} = 0`. -/
theorem sum_pd_eF (i : Fin 3) (x : R3) : ∑ j, BoundedDomain.pd j (eF (i, j)) x = 0 := by
  simp only [eF, pd_linF]
  fin_cases i <;> simp [ecoef, Fin.sum_univ_three]

/-- The constant `curl E₀ = diag(-1, -1, 2)`. -/
def Mc (ij : Ix) : ℝ := if ij.1 = ij.2 then (if ij.1 = 2 then 2 else -1) else 0

/-- `curl E₀ = diag(-1, -1, 2)`. -/
theorem curlM_eF (ij : Ix) (x : R3) : curlM eF ij x = Mc ij := by
  obtain ⟨i, k⟩ := ij
  simp only [curlM, eF, pd_linF]
  fin_cases i <;> fin_cases k <;> norm_num [ecoef, Mc]

/-! ## `E₀ ∈ H̊(div div, S)`: radial cutoffs commute with `div div` on `E₀` -/

theorem pd_const_fun (c : ℝ) (k : Fin 3) (x : R3) :
    BoundedDomain.pd k (fun _ : R3 => c) x = 0 := by
  simp [BoundedDomain.pd]

/-- The Hessian of the radial cutoff: `∂_i ∂_j η(|x|²) = 4 η''(|x|²) x_i x_j + 2 η'(|x|²) δ_ij`. -/
theorem pd_pd_chi (n : ℕ) (i j : Fin 3) (x : R3) :
    BoundedDomain.pd i (BoundedDomain.pd j (chi n)) x =
      deriv (deriv (eta n)) (rho x) * (2 * x i) * (2 * x j) +
        deriv (eta n) (rho x) * (2 * if i = j then 1 else 0) := by
  have e : BoundedDomain.pd j (chi n) = fun y => deriv (eta n) (rho y) * (2 * y j) :=
    funext (pd_chi n j)
  have hf : DifferentiableAt ℝ (fun y => deriv (eta n) (rho y)) x :=
    ((differentiable_deriv_eta n).comp differentiable_rho) x
  have hg : DifferentiableAt ℝ (fun y : R3 => 2 * y j) x := by fun_prop
  rw [e, BoundedDomain.pd_mul hf hg i, pd_comp_rho (differentiable_deriv_eta n),
    BoundedDomain.pd_const_mul (by fun_prop) 2 i x, pd_coord]

/-- Product rule twice for `χ_n · (c · x)`. -/
theorem pd_pd_chi_mul_linF (n : ℕ) (c : Fin 3 → ℝ) (i j : Fin 3) (x : R3) :
    BoundedDomain.pd i (BoundedDomain.pd j (fun y => chi n y * linF c y)) x =
      BoundedDomain.pd i (BoundedDomain.pd j (chi n)) x * linF c x +
        BoundedDomain.pd j (chi n) x * c i + BoundedDomain.pd i (chi n) x * c j := by
  have hdj : Differentiable ℝ (BoundedDomain.pd j (chi n)) :=
    (contDiff_pd_top (contDiff_chi n) j).differentiable (by simp)
  have e : BoundedDomain.pd j (fun y => chi n y * linF c y) =
      (fun y => BoundedDomain.pd j (chi n) y * linF c y) + (fun y => chi n y * c j) :=
    funext fun y => by
      rw [BoundedDomain.pd_mul (differentiable_chi n y) (differentiable_linF c y), pd_linF]
      rfl
  rw [e, BoundedDomain.pd_add (f := fun y => BoundedDomain.pd j (chi n) y * linF c y)
      (g := fun y => chi n y * c j) (fun y => (hdj y).mul (differentiable_linF c y))
      (fun y => (differentiable_chi n y).mul (differentiableAt_const _)),
    BoundedDomain.pd_mul (hdj x) (differentiable_linF c x),
    BoundedDomain.pd_mul (differentiable_chi n x) (differentiableAt_const _), pd_linF, pd_const_fun]
  ring

/-- **`div div (χ_n E₀) = 0`**: `div E₀ = 0`, and `E₀ : ∇²χ_n = 0` because `E₀` is trace-free and
`xᵀ E₀ x = 0`. -/
theorem divdivF_chi_eF (n : ℕ) (x : R3) : divdivF (fun ij y => chi n y * eF ij y) x = 0 := by
  unfold divdivF
  simp only [eF, pd_pd_chi_mul_linF, pd_pd_chi, pd_chi]
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, ecoef, linF]
  ring

/-- A cutoff times a smooth function is a test function on `B`. -/
theorem isTest_chi_mul (n : ℕ) {g : R3 → ℝ} (hg : ContDiff ℝ ∞ g) :
    IsTest ball3 (fun y => chi n y * g y) :=
  ⟨(contDiff_chi n).mul hg, (isTest_chi n).hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans (isTest_chi n).tsupport_subset⟩

theorem pd_eF_diag (i j : Fin 3) (x : R3) : BoundedDomain.pd j (eF (i, j)) x = 0 := by
  simp only [eF, pd_linF]
  fin_cases i <;> fin_cases j <;> simp [ecoef]

theorem abs_eF_le {x : R3} (hx : rho x ≤ 1) (ij : Ix) : |eF ij x| ≤ 1 := by
  have h0 := abs_le_one_of_rho_le hx 0
  have h1 := abs_le_one_of_rho_le hx 1
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j <;> simp [eF, ecoef, linF, h0, h1]

theorem contDiff_one_eF (ij : Ix) : ContDiff ℝ 1 (eF ij) := (contDiff_linF _).of_le (by simp)

/-! ## The datum `x₀ = (0, E₀, 0)` on the unit ball -/

/-- `E₀ = e₃ uᵀ + u e₃ᵀ`, `u = e₃ × x`, as an element of `L²(B; S)`. -/
def E0 : L2S ball3 := smoothS isOpen_ball3 isBounded_ball3 contDiff_one_eF eF_symm

theorem coe_E0 : (E0 : L2M ball3) =
    smoothField isOpen_ball3 isBounded_ball3 eF (fun ij => (contDiff_one_eF ij).continuous) :=
  rfl

/-- **`E₀ ∈ L²(TSD)`**: symmetric, trace-free and divergence-free. -/
theorem E0_mem_TSDS : E0 ∈ TSDS ball3 := by
  have hKc := coeFn_smoothField isOpen_ball3 isBounded_ball3 eF
    (fun ij => (contDiff_one_eF ij).continuous)
  show smoothField isOpen_ball3 isBounded_ball3 eF (fun ij => (contDiff_one_eF ij).continuous) ∈
    TSD ball3
  refine ⟨E0.2, ?_, fun φ hφ => ?_⟩
  · simp only [Fin.sum_univ_three]
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add (smoothField isOpen_ball3 isBounded_ball3 eF
        (fun ij => (contDiff_one_eF ij).continuous) (0, 0) + smoothField isOpen_ball3
        isBounded_ball3 eF (fun ij => (contDiff_one_eF ij).continuous) (1, 1))
      (smoothField isOpen_ball3 isBounded_ball3 eF (fun ij => (contDiff_one_eF ij).continuous)
        (2, 2)),
      Lp.coeFn_add (smoothField isOpen_ball3 isBounded_ball3 eF
        (fun ij => (contDiff_one_eF ij).continuous) (0, 0)) (smoothField isOpen_ball3
        isBounded_ball3 eF (fun ij => (contDiff_one_eF ij).continuous) (1, 1)),
      hKc (0, 0), hKc (1, 1), hKc (2, 2), Lp.coeFn_zero ℝ 2 (volume.restrict ball3)]
      with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5, h6]
    have := eF_trace x
    simp only [Fin.sum_univ_three] at this
    simpa using this
  · refine Finset.sum_eq_zero fun ij _ => ?_
    rw [integral_congr_ae (g := fun x => BoundedDomain.pd ij.2 (φ ij.1) x * eF ij x)
      ((hKc ij).mono fun x hx => by simp only; rw [hx, mul_comm]),
      integral_pd_mul (hφ ij.1) (contDiff_one_eF ij) ij.2]
    obtain ⟨i, j⟩ := ij
    simp [pd_eF_diag]

/-- **`E₀ ∈ H(curl, S) = D(d1)`** for `symComplexD`, with `d1 E₀ = curl E₀ = diag(-1, -1, 2)`. -/
theorem E0_mem_d1 :
    ∃ h : E0 ∈ (symComplexD isOpen_ball3 isBounded_ball3).d1.domain,
      (symComplexD isOpen_ball3 isBounded_ball3).d1 ⟨_, h⟩ =
        curlSmoothS isOpen_ball3 isBounded_ball3 contDiff_one_eF eF_symm :=
  smoothS_mem_symComplexD_d1 isOpen_ball3 isBounded_ball3 contDiff_one_eF eF_symm

/-- The approximants `χ_n E₀ ∈ C_c^∞(B; S)`. -/
def psiN (n : ℕ) : Ix → R3 → ℝ := fun ij y => chi n y * eF ij y

theorem isTest_psiN (n : ℕ) (ij : Ix) : IsTest ball3 (psiN n ij) :=
  isTest_chi_mul n (contDiff_linF _)

theorem psiN_symm (n : ℕ) (i j : Fin 3) : psiN n (i, j) = psiN n (j, i) := by
  unfold psiN; rw [eF_symm i j]

theorem divdivTestField_psiN (n : ℕ) :
    divdivTestField isOpen_ball3 isBounded_ball3 (isTest_psiN n) = 0 := by
  refine Lp.ext ?_
  filter_upwards [(memLp_of_continuous isOpen_ball3 isBounded_ball3 (continuous_divdivF fun ij =>
    (isTest_psiN n ij).contDiff.of_le (by simp))).coeFn_toLp,
    Lp.coeFn_zero ℝ 2 (volume.restrict ball3)] with x h1 h2
  rw [divdivTestField, h1, h2]
  exact divdivF_chi_eF n x

/-- `χ_n E₀ → E₀` in `L²(B; S)`. -/
theorem tendsto_testFieldS_psiN :
    Tendsto (fun n => testFieldS isOpen_ball3 isBounded_ball3 (isTest_psiN n) (psiN_symm n))
      atTop (𝓝 E0) := by
  refine tendsto_subtype_rng.2 ?_
  simp only [testFieldS, coe_E0, smoothField]
  refine (PiLp.continuous_toLp 2 _).tendsto _ |>.comp (tendsto_pi_nhds.2 fun ij => ?_)
  refine tendsto_toLp_of_bound isOpen_ball3.measurableSet isBounded_ball3.measure_lt_top.ne
    _ _ (C := 1) (fun n x hx => ?_) (fun x hx => ?_)
  · have h1 := abs_eF_le (le_of_lt hx) ij
    have h2 := eta_nonneg n (rho x)
    have h3 := eta_le_one n (rho x)
    rw [show psiN n ij x - eF ij x = (chi n x - 1) * eF ij x by simp only [psiN]; ring, abs_mul]
    have : |chi n x - 1| ≤ 1 := by
      rw [abs_le]; constructor <;> simp only [chi] <;> linarith
    nlinarith [abs_nonneg (chi n x - 1), abs_nonneg (eF ij x)]
  · simpa [psiN] using (tendsto_chi hx).mul_const (eF ij x)

/-- **`E₀ ∈ H̊(div div, S) = D(d0*)`** for `symComplexD`, with `div div E₀ = 0`: `E₀` is the
`L²` limit of `χ_n E₀ ∈ C_c^∞(B; S)`, and `div div (χ_n E₀) = 0` exactly. -/
theorem E0_mem_divdivD : E0 ∈ (divdivD (Ω := ball3)).domain := by
  have hcl : IsClosed ((divdivD (Ω := ball3)).graph : Set (L2S ball3 × L2 ball3)) :=
    isClosed_divdivD isOpen_ball3 isBounded_ball3
  have hmem : ((E0 : L2S ball3), (0 : L2 ball3)) ∈ (divdivD (Ω := ball3)).graph := by
    refine hcl.mem_of_tendsto (tendsto_testFieldS_psiN.prodMk_nhds tendsto_const_nhds)
      (Eventually.of_forall fun n => ?_)
    have h := testFieldS_mem_graph_divdivD isOpen_ball3 isBounded_ball3 (isTest_psiN n)
      (psiN_symm n)
    rwa [divdivTestField_psiN] at h
  obtain ⟨y, hy, -⟩ := (LinearPMap.mem_graph_iff _).1 hmem
  have e : (y : L2S ball3) = E0 := hy
  exact e ▸ y.2

theorem E0_mem_adjoint_d0 : E0 ∈ (symComplexD isOpen_ball3 isBounded_ball3).d0†.domain := by
  rw [symComplexD_adjoint_d0]
  exact E0_mem_divdivD

/-- The datum `x₀ = (0, E₀, 0)`. -/
def x0 : Tot (L2 ball3) (L2S ball3) (L2T ball3) := ini (L2 ball3) E0 0

theorem x0_mem_domL : x0 ∈ (symComplexD isOpen_ball3 isBounded_ball3).domL := by
  rw [Feec.Constraints.mem_domL, x0, tot_ini]
  exact ⟨Submodule.zero_mem _, Submodule.mem_inf.2 ⟨E0_mem_d1.1, E0_mem_adjoint_d0⟩,
    Submodule.zero_mem _⟩

theorem x0_mem_Kc : x0 ∈ Kc (L2 ball3) (TSDS ball3) (TSDT ball3) := by
  rw [mem_Kc, x0, tot_ini]
  exact ⟨rfl, E0_mem_TSDS, Submodule.zero_mem _⟩

/-! ## The test field `N = (0, 0, curl Q)`, `Q = sym ∇v`, `v ∈ H̊¹(B)` -/

/-- The polynomial factors `p = (-x₁x₂, x₀x₂, 0)`. -/
def pF : Fin 3 → R3 → ℝ := ![fun x => -(x 1 * x 2), fun x => x 0 * x 2, fun _ => 0]

/-- `v = (1 - |x|²) p`, a vector field vanishing on `∂B`. -/
def vF (i : Fin 3) (x : R3) : ℝ := (1 - rho x) * pF i x

theorem contDiff_pF (i : Fin 3) : ContDiff ℝ ∞ (pF i) := by
  fin_cases i <;> simp [pF] <;> fun_prop

theorem contDiff_vF (i : Fin 3) : ContDiff ℝ ∞ (vF i) :=
  (contDiff_const.sub contDiff_rho).mul (contDiff_pF i)

/-- The gradient `(∇v)_{ij} = ∂_j v_i`, explicitly. -/
def gExp (ij : Ix) (x : R3) : ℝ :=
  if ij = (0, 0) then 2 * x 0 * x 1 * x 2
  else if ij = (0, 1) then x 2 * (x 0 * x 0 + 3 * (x 1 * x 1) + x 2 * x 2 - 1)
  else if ij = (0, 2) then x 1 * (x 0 * x 0 + x 1 * x 1 + 3 * (x 2 * x 2) - 1)
  else if ij = (1, 0) then -(x 2 * (3 * (x 0 * x 0) + x 1 * x 1 + x 2 * x 2 - 1))
  else if ij = (1, 1) then -(2 * x 0 * x 1 * x 2)
  else if ij = (1, 2) then -(x 0 * (x 0 * x 0 + x 1 * x 1 + 3 * (x 2 * x 2) - 1))
  else 0

theorem pd_vF (i j : Fin 3) (x : R3) : BoundedDomain.pd j (vF i) x = gExp (i, j) x := by
  have X := fun a : Fin 3 => hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) a x
  have hr : HasFDerivAt rho _ x := (((X 0).mul (X 0)).add ((X 1).mul (X 1))).add ((X 2).mul (X 2))
  have h1 := (hasFDerivAt_const (1 : ℝ) x).sub hr
  fin_cases i
  · show BoundedDomain.pd j (vF 0) x = gExp (0, j) x
    have h : HasFDerivAt (vF 0) _ x := h1.mul ((X 1).mul (X 2)).neg
    rw [pd_of_hasFDerivAt h]
    fin_cases j <;> simp [gExp, rho, pF] <;> ring
  · show BoundedDomain.pd j (vF 1) x = gExp (1, j) x
    have h : HasFDerivAt (vF 1) _ x := h1.mul ((X 0).mul (X 2))
    rw [pd_of_hasFDerivAt h]
    fin_cases j <;> simp [gExp, rho, pF] <;> ring
  · show BoundedDomain.pd j (vF 2) x = gExp (2, j) x
    have h : HasFDerivAt (vF 2) _ x := h1.mul (hasFDerivAt_const (0 : ℝ) x)
    rw [pd_of_hasFDerivAt h]
    fin_cases j <;> simp [gExp, pF]

/-- `Q = sym ∇v`, explicitly. -/
def qExp (ij : Ix) (x : R3) : ℝ :=
  if ij = (0, 0) then 2 * x 0 * x 1 * x 2
  else if ij = (1, 1) then -(2 * x 0 * x 1 * x 2)
  else if ij = (0, 1) ∨ ij = (1, 0) then x 2 * (x 1 * x 1 - x 0 * x 0)
  else if ij = (0, 2) ∨ ij = (2, 0) then x 1 * (x 0 * x 0 + x 1 * x 1 + 3 * (x 2 * x 2) - 1) / 2
  else if ij = (1, 2) ∨ ij = (2, 1) then
    -(x 0 * (x 0 * x 0 + x 1 * x 1 + 3 * (x 2 * x 2) - 1)) / 2
  else 0

theorem qExp_eq_symF : qExp = symF gExp := by
  funext ij x
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j <;> simp [qExp, gExp, symF] <;> ring

theorem qExp_symm (i j : Fin 3) : qExp (i, j) = qExp (j, i) := by
  rw [qExp_eq_symF]; exact symF_swap _ i j

theorem gExp_eq_pd (ij : Ix) : gExp ij = BoundedDomain.pd ij.2 (vF ij.1) :=
  funext fun x => (pd_vF ij.1 ij.2 x).symm

theorem contDiff_gExp (ij : Ix) : ContDiff ℝ ∞ (gExp ij) := by
  rw [gExp_eq_pd]; exact contDiff_pd_top (contDiff_vF _) _

theorem contDiff_qExp (ij : Ix) : ContDiff ℝ ∞ (qExp ij) := by
  rw [qExp_eq_symF]
  exact ((contDiff_gExp ij).add (contDiff_gExp _)).div_const 2

theorem contDiff_one_qExp (ij : Ix) : ContDiff ℝ 1 (qExp ij) :=
  (contDiff_qExp ij).of_le (by simp)

theorem pd2_q01 (x : R3) : BoundedDomain.pd 2 (qExp (0, 1)) x = x 1 * x 1 - x 0 * x 0 := by
  have X := fun a : Fin 3 => hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) a x
  have h := (X 2).mul (((X 1).mul (X 1)).sub ((X 0).mul (X 0)))
  have h' : HasFDerivAt (qExp (0, 1)) _ x :=
    h.congr_of_eventuallyEq (Eventually.of_forall fun y => by simp [qExp])
  rw [pd_of_hasFDerivAt h']
  simp

theorem pd2_q10 (x : R3) : BoundedDomain.pd 2 (qExp (1, 0)) x = x 1 * x 1 - x 0 * x 0 := by
  rw [← qExp_symm]; exact pd2_q01 x

theorem pd1_q02 (x : R3) : BoundedDomain.pd 1 (qExp (0, 2)) x =
    (x 0 * x 0 + 3 * (x 1 * x 1) + 3 * (x 2 * x 2) - 1) / 2 := by
  have X := fun a : Fin 3 => hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) a x
  have h := ((X 1).mul (((((X 0).mul (X 0)).add ((X 1).mul (X 1))).add
      (((X 2).mul (X 2)).const_mul 3)).sub_const 1)).const_mul (1 / 2)
  have h' : HasFDerivAt (qExp (0, 2)) _ x :=
    h.congr_of_eventuallyEq (Eventually.of_forall fun y => by simp [qExp]; ring)
  rw [pd_of_hasFDerivAt h']
  simp; ring

theorem pd1_q20 (x : R3) : BoundedDomain.pd 1 (qExp (2, 0)) x =
    (x 0 * x 0 + 3 * (x 1 * x 1) + 3 * (x 2 * x 2) - 1) / 2 := by
  rw [← qExp_symm]; exact pd1_q02 x

theorem pd0_q12 (x : R3) : BoundedDomain.pd 0 (qExp (1, 2)) x =
    -(3 * (x 0 * x 0) + x 1 * x 1 + 3 * (x 2 * x 2) - 1) / 2 := by
  have X := fun a : Fin 3 => hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) a x
  have h := ((X 0).mul (((((X 0).mul (X 0)).add ((X 1).mul (X 1))).add
      (((X 2).mul (X 2)).const_mul 3)).sub_const 1)).neg.const_mul (1 / 2)
  have h' : HasFDerivAt (qExp (1, 2)) _ x :=
    h.congr_of_eventuallyEq (Eventually.of_forall fun y => by simp [qExp]; ring)
  rw [pd_of_hasFDerivAt h']
  simp; ring

theorem pd0_q21 (x : R3) : BoundedDomain.pd 0 (qExp (2, 1)) x =
    -(3 * (x 0 * x 0) + x 1 * x 1 + 3 * (x 2 * x 2) - 1) / 2 := by
  rw [← qExp_symm]; exact pd0_q12 x

/-- `curl Q` paired with `curl E₀ = diag(-1, -1, 2)`, pointwise:
`Σ_{ij} (curl E₀)_{ij} (curl Q)_{ij} = 3 (1 - 2x₀² - 2x₁² - 3x₂²)`. -/
theorem sum_Mc_curlM_qExp (x : R3) :
    ∑ ij : Ix, Mc ij * curlM qExp ij x =
      3 * (1 - 2 * (x 0 * x 0) - 2 * (x 1 * x 1) - 3 * (x 2 * x 2)) := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Mc, curlM]
  simp only [Fin.isValue, Fin.reduceAdd, pd2_q01, pd2_q10, pd1_q02, pd1_q20, pd0_q12, pd0_q21]
  simp
  ring

/-- A continuous function is bounded on `B`. -/
theorem exists_bound_ball3 {g : R3 → ℝ} (hg : Continuous g) : ∃ C, ∀ x ∈ ball3, |g x| ≤ C := by
  obtain ⟨C, hC⟩ := isBounded_ball3.isCompact_closure.exists_bound_of_continuousOn hg.continuousOn
  exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x (subset_closure hx)⟩

/-- `∂_j (χ_n v_i) → ∂_j v_i` in `L²(B)`: `v ∈ H̊¹(B)`, and the cutoff term
`2 η_n'(|x|²) (1 - |x|²) x_j p_i` stays bounded. -/
theorem tendsto_pd_chi_vF (i j : Fin 3) :
    Tendsto (fun n => (memLp_of_continuous isOpen_ball3 isBounded_ball3
      (continuous_pd ((isTest_chi_mul n (contDiff_vF i)).contDiff_one) j)).toLp
        (BoundedDomain.pd j (fun y => chi n y * vF i y))) atTop
      (𝓝 ((memLp_of_continuous isOpen_ball3 isBounded_ball3 (contDiff_gExp (i, j)).continuous).toLp
        (gExp (i, j)))) := by
  obtain ⟨D, hD⟩ := exists_abs_dχ_le
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  obtain ⟨Cp, hCp⟩ := exists_bound_ball3 (g := fun x => 2 * x j * pF i x)
    ((continuous_const.mul (continuous_apply j)).mul (contDiff_pF i).continuous)
  obtain ⟨Cg, hCg⟩ := exists_bound_ball3 (contDiff_gExp (i, j)).continuous
  have hF : ∀ n x, BoundedDomain.pd j (fun y => chi n y * vF i y) x =
      (1 - rho x) * deriv (eta n) (rho x) * (2 * x j * pF i x) + chi n x * gExp (i, j) x := by
    intro n x
    rw [BoundedDomain.pd_mul (differentiable_chi n x)
      ((contDiff_vF i).differentiable (by simp) x), pd_chi, pd_vF, vF]
    ring
  refine tendsto_toLp_of_bound isOpen_ball3.measurableSet isBounded_ball3.measure_lt_top.ne
    _ _ (C := 2 * D * Cp + Cg) (fun n x hx => ?_) (fun x hx => ?_)
  · rw [hF]
    have h1 := abs_mul_deriv_eta_le hD n (rho x)
    have h2 := hCp x hx
    have h3 := hCg x hx
    have h4 : |chi n x - 1| ≤ 1 := by
      have := eta_nonneg n (rho x); have := eta_le_one n (rho x)
      rw [abs_le]; constructor <;> simp only [chi] <;> linarith
    calc |(1 - rho x) * deriv (eta n) (rho x) * (2 * x j * pF i x) + chi n x * gExp (i, j) x -
          gExp (i, j) x|
        = |(1 - rho x) * deriv (eta n) (rho x) * (2 * x j * pF i x) +
            (chi n x - 1) * gExp (i, j) x| := by ring_nf
      _ ≤ |(1 - rho x) * deriv (eta n) (rho x)| * |2 * x j * pF i x| +
            |chi n x - 1| * |gExp (i, j) x| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 2 * D * Cp + 1 * Cg := by
          gcongr
      _ = 2 * D * Cp + Cg := by ring
  · refine tendsto_const_nhds.congr' ((eventually_eta_eq_one hx).mono fun n hn => ?_)
    show gExp (i, j) x = BoundedDomain.pd j (fun y => chi n y * vF i y) x
    rw [hF, chi, hn.1, hn.2]
    ring

/-- **`Q = sym ∇v` is orthogonal to `L²(TSD)`**: for every `C ∈ L²(TSD)`, `⟪C, Q⟫ = ⟪C, ∇v⟫ = 0`,
because `v ∈ H̊¹(B)` (the `L²(TSD)` divergence condition is tested against `χ_n v ∈ C_c^∞`). -/
theorem sum_integral_mul_qExp_eq_zero {C : L2M ball3} (hC : C ∈ TSD ball3) :
    ∑ ij, ∫ x, C ij x * qExp ij x ∂volume.restrict ball3 = 0 := by
  rw [qExp_eq_symF, sum_integral_mul_symF isOpen_ball3 isBounded_ball3 hC.1
    (fun ij => (contDiff_gExp ij).continuous)]
  have hlim : Tendsto (fun n => ∑ ij : Ix, ∫ x, C ij x *
      BoundedDomain.pd ij.2 (fun y => chi n y * vF ij.1 y) x ∂volume.restrict ball3) atTop
      (𝓝 (∑ ij : Ix, ∫ x, C ij x * gExp ij x ∂volume.restrict ball3)) := by
    refine tendsto_finsetSum _ fun ij _ => ?_
    have h := (tendsto_const_nhds (x := (C ij : L2 ball3))).inner (𝕜 := ℝ)
      (tendsto_pd_chi_vF ij.1 ij.2)
    simp only [← integral_mul_eq_inner] at h
    exact h
  have h0 : ∀ n, ∑ ij : Ix, ∫ x, C ij x *
      BoundedDomain.pd ij.2 (fun y => chi n y * vF ij.1 y) x ∂volume.restrict ball3 = 0 :=
    fun n => hC.2.2 (fun i y => chi n y * vF i y) fun i => isTest_chi_mul n (contDiff_vF i)
  simp only [h0] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

/-! ## The radial moment `∫_B |x|² = (3/5) |B|` -/

theorem integral_Ioi_radial (k : ℕ) :
    ∫ t in Ioi (0 : ℝ), t ^ 2 • (if t < 1 then t ^ k else 0) = 1 / ((k : ℝ) + 3) := by
  have e : (fun t : ℝ => t ^ 2 • (if t < 1 then t ^ k else 0)) =
      (Iio 1).indicator (fun t => t ^ (k + 2)) := by
    funext t
    simp only [indicator, mem_Iio, smul_eq_mul]
    split_ifs <;> ring
  rw [e, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
  push_cast
  field_simp
  ring

/-- `∫_{ℝ³} F(|x|) dx` for the Euclidean norm, transported to `R3 = Fin 3 → ℝ`. -/
theorem integral_ball3_radial (k : ℕ) :
    ∫ x in ball3, (rho x) ^ k =
      3 * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) * (1 / (2 * (k : ℝ) + 3)) := by
  have hp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  rw [← integral_indicator isOpen_ball3.measurableSet, ← hp.integral_comp']
  have e : ∀ y : EuclideanSpace ℝ (Fin 3),
      ball3.indicator (fun x => rho x ^ k) ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm y) =
        (fun t : ℝ => if t < 1 then t ^ (2 * k) else 0) ‖y‖ := by
    intro y
    have hr : rho ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm y) = ‖y‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, rho]
      simp [Fin.sum_univ_three, sq]
    have hiff : ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm y) ∈ ball3 ↔ ‖y‖ < 1 := by
      show rho _ < 1 ↔ _
      rw [hr]
      exact pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero
    by_cases h : ‖y‖ < 1
    · rw [indicator_of_mem (hiff.2 h), hr, ← pow_mul]
      simp [h]
    · rw [indicator_of_notMem (fun h' => h (hiff.1 h'))]
      simp [h]
  simp only [e]
  rw [integral_fun_norm_addHaar volume (fun t : ℝ => if t < 1 then t ^ (2 * k) else 0)]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [show (3 - 1 : ℕ) = 2 from rfl, integral_Ioi_radial]
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring

theorem volume_real_ball3 :
    volume.real ball3 =
      3 * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) * (1 / 3) := by
  have h := integral_ball3_radial 0
  simp only [pow_zero, integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ,
    Nat.cast_zero, mul_zero, zero_add] at h
  exact h

/-- **`∫_B |x|² = (3/5) |B|`**. -/
theorem integral_rho_ball3 : ∫ x in ball3, rho x = 3 / 5 * volume.real ball3 := by
  have h := integral_ball3_radial 1
  simp only [pow_one, Nat.cast_one] at h
  rw [h, volume_real_ball3]
  ring

theorem integrable_ball3 {f : R3 → ℝ} (hf : Continuous f) : Integrable f (volume.restrict ball3) :=
  (hf.continuousOn.integrableOn_compact isBounded_ball3.isCompact_closure).mono_set subset_closure

/-! ## A generic refutation criterion -/

section Criterion

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]

/-- **Refutation criterion**: if `N ⊥ D(L) ∩ K` and `⟪-L x₀, N⟫ ≠ 0`, then every strong solution
of `ξ' = -L ξ` from `x₀` leaves `K` on every `[0, T]`, `T > 0` (strong solutions take values in
`D(L)`, and `t ↦ ⟪ξ(t), N⟫` would vanish on `[0, T]` with derivative `⟪-L x₀, N⟫` at `0`). -/
theorem not_propagate_of_inner (H : HilbertComplex2 W0 W1 W2) {K : Set (Tot W0 W1 W2)}
    (N : Tot W0 W1 W2) (hN : ∀ y ∈ H.domL, y ∈ K → ⟪y, N⟫ = 0) {x : Tot W0 W1 W2}
    (hx : x ∈ H.domL) (hc : ⟪(-H.waveOp) ⟨x, hx⟩, N⟫ ≠ 0) :
    ∀ T > 0, ∀ U : ℝ → Tot W0 W1 W2, IsStrongSolution (-H.waveOp) T x 0 U →
      ∃ t ∈ Icc 0 T, U t ∉ K := by
  intro T hT U hU
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hmem : ∀ t ∈ Icc 0 T, U t ∈
      LinearMap.ker ((innerSL ℝ N : Tot W0 W1 W2 →L[ℝ] ℝ) : Tot W0 W1 W2 →ₗ[ℝ] ℝ) := by
    intro t ht
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply, real_inner_comm]
    exact hN _ (hU.mem t ht) (hall t ht)
  have hm := mem_of_hasDerivWithinAt_Icc (innerSL ℝ N).isClosed_ker hT (hU.deriv 0 h0) hmem
  rw [Pi.zero_apply, add_zero, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    innerSL_apply_apply, real_inner_comm] at hm
  have e : (⟨U 0, hU.mem 0 h0⟩ : (-H.waveOp).domain) = ⟨x, hx⟩ := Subtype.ext hU.init
  rw [e] at hm
  exact hc hm

/-- For `x = (0, E, 0) ∈ D(L)` and `N = (0, 0, N₂)`: `⟪-L x, N⟫ = ⟪d1 E, N₂⟫`. -/
theorem inner_negL_ini (H : HilbertComplex2 W0 W1 W2) {E : W1}
    (hx : ini W0 E (0 : W2) ∈ H.domL) (hE : E ∈ H.d1.domain) (N₂ : W2) :
    ⟪(-H.waveOp) ⟨ini W0 E 0, hx⟩, ini W0 (0 : W1) N₂⟫ = ⟪H.d1 ⟨E, hE⟩, N₂⟫ := by
  have hp0 : H.pr0 ⟨ini W0 E 0, hx⟩ = 0 := Subtype.ext (by simp)
  have hp2 : H.prV2s ⟨ini W0 E 0, hx⟩ = 0 := Subtype.ext (by simp)
  have hp1 : H.prV1 ⟨ini W0 E 0, hx⟩ = ⟨E, hE⟩ := Subtype.ext (by simp)
  rw [inner_tot, LinearPMap.neg_apply, _root_.map_neg, Feec.Constraints.tot_waveOp, tot_ini]
  simp only
  rw [hp0, hp2, hp1]
  simp

end Criterion

/-! ## The refutation on the unit ball -/

/-- `Q = sym ∇v`, as an element of `L²(B; S)`. -/
def Qs : L2S ball3 := smoothS isOpen_ball3 isBounded_ball3 contDiff_one_qExp qExp_symm

theorem Qs_mem_d1 :
    ∃ h : Qs ∈ (symComplexD isOpen_ball3 isBounded_ball3).d1.domain,
      (symComplexD isOpen_ball3 isBounded_ball3).d1 ⟨_, h⟩ =
        curlSmoothS isOpen_ball3 isBounded_ball3 contDiff_one_qExp qExp_symm :=
  smoothS_mem_symComplexD_d1 isOpen_ball3 isBounded_ball3 contDiff_one_qExp qExp_symm

/-- The test vector `N = (0, 0, curl Q)`. -/
def Nvec : Tot (L2 ball3) (L2S ball3) (L2T ball3) :=
  ini (L2 ball3) 0 ((symComplexD isOpen_ball3 isBounded_ball3).d1 ⟨_, Qs_mem_d1.1⟩)

/-- `⟪C, Q⟫ = 0` for `C ∈ L²(TSD)`. -/
theorem inner_Qs_eq_zero {C : L2S ball3} (hC : C ∈ TSDS ball3) : ⟪C, Qs⟫ = 0 := by
  rw [Submodule.coe_inner]
  change ⟪(C : L2M ball3), smoothField isOpen_ball3 isBounded_ball3 qExp
    (fun ij => (contDiff_one_qExp ij).continuous)⟫ = 0
  rw [inner_smoothField]
  exact sum_integral_mul_qExp_eq_zero hC

/-- **`N ⊥ D(L) ∩ K`**: for `y = (0, E, B) ∈ D(L)` with `B ∈ L²(TSD)`,
`⟪y, N⟫ = ⟪B, curl Q⟫ = ⟪sym curl B, Q⟫ = 0`, since `sym curl B ∈ L²(TSD)` (Lemma 3.5) and
`Q = sym ∇v` with `v ∈ H̊¹(B)`. -/
theorem inner_Nvec_eq_zero (y : Tot (L2 ball3) (L2S ball3) (L2T ball3))
    (hy : y ∈ (symComplexD isOpen_ball3 isBounded_ball3).domL)
    (hyK : y ∈ Kc (L2 ball3) (TSDS ball3) (TSDT ball3)) : ⟪y, Nvec⟫ = 0 := by
  have hD := (Feec.Constraints.mem_domL _).1 hy
  obtain ⟨-, -, hB⟩ := (mem_Kc).1 hyK
  rw [inner_tot, Nvec, tot_ini, inner_zero_right, inner_zero_right, zero_add, zero_add]
  have e := LinearPMap.adjoint_isFormalAdjoint (symComplexD isOpen_ball3 isBounded_ball3).dense1
    ⟨_, hD.2.2⟩ ⟨_, Qs_mem_d1.1⟩
  simp only at e
  rw [← e]
  exact inner_Qs_eq_zero (symComplexD_adjoint_d1_mem_TSDS isOpen_ball3 isBounded_ball3 _ hB)

/-- `⟪-L x₀, N⟫ = ⟪curl E₀, curl Q⟫`. -/
theorem inner_negL_x0 :
    ⟪(-(symComplexD isOpen_ball3 isBounded_ball3).waveOp) ⟨x0, x0_mem_domL⟩, Nvec⟫ =
      ⟪(symComplexD isOpen_ball3 isBounded_ball3).d1 ⟨_, E0_mem_d1.1⟩,
        (symComplexD isOpen_ball3 isBounded_ball3).d1 ⟨_, Qs_mem_d1.1⟩⟫ :=
  inner_negL_ini _ x0_mem_domL E0_mem_d1.1 _

/-- `⟪curl E₀, curl Q⟫ = 3 ∫_B (1 - 2x₀² - 2x₁² - 3x₂²)`. -/
theorem inner_curlE0_curlQ :
    ⟪(symComplexD isOpen_ball3 isBounded_ball3).d1 ⟨_, E0_mem_d1.1⟩,
        (symComplexD isOpen_ball3 isBounded_ball3).d1 ⟨_, Qs_mem_d1.1⟩⟫ =
      ∫ x in ball3, 3 * (1 - 2 * (x 0 * x 0) - 2 * (x 1 * x 1) - 3 * (x 2 * x 2)) := by
  rw [E0_mem_d1.2, Qs_mem_d1.2, Submodule.coe_inner]
  change ⟪smoothField isOpen_ball3 isBounded_ball3 (curlM eF)
      (continuous_curlM contDiff_one_eF), smoothField isOpen_ball3 isBounded_ball3 (curlM qExp)
      (continuous_curlM contDiff_one_qExp)⟫ = _
  rw [inner_smoothField, sum_integral_congr (coeFn_smoothField isOpen_ball3 isBounded_ball3 _
    (continuous_curlM contDiff_one_eF))]
  simp only [curlM_eF]
  have hint : ∀ ij : Ix, Integrable (fun x => Mc ij * curlM qExp ij x) (volume.restrict ball3) :=
    fun ij => integrable_ball3 (continuous_const.mul (continuous_curlM contDiff_one_qExp ij))
  rw [← integral_finsetSum _ fun ij _ => hint ij]
  simp only [sum_Mc_curlM_qExp]

/-- **`⟪-L x₀, N⟫ ≤ -(3/5) |B| < 0`**. -/
theorem inner_negL_x0_lt :
    ⟪(-(symComplexD isOpen_ball3 isBounded_ball3).waveOp) ⟨x0, x0_mem_domL⟩, Nvec⟫ ≤
      -(3 / 5 * volume.real ball3) := by
  rw [inner_negL_x0, inner_curlE0_curlQ]
  have hc : ∀ f : R3 → ℝ, Continuous f → Integrable f (volume.restrict ball3) := fun f hf =>
    integrable_ball3 hf
  have h1 : ∫ x in ball3, 3 * (1 - 2 * (x 0 * x 0) - 2 * (x 1 * x 1) - 3 * (x 2 * x 2)) ≤
      ∫ x in ball3, (3 - 6 * rho x) :=
    integral_mono (hc _ (by fun_prop)) (hc _ (by unfold rho; fun_prop)) fun x => by
      simp only [rho]; nlinarith [mul_self_nonneg (x 2)]
  have h2 : ∫ x in ball3, (3 - 6 * rho x) =
      3 * volume.real ball3 - 6 * (3 / 5 * volume.real ball3) := by
    rw [integral_sub (f := fun _ => (3 : ℝ)) (g := fun x => 6 * rho x) (hc _ continuous_const)
      (hc _ (continuous_const.mul continuous_rho)), integral_const_mul, integral_rho_ball3]
    simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
    ring
  linarith

theorem inner_negL_x0_ne_zero :
    ⟪(-(symComplexD isOpen_ball3 isBounded_ball3).waveOp) ⟨x0, x0_mem_domL⟩, Nvec⟫ ≠ 0 := by
  have h := inner_negL_x0_lt
  have hpos := volume_real_pos isOpen_ball3 isBounded_ball3 ball3_nonempty
  intro h0
  rw [h0] at h
  linarith

/-- **The mechanism**: `-L x₀ ∉ closure (D(L) ∩ K)`. `K` itself is invariant under `L` on
`D(L) ∩ K` (Lemma 3.5, `symComplexD_diagnosis`), but the closure of `D(L) ∩ K` is not, because
`N ⊥ D(L) ∩ K` while `⟪-L x₀, N⟫ ≠ 0`. -/
theorem negL_x0_not_mem_closure :
    (-(symComplexD isOpen_ball3 isBounded_ball3).waveOp) ⟨x0, x0_mem_domL⟩ ∉
      closure (((symComplexD isOpen_ball3 isBounded_ball3).domL : Set _) ∩
        (Kc (L2 ball3) (TSDS ball3) (TSDT ball3) : Set _)) := by
  intro hmem
  have hsub : ((symComplexD isOpen_ball3 isBounded_ball3).domL : Set _) ∩
      (Kc (L2 ball3) (TSDS ball3) (TSDT ball3) : Set _) ⊆ (fun y => ⟪y, Nvec⟫) ⁻¹' {0} :=
    fun y hy => inner_Nvec_eq_zero y hy.1 hy.2
  have h0 := closure_minimal hsub (isClosed_singleton.preimage (continuous_id.inner
    continuous_const)) hmem
  exact inner_negL_x0_ne_zero h0

/-- **The conclusion of Prop 4.19 fails for the boundary conditions as printed, on the unit
ball** (`symComplexD`, `D(L) = H² × (H(curl, S) ∩ H̊(div div, S)) × H̊(sym curl, T)`): the TSD
datum `(σ₀, E₀, B₀) = (0, E₀, 0)`, `E₀ = e₃ uᵀ + u e₃ᵀ`, `u = e₃ × x`, lies in `D(L) ∩ K`,
`K = {0} × L²(TSD) × L²(TSD)`, and for every `T > 0` every strong solution of (4.18) on `[0, T]`
from it leaves `K`. -/
theorem tsd_not_propagates :
    E0 ∈ TSDS ball3 ∧ x0 ∈ (symComplexD isOpen_ball3 isBounded_ball3).domL ∧
      x0 ∈ Kc (L2 ball3) (TSDS ball3) (TSDT ball3) ∧
      ∀ T > 0, ∀ U : ℝ → Tot (L2 ball3) (L2S ball3) (L2T ball3),
        IsStrongSolution (-(symComplexD isOpen_ball3 isBounded_ball3).waveOp) T x0 0 U →
          ∃ t ∈ Icc 0 T, U t ∉ Kc (L2 ball3) (TSDS ball3) (TSDT ball3) :=
  ⟨E0_mem_TSDS, x0_mem_domL, x0_mem_Kc,
    not_propagate_of_inner _ Nvec inner_Nvec_eq_zero x0_mem_domL inner_negL_x0_ne_zero⟩

/-- **Unconditional form**: on every `[0, T]`, `T > 0`, the Hodge wave equation (4.18) for
`symComplexD` on the unit ball has a strong solution from `x₀ = (0, E₀, 0)` (Stone's theorem,
`Feec.HilbertComplex2.waveGroup`), it is unique, and it leaves `K = {0} × L²(TSD) × L²(TSD)`;
the same holds for the variant `K = {0} × (L²(TSD) ∩ ker d0*) × L²(TSD)`, which has the same data
in `D(L)` (`symComplexD_mem_Kc_iff`).

Correction: [QuennevilleBelair2015, §4.11, Prop 4.19], with the boundary conditions of its
data space. -/
theorem not_propagates :
    E0 ∈ TSDS ball3 ∧ x0 ∈ (symComplexD isOpen_ball3 isBounded_ball3).domL ∧
      x0 ∈ Kc (L2 ball3) (TSDSk ball3 isOpen_ball3 isBounded_ball3) (TSDT ball3) ∧
      ∀ T > 0, IsStrongSolution (-(symComplexD isOpen_ball3 isBounded_ball3).waveOp) T x0 0
          (fun t => (symComplexD isOpen_ball3 isBounded_ball3).waveGroup.S t x0) ∧
        (∀ U, IsStrongSolution (-(symComplexD isOpen_ball3 isBounded_ball3).waveOp) T x0 0 U →
          EqOn U (fun t => (symComplexD isOpen_ball3 isBounded_ball3).waveGroup.S t x0)
            (Icc 0 T)) ∧
        ∃ t ∈ Icc 0 T, (symComplexD isOpen_ball3 isBounded_ball3).waveGroup.S t x0 ∉
          Kc (L2 ball3) (TSDS ball3) (TSDT ball3) := by
  set H := symComplexD isOpen_ball3 isBounded_ball3
  refine ⟨E0_mem_TSDS, x0_mem_domL,
    (symComplexD_mem_Kc_iff isOpen_ball3 isBounded_ball3 _ x0_mem_domL).1 x0_mem_Kc,
    fun T hT => ?_⟩
  have hU := isStrongSolution_orbit H.waveGroup T ⟨x0, x0_mem_domL⟩
  have skew := H.neg_waveOp_isSkewAdjoint.isSkewSymm H.neg_waveOp_isSkewAdjoint.dense_domain
  exact ⟨hU, fun U hU' => strongSolution_unique _ skew hU' hU,
    tsd_not_propagates.2.2.2 T hT _ hU⟩

/-- **The `TSDSk` variant, stated directly**: for `K = {0} × (L²(TSD) ∩ ker d0*) × L²(TSD)`,
the datum `x₀` lies in `D(L) ∩ K` and, for every `T > 0`, every strong solution of (4.18) on
`[0, T]` from `x₀` leaves `K` (it already leaves the larger `{0} × L²(TSD) × L²(TSD)`). -/
theorem tsdSk_not_propagates :
    x0 ∈ (symComplexD isOpen_ball3 isBounded_ball3).domL ∧
      x0 ∈ Kc (L2 ball3) (TSDSk ball3 isOpen_ball3 isBounded_ball3) (TSDT ball3) ∧
      ∀ T > 0, ∀ U : ℝ → Tot (L2 ball3) (L2S ball3) (L2T ball3),
        IsStrongSolution (-(symComplexD isOpen_ball3 isBounded_ball3).waveOp) T x0 0 U →
          ∃ t ∈ Icc 0 T, U t ∉ Kc (L2 ball3) (TSDSk ball3 isOpen_ball3 isBounded_ball3)
            (TSDT ball3) := by
  refine ⟨x0_mem_domL, not_propagates.2.2.1, fun T hT U hU => ?_⟩
  obtain ⟨t, ht, hnot⟩ := tsd_not_propagates.2.2.2 T hT U hU
  exact ⟨t, ht, fun h => hnot (Kc_mono inf_le_left le_rfl h)⟩

/-- **`K*` does not contain `D(L) ∩ K`** on the unit ball: `x₀ ∈ D(L) ∩ K` but `x₀ ∉ K*`, for
`K = {0} × (L²(TSD) ∩ ker d0*) × L²(TSD)` and the Hodge wave group of `symComplexD`. So the
maximal form `symComplexD_prop_4_19_max` is a strict restriction of the data of Prop 4.19. -/
theorem x0_not_mem_Kmax :
    x0 ∉ Kmax (symComplexD isOpen_ball3 isBounded_ball3).waveGroup
      (Kc (L2 ball3) (TSDSk ball3 isOpen_ball3 isBounded_ball3) (TSDT ball3)) := by
  intro h
  obtain ⟨-, -, -, hall⟩ := not_propagates
  obtain ⟨t, -, ht⟩ := (hall 1 one_pos).2.2
  exact ht (Kc_mono inf_le_left le_rfl (h t))

/-- **Density fails in the magnetic slot**: the constant field
`curl E₀ = diag(-1, -1, 2) ∈ L²(TSD)` is not in the closure of `L²(TSD) ∩ H̊(sym curl, T)`
(`⟪·, curl Q⟫` vanishes on that set, and `⟪curl E₀, curl Q⟫ ≤ -(3/5) |B|`). So
`L²(TSD) ∩ H̊(sym curl, T)` is not dense in `L²(TSD)` on the unit ball. -/
theorem curlE0_not_mem_closure :
    (symComplexD isOpen_ball3 isBounded_ball3).d1 ⟨_, E0_mem_d1.1⟩ ∈ TSDT ball3 ∧
      (symComplexD isOpen_ball3 isBounded_ball3).d1 ⟨_, E0_mem_d1.1⟩ ∉
        closure ((TSDT ball3 : Set (L2T ball3)) ∩
          (symComplexD isOpen_ball3 isBounded_ball3).d1†.domain) := by
  refine ⟨symComplexD_d1_mem_TSDT isOpen_ball3 isBounded_ball3 _ E0_mem_TSDS, fun hmem => ?_⟩
  set H := symComplexD isOpen_ball3 isBounded_ball3
  have hsub : (TSDT ball3 : Set (L2T ball3)) ∩ H.d1†.domain ⊆
      (fun B => ⟪B, H.d1 ⟨_, Qs_mem_d1.1⟩⟫) ⁻¹' {0} := by
    rintro B ⟨hB, hD⟩
    have e := LinearPMap.adjoint_isFormalAdjoint H.dense1 ⟨_, hD⟩ ⟨_, Qs_mem_d1.1⟩
    simp only at e
    simp only [mem_preimage, mem_singleton_iff]
    rw [← e]
    exact inner_Qs_eq_zero (symComplexD_adjoint_d1_mem_TSDS isOpen_ball3 isBounded_ball3 _ hB)
  have h0 := closure_minimal hsub (isClosed_singleton.preimage (continuous_id.inner
    continuous_const)) hmem
  simp only [mem_preimage, mem_singleton_iff] at h0
  have h := inner_negL_x0_ne_zero
  rw [inner_negL_x0] at h
  exact h h0

end Feec.Counterexamples.BallSymTSD
