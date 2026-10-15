module

public import Feec.Ch4.BoundedDomainExt
public import Feec.Ch4.StoneApplications
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Interior TSD propagation (finite speed of propagation)

On a bounded open `Ω ⊆ ℝ³`, TSD propagation (the conclusion of thesis Prop 4.17,
[QuennevilleBelair2015, §4.10]) fails for the system (4.14) of the complex
`H̊¹ → H̊(curl) → L²` (`Feec.BoundedDomain.thesisComplex_not_propagate`): the electric boundary
condition creates a TSD violation at `∂Ω`. This file proves that the violation cannot enter the
**domain of dependence**: for TSD data, the solution stays TSD at time `t` at every point whose
Euclidean distance to `ℝ³ \ Ω` exceeds `t`. So the obstruction travels inward at most at unit
speed, and for the explicit datum `(0, 0, β)` it is confined to the boundary layer of width `t`
and nonzero there.

The interior argument uses no boundary condition and no boundedness: `WeakEB.ae_viol_eq_zero`
and `WeakEB.ae_viol_eq_zero_depDomain` hold on every open `Ω ⊆ ℝ³`, bounded or not. For
`Ω = ℝ³` the domain of dependence is all of `ℝ³`, which gives global TSD propagation on the
whole space (`WeakEB.mem_TSD_univ`). Boundedness and the boundary condition `H̊(curl)` enter only
through the thesis' complex `thesisComplex`: its existence theory and the boundary-layer
violation.

## The mathematics

1. *Constraints that propagate globally.* Prop 4.18 (i) gives `σ ≡ 0`, `div E ≡ 0` and the
   reduced system `Ė = -curl* B`, `Ḃ = curl E`; `∂_t div B = div curl E = 0`, so `div B ≡ 0`
   (`weakEB_of_strongSolution`). In the interior, tested against `C_c^∞(Ω; ℝ³ˣ³)`, both curls are
   the classical curl (`WeakEB`); no boundary condition enters.
2. *The violation system.* Let `a(X)_k = ε_{kij} X_{ij}` (twice the axial vector of `skw X`) and
   `τ(X) = tr X`. The distributional Lemma 3.5 identities are `τ(curl Y) = -div a(Y)`, which holds
   for every `Y ∈ L²` (`sum_integral_curlM_cTr`), and `a(curl Y) = ∇τ(Y) + curl a(Y)`, which holds
   for weakly divergence-free `Y` (`sum_integral_curlM_cAx`). So `W = (a_E, τ_E, a_B, τ_B)`
   solves, weakly in `Ω`, the closed first-order system
   `∂_t a_E = -∇τ_B - curl a_B`, `∂_t τ_E = div a_B`, `∂_t a_B = ∇τ_E + curl a_E`,
   `∂_t τ_B = -div a_E` (`WeakEB.deriv_axE`, …; the closed system of Prop 3.6,
   cf. `Feec.violation_evolution`). It has the energy identity `½ ∂_t |W|² = div F(W)`,
   `F = a_E × a_B - τ_B a_E + τ_E a_B` (`energy_identity`), and unit speed:
   `|2 ξ · F(W)| ≤ |ξ| |W|²` (`abs_two_flux_le`).
3. *Mollification.* `W` is only `L²` in space. Convolving with a smooth kernel `ρ` supported in
   `B̄(0, ε)` gives `W_ε(t, y) = ⟨W(t), ρ(y - ·)⟩`, smooth in `y` (`mol`, `contDiff_mol`,
   `pd_mol`), which solves the violation system classically wherever `B̄(y, ε) ⊆ Ω`, because
   `ρ(y - ·)` is then a test function (`hasDerivAt_mA_E`, …).
4. *Local energy estimate.* With the cone weight `ψ(t, y) = χ(R - t - √(δ² + |y - x|²))`
   (`χ` the smooth transition; `|∇ψ| ≤ -∂_t ψ`, `sum_pd_wt_sq_le`), the energy
   `e(t) = ∫ ψ |W_ε|²` satisfies `e' = ∫ (∂_t ψ |W_ε|² - 2 ∇ψ · F(W_ε)) ≤ 0` (differentiation under
   the integral, integration by parts), and `e(0) = 0`; so `W_ε` vanishes on the cone
   (`Nf_eq_zero_of_cone`).
5. *Removing the mollifier.* Letting `ε → 0`, Lebesgue differentiation
   (`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`) gives `W(t) = 0` a.e. on
   `{|y - x| < r - t}` whenever `{|z - x| < r} ⊆ Ω` (`WeakEB.ae_viol_eq_zero`), and a countable
   cover gives the statement on the whole domain of dependence (`WeakEB.ae_viol_eq_zero_depDomain`,
   `thesisComplex_TSD_depDomain`). Local integrability `L² ⊆ L¹_loc` and the Cauchy–Schwarz bound
   `|X ⋆ ρ| ≤ ‖ρ‖_{L²(ℝ³)} ‖X‖` replace any finiteness of `|Ω|`.

## Main results

* `thesisComplex_TSD_cone`: for every strong solution of (4.14) with TSD data and every Euclidean
  ball `{|z - x| < r} ⊆ Ω`, at time `t ∈ [0, T]`: `σ(t) = 0`, `E(t)`, `B(t)` are weakly
  divergence-free in `Ω`, and symmetric and trace-free a.e. on `{|y - x| < r - t}`.
* `thesisComplex_TSD_depDomain`: the same a.e. on `depDomain Ω t` (distance to `ℝ³ \ Ω` larger
  than `t`); `thesisComplex_TSD_depDomain_exists`: with existence and uniqueness of the solution
  (Stone's theorem).
* `thesisComplex_TSD_depDomain_distrib` (distributional form: `∫_Ω (E_{ij} - E_{ji}) g = 0`,
  `∫_Ω (tr E) g = 0` for `g` supported in `depDomain Ω t`) and `thesisComplex_TSD_depDomain_local`
  (the restrictions of `E(t)`, `B(t)` to `depDomain Ω t` lie in `L²(TSD)(depDomain Ω t)`).
* `thesisComplex_beta_violation_boundary_layer`: for the explicit datum `(0, 0, β)`,
  `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)` (`betaL2`), the unique solution is TSD on `depDomain Ω t` for all
  `t ∈ [0, T]` but, for some `t ∈ [0, T]`, not symmetric and trace-free on a non-null subset of
  `Ω \ depDomain Ω t` (`thesisComplex_violation_boundary_layer`: existential-datum form).
* Abstract core, on any open `Ω ⊆ ℝ³`: `WeakEB.ae_viol_eq_zero` (any `L²` pair `E, B` with the
  interior weak equations, divergence-free, with vanishing initial violation),
  `WeakEB.ae_viol_eq_zero_depDomain`, `Nf_eq_zero_of_cone` (mollified form). Whole space:
  `WeakEB.ae_symTF_univ`, `WeakEB.mem_TSD_univ`.

## Model and conventions

As in `Feec.Ch4.BoundedDomain`: `L²(Ω; ℝ³ˣ³) = L2M Ω` (nine copies of `L²(Ω)`), test functions
`IsTest`, row-wise curl `curlM`. `R3 = Fin 3 → ℝ` carries the sup metric, so Euclidean balls are
written with `dist₂`. Symmetry and trace-freeness are stated pointwise a.e. for representatives
(`SymTF`); with the global divergence-free property this is `L²(TSD)` locally
(`resM_mem_TSD`; `mem_TSD_of_ae_symTF` for the global version).

## Thesis gap

The thesis does not discuss domains of dependence; Prop 4.17 asserts global TSD propagation, which
fails on bounded domains. What survives is local: TSD propagates in the interior at unit speed,
and the boundary obstruction is confined to the layer `{dist(·, ∂Ω) ≤ t}`. Not proved here: that
the violation actually reaches distance `t` from `∂Ω` (sharpness of the unit speed); only its
existence somewhere in the layer, at some time in every `[0, T]`, is shown. On `ℝ³`,
`WeakEB.mem_TSD_univ` assumes the interior equations (`WeakEB`) and does not construct the
solution; the Fourier model of the whole space is in `Feec.Ch4.WholeSym`.

## References

* [QuennevilleBelair2015], §3.4 (Lemma 3.5, Prop 3.6), §4.10 (Prop 4.17, Prop 4.18, (4.14))
* [Brezis2011] (mollifiers, Lebesgue points, the fundamental lemma of the calculus of variations)
* [ACBY1997] (the Einstein–Bianchi system)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal ContDiff Matrix
open MeasureTheory Set Filter Topology

namespace Feec.BoundedDomain

/-! ## Pointwise algebra of the violation system -/

/-- The energy density `|W|² = |a_E|² + τ_E² + |a_B|² + τ_B²` of a violation vector
`W = (a_E, τ_E, a_B, τ_B) ∈ ℝ³ × ℝ × ℝ³ × ℝ`. -/
def dens (aE aB : Fin 3 → ℝ) (τE τB : ℝ) : ℝ :=
  ∑ k, aE k ^ 2 + τE ^ 2 + ∑ k, aB k ^ 2 + τB ^ 2

/-- The energy flux `F = a_E × a_B - τ_B a_E + τ_E a_B` (component `c`). -/
def vflux (aE aB : Fin 3 → ℝ) (τE τB : ℝ) (c : Fin 3) : ℝ :=
  aE (c + 1) * aB (c + 2) - aE (c + 2) * aB (c + 1) - τB * aE c + τE * aB c

theorem dens_nonneg (aE aB : Fin 3 → ℝ) (τE τB : ℝ) : 0 ≤ dens aE aB τE τB := by
  unfold dens; positivity

theorem eq_zero_of_dens_eq_zero {aE aB : Fin 3 → ℝ} {τE τB : ℝ} (h : dens aE aB τE τB = 0) :
    (∀ k, aE k = 0) ∧ τE = 0 ∧ (∀ k, aB k = 0) ∧ τB = 0 := by
  simp only [dens, Fin.sum_univ_three] at h
  have h0 := sq_nonneg (aE 0); have h1 := sq_nonneg (aE 1); have h2 := sq_nonneg (aE 2)
  have h3 := sq_nonneg (aB 0); have h4 := sq_nonneg (aB 1); have h5 := sq_nonneg (aB 2)
  have h6 := sq_nonneg τE; have h7 := sq_nonneg τB
  refine ⟨fun k => ?_, by nlinarith, fun k => ?_, by nlinarith⟩
  · fin_cases k <;> simp <;> nlinarith
  · fin_cases k <;> simp <;> nlinarith

/-- Cauchy–Schwarz in `ℝ⁴`. -/
theorem sq_dot4_le (u0 u1 u2 u3 v0 v1 v2 v3 : ℝ) :
    (u0 * v0 + u1 * v1 + u2 * v2 + u3 * v3) ^ 2 ≤
      (u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * (v0 ^ 2 + v1 ^ 2 + v2 ^ 2 + v3 ^ 2) := by
  have e : (u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * (v0 ^ 2 + v1 ^ 2 + v2 ^ 2 + v3 ^ 2) -
      (u0 * v0 + u1 * v1 + u2 * v2 + u3 * v3) ^ 2 = (u0 * v1 - u1 * v0) ^ 2 +
      (u0 * v2 - u2 * v0) ^ 2 + (u0 * v3 - u3 * v0) ^ 2 + (u1 * v2 - u2 * v1) ^ 2 +
      (u1 * v3 - u3 * v1) ^ 2 + (u2 * v3 - u3 * v2) ^ 2 := by ring
  have : 0 ≤ (u0 * v1 - u1 * v0) ^ 2 + (u0 * v2 - u2 * v0) ^ 2 + (u0 * v3 - u3 * v0) ^ 2 +
      (u1 * v2 - u2 * v1) ^ 2 + (u1 * v3 - u3 * v1) ^ 2 + (u2 * v3 - u3 * v2) ^ 2 := by
    positivity
  linarith

/-- From `P² ≤ U (s V)`, `s ≤ c²`: `|2P| ≤ c (U + V)`. -/
theorem abs_two_le_of_sq_le {P U V s c : ℝ} (h : P ^ 2 ≤ U * (s * V)) (hs : s ≤ c ^ 2)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hc : 0 ≤ c) : |2 * P| ≤ c * (U + V) := by
  have h1 : P ^ 2 ≤ c ^ 2 * (U * V) := by
    calc P ^ 2 ≤ U * (s * V) := h
      _ ≤ U * (c ^ 2 * V) := by gcongr
      _ = c ^ 2 * (U * V) := by ring
  have h4 : 4 * (U * V) ≤ (U + V) ^ 2 := by nlinarith [sq_nonneg (U - V)]
  have h2 : (2 * P) ^ 2 ≤ (c * (U + V)) ^ 2 := by
    have : c ^ 2 * (4 * (U * V)) ≤ c ^ 2 * (U + V) ^ 2 := by gcongr
    nlinarith
  exact abs_le_of_sq_le_sq' h2 (by positivity) |> fun h => abs_le.2 ⟨h.1, h.2⟩

/-- **Unit propagation speed** of the violation system: `|2 ξ · F(W)| ≤ c |W|²` whenever
`|ξ| ≤ c`. (The symbol of the violation operator is `[[0, J_ξ], [-J_ξ, 0]]` with `J_ξ` skew and
`|J_ξ w| = |ξ| |w|`.) -/
theorem abs_two_flux_le (ξ aE aB : Fin 3 → ℝ) (τE τB c : ℝ) (hc : 0 ≤ c)
    (hξ : ∑ k, ξ k ^ 2 ≤ c ^ 2) :
    |2 * ∑ k, ξ k * vflux aE aB τE τB k| ≤ c * dens aE aB τE τB := by
  have hcs := sq_dot4_le (aE 0) (aE 1) (aE 2) τE (aB 1 * ξ 2 - aB 2 * ξ 1 - τB * ξ 0)
    (aB 2 * ξ 0 - aB 0 * ξ 2 - τB * ξ 1) (aB 0 * ξ 1 - aB 1 * ξ 0 - τB * ξ 2)
    (ξ 0 * aB 0 + ξ 1 * aB 1 + ξ 2 * aB 2)
  have e1 : ∑ k, ξ k * vflux aE aB τE τB k = aE 0 * (aB 1 * ξ 2 - aB 2 * ξ 1 - τB * ξ 0) +
      aE 1 * (aB 2 * ξ 0 - aB 0 * ξ 2 - τB * ξ 1) + aE 2 * (aB 0 * ξ 1 - aB 1 * ξ 0 - τB * ξ 2) +
      τE * (ξ 0 * aB 0 + ξ 1 * aB 1 + ξ 2 * aB 2) := by
    simp only [vflux, Fin.sum_univ_three]
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
      show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
      show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
    ring
  have e2 : (aB 1 * ξ 2 - aB 2 * ξ 1 - τB * ξ 0) ^ 2 + (aB 2 * ξ 0 - aB 0 * ξ 2 - τB * ξ 1) ^ 2 +
      (aB 0 * ξ 1 - aB 1 * ξ 0 - τB * ξ 2) ^ 2 + (ξ 0 * aB 0 + ξ 1 * aB 1 + ξ 2 * aB 2) ^ 2 =
      (∑ k, ξ k ^ 2) * (aB 0 ^ 2 + aB 1 ^ 2 + aB 2 ^ 2 + τB ^ 2) := by
    simp only [Fin.sum_univ_three]; ring
  have e3 : dens aE aB τE τB = (aE 0 ^ 2 + aE 1 ^ 2 + aE 2 ^ 2 + τE ^ 2) +
      (aB 0 ^ 2 + aB 1 ^ 2 + aB 2 ^ 2 + τB ^ 2) := by
    simp only [dens, Fin.sum_univ_three]; ring
  rw [e1, e3]
  rw [e2] at hcs
  exact abs_two_le_of_sq_le hcs hξ (by positivity) (by positivity) hc

/-! ## The cone weight -/

/-- The Euclidean distance on `ℝ³` (`R3 = Fin 3 → ℝ` carries the sup metric). -/
def dist₂ (y x : R3) : ℝ := Real.sqrt (∑ i, (y i - x i) ^ 2)

theorem abs_sub_le_dist₂ (y x : R3) (i : Fin 3) : |y i - x i| ≤ dist₂ y x := by
  rw [dist₂, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => (y i - x i) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ i))

theorem dist_le_dist₂ (y x : R3) : dist y x ≤ dist₂ y x := by
  refine (dist_pi_le_iff (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.dist_eq]
  exact abs_sub_le_dist₂ y x i

theorem dist₂_eq (y x : R3) : dist₂ y x = dist (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 3))
    (WithLp.toLp 2 x) := by
  rw [EuclideanSpace.dist_eq, dist₂]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.dist_eq, sq_abs]

theorem dist₂_triangle (y z x : R3) : dist₂ y x ≤ dist₂ y z + dist₂ z x := by
  simp only [dist₂_eq]; exact dist_triangle _ _ _

theorem dist₂_comm (y x : R3) : dist₂ y x = dist₂ x y := by
  simp only [dist₂_eq]; exact dist_comm _ _

@[simp] theorem dist₂_self (x : R3) : dist₂ x x = 0 := by simp [dist₂]

theorem dist₂_le_two_dist (y x : R3) : dist₂ y x ≤ 2 * dist y x := by
  rw [dist₂, Real.sqrt_le_left (by positivity)]
  have h : ∀ i, (y i - x i) ^ 2 ≤ dist y x ^ 2 := fun i => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (by
      rw [← Real.dist_eq]; exact dist_le_pi_dist y x i) 2
  simp only [Fin.sum_univ_three]
  nlinarith [h 0, h 1, h 2, sq_nonneg (dist y x)]

theorem continuous_dist₂ (x : R3) : Continuous fun y => dist₂ y x := by
  unfold dist₂; fun_prop

theorem isOpen_ball₂ (x : R3) (r : ℝ) : IsOpen {y | dist₂ y x < r} :=
  isOpen_lt (continuous_dist₂ x) continuous_const

/-- The regularized distance `q(y) = √(δ² + |y - x|²)`. -/
def qd (x : R3) (δ : ℝ) (y : R3) : ℝ := Real.sqrt (δ ^ 2 + ∑ i, (y i - x i) ^ 2)

variable {x : R3} {δ : ℝ}

theorem qd_pos (hδ : 0 < δ) (y : R3) : 0 < qd x δ y :=
  Real.sqrt_pos.2 (by positivity)

theorem dist₂_le_qd (y : R3) : dist₂ y x ≤ qd x δ y :=
  Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])

theorem qd_le (hδ : 0 ≤ δ) (y : R3) : qd x δ y ≤ dist₂ y x + δ := by
  rw [qd, dist₂]
  rw [Real.sqrt_le_left (by positivity)]
  have h := Real.sq_sqrt (show 0 ≤ ∑ i, (y i - x i) ^ 2 by positivity)
  nlinarith [Real.sqrt_nonneg (∑ i, (y i - x i) ^ 2)]

theorem hasFDerivAt_qd (hδ : 0 < δ) (y : R3) :
    HasFDerivAt (qd x δ) ((1 / (2 * qd x δ y)) • ∑ i, (2 * (y i - x i)) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i) y := by
  have hg : HasFDerivAt (fun y : R3 => δ ^ 2 + ∑ i, (y i - x i) ^ 2)
      (∑ i, (2 * (y i - x i)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i)
      y := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) (A := fun i (y : R3) => (y i - x i) ^ 2)
      (A' := fun i => (2 * (y i - x i)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i) (x := y) (fun i _ => by
        have h1 := ((hasFDerivAt_apply (𝕜 := ℝ) i y).sub_const (x i)).pow 2
        convert h1 using 1
        ext v; simp)
    exact this.const_add _
  exact hg.sqrt (by positivity)

theorem pd_qd (hδ : 0 < δ) (k : Fin 3) (y : R3) :
    pd k (qd x δ) y = (y k - x k) / qd x δ y := by
  rw [pd_of_hasFDerivAt (hasFDerivAt_qd hδ y)]
  simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k (fun i _ hik => by simp [hik]) (by simp)]
  simp only [Pi.single_eq_same, mul_one]
  field_simp

theorem contDiff_qd (hδ : 0 < δ) : ContDiff ℝ ∞ (qd x δ) := by
  unfold qd
  refine ContDiff.sqrt (by fun_prop) fun y => ?_
  positivity

theorem sum_pd_qd_sq_le_one (hδ : 0 < δ) (y : R3) : ∑ k, pd k (qd x δ) y ^ 2 ≤ 1 := by
  simp only [pd_qd hδ, div_pow]
  rw [← Finset.sum_div, div_le_one (by have := qd_pos (x := x) hδ y; positivity), qd,
    Real.sq_sqrt (by positivity)]
  nlinarith [sq_nonneg δ]

/-- The cone weight `ψ(t, y) = χ(R - t - q(y))`, `χ` the smooth transition (`0` on `(-∞, 0]`,
`1` on `[1, ∞)`, nondecreasing). -/
def wt (x : R3) (δ R t : ℝ) (y : R3) : ℝ := Real.smoothTransition (R - t - qd x δ y)

/-- `χ'`. -/
def dχ (s : ℝ) : ℝ := deriv Real.smoothTransition s

theorem dχ_nonneg (s : ℝ) : 0 ≤ dχ s := Real.smoothTransition.monotone.deriv_nonneg

theorem hasDerivAt_χ (s : ℝ) : HasDerivAt Real.smoothTransition (dχ s) s :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero s).hasDerivAt

theorem continuous_dχ : Continuous dχ :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

theorem dχ_eq_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) : dχ s = 0 := by
  -- `χ` vanishes on `(-∞, 0]`, so `χ' = 0` there (left derivative at `0`)
  have h := hasDerivAt_χ s
  have hl : HasDerivWithinAt Real.smoothTransition 0 (Iic s) s :=
    (hasDerivWithinAt_const s (Iic s) (0 : ℝ)).congr
      (fun y hy => Real.smoothTransition.zero_of_nonpos (le_trans hy hs))
      (Real.smoothTransition.zero_of_nonpos hs)
  exact (uniqueDiffWithinAt_Iic s).eq_deriv _ (h.hasDerivWithinAt) hl

theorem wt_nonneg (R t : ℝ) (y : R3) : 0 ≤ wt x δ R t y := Real.smoothTransition.nonneg _

theorem wt_le_one (R t : ℝ) (y : R3) : wt x δ R t y ≤ 1 := Real.smoothTransition.le_one _

theorem wt_eq_zero {R t : ℝ} {y : R3} (h : R - t ≤ qd x δ y) : wt x δ R t y = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem wt_pos {R t : ℝ} {y : R3} (h : qd x δ y < R - t) : 0 < wt x δ R t y :=
  Real.smoothTransition.pos_of_pos (by linarith)

/-- `ψ(t, ·)` vanishes off the sup-ball `closedBall x |R - t|`. -/
theorem wt_eq_zero_of_notMem {R t : ℝ} {y : R3} (hy : y ∉ Metric.closedBall x |R - t|) :
    wt x δ R t y = 0 := by
  apply wt_eq_zero
  rw [Metric.mem_closedBall, not_le] at hy
  have := (dist_le_dist₂ y x).trans (dist₂_le_qd (δ := δ) y)
  linarith [le_abs_self (R - t)]

theorem contDiff_wt (hδ : 0 < δ) (R t : ℝ) : ContDiff ℝ ∞ (wt x δ R t) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_qd hδ))

theorem hasCompactSupport_wt (R t : ℝ) : HasCompactSupport (wt x δ R t) :=
  HasCompactSupport.intro (isCompact_closedBall x |R - t|) fun _ hy => wt_eq_zero_of_notMem hy

theorem isTest_wt (hδ : 0 < δ) (R t : ℝ) : IsTest univ (wt x δ R t) :=
  ⟨contDiff_wt hδ R t, hasCompactSupport_wt R t, subset_univ _⟩

theorem pd_wt (hδ : 0 < δ) (R t : ℝ) (k : Fin 3) (y : R3) :
    pd k (wt x δ R t) y = -dχ (R - t - qd x δ y) * pd k (qd x δ) y := by
  have h := (hasDerivAt_χ (R - t - qd x δ y)).comp_hasFDerivAt y
    ((hasFDerivAt_const (R - t) y).sub (hasFDerivAt_qd (x := x) hδ y))
  have h' : HasFDerivAt (wt x δ R t) _ y := h
  rw [pd_of_hasFDerivAt h', pd_of_hasFDerivAt (hasFDerivAt_qd (x := x) hδ y)]
  simp [dχ]

/-- `|∇ψ| ≤ -∂_t ψ = χ'`: the weight is adapted to unit speed. -/
theorem sum_pd_wt_sq_le (hδ : 0 < δ) (R t : ℝ) (y : R3) :
    ∑ k, pd k (wt x δ R t) y ^ 2 ≤ dχ (R - t - qd x δ y) ^ 2 := by
  simp only [pd_wt hδ, mul_pow, neg_sq, ← Finset.mul_sum]
  calc dχ (R - t - qd x δ y) ^ 2 * ∑ k, pd k (qd x δ) y ^ 2
      ≤ dχ (R - t - qd x δ y) ^ 2 * 1 := by gcongr; exact sum_pd_qd_sq_le_one hδ y
    _ = _ := mul_one _

theorem hasDerivAt_wt_time (R t : ℝ) (y : R3) :
    HasDerivAt (fun s => wt x δ R s y) (-dχ (R - t - qd x δ y)) t := by
  have := (hasDerivAt_χ (R - t - qd x δ y)).comp t
    (((hasDerivAt_id t).const_sub R).sub_const (qd x δ y))
  simpa [wt, Function.comp_def] using this

theorem continuous_qd (hδ : 0 < δ) : Continuous (qd x δ) := (contDiff_qd hδ).continuous

theorem dχ_eq_zero_of_one_le {s : ℝ} (hs : 1 ≤ s) : dχ s = 0 := by
  have h := hasDerivAt_χ s
  have hl : HasDerivWithinAt Real.smoothTransition 0 (Ici s) s :=
    (hasDerivWithinAt_const s (Ici s) (1 : ℝ)).congr
      (fun y hy => Real.smoothTransition.one_of_one_le (le_trans hs hy))
      (Real.smoothTransition.one_of_one_le hs)
  exact (uniqueDiffWithinAt_Ici s).eq_deriv _ (h.hasDerivWithinAt) hl

theorem exists_abs_dχ_le : ∃ D, ∀ s, |dχ s| ≤ D := by
  have hc : HasCompactSupport dχ := HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ))
    (b := 1)) fun s hs => by
      rw [mem_Icc, not_and_or, not_le, not_le] at hs
      rcases hs with hs | hs
      · exact dχ_eq_zero_of_nonpos hs.le
      · exact dχ_eq_zero_of_one_le hs.le
  obtain ⟨D, hD⟩ := continuous_dχ.bounded_above_of_compact_support hc
  exact ⟨D, fun s => by simpa using hD s⟩

/-- Away from the cone base (`|y - x| ≥ R`), the weight and its time derivative vanish for
`s ≥ 0`. -/
theorem wt_far {R s : ℝ} (hs : 0 ≤ s) {y : R3} (hy : R ≤ dist₂ y x) :
    wt x δ R s y = 0 ∧ dχ (R - s - qd x δ y) = 0 := by
  have := dist₂_le_qd (δ := δ) (x := x) y
  exact ⟨wt_eq_zero (by linarith), dχ_eq_zero_of_nonpos (by linarith)⟩

theorem pd_wt_far (hδ : 0 < δ) {R s : ℝ} (hs : 0 ≤ s) {y : R3} (hy : R ≤ dist₂ y x) (c : Fin 3) :
    pd c (wt x δ R s) y = 0 := by
  rw [pd_wt hδ, (wt_far hs hy).2]; simp

theorem le_dist₂_of_notMem {R : ℝ} {y : R3} (hy : y ∉ Metric.closedBall x R) : R ≤ dist₂ y x := by
  rw [Metric.mem_closedBall, not_le] at hy
  exact hy.le.trans (dist_le_dist₂ y x)

/-- A continuous function vanishing off a sup-ball is integrable. -/
theorem integrable_of_eq_zero_off {f : R3 → ℝ} (hf : Continuous f) {R : ℝ}
    (h0 : ∀ y, y ∉ Metric.closedBall x R → f y = 0) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedBall x R) h0)

/-! ## Mollification of `L²(Ω)` functions -/

section Mollify

variable {Ω : Set R3}

/-- Extension by zero of `X ∈ L²(Ω)` to `ℝ³`. -/
def ext0 (X : L2 Ω) : R3 → ℝ := Ω.indicator (X : R3 → ℝ)

/-- `X ∈ L²(Ω)` extended by zero is locally integrable on `ℝ³` (`L² ⊆ L¹_loc`); no boundedness
of `Ω` is needed. -/
theorem locallyIntegrable_ext0 (hΩ : IsOpen Ω) (X : L2 Ω) : LocallyIntegrable (ext0 X) :=
  ((memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).2
    (Lp.memLp X)).locallyIntegrable (by norm_num)

/-- Mollification `(X ⋆ ρ)(y) = ∫_Ω X(z) ρ(y - z) dz` (`X` extended by zero). -/
def mol (ρ : R3 → ℝ) (X : L2 Ω) : R3 → ℝ :=
  convolution (ext0 X) ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume

theorem mol_apply (hΩ : IsOpen Ω) (ρ : R3 → ℝ) (X : L2 Ω) (y : R3) :
    mol ρ X y = ∫ z, X z * ρ (y - z) ∂volume.restrict Ω := by
  rw [mol, convolution_def, ← integral_indicator hΩ.measurableSet]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, ext0]
  rw [indicator_mul_left]

theorem contDiff_mol (hΩ : IsOpen Ω) {ρ : R3 → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hcρ : HasCompactSupport ρ) (X : L2 Ω) : ContDiff ℝ 1 (mol ρ X) := by
  have := hcρ.contDiff_convolution_right (n := 1) (ContinuousLinearMap.lsmul ℝ ℝ)
    (locallyIntegrable_ext0 hΩ X) (by exact_mod_cast hρ)
  exact_mod_cast this

theorem pd_mol (hΩ : IsOpen Ω) {ρ : R3 → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hcρ : HasCompactSupport ρ) (X : L2 Ω) (k : Fin 3) (y : R3) :
    pd k (mol ρ X) y = mol (pd k ρ) X y := by
  have h : HasFDerivAt (mol ρ X) _ y := hcρ.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) (locallyIntegrable_ext0 hΩ X) hρ y
  rw [pd, h.fderiv, convolution_precompR_apply (𝕜 := ℝ) (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (locallyIntegrable_ext0 hΩ X) (hcρ.fderiv (𝕜 := ℝ))
    (hρ.continuous_fderiv one_ne_zero)]
  rfl

theorem mol_zero (hΩ : IsOpen Ω) (ρ : R3 → ℝ) (y : R3) : mol ρ (0 : L2 Ω) y = 0 := by
  rw [mol_apply hΩ]
  have : (fun z => (0 : L2 Ω) z * ρ (y - z)) =ᵐ[volume.restrict Ω] fun _ => 0 := by
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with z hz
    rw [hz, Pi.zero_apply, zero_mul]
  rw [integral_congr_ae this, integral_zero]

/-- The reflected, translated kernel `z ↦ ρ(y - z)` is in `L²(ℝ³)`. -/
theorem memLp_ker {ρ : R3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (y : R3) :
    MemLp (fun z => ρ (y - z)) 2 volume :=
  (hρ.comp (continuous_const.sub continuous_id)).memLp_of_hasCompactSupport
    (hcρ.comp_homeomorph (Homeomorph.subLeft y))

theorem eLpNorm_ker {ρ : R3 → ℝ} (hρ : Continuous ρ) (y : R3) :
    eLpNorm (fun z => ρ (y - z)) 2 volume = eLpNorm ρ 2 volume :=
  eLpNorm_comp_measurePreserving (g := ρ) (f := fun z => y - z) hρ.aestronglyMeasurable
    (Measure.measurePreserving_sub_left volume y)

/-- The reflected, translated kernel `z ↦ ρ(y - z)` as an element of `L²(Ω)`. -/
def kerL {ρ : R3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (y : R3) : L2 Ω :=
  ((memLp_ker hρ hcρ y).restrict Ω).toLp _

/-- `‖ρ(y - ·)‖_{L²(Ω)} ≤ ‖ρ‖_{L²(ℝ³)}`, uniformly in `y`. -/
theorem norm_kerL_le {ρ : R3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (y : R3) :
    ‖(kerL hρ hcρ y : L2 Ω)‖ ≤ (eLpNorm ρ 2 volume).toReal := by
  rw [kerL, Lp.norm_toLp, ← eLpNorm_ker hρ y]
  exact ENNReal.toReal_mono (memLp_ker hρ hcρ y).eLpNorm_ne_top
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- `mol` as an inner product with the reflected, translated kernel. -/
theorem mol_eq_inner (hΩ : IsOpen Ω) {ρ : R3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) (X : L2 Ω) (y : R3) : mol ρ X y = ⟪X, kerL hρ hcρ y⟫ := by
  rw [mol_apply hΩ]
  exact integral_mul_eq_inner X _

/-- Uniform bound `|mol ρ X y| ≤ ‖ρ‖_{L²(ℝ³)} ‖X‖` (Cauchy–Schwarz; any open `Ω`). -/
theorem exists_abs_mol_le (hΩ : IsOpen Ω) {ρ : R3 → ℝ}
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) :
    ∃ M, 0 ≤ M ∧ ∀ (X : L2 Ω) y, |mol ρ X y| ≤ M * ‖X‖ := by
  refine ⟨(eLpNorm ρ 2 volume).toReal, ENNReal.toReal_nonneg, fun X y => ?_⟩
  rw [mol_eq_inner hΩ hρ hcρ]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [mul_comm]
  gcongr
  exact norm_kerL_le hρ hcρ y

end Mollify

/-! ## The violation fields and their weak curl identities -/

section Static

variable {Ω : Set R3}

/-- The axial vector of twice the skew part, `a(X)_k = X_{k+1,k+2} - X_{k+2,k+1} = ε_{kij} X_{ij}`
(indices mod 3). -/
def axV (X : L2M Ω) (k : Fin 3) : L2 Ω := X (k + 1, k + 2) - X (k + 2, k + 1)

/-- The trace `τ(X) = Σ_i X_{ii}`. -/
def trV (X : L2M Ω) : L2 Ω := ∑ i, X (i, i)

/-- `X` is pointwise symmetric and trace-free iff `a(X) = 0` and `τ(X) = 0`. -/
theorem symm_trace_iff (X : L2M Ω) :
    ((∀ i j, X (i, j) = X (j, i)) ∧ ∑ i, X (i, i) = 0) ↔ (∀ k, axV X k = 0) ∧ trV X = 0 := by
  refine ⟨fun ⟨h1, h2⟩ => ⟨fun k => by simp [axV, h1 (k + 1)], h2⟩, fun ⟨h1, h2⟩ => ⟨?_, h2⟩⟩
  have e0 : X (1, 2) = X (2, 1) := sub_eq_zero.1 (h1 0)
  have e1 : X (2, 0) = X (0, 2) := sub_eq_zero.1 (h1 1)
  have e2 : X (0, 1) = X (1, 0) := sub_eq_zero.1 (h1 2)
  intro i j
  fin_cases i <;> fin_cases j <;> simp [e0, e1, e2]

/-- Coefficient test fields `Φ_{ij} = c_{ij} ψ`. -/
def cT (c : Ix → ℝ) (ψ : R3 → ℝ) : Ix → R3 → ℝ := fun ij x => c ij * ψ x

/-- Coefficients of `ψ I` (pairs with the trace). -/
def cTr : Ix → ℝ := fun ij => if ij.1 = ij.2 then 1 else 0

/-- Coefficients of `ψ ε_{k··}` (pairs with `a_k`). -/
def cAx (k : Fin 3) : Ix → ℝ := fun ij =>
  (if ij = (k + 1, k + 2) then 1 else 0) - (if ij = (k + 2, k + 1) then 1 else 0)

theorem isTest_cT (c : Ix → ℝ) {ψ : R3 → ℝ} (hψ : IsTest Ω ψ) (ij : Ix) :
    IsTest Ω (cT c ψ ij) := hψ.const_mul (c ij)

theorem curlM_cT (c : Ix → ℝ) {ψ : R3 → ℝ} (hψ : Differentiable ℝ ψ) (ab : Ix) (x : R3) :
    curlM (cT c ψ) ab x = c (ab.1, ab.2 + 2) * pd (ab.2 + 1) ψ x -
      c (ab.1, ab.2 + 1) * pd (ab.2 + 2) ψ x := by
  unfold curlM cT
  rw [pd_const_mul hψ, pd_const_mul hψ]

/-- `∫ Y (c f - d g) = c ∫ Y f - d ∫ Y g`. -/
theorem integral_mul_sub_mul (Y : L2 Ω) {f g : R3 → ℝ} (hf : MemLp f 2 (volume.restrict Ω))
    (hg : MemLp g 2 (volume.restrict Ω)) (c d : ℝ) :
    ∫ x, Y x * (c * f x - d * g x) ∂volume.restrict Ω =
      c * ∫ x, Y x * f x ∂volume.restrict Ω - d * ∫ x, Y x * g x ∂volume.restrict Ω := by
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub ((integrable_mul Y hf).const_mul c) ((integrable_mul Y hg).const_mul d)]
  congr 1; ext x; ring

theorem sum_integral_cT (X : L2M Ω) (c : Ix → ℝ) (ψ : R3 → ℝ) :
    ∑ ij, ∫ x, X ij x * cT c ψ ij x ∂volume.restrict Ω =
      ∑ ij, c ij * ∫ x, X ij x * ψ x ∂volume.restrict Ω := by
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [← integral_const_mul]
  congr 1; ext x; simp only [cT]; ring

/-- `∫ τ(X) ψ = ⟨X, ψ I⟩`. -/
theorem integral_trV (X : L2M Ω) {ψ : R3 → ℝ} (hψ : MemLp ψ 2 (volume.restrict Ω)) :
    ∫ x, trV X x * ψ x ∂volume.restrict Ω =
      ∑ ij, ∫ x, X ij x * cT cTr ψ ij x ∂volume.restrict Ω := by
  rw [sum_integral_cT, integral_mul_eq_inner _ hψ, trV, sum_inner]
  simp only [← integral_mul_eq_inner _ hψ, cTr, Fintype.sum_prod_type, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- `∫ a(X)_k ψ = ⟨X, ψ ε_{k··}⟩`. -/
theorem integral_axV (X : L2M Ω) (k : Fin 3) {ψ : R3 → ℝ} (hψ : MemLp ψ 2 (volume.restrict Ω)) :
    ∫ x, axV X k x * ψ x ∂volume.restrict Ω =
      ∑ ij, ∫ x, X ij x * cT (cAx k) ψ ij x ∂volume.restrict Ω := by
  rw [sum_integral_cT, integral_mul_eq_inner _ hψ, axV, inner_sub_left,
    ← integral_mul_eq_inner _ hψ, ← integral_mul_eq_inner _ hψ]
  fin_cases k <;> simp [cAx, Fintype.sum_prod_type, Fin.sum_univ_three] <;> ring

theorem integral_axV_mul (Y : L2M Ω) (k : Fin 3) {f : R3 → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω)) :
    ∫ x, axV Y k x * f x ∂volume.restrict Ω = ∫ x, Y (k + 1, k + 2) x * f x ∂volume.restrict Ω -
      ∫ x, Y (k + 2, k + 1) x * f x ∂volume.restrict Ω := by
  rw [integral_mul_eq_inner _ hf, axV, inner_sub_left, ← integral_mul_eq_inner _ hf,
    ← integral_mul_eq_inner _ hf]

theorem integral_trV_mul (Y : L2M Ω) {f : R3 → ℝ} (hf : MemLp f 2 (volume.restrict Ω)) :
    ∫ x, trV Y x * f x ∂volume.restrict Ω = ∑ i, ∫ x, Y (i, i) x * f x ∂volume.restrict Ω := by
  rw [integral_mul_eq_inner _ hf, trV, sum_inner]
  simp only [← integral_mul_eq_inner _ hf]

/-- `⟨Y, curl (ψ I)⟩ = ⟨a(Y), ∇ψ⟩` (no condition on `Y`). -/
theorem sum_integral_curlM_cTr (Y : L2M Ω) {ψ : R3 → ℝ} (hψ : IsTest Ω ψ) :
    ∑ ab, ∫ x, Y ab x * curlM (cT cTr ψ) ab x ∂volume.restrict Ω =
      ∑ c, ∫ x, axV Y c x * pd c ψ x ∂volume.restrict Ω := by
  have hm : ∀ m, MemLp (pd m ψ) 2 (volume.restrict Ω) := fun m => (hψ.pdiff m).memLp
  simp_rw [curlM_cT cTr hψ.differentiable]
  simp only [integral_mul_sub_mul _ (hm _) (hm _), integral_axV_mul _ _ (hm _)]
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, cTr]
  ring

/-- For weakly divergence-free `Y`:
`⟨Y, curl (ψ ε_{k··})⟩ = -⟨τ(Y), ∂_k ψ⟩ + ⟨a(Y)_{k+1}, ∂_{k+2} ψ⟩ - ⟨a(Y)_{k+2}, ∂_{k+1} ψ⟩`
(the distributional form of `a(curl Y) = grad τ(Y) + curl a(Y)`, Lemma 3.5). -/
theorem sum_integral_curlM_cAx (Y : L2M Ω)
    (hdiv : ∀ φ : Fin 3 → R3 → ℝ, (∀ i, IsTest Ω (φ i)) →
      ∑ ij : Ix, ∫ x, Y ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω = 0)
    (k : Fin 3) {ψ : R3 → ℝ} (hψ : IsTest Ω ψ) :
    ∑ ab, ∫ x, Y ab x * curlM (cT (cAx k) ψ) ab x ∂volume.restrict Ω =
      -∫ x, trV Y x * pd k ψ x ∂volume.restrict Ω +
        ∫ x, axV Y (k + 1) x * pd (k + 2) ψ x ∂volume.restrict Ω -
        ∫ x, axV Y (k + 2) x * pd (k + 1) ψ x ∂volume.restrict Ω := by
  have hm : ∀ m, MemLp (pd m ψ) 2 (volume.restrict Ω) := fun m => (hψ.pdiff m).memLp
  have hφ : ∀ i, IsTest Ω (if i = k then ψ else 0) := fun i => by
    split_ifs
    exacts [hψ, IsTest.zero]
  have hd := hdiv _ hφ
  simp only [pd_ite_zero, mul_ite, mul_zero] at hd
  simp_rw [curlM_cT (cAx k) hψ.differentiable]
  simp only [integral_mul_sub_mul _ (hm _) (hm _), integral_axV_mul _ _ (hm _),
    integral_trV_mul _ (hm _)]
  fin_cases k <;> simp [Fintype.sum_prod_type, Fin.sum_univ_three, cAx] at hd ⊢ <;> linarith

end Static

/-! ## The interior equations satisfied by strong solutions of (4.14) -/

section Weak

variable {Ω : Set R3}

/-- The weak (interior, distributional) content of a solution of (4.15) on `[0, T]`:
`E, B` are continuous, weakly divergence-free, and `Ė = -curl B`, `Ḃ = curl E` tested against
`C_c^∞(Ω; ℝ³ˣ³)`. No boundary condition enters. -/
structure WeakEB (Ω : Set R3) (T : ℝ) (E B : ℝ → L2M Ω) : Prop where
  contE : ContinuousOn E (Icc 0 T)
  contB : ContinuousOn B (Icc 0 T)
  divE : ∀ t ∈ Icc 0 T, E t ∈ HdivZero Ω
  divB : ∀ t ∈ Icc 0 T, B t ∈ HdivZero Ω
  derivE : ∀ t ∈ Icc 0 T, ∀ Φ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Φ ij)) →
    HasDerivWithinAt (fun s => ∑ ij, ∫ x, E s ij x * Φ ij x ∂volume.restrict Ω)
      (-∑ ij, ∫ x, B t ij x * curlM Φ ij x ∂volume.restrict Ω) (Icc 0 T) t
  derivB : ∀ t ∈ Icc 0 T, ∀ Φ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Φ ij)) →
    HasDerivWithinAt (fun s => ∑ ij, ∫ x, B s ij x * Φ ij x ∂volume.restrict Ω)
      (∑ ij, ∫ x, E t ij x * curlM Φ ij x ∂volume.restrict Ω) (Icc 0 T) t

open Feec.HilbertComplex2 Feec.Constraints in
/-- **Strong solutions of (4.14) with TSD data satisfy the interior equations.** For data
`(0, E₀, B₀)`, `E₀, B₀ ∈ L²(TSD)`, Prop 4.18 (i) gives `σ ≡ 0`, `div E ≡ 0` and the reduced
system (4.15); `div B ≡ 0` because `∂_t div B = div curl E = 0`. -/
theorem weakEB_of_strongSolution (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {T : ℝ}
    {E₀ B₀ : L2M Ω} (hE₀ : E₀ ∈ TSD Ω) (hB₀ : B₀ ∈ TSD Ω) {U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω)}
    (hU : IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) E₀ B₀) 0 U) :
    (∀ t ∈ Icc 0 T, (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).1 = 0) ∧
      WeakEB Ω T (fun t => (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1)
        (fun t => (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2) := by
  set H := thesisComplex hΩ hb
  obtain ⟨h1, hR⟩ := prop_4_18_i (H := H) (thesisComplex_TSD_le_ker hΩ hb hE₀) hU
  set E := fun t => (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1
  set B := fun t => (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2
  have hdE : ∀ t (ht : t ∈ Icc 0 T) (Φ : Ix → R3 → ℝ) (hΦ : ∀ ij, IsTest Ω (Φ ij)),
      HasDerivWithinAt (fun s => ∑ ij, ∫ x, E s ij x * Φ ij x ∂volume.restrict Ω)
        (-∑ ij, ∫ x, B t ij x * curlM Φ ij x ∂volume.restrict Ω) (Icc 0 T) t := by
    intro t ht Φ hΦ
    have := (innerSL ℝ (testField hΦ)).hasFDerivAt.comp_hasDerivWithinAt t (hR.derivE t ht)
    have e1 : (fun s => ∑ ij, ∫ x, E s ij x * Φ ij x ∂volume.restrict Ω) =
        (innerSL ℝ (testField hΦ)) ∘ E := funext fun s => by
      simp only [Function.comp_apply, innerSL_apply_apply, real_inner_comm _ (testField hΦ),
        inner_testField]
    rw [e1]
    convert this using 1
    rw [innerSL_apply_apply, inner_neg_right, real_inner_comm _ (testField hΦ), inner_testField,
      neg_inj]
    exact (adjoint_curlClosure_inner hΩ hb ⟨B t, hR.memB t ht⟩ hΦ).symm
  have hdB : ∀ t (ht : t ∈ Icc 0 T) (Φ : Ix → R3 → ℝ) (hΦ : ∀ ij, IsTest Ω (Φ ij)),
      HasDerivWithinAt (fun s => ∑ ij, ∫ x, B s ij x * Φ ij x ∂volume.restrict Ω)
        (∑ ij, ∫ x, E t ij x * curlM Φ ij x ∂volume.restrict Ω) (Icc 0 T) t := by
    intro t ht Φ hΦ
    have := (innerSL ℝ (testField hΦ)).hasFDerivAt.comp_hasDerivWithinAt t (hR.derivB t ht)
    have e1 : (fun s => ∑ ij, ∫ x, B s ij x * Φ ij x ∂volume.restrict Ω) =
        (innerSL ℝ (testField hΦ)) ∘ B := funext fun s => by
      simp only [Function.comp_apply, innerSL_apply_apply, real_inner_comm _ (testField hΦ),
        inner_testField]
    rw [e1]
    convert this using 1
    simp only [innerSL_apply_apply, real_inner_comm _ (testField hΦ), inner_testField]
    exact (closure_curlGraph_identity hΩ hb (mem_closure_curlClosure hΩ hb ⟨E t, hR.memE t ht⟩)
      fun ij => (hΦ ij).contDiff_one).symm
  refine ⟨fun t ht => (h1 t ht).1, ⟨fun t ht => (hR.derivE t ht).continuousWithinAt,
    fun t ht => (hR.derivB t ht).continuousWithinAt,
    fun t ht => (mem_ker_adjoint_gradClosure_iff hΩ hb).1 (h1 t ht).2, ?_, hdE, hdB⟩⟩
  -- `div B` is conserved
  intro t ht φ hφ
  have hg : ∀ ij, IsTest Ω (gradM φ ij) := isTest_gradM hφ
  have hc := const_of_hasDerivWithinAt_zero (T := T)
    (f := fun s => ∑ ij, ∫ x, B s ij x * gradM φ ij x ∂volume.restrict Ω) (fun s hs => by
      refine (hdB s hs _ hg).congr_deriv ?_
      refine Finset.sum_eq_zero fun ij _ => ?_
      simp [curlM_gradM fun i => (hφ i).contDiff.of_le (by simp)]) t ht
  simp only [gradM] at hc
  rw [hc]
  have h0 : B 0 = B₀ := hR.initB
  rw [h0]
  exact hB₀.2.2 φ hφ

end Weak

/-! ## The weak violation system and its mollification -/

section Viol

variable {Ω : Set R3} {T : ℝ} {E B : ℝ → L2M Ω}

theorem WeakEB.deriv_axE (h : WeakEB Ω T E B) {t : ℝ} (ht : t ∈ Icc 0 T) (k : Fin 3)
    {ψ : R3 → ℝ} (hψ : IsTest Ω ψ) :
    HasDerivWithinAt (fun s => ∫ x, axV (E s) k x * ψ x ∂volume.restrict Ω)
      (∫ x, trV (B t) x * pd k ψ x ∂volume.restrict Ω -
        ∫ x, axV (B t) (k + 1) x * pd (k + 2) ψ x ∂volume.restrict Ω +
        ∫ x, axV (B t) (k + 2) x * pd (k + 1) ψ x ∂volume.restrict Ω) (Icc 0 T) t := by
  simp_rw [integral_axV _ k hψ.memLp]
  refine (h.derivE t ht _ (isTest_cT (cAx k) hψ)).congr_deriv ?_
  rw [sum_integral_curlM_cAx _ (h.divB t ht) k hψ]
  ring

theorem WeakEB.deriv_trE (h : WeakEB Ω T E B) {t : ℝ} (ht : t ∈ Icc 0 T)
    {ψ : R3 → ℝ} (hψ : IsTest Ω ψ) :
    HasDerivWithinAt (fun s => ∫ x, trV (E s) x * ψ x ∂volume.restrict Ω)
      (-∑ c, ∫ x, axV (B t) c x * pd c ψ x ∂volume.restrict Ω) (Icc 0 T) t := by
  simp_rw [integral_trV _ hψ.memLp]
  refine (h.derivE t ht _ (isTest_cT cTr hψ)).congr_deriv ?_
  rw [sum_integral_curlM_cTr _ hψ]

theorem WeakEB.deriv_axB (h : WeakEB Ω T E B) {t : ℝ} (ht : t ∈ Icc 0 T) (k : Fin 3)
    {ψ : R3 → ℝ} (hψ : IsTest Ω ψ) :
    HasDerivWithinAt (fun s => ∫ x, axV (B s) k x * ψ x ∂volume.restrict Ω)
      (-∫ x, trV (E t) x * pd k ψ x ∂volume.restrict Ω +
        ∫ x, axV (E t) (k + 1) x * pd (k + 2) ψ x ∂volume.restrict Ω -
        ∫ x, axV (E t) (k + 2) x * pd (k + 1) ψ x ∂volume.restrict Ω) (Icc 0 T) t := by
  simp_rw [integral_axV _ k hψ.memLp]
  refine (h.derivB t ht _ (isTest_cT (cAx k) hψ)).congr_deriv ?_
  rw [sum_integral_curlM_cAx _ (h.divE t ht) k hψ]

theorem WeakEB.deriv_trB (h : WeakEB Ω T E B) {t : ℝ} (ht : t ∈ Icc 0 T)
    {ψ : R3 → ℝ} (hψ : IsTest Ω ψ) :
    HasDerivWithinAt (fun s => ∫ x, trV (B s) x * ψ x ∂volume.restrict Ω)
      (∑ c, ∫ x, axV (E t) c x * pd c ψ x ∂volume.restrict Ω) (Icc 0 T) t := by
  simp_rw [integral_trV _ hψ.memLp]
  refine (h.derivB t ht _ (isTest_cT cTr hψ)).congr_deriv ?_
  rw [sum_integral_curlM_cTr _ hψ]

variable {ρ : R3 → ℝ} {ε : ℝ}

/-- The reflected kernel `z ↦ ρ(y - z)` is a test function on `Ω` if `B̄(y, ε) ⊆ Ω`. -/
theorem isTest_refl (hρ : ContDiff ℝ ∞ ρ) (hsupp : tsupport ρ ⊆ Metric.closedBall 0 ε)
    {y : R3} (hy : Metric.closedBall y ε ⊆ Ω) : IsTest Ω (fun z => ρ (y - z)) := by
  have hz : ∀ z, z ∉ Metric.closedBall y ε → ρ (y - z) = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (by
      have := hsupp h
      rw [Metric.mem_closedBall, dist_zero_right] at this
      rwa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev])
  refine ⟨hρ.comp (contDiff_const.sub contDiff_id),
    HasCompactSupport.intro (isCompact_closedBall y ε) hz, ?_⟩
  refine (closure_minimal (fun z hz' => ?_) Metric.isClosed_closedBall).trans hy
  by_contra hc
  exact hz' (hz z hc)

theorem pd_refl (hρ : ContDiff ℝ 1 ρ) (y : R3) (c : Fin 3) (z : R3) :
    pd c (fun z => ρ (y - z)) z = -pd c ρ (y - z) := by
  have h1 : HasFDerivAt (fun z : R3 => y - z) (-ContinuousLinearMap.id ℝ R3) z :=
    (hasFDerivAt_id z).const_sub y
  have h : HasFDerivAt (fun z => ρ (y - z)) _ z :=
    ((hρ.differentiable one_ne_zero (y - z)).hasFDerivAt).comp z h1
  rw [pd_of_hasFDerivAt h, pd]
  simp

/-- `∫_Ω X ∂_c[ρ(y - ·)] = -∂_c (X ⋆ ρ)(y)`. -/
theorem integral_mul_pd_refl (hΩ : IsOpen Ω) (hρ : ContDiff ℝ 1 ρ)
    (hcρ : HasCompactSupport ρ) (X : L2 Ω) (y : R3) (c : Fin 3) :
    ∫ z, X z * pd c (fun z => ρ (y - z)) z ∂volume.restrict Ω = -pd c (mol ρ X) y := by
  simp_rw [pd_refl hρ y c, mul_neg]
  rw [integral_neg, pd_mol hΩ hρ hcρ, mol_apply hΩ]

end Viol

/-- The energy identity of the violation system, pointwise on jets: with
`∂_t a_E = -∇τ_B - curl a_B`, `∂_t τ_E = div a_B`, `∂_t a_B = ∇τ_E + curl a_E`,
`∂_t τ_B = -div a_E`, `½ ∂_t |W|² = div F` (here `daE c k = ∂_c (a_E)_k`, `dtE c = ∂_c τ_E`).
The algebraic core of the energy method of Prop 3.6 (cf. `Feec.energy_flux`). -/
theorem energy_identity (aE aB : Fin 3 → ℝ) (tE tB : ℝ) (daE daB : Fin 3 → Fin 3 → ℝ)
    (dtE dtB : Fin 3 → ℝ) :
    ∑ k, aE k * (-dtB k + daB (k + 2) (k + 1) - daB (k + 1) (k + 2)) + tE * ∑ c, daB c c +
      ∑ k, aB k * (dtE k - daE (k + 2) (k + 1) + daE (k + 1) (k + 2)) + tB * -∑ c, daE c c =
    ∑ c, (daE c (c + 1) * aB (c + 2) + aE (c + 1) * daB c (c + 2) -
      (daE c (c + 2) * aB (c + 1) + aE (c + 2) * daB c (c + 1)) -
      (dtB c * aE c + tB * daE c c) + (dtE c * aB c + tE * daB c c)) := by
  simp only [Fin.sum_univ_three]
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  ring

/-- The product rule for `∂_c`. -/
theorem pd_mul {f g : R3 → ℝ} {y : R3} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (c : Fin 3) :
    pd c (fun y => f y * g y) y = pd c f y * g y + f y * pd c g y := by
  have h : HasFDerivAt (fun y => f y * g y) _ y := hf.hasFDerivAt.mul hg.hasFDerivAt
  rw [pd_of_hasFDerivAt h, pd, pd]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- `∂_c` of the flux of differentiable fields. -/
theorem pd_vflux {aE aB : Fin 3 → R3 → ℝ} {tE tB : R3 → ℝ} (haE : ∀ k, Differentiable ℝ (aE k))
    (haB : ∀ k, Differentiable ℝ (aB k)) (htE : Differentiable ℝ tE)
    (htB : Differentiable ℝ tB) (c : Fin 3) (y : R3) :
    pd c (fun y => vflux (fun k => aE k y) (fun k => aB k y) (tE y) (tB y) c) y =
      pd c (aE (c + 1)) y * aB (c + 2) y + aE (c + 1) y * pd c (aB (c + 2)) y -
        (pd c (aE (c + 2)) y * aB (c + 1) y + aE (c + 2) y * pd c (aB (c + 1)) y) -
        (pd c tB y * aE c y + tB y * pd c (aE c) y) +
          (pd c tE y * aB c y + tE y * pd c (aB c) y) := by
  have d := fun (f : R3 → ℝ) (hf : Differentiable ℝ f) => (hf y).hasFDerivAt
  have h := ((((d _ (haE (c + 1))).mul (d _ (haB (c + 2)))).sub
    ((d _ (haE (c + 2))).mul (d _ (haB (c + 1))))).sub ((d _ htB).mul (d _ (haE c)))).add
    ((d _ htE).mul (d _ (haB c)))
  have h' : HasFDerivAt (fun y => vflux (fun k => aE k y) (fun k => aB k y) (tE y) (tB y) c) _ y :=
    h
  rw [pd_of_hasFDerivAt h', pd, pd, pd, pd, pd, pd, pd, pd]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

/-! ## The mollified violation system -/

section Moll

variable {Ω : Set R3} {T : ℝ} {E B : ℝ → L2M Ω} {ρ : R3 → ℝ} {ε : ℝ}

/-- Mollified axial violation `(a(X(s))_k ⋆ ρ)(y)`. -/
def mA (ρ : R3 → ℝ) (X : ℝ → L2M Ω) (k : Fin 3) (s : ℝ) (y : R3) : ℝ := mol ρ (axV (X s) k) y

/-- Mollified trace violation `(τ(X(s)) ⋆ ρ)(y)`. -/
def mT (ρ : R3 → ℝ) (X : ℝ → L2M Ω) (s : ℝ) (y : R3) : ℝ := mol ρ (trV (X s)) y

theorem hasDerivAt_of_within {f : ℝ → ℝ} {f' t : ℝ}
    (h : HasDerivWithinAt f f' (Icc 0 T) t) (ht : t ∈ Ioo 0 T) : HasDerivAt f f' t :=
  h.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

section
variable (hΩ : IsOpen Ω) (h : WeakEB Ω T E B)
  (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hsupp : tsupport ρ ⊆ Metric.closedBall 0 ε)
include hΩ h hρ hcρ hsupp

theorem hasDerivAt_mA_E {s : ℝ} (hs : s ∈ Ioo 0 T) {y : R3} (hy : Metric.closedBall y ε ⊆ Ω)
    (k : Fin 3) :
    HasDerivAt (fun s => mA ρ E k s y)
      (-pd k (mT ρ B s) y + pd (k + 2) (mA ρ B (k + 1) s) y -
        pd (k + 1) (mA ρ B (k + 2) s) y) s := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  have := hasDerivAt_of_within (h.deriv_axE (Ioo_subset_Icc_self hs) k
    (isTest_refl hρ hsupp hy)) hs
  simp only [integral_mul_pd_refl hΩ hρ1 hcρ] at this
  simp only [← mol_apply hΩ] at this
  delta mA mT
  convert this using 1
  ring

theorem hasDerivAt_mT_E {s : ℝ} (hs : s ∈ Ioo 0 T) {y : R3} (hy : Metric.closedBall y ε ⊆ Ω) :
    HasDerivAt (fun s => mT ρ E s y) (∑ c, pd c (mA ρ B c s) y) s := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  have := hasDerivAt_of_within (h.deriv_trE (Ioo_subset_Icc_self hs)
    (isTest_refl hρ hsupp hy)) hs
  simp only [integral_mul_pd_refl hΩ hρ1 hcρ, Finset.sum_neg_distrib, neg_neg] at this
  simp only [← mol_apply hΩ] at this
  delta mA mT
  exact this

theorem hasDerivAt_mA_B {s : ℝ} (hs : s ∈ Ioo 0 T) {y : R3} (hy : Metric.closedBall y ε ⊆ Ω)
    (k : Fin 3) :
    HasDerivAt (fun s => mA ρ B k s y)
      (pd k (mT ρ E s) y - pd (k + 2) (mA ρ E (k + 1) s) y +
        pd (k + 1) (mA ρ E (k + 2) s) y) s := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  have := hasDerivAt_of_within (h.deriv_axB (Ioo_subset_Icc_self hs) k
    (isTest_refl hρ hsupp hy)) hs
  simp only [integral_mul_pd_refl hΩ hρ1 hcρ] at this
  simp only [← mol_apply hΩ] at this
  delta mA mT
  convert this using 1
  ring

theorem hasDerivAt_mT_B {s : ℝ} (hs : s ∈ Ioo 0 T) {y : R3} (hy : Metric.closedBall y ε ⊆ Ω) :
    HasDerivAt (fun s => mT ρ B s y) (-∑ c, pd c (mA ρ E c s) y) s := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  have := hasDerivAt_of_within (h.deriv_trB (Ioo_subset_Icc_self hs)
    (isTest_refl hρ hsupp hy)) hs
  simp only [integral_mul_pd_refl hΩ hρ1 hcρ, Finset.sum_neg_distrib] at this
  simp only [← mol_apply hΩ] at this
  delta mA mT
  exact this

end

/-- The mollified violation energy density `|W(s, y)|²`. -/
def Nf (ρ : R3 → ℝ) (E B : ℝ → L2M Ω) (s : ℝ) (y : R3) : ℝ :=
  dens (fun k => mA ρ E k s y) (fun k => mA ρ B k s y) (mT ρ E s y) (mT ρ B s y)

/-- The mollified violation flux `F(W(s, y))`. -/
def Flf (ρ : R3 → ℝ) (E B : ℝ → L2M Ω) (c : Fin 3) (s : ℝ) (y : R3) : ℝ :=
  vflux (fun k => mA ρ E k s y) (fun k => mA ρ B k s y) (mT ρ E s y) (mT ρ B s y) c

/-- `W · A(∂) W`, the spatial operator of the violation system paired with `W`. -/
def Qf (ρ : R3 → ℝ) (E B : ℝ → L2M Ω) (s : ℝ) (y : R3) : ℝ :=
  ∑ k, mA ρ E k s y * (-pd k (mT ρ B s) y + pd (k + 2) (mA ρ B (k + 1) s) y -
      pd (k + 1) (mA ρ B (k + 2) s) y) + mT ρ E s y * ∑ c, pd c (mA ρ B c s) y +
    ∑ k, mA ρ B k s y * (pd k (mT ρ E s) y - pd (k + 2) (mA ρ E (k + 1) s) y +
      pd (k + 1) (mA ρ E (k + 2) s) y) + mT ρ B s y * -∑ c, pd c (mA ρ E c s) y

theorem contDiff_mA (hΩ : IsOpen Ω) (hρ : ContDiff ℝ 1 ρ)
    (hcρ : HasCompactSupport ρ) (X : ℝ → L2M Ω) (k : Fin 3) (s : ℝ) :
    ContDiff ℝ 1 (mA ρ X k s) := contDiff_mol hΩ hρ hcρ _

theorem contDiff_mT (hΩ : IsOpen Ω) (hρ : ContDiff ℝ 1 ρ)
    (hcρ : HasCompactSupport ρ) (X : ℝ → L2M Ω) (s : ℝ) :
    ContDiff ℝ 1 (mT ρ X s) := contDiff_mol hΩ hρ hcρ _

/-- `W · A(∂) W = div F(W)` for the mollified violations, everywhere. -/
theorem Qf_eq (hΩ : IsOpen Ω) (hρ : ContDiff ℝ 1 ρ)
    (hcρ : HasCompactSupport ρ) (E B : ℝ → L2M Ω) (s : ℝ) (y : R3) :
    Qf ρ E B s y = ∑ c, pd c (fun y => Flf ρ E B c s y) y := by
  have dA := fun (X : ℝ → L2M Ω) k => (contDiff_mA hΩ hρ hcρ X k s).differentiable one_ne_zero
  have dT := fun (X : ℝ → L2M Ω) => (contDiff_mT hΩ hρ hcρ X s).differentiable one_ne_zero
  simp only [Flf]
  simp only [pd_vflux (aE := fun k => mA ρ E k s) (aB := fun k => mA ρ B k s) (dA E) (dA B)
    (dT E) (dT B)]
  exact energy_identity (fun k => mA ρ E k s y) (fun k => mA ρ B k s y) (mT ρ E s y)
    (mT ρ B s y) (fun c k => pd c (mA ρ E k s) y) (fun c k => pd c (mA ρ B k s) y)
    (fun c => pd c (mT ρ E s) y) (fun c => pd c (mT ρ B s) y)

theorem hasDerivAt_Nf (hΩ : IsOpen Ω) (h : WeakEB Ω T E B)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hsupp : tsupport ρ ⊆ Metric.closedBall 0 ε)
    {s : ℝ} (hs : s ∈ Ioo 0 T) {y : R3} (hy : Metric.closedBall y ε ⊆ Ω) :
    HasDerivAt (fun s => Nf ρ E B s y) (2 * Qf ρ E B s y) s := by
  have aE := fun k => hasDerivAt_mA_E hΩ h hρ hcρ hsupp hs hy k
  have aB := fun k => hasDerivAt_mA_B hΩ h hρ hcρ hsupp hs hy k
  have tE := hasDerivAt_mT_E hΩ h hρ hcρ hsupp hs hy
  have tB := hasDerivAt_mT_B hΩ h hρ hcρ hsupp hs hy
  have hN := (((((((((aE 0).pow 2).add ((aE 1).pow 2)).add ((aE 2).pow 2)).add (tE.pow 2)).add
    ((aB 0).pow 2)).add ((aB 1).pow 2)).add ((aB 2).pow 2)).add (tB.pow 2))
  have e : (fun s => Nf ρ E B s y) = fun s => mA ρ E 0 s y ^ 2 + mA ρ E 1 s y ^ 2 +
      mA ρ E 2 s y ^ 2 + mT ρ E s y ^ 2 + mA ρ B 0 s y ^ 2 + mA ρ B 1 s y ^ 2 +
      mA ρ B 2 s y ^ 2 + mT ρ B s y ^ 2 := by
    funext s; simp only [Nf, dens, Fin.sum_univ_three]; ring
  rw [e]
  convert hN using 1
  simp only [Qf, Fin.sum_univ_three, Nat.cast_ofNat]
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  ring


theorem norm_axV_le (X : L2M Ω) (k : Fin 3) : ‖axV X k‖ ≤ 3 * ‖X‖ := by
  have h1 := PiLp.norm_apply_le X (k + 1, k + 2)
  have h2 := PiLp.norm_apply_le X (k + 2, k + 1)
  have := norm_sub_le (X (k + 1, k + 2)) (X (k + 2, k + 1))
  rw [axV]
  linarith [norm_nonneg X]

theorem norm_trV_le (X : L2M Ω) : ‖trV X‖ ≤ 3 * ‖X‖ := by
  refine (norm_sum_le _ _).trans ?_
  simp only [Fin.sum_univ_three]
  linarith [PiLp.norm_apply_le X (0, 0), PiLp.norm_apply_le X (1, 1),
    PiLp.norm_apply_le X (2, 2)]

/-- Uniform bounds on the mollified violations and their first derivatives on `[0, T] × ℝ³`. -/
theorem exists_bound_moll (hΩ : IsOpen Ω) (h : WeakEB Ω T E B)
    (hρ : ContDiff ℝ 1 ρ) (hcρ : HasCompactSupport ρ) :
    ∃ A, 0 ≤ A ∧ ∀ s ∈ Icc 0 T, ∀ X ∈ ({E, B} : Set (ℝ → L2M Ω)), ∀ y,
      (∀ k, |mA ρ X k s y| ≤ A) ∧ |mT ρ X s y| ≤ A ∧
      ∀ c, (∀ k, |pd c (mA ρ X k s) y| ≤ A) ∧ |pd c (mT ρ X s) y| ≤ A := by
  obtain ⟨CE, hCE⟩ := isCompact_Icc.exists_bound_of_continuousOn h.contE
  obtain ⟨CB, hCB⟩ := isCompact_Icc.exists_bound_of_continuousOn h.contB
  set C := max CE 0 + max CB 0
  have hC : ∀ s ∈ Icc 0 T, ∀ X ∈ ({E, B} : Set (ℝ → L2M Ω)), ‖X s‖ ≤ C := by
    rintro s hs X (rfl | rfl)
    · exact (hCE s hs).trans (by simp only [C]; linarith [le_max_left CE 0, le_max_right CB 0])
    · exact (hCB s hs).trans (by simp only [C]; linarith [le_max_right CE 0, le_max_left CB 0])
  have hC0 : 0 ≤ C := by positivity
  have hpd : ∀ c, Continuous (pd c ρ) ∧ HasCompactSupport (pd c ρ) := fun c =>
    ⟨continuous_pd hρ c, HasCompactSupport.fderiv_apply ℝ hcρ _⟩
  obtain ⟨M, hM0, hM⟩ := exists_abs_mol_le hΩ hρ.continuous hcρ
  obtain ⟨M0, hM00, hM0'⟩ := exists_abs_mol_le hΩ (hpd 0).1 (hpd 0).2
  obtain ⟨M1, hM10, hM1'⟩ := exists_abs_mol_le hΩ (hpd 1).1 (hpd 1).2
  obtain ⟨M2, hM20, hM2'⟩ := exists_abs_mol_le hΩ (hpd 2).1 (hpd 2).2
  set Ms := M + M0 + M1 + M2
  have hMs : ∀ c, ∀ (Y : L2 Ω) y, |mol (pd c ρ) Y y| ≤ Ms * ‖Y‖ := by
    intro c Y y
    fin_cases c
    · exact (hM0' Y y).trans (by gcongr; simp only [Ms]; linarith)
    · exact (hM1' Y y).trans (by gcongr; simp only [Ms]; linarith)
    · exact (hM2' Y y).trans (by gcongr; simp only [Ms]; linarith)
  have hMs' : ∀ (Y : L2 Ω) y, |mol ρ Y y| ≤ Ms * ‖Y‖ := fun Y y =>
    (hM Y y).trans (by gcongr; simp only [Ms]; linarith)
  refine ⟨Ms * (3 * C), by positivity, fun s hs X hX y => ?_⟩
  have hA : ∀ Y : L2 Ω, ‖Y‖ ≤ 3 * C → Ms * ‖Y‖ ≤ Ms * (3 * C) := fun Y hY => by gcongr
  have hax : ∀ k, ‖axV (X s) k‖ ≤ 3 * C := fun k =>
    (norm_axV_le _ k).trans (by linarith [hC s hs X hX])
  have htr : ‖trV (X s)‖ ≤ 3 * C := (norm_trV_le _).trans (by linarith [hC s hs X hX])
  refine ⟨fun k => (hMs' _ y).trans (hA _ (hax k)), (hMs' _ y).trans (hA _ htr), fun c =>
    ⟨fun k => ?_, ?_⟩⟩
  · change |pd c (mol ρ (axV (X s) k)) y| ≤ _
    rw [pd_mol hΩ hρ hcρ]
    exact (hMs c _ y).trans (hA _ (hax k))
  · change |pd c (mol ρ (trV (X s))) y| ≤ _
    rw [pd_mol hΩ hρ hcρ]
    exact (hMs c _ y).trans (hA _ htr)

theorem continuousOn_mA (hΩ : IsOpen Ω) (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    {X : ℝ → L2M Ω} (hX : ContinuousOn X (Icc 0 T)) (k : Fin 3) (y : R3) :
    ContinuousOn (fun s => mA ρ X k s y) (Icc 0 T) := by
  simp only [mA, mol_eq_inner hΩ hρ hcρ]
  refine ContinuousOn.inner ?_ continuousOn_const
  exact ((continuous_component _).comp_continuousOn hX).sub
    ((continuous_component _).comp_continuousOn hX)

theorem continuousOn_mT (hΩ : IsOpen Ω) (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    {X : ℝ → L2M Ω} (hX : ContinuousOn X (Icc 0 T)) (y : R3) :
    ContinuousOn (fun s => mT ρ X s y) (Icc 0 T) := by
  simp only [mT, mol_eq_inner hΩ hρ hcρ]
  refine ContinuousOn.inner ?_ continuousOn_const
  simp only [trV]
  exact continuousOn_finsetSum _ fun i _ => (continuous_component _).comp_continuousOn hX


theorem abs_sum3_mul_le (a g : Fin 3 → ℝ) {A G : ℝ} (ha : ∀ k, |a k| ≤ A) (hg : ∀ k, |g k| ≤ G) :
    |∑ k, a k * g k| ≤ 3 * (A * G) := by
  have hG : 0 ≤ G := (abs_nonneg _).trans (hg 0)
  have hm : ∀ k, |a k * g k| ≤ A * G := fun k => by
    rw [abs_mul]; exact mul_le_mul (ha k) (hg k) (abs_nonneg _) ((abs_nonneg _).trans (ha k))
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simp only [Fin.sum_univ_three]
  linarith [hm 0, hm 1, hm 2]

theorem abs_three_le {u v w A : ℝ} (hu : |u| ≤ A) (hv : |v| ≤ A) (hw : |w| ≤ A) :
    |-u + v - w| ≤ 3 * A ∧ |u - v + w| ≤ 3 * A ∧ |u + v + w| ≤ 3 * A := by
  rw [abs_le] at hu hv hw ⊢
  rw [abs_le, abs_le]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith [hu.1, hu.2, hv.1, hv.2, hw.1, hw.2]

theorem abs_Nf_le {s : ℝ} {y : R3} {A : ℝ}
    (hE : ∀ k, |mA ρ E k s y| ≤ A) (hτE : |mT ρ E s y| ≤ A) (hB : ∀ k, |mA ρ B k s y| ≤ A)
    (hτB : |mT ρ B s y| ≤ A) : |Nf ρ E B s y| ≤ 8 * A ^ 2 := by
  have hsq : ∀ {u : ℝ}, |u| ≤ A → u ^ 2 ≤ A ^ 2 := fun h => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [Nf, abs_of_nonneg (dens_nonneg _ _ _ _)]
  simp only [dens, Fin.sum_univ_three]
  linarith [hsq (hE 0), hsq (hE 1), hsq (hE 2), hsq hτE, hsq (hB 0), hsq (hB 1), hsq (hB 2),
    hsq hτB]

theorem abs_Qf_le {s : ℝ} {y : R3} {A : ℝ} (hA : 0 ≤ A)
    (hE : ∀ k, |mA ρ E k s y| ≤ A) (hτE : |mT ρ E s y| ≤ A) (hB : ∀ k, |mA ρ B k s y| ≤ A)
    (hτB : |mT ρ B s y| ≤ A)
    (dE : ∀ c, (∀ k, |pd c (mA ρ E k s) y| ≤ A) ∧ |pd c (mT ρ E s) y| ≤ A)
    (dB : ∀ c, (∀ k, |pd c (mA ρ B k s) y| ≤ A) ∧ |pd c (mT ρ B s) y| ≤ A) :
    |Qf ρ E B s y| ≤ 24 * A ^ 2 := by
  have g1 : ∀ k, |-pd k (mT ρ B s) y + pd (k + 2) (mA ρ B (k + 1) s) y -
      pd (k + 1) (mA ρ B (k + 2) s) y| ≤ 3 * A := fun k =>
    (abs_three_le (dB k).2 ((dB _).1 _) ((dB _).1 _)).1
  have g3 : ∀ k, |pd k (mT ρ E s) y - pd (k + 2) (mA ρ E (k + 1) s) y +
      pd (k + 1) (mA ρ E (k + 2) s) y| ≤ 3 * A := fun k =>
    (abs_three_le (dE k).2 ((dE _).1 _) ((dE _).1 _)).2.1
  have g2 : |∑ c, pd c (mA ρ B c s) y| ≤ 3 * A := by
    simp only [Fin.sum_univ_three]
    exact (abs_three_le ((dB 0).1 0) ((dB 1).1 1) ((dB 2).1 2)).2.2
  have g4 : |-∑ c, pd c (mA ρ E c s) y| ≤ 3 * A := by
    rw [abs_neg]
    simp only [Fin.sum_univ_three]
    exact (abs_three_le ((dE 0).1 0) ((dE 1).1 1) ((dE 2).1 2)).2.2
  have t1 := abs_sum3_mul_le _ _ hE g1
  have t3 := abs_sum3_mul_le _ _ hB g3
  have t2 : |mT ρ E s y * ∑ c, pd c (mA ρ B c s) y| ≤ A * (3 * A) := by
    rw [abs_mul]; exact mul_le_mul hτE g2 (abs_nonneg _) hA
  have t4 : |mT ρ B s y * -∑ c, pd c (mA ρ E c s) y| ≤ A * (3 * A) := by
    rw [abs_mul]; exact mul_le_mul hτB g4 (abs_nonneg _) hA
  rw [Qf]
  have := abs_add_le (∑ k, mA ρ E k s y * (-pd k (mT ρ B s) y + pd (k + 2) (mA ρ B (k + 1) s) y -
      pd (k + 1) (mA ρ B (k + 2) s) y) + mT ρ E s y * ∑ c, pd c (mA ρ B c s) y +
    ∑ k, mA ρ B k s y * (pd k (mT ρ E s) y - pd (k + 2) (mA ρ E (k + 1) s) y +
      pd (k + 1) (mA ρ E (k + 2) s) y)) (mT ρ B s y * -∑ c, pd c (mA ρ E c s) y)
  have := abs_add_le (∑ k, mA ρ E k s y * (-pd k (mT ρ B s) y + pd (k + 2) (mA ρ B (k + 1) s) y -
      pd (k + 1) (mA ρ B (k + 2) s) y) + mT ρ E s y * ∑ c, pd c (mA ρ B c s) y)
    (∑ k, mA ρ B k s y * (pd k (mT ρ E s) y - pd (k + 2) (mA ρ E (k + 1) s) y +
      pd (k + 1) (mA ρ E (k + 2) s) y))
  have := abs_add_le (∑ k, mA ρ E k s y * (-pd k (mT ρ B s) y + pd (k + 2) (mA ρ B (k + 1) s) y -
      pd (k + 1) (mA ρ B (k + 2) s) y)) (mT ρ E s y * ∑ c, pd c (mA ρ B c s) y)
  nlinarith [t1, t2, t3, t4]


theorem contDiff_Flf (hΩ : IsOpen Ω) (hρ : ContDiff ℝ 1 ρ)
    (hcρ : HasCompactSupport ρ) (E B : ℝ → L2M Ω) (c : Fin 3) (s : ℝ) :
    ContDiff ℝ 1 (fun y => Flf ρ E B c s y) := by
  have a := fun (X : ℝ → L2M Ω) k => contDiff_mA hΩ hρ hcρ X k s
  have t := fun (X : ℝ → L2M Ω) => contDiff_mT hΩ hρ hcρ X s
  simp only [Flf, vflux]
  exact ((((a E _).mul (a B _)).sub ((a E _).mul (a B _))).sub ((t B).mul (a E _))).add
    ((t E).mul (a B _))

theorem continuous_Nf (hΩ : IsOpen Ω) (hρ : ContDiff ℝ 1 ρ)
    (hcρ : HasCompactSupport ρ) (E B : ℝ → L2M Ω) (s : ℝ) : Continuous (Nf ρ E B s) := by
  have a := fun (X : ℝ → L2M Ω) k => (contDiff_mA hΩ hρ hcρ X k s).continuous
  have t := fun (X : ℝ → L2M Ω) => (contDiff_mT hΩ hρ hcρ X s).continuous
  change Continuous fun y => dens _ _ _ _
  unfold dens
  exact (((continuous_finsetSum _ fun k _ => (a E k).pow 2).add ((t E).pow 2)).add
    (continuous_finsetSum _ fun k _ => (a B k).pow 2)).add ((t B).pow 2)

theorem continuous_Qf (hΩ : IsOpen Ω) (hρ : ContDiff ℝ 1 ρ)
    (hcρ : HasCompactSupport ρ) (E B : ℝ → L2M Ω) (s : ℝ) : Continuous (Qf ρ E B s) := by
  have e : Qf ρ E B s = fun y => ∑ c, pd c (fun y => Flf ρ E B c s y) y :=
    funext (Qf_eq hΩ hρ hcρ E B s)
  rw [e]
  exact continuous_finsetSum _ fun c _ => continuous_pd (contDiff_Flf hΩ hρ hcρ E B c s) c

/-- **Local energy estimate (finite speed of propagation) for the mollified violations.**
If the violations vanish at `t = 0` and the mollifier radius `ε` is such that `B̄(y, ε) ⊆ Ω` for
`|y - x| < R`, then the mollified violation `W(t, y)` vanishes wherever `q(y) < R - t`, i.e. in
the backward cone `√(δ² + |y - x|²) < R - t` (unit speed). Proof: the weighted energy
`e(t) = ∫ χ(R - t - q) |W|²` satisfies `e' = ∫ (-χ' |W|² - 2 ∇ψ · F(W)) ≤ 0` (`Qf_eq`,
integration by parts, `abs_two_flux_le`, `sum_pd_wt_sq_le`) and `e(0) = 0`. -/
theorem Nf_eq_zero_of_cone (hΩ : IsOpen Ω) (h : WeakEB Ω T E B)
    (h0 : (∀ k, axV (E 0) k = 0) ∧ trV (E 0) = 0 ∧ (∀ k, axV (B 0) k = 0) ∧ trV (B 0) = 0)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hsupp : tsupport ρ ⊆ Metric.closedBall 0 ε)
    {x : R3} {R δ : ℝ} (hδ : 0 < δ) (hgood : ∀ y, dist₂ y x < R → Metric.closedBall y ε ⊆ Ω)
    {t : ℝ} (ht : t ∈ Icc 0 T) {y : R3} (hy : qd x δ y < R - t) : Nf ρ E B t y = 0 := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  obtain ⟨A, hA0, hA⟩ := exists_bound_moll hΩ h hρ1 hcρ
  obtain ⟨D, hD⟩ := exists_abs_dχ_le
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hEm : E ∈ ({E, B} : Set (ℝ → L2M Ω)) := by simp
  have hBm : B ∈ ({E, B} : Set (ℝ → L2M Ω)) := by simp
  have bN : ∀ s ∈ Icc 0 T, ∀ y, |Nf ρ E B s y| ≤ 8 * A ^ 2 := fun s hs y =>
    abs_Nf_le (hA s hs E hEm y).1 (hA s hs E hEm y).2.1 (hA s hs B hBm y).1 (hA s hs B hBm y).2.1
  have bQ : ∀ s ∈ Icc 0 T, ∀ y, |Qf ρ E B s y| ≤ 24 * A ^ 2 := fun s hs y =>
    abs_Qf_le hA0 (hA s hs E hEm y).1 (hA s hs E hEm y).2.1 (hA s hs B hBm y).1
      (hA s hs B hBm y).2.1 (hA s hs E hEm y).2.2 (hA s hs B hBm y).2.2
  have cwt : ∀ s, Continuous (wt x δ R s) := fun s => (contDiff_wt hδ R s).continuous
  have cdχ : ∀ s, Continuous fun y => dχ (R - s - qd x δ y) := fun s =>
    continuous_dχ.comp (continuous_const.sub (continuous_qd hδ))
  set F : ℝ → R3 → ℝ := fun s y => wt x δ R s y * Nf ρ E B s y with hF
  set F' : ℝ → R3 → ℝ := fun s y =>
    -dχ (R - s - qd x δ y) * Nf ρ E B s y + wt x δ R s y * (2 * Qf ρ E B s y) with hF'
  have cF : ∀ s, Continuous (F s) := fun s => (cwt s).mul (continuous_Nf hΩ hρ1 hcρ E B s)
  have cF' : ∀ s, Continuous (F' s) := fun s =>
    ((cdχ s).neg.mul (continuous_Nf hΩ hρ1 hcρ E B s)).add
      ((cwt s).mul (continuous_const.mul (continuous_Qf hΩ hρ1 hcρ E B s)))
  have F0 : ∀ s, 0 ≤ s → ∀ y, y ∉ Metric.closedBall x R → F s y = 0 := fun s hs y hy => by
    simp only [hF, (wt_far hs (le_dist₂_of_notMem hy)).1, zero_mul]
  have F'0 : ∀ s, 0 ≤ s → ∀ y, R ≤ dist₂ y x → F' s y = 0 := fun s hs y hy => by
    simp only [hF', (wt_far hs hy).1, (wt_far hs hy).2, neg_zero, zero_mul, add_zero]
  have intF : ∀ s ∈ Icc 0 T, Integrable (F s) := fun s hs =>
    integrable_of_eq_zero_off (x := x) (R := R) (cF s) (F0 s hs.1)
  set bound : R3 → ℝ := (Metric.closedBall x R).indicator fun _ => D * (8 * A ^ 2) +
    2 * (24 * A ^ 2) + 8 * A ^ 2 with hbd
  have hbound : Integrable bound :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (integrableOn_const (measure_closedBall_lt_top).ne)
  -- step 1: `e` is continuous on `[0, T]`
  have hcont : ContinuousOn (fun s => ∫ y, F s y) (Icc 0 T) := by
    refine continuousOn_of_dominated (bound := bound) (fun s _ => (cF s).aestronglyMeasurable)
      (fun s hs => Eventually.of_forall fun y => ?_) hbound (Eventually.of_forall fun y => ?_)
    · by_cases hy : y ∈ Metric.closedBall x R
      · rw [hbd, indicator_of_mem hy, Real.norm_eq_abs, abs_mul, abs_of_nonneg (wt_nonneg _ _ _)]
        have := bN s hs y
        have := wt_le_one (x := x) (δ := δ) R s y
        nlinarith [abs_nonneg (Nf ρ E B s y), wt_nonneg (x := x) (δ := δ) R s y, sq_nonneg A,
          mul_nonneg hD0 (sq_nonneg A)]
      · rw [hbd, indicator_of_notMem hy, F0 s hs.1 y hy, norm_zero]
    · have hw : Continuous fun s => wt x δ R s y :=
        Real.smoothTransition.continuous.comp ((continuous_const.sub continuous_id).sub
          continuous_const)
      have hN : ContinuousOn (fun s => Nf ρ E B s y) (Icc 0 T) := by
        have a := fun (X : ℝ → L2M Ω) (hX : ContinuousOn X (Icc 0 T)) k =>
          continuousOn_mA hΩ hρ1.continuous hcρ hX k y
        have b := fun (X : ℝ → L2M Ω) (hX : ContinuousOn X (Icc 0 T)) =>
          continuousOn_mT hΩ hρ1.continuous hcρ hX y
        change ContinuousOn (fun s => dens _ _ _ _) _
        unfold dens
        exact (((continuousOn_finsetSum _ fun k _ => (a E h.contE k).pow 2).add
          ((b E h.contE).pow 2)).add (continuousOn_finsetSum _ fun k _ =>
            (a B h.contB k).pow 2)).add ((b B h.contB).pow 2)
      exact hw.continuousOn.mul hN
  -- step 2: `e' ≤ 0` on `(0, T)`
  have hderiv : ∀ t' ∈ Ioo 0 T, HasDerivAt (fun s => ∫ y, F s y) (∫ y, F' t' y) t' ∧
      ∫ y, F' t' y ≤ 0 := by
    intro t' ht'
    have hIcc : t' ∈ Icc 0 T := Ioo_subset_Icc_self ht'
    have hbnd : ∀ᵐ y ∂volume, ∀ s ∈ Ioo 0 T, ‖F' s y‖ ≤ bound y := by
      refine Eventually.of_forall fun y s hs => ?_
      -- the derivative bound
      have hs' : s ∈ Icc 0 T := Ioo_subset_Icc_self hs
      by_cases hy : y ∈ Metric.closedBall x R
      · rw [hbd, indicator_of_mem hy, Real.norm_eq_abs]
        have h1 := bN s hs' y
        have h2 := bQ s hs' y
        have h3 := hD (R - s - qd x δ y)
        have h4 := wt_le_one (x := x) (δ := δ) R s y
        have h5 := wt_nonneg (x := x) (δ := δ) R s y
        simp only [hF']
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg h5, abs_mul, abs_two]
        have : |dχ (R - s - qd x δ y)| * |Nf ρ E B s y| ≤ D * (8 * A ^ 2) :=
          mul_le_mul h3 h1 (abs_nonneg _) hD0
        have : wt x δ R s y * (2 * |Qf ρ E B s y|) ≤ 1 * (2 * (24 * A ^ 2)) :=
          mul_le_mul h4 (by linarith) (by positivity) zero_le_one
        nlinarith [sq_nonneg A]
      · rw [hbd, indicator_of_notMem hy, F'0 s hs.1.le y (le_dist₂_of_notMem hy), norm_zero]
    have hdif : ∀ᵐ y ∂volume, ∀ s ∈ Ioo 0 T, HasDerivAt (F · y) (F' s y) s := by
      refine Eventually.of_forall fun y s hs => ?_
      -- differentiability in time
      by_cases hy : dist₂ y x < R
      · exact (hasDerivAt_wt_time R s y).mul
          (hasDerivAt_Nf hΩ h hρ hcρ hsupp hs (hgood y hy))
      · rw [not_lt] at hy
        rw [show F' s y = 0 from F'0 s hs.1.le y hy]
        refine (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds hs.1] with s'' hs''
        simp only [hF, (wt_far (δ := δ) (le_of_lt hs'') hy).1, zero_mul]
    obtain ⟨hF'int, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := bound)
      (Ioo_mem_nhds ht'.1 ht'.2) (Eventually.of_forall fun s => (cF s).aestronglyMeasurable)
      (intF t' hIcc) (cF' t').aestronglyMeasurable
      hbnd hbound hdif
    refine ⟨hd, ?_⟩
    -- integrate by parts the flux term
    set G : R3 → ℝ := fun y => -dχ (R - t' - qd x δ y) * Nf ρ E B t' y -
      2 * ∑ c, pd c (wt x δ R t') y * Flf ρ E B c t' y with hG
    have cFl := fun c => contDiff_Flf hΩ hρ1 hcρ E B c t'
    have cpw : ∀ c, Continuous (pd c (wt x δ R t')) := fun c =>
      continuous_pd ((contDiff_wt hδ R t').of_le (by simp)) c
    have cG : Continuous G := ((cdχ t').neg.mul (continuous_Nf hΩ hρ1 hcρ E B t')).sub
      (continuous_const.mul (continuous_finsetSum _ fun c _ => (cpw c).mul (cFl c).continuous))
    have G0 : ∀ y, y ∉ Metric.closedBall x R → G y = 0 := fun y hy => by
      have hy' := le_dist₂_of_notMem hy
      simp only [hG, (wt_far ht'.1.le hy').2, pd_wt_far hδ ht'.1.le hy', zero_mul, neg_zero,
        Finset.sum_const_zero, mul_zero, sub_zero]
    have intG : Integrable G := integrable_of_eq_zero_off (x := x) (R := R) cG G0
    have hP : ∀ c, Integrable fun y => wt x δ R t' y * pd c (fun y => Flf ρ E B c t' y) y +
        pd c (wt x δ R t') y * Flf ρ E B c t' y := fun c =>
      integrable_of_eq_zero_off (x := x) (R := R) (((cwt t').mul (continuous_pd (cFl c) c)).add
        ((cpw c).mul (cFl c).continuous)) fun y hy => by
        have hy' := le_dist₂_of_notMem hy
        show wt x δ R t' y * pd c (fun y => Flf ρ E B c t' y) y +
          pd c (wt x δ R t') y * Flf ρ E B c t' y = 0
        rw [(wt_far (δ := δ) ht'.1.le hy').1, pd_wt_far hδ ht'.1.le hy']
        ring
    have hP0 : ∀ c, ∫ y, (wt x δ R t' y * pd c (fun y => Flf ρ E B c t' y) y +
        pd c (wt x δ R t') y * Flf ρ E B c t' y) = 0 := fun c => by
      have hibp := integral_pd_mul (isTest_wt (x := x) hδ R t') (cFl c) c
      simp only [Measure.restrict_univ] at hibp
      rw [integral_add, hibp]
      · ring
      · exact integrable_of_eq_zero_off (x := x) (R := R)
          ((cwt t').mul (continuous_pd (cFl c) c)) fun y hy => by
          simp only [(wt_far (δ := δ) ht'.1.le (le_dist₂_of_notMem (x := x) hy)).1, zero_mul]
      · exact integrable_of_eq_zero_off (x := x) (R := R)
          ((cpw c).mul (cFl c).continuous) fun y hy => by
          simp only [pd_wt_far hδ ht'.1.le (le_dist₂_of_notMem (x := x) hy), zero_mul]
    have hsplit : ∀ y, F' t' y = G y + 2 * ∑ c, (wt x δ R t' y *
        pd c (fun y => Flf ρ E B c t' y) y + pd c (wt x δ R t') y * Flf ρ E B c t' y) :=
      fun y => by
        have e1 : wt x δ R t' y * ∑ c, pd c (fun y => Flf ρ E B c t' y) y =
            ∑ c, wt x δ R t' y * pd c (fun y => Flf ρ E B c t' y) y := Finset.mul_sum _ _ _
        simp only [hF', hG, Qf_eq hΩ hρ1 hcρ E B t' y, Finset.sum_add_distrib, ← e1]
        ring
    rw [integral_congr_ae (Eventually.of_forall hsplit), integral_add intG
      ((integrable_finsetSum _ fun c _ => hP c).const_mul 2), integral_const_mul,
      integral_finsetSum _ fun c _ => hP c]
    simp only [hP0, Finset.sum_const_zero, mul_zero, add_zero]
    refine integral_nonpos fun y => ?_
    have hfl := abs_two_flux_le (fun c => pd c (wt x δ R t') y) (fun k => mA ρ E k t' y)
      (fun k => mA ρ B k t' y) (mT ρ E t' y) (mT ρ B t' y) (dχ (R - t' - qd x δ y))
      (dχ_nonneg _) (sum_pd_wt_sq_le hδ R t' y)
    simp only [hG, Pi.zero_apply]
    change -dχ (R - t' - qd x δ y) * Nf ρ E B t' y -
      2 * ∑ c, pd c (wt x δ R t') y * Flf ρ E B c t' y ≤ 0
    have hfl' : |2 * ∑ c, pd c (wt x δ R t') y * Flf ρ E B c t' y| ≤
        dχ (R - t' - qd x δ y) * Nf ρ E B t' y := hfl
    linarith [neg_abs_le (2 * ∑ c, pd c (wt x δ R t') y * Flf ρ E B c t' y)]
  -- step 3: monotonicity
  have hanti : AntitoneOn (fun s => ∫ y, F s y) (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hcont (fun t' ht' => ?_) fun t' ht' => ?_
    · rw [interior_Icc] at ht'
      exact (hderiv t' ht').1.differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht'
      rw [(hderiv t' ht').1.deriv]
      exact (hderiv t' ht').2
  have hN0 : ∀ y, Nf ρ E B 0 y = 0 := fun y => by
    simp only [Nf, mA, mT, h0.1, h0.2.1, h0.2.2.1, h0.2.2.2, mol_zero hΩ]
    simp [dens]
  have he0 : ∫ y, F 0 y = 0 := by simp [hF, hN0]
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have het : ∫ y, F t y = 0 := le_antisymm (he0 ▸ hanti h0T ht ht.1)
    (integral_nonneg fun y => mul_nonneg (wt_nonneg _ _ _) (dens_nonneg _ _ _ _))
  have hFt : F t = 0 := by
    have hae := (integral_eq_zero_iff_of_nonneg (fun y => mul_nonneg (wt_nonneg _ _ _)
      (dens_nonneg _ _ _ _)) (intF t ht)).1 het
    exact (Continuous.ae_eq_iff_eq volume (cF t) continuous_zero).1 hae
  have := congrFun hFt y
  simp only [hF, Pi.zero_apply, mul_eq_zero] at this
  exact this.resolve_left (wt_pos hy).ne'

end Moll

/-! ## Removing the mollifier: interior propagation for `L²` solutions -/

section Limit

variable {Ω : Set R3} {T : ℝ} {E B : ℝ → L2M Ω}

theorem mol_eq_conv (ρ : R3 → ℝ) (X : L2 Ω) :
    mol ρ X = convolution ρ (ext0 X) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  rw [mol]
  exact convolution_symm _ (by ext; simp)

/-- Mollifiers of radius `2 / (n + 2)`. -/
def bumpSeq (n : ℕ) : ContDiffBump (0 : R3) where
  rIn := 1 / (n + 2)
  rOut := 2 / (n + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num

theorem tendsto_bumpSeq_rOut : Tendsto (fun n => (bumpSeq n).rOut) atTop (𝓝 0) := by
  simp only [bumpSeq]
  exact tendsto_const_nhds.div_atTop
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

/-- Lebesgue differentiation: if the mollifications of `V` vanish eventually at every point of
`S ⊆ Ω`, then `V = 0` a.e. on `S`. -/
theorem ae_eq_zero_of_mol_eventually (hΩ : IsOpen Ω) (V : L2 Ω)
    {S : Set R3} (hS : MeasurableSet S) (hSΩ : S ⊆ Ω)
    (hev : ∀ y ∈ S, ∀ᶠ n in atTop, mol ((bumpSeq n).normed volume) V y = 0) :
    ∀ᵐ y ∂volume.restrict S, V y = 0 := by
  have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    (φ := bumpSeq) (l := atTop) (K := 2) tendsto_bumpSeq_rOut
    (Eventually.of_forall fun n => by simp only [bumpSeq]; ring_nf; rfl)
    (locallyIntegrable_ext0 hΩ V)
  rw [ae_restrict_iff' hS]
  filter_upwards [hconv] with y hy hyS
  simp only [← mol_eq_conv] at hy
  have h0 : Tendsto (fun n => mol ((bumpSeq n).normed volume) V y) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [hev y hyS] with n hn using hn.symm)
  have := tendsto_nhds_unique hy h0
  rwa [ext0, indicator_of_mem (hSΩ hyS)] at this

/-- **Interior TSD propagation, in the `L²` setting of `WeakEB`.** If the violations vanish at
`t = 0` and the Euclidean ball `{|z - x| < r}` lies in `Ω`, then at time `t ∈ [0, T]` the
violations `a(E), τ(E), a(B), τ(B)` vanish a.e. on the ball `{|y - x| < r - t}`. -/
theorem WeakEB.ae_viol_eq_zero (hΩ : IsOpen Ω) (h : WeakEB Ω T E B)
    (h0 : (∀ k, axV (E 0) k = 0) ∧ trV (E 0) = 0 ∧ (∀ k, axV (B 0) k = 0) ∧ trV (B 0) = 0)
    {x : R3} {r : ℝ} (hr : ∀ z, dist₂ z x < r → z ∈ Ω) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᵐ y ∂volume.restrict {y | dist₂ y x < r - t}, (∀ k, axV (E t) k y = 0) ∧
      trV (E t) y = 0 ∧ (∀ k, axV (B t) k y = 0) ∧ trV (B t) y = 0 := by
  set ε : ℕ → ℝ := fun n => (bumpSeq n).rOut
  have hε : ∀ n, 0 < ε n := fun n => (bumpSeq n).rOut_pos
  -- the mollified violations vanish in the shrunken cone
  have hcone : ∀ n y, dist₂ y x < r - t - 3 * ε n →
      Nf ((bumpSeq n).normed volume) E B t y = 0 := by
    intro n y hy
    refine Nf_eq_zero_of_cone (x := x) (ε := ε n) (R := r - 2 * ε n) (δ := ε n) hΩ h h0
      ((bumpSeq n).contDiff_normed (n := ⊤)) (bumpSeq n).hasCompactSupport_normed
      (bumpSeq n).tsupport_normed_eq.subset (hε n) (fun z hz w hw => hr w ?_) ht ?_
    · have h1 := dist₂_le_two_dist w z
      have h2 := dist₂_triangle w z x
      rw [Metric.mem_closedBall] at hw
      linarith
    · have := qd_le (x := x) (hε n).le y
      linarith
  have hS : MeasurableSet {y | dist₂ y x < r - t} := (isOpen_ball₂ x (r - t)).measurableSet
  have hSΩ : {y | dist₂ y x < r - t} ⊆ Ω := fun y hy => hr y (by
    simp only [mem_ofPred_eq] at hy; linarith [ht.1])
  -- eventually in `n`, every point of the cone is in the shrunken cone
  have hev : ∀ y ∈ {y | dist₂ y x < r - t}, ∀ᶠ n in atTop,
      Nf ((bumpSeq n).normed volume) E B t y = 0 := by
    intro y hy
    have hlt : 0 < r - t - dist₂ y x := by simp only [mem_ofPred_eq] at hy; linarith
    have := (tendsto_order.1 (tendsto_bumpSeq_rOut.const_mul 3)).2 _
      (by linarith : 3 * 0 < r - t - dist₂ y x)
    filter_upwards [this] with n hn
    exact hcone n y (by simp only [ε]; linarith)
  have comp := fun n y (hn : Nf ((bumpSeq n).normed volume) E B t y = 0) =>
    eq_zero_of_dens_eq_zero hn
  have haE : ∀ k, ∀ᵐ y ∂volume.restrict {y | dist₂ y x < r - t}, axV (E t) k y = 0 := fun k =>
    ae_eq_zero_of_mol_eventually hΩ _ hS hSΩ fun y hy => (hev y hy).mono fun n hn =>
      (comp n y hn).1 k
  have hτE : ∀ᵐ y ∂volume.restrict {y | dist₂ y x < r - t}, trV (E t) y = 0 :=
    ae_eq_zero_of_mol_eventually hΩ _ hS hSΩ fun y hy => (hev y hy).mono fun n hn =>
      (comp n y hn).2.1
  have haB : ∀ k, ∀ᵐ y ∂volume.restrict {y | dist₂ y x < r - t}, axV (B t) k y = 0 := fun k =>
    ae_eq_zero_of_mol_eventually hΩ _ hS hSΩ fun y hy => (hev y hy).mono fun n hn =>
      (comp n y hn).2.2.1 k
  have hτB : ∀ᵐ y ∂volume.restrict {y | dist₂ y x < r - t}, trV (B t) y = 0 :=
    ae_eq_zero_of_mol_eventually hΩ _ hS hSΩ fun y hy => (hev y hy).mono fun n hn =>
      (comp n y hn).2.2.2
  filter_upwards [ae_all_iff.2 haE, hτE, ae_all_iff.2 haB, hτB] with y h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end Limit

/-! ## Interior TSD propagation for the thesis' system (4.14) -/

section Main

variable {Ω : Set R3}

/-- `X(y)` is symmetric and trace-free (pointwise, for the chosen representatives). -/
def SymTF (X : L2M Ω) (y : R3) : Prop := (∀ i j, X (i, j) y = X (j, i) y) ∧ ∑ i, X (i, i) y = 0

theorem ae_symTF_of_viol (X : L2M Ω) {S : Set R3} (hSΩ : S ⊆ Ω)
    (h : ∀ᵐ y ∂volume.restrict S, (∀ k, axV X k y = 0) ∧ trV X y = 0) :
    ∀ᵐ y ∂volume.restrict S, SymTF X y := by
  have ha : ∀ k, ∀ᵐ y ∂volume.restrict S, axV X k y = X (k + 1, k + 2) y - X (k + 2, k + 1) y :=
    fun k => ae_restrict_of_ae_restrict_of_subset hSΩ (Lp.coeFn_sub _ _)
  have ht : ∀ᵐ y ∂volume.restrict S, trV X y = X (0, 0) y + X (1, 1) y + X (2, 2) y := by
    have e : trV X = X (0, 0) + X (1, 1) + X (2, 2) := by simp [trV, Fin.sum_univ_three]
    rw [e]
    refine ae_restrict_of_ae_restrict_of_subset hSΩ ?_
    filter_upwards [Lp.coeFn_add (X (0, 0) + X (1, 1)) (X (2, 2)),
      Lp.coeFn_add (X (0, 0)) (X (1, 1))] with y h1 h2
    rw [h1, Pi.add_apply, h2, Pi.add_apply]
  filter_upwards [h, ae_all_iff.2 ha, ht] with y ⟨h1, h2⟩ h3 h4
  have e0 := (h3 0).symm.trans (h1 0)
  have e1 := (h3 1).symm.trans (h1 1)
  have e2 := (h3 2).symm.trans (h1 2)
  simp only [Fin.isValue, Fin.reduceAdd] at e0 e1 e2
  refine ⟨fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp <;> linarith
  · rw [Fin.sum_univ_three, ← h4, h2]

theorem symm_trace_viol_of_TSD {X : L2M Ω} (hX : X ∈ TSD Ω) : (∀ k, axV X k = 0) ∧ trV X = 0 :=
  ⟨fun k => by simp [axV, hX.1 (k + 1) (k + 2)], hX.2.1⟩

open Feec.HilbertComplex2 Feec.Constraints

/-- **Interior TSD propagation (finite speed of propagation) for (4.14) on a bounded domain.**
Let `(σ, E, B)` be a strong solution on `[0, T]` of the thesis' system (4.14) for the complex
`H̊¹ → H̊(curl) → L²` on a bounded open `Ω ⊆ ℝ³` (`thesisComplex`), with TSD data `(0, E₀, B₀)`.
If the Euclidean ball `{|z - x| < r}` lies in `Ω`, then for every `t ∈ [0, T]`:
`σ(t) = 0`, `E(t)` and `B(t)` are weakly divergence-free in `Ω`, and `E(t)`, `B(t)` are
symmetric and trace-free a.e. on the ball `{|y - x| < r - t}`. So the solution stays TSD on the
backward light cone of every ball in `Ω`; the TSD violation produced by the boundary condition
(`thesisComplex_not_propagate`) travels inward at most at unit speed.

Proof: Prop 4.18 (i) gives `σ ≡ 0`, `div E ≡ 0` and the reduced system; `div B` is conserved
(`weakEB_of_strongSolution`). The violations `W = (a(E), τ(E), a(B), τ(B))`, with `a` the axial
vector of the skew part and `τ` the trace, satisfy in the interior the closed first-order system
`∂_t a_E = -∇τ_B - curl a_B`, `∂_t τ_E = div a_B`, `∂_t a_B = ∇τ_E + curl a_E`,
`∂_t τ_B = -div a_E` (distributional Lemma 3.5, `sum_integral_curlM_cAx`; the closed system of
Prop 3.6), whose symbol has norm `|ξ|` (`abs_two_flux_le`). Mollify in space
(`Nf_eq_zero_of_cone`: weighted energy with cone weight `χ(R - t - √(δ² + |y - x|²))`) and let the
mollifier shrink (Lebesgue differentiation, `ae_eq_zero_of_mol_eventually`).

Existence: for data in `D(L)` the solution exists and is unique by Stone's theorem
(`Feec.HilbertComplex2.thm_4_6_unconditional`), so the statement is not vacuous.

Thesis gap: the thesis does not discuss the domain of dependence; Prop 4.17 claims global TSD
propagation, which fails (`thesisComplex_not_propagate`). This is what survives locally. -/
theorem thesisComplex_TSD_cone (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {E₀ B₀ : L2M Ω}
    (hE₀ : E₀ ∈ TSD Ω) (hB₀ : B₀ ∈ TSD Ω) {T : ℝ} {U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω)}
    (hU : IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) E₀ B₀) 0 U)
    {x : R3} {r : ℝ} (hr : ∀ z, dist₂ z x < r → z ∈ Ω) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).1 = 0 ∧
      (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1 ∈ HdivZero Ω ∧
      (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2 ∈ HdivZero Ω ∧
      ∀ᵐ y ∂volume.restrict {y | dist₂ y x < r - t},
        SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1 y ∧
          SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2 y := by
  obtain ⟨hσ, hW⟩ := weakEB_of_strongSolution hΩ hb hE₀ hB₀ hU
  have hU0 : tot (L2V Ω) (L2M Ω) (L2M Ω) (U 0) = (0, E₀, B₀) := by rw [hU.init, tot_ini]
  have h0 : (∀ k, axV ((tot (L2V Ω) (L2M Ω) (L2M Ω) (U 0)).2.1) k = 0) ∧
      trV ((tot (L2V Ω) (L2M Ω) (L2M Ω) (U 0)).2.1) = 0 ∧
      (∀ k, axV ((tot (L2V Ω) (L2M Ω) (L2M Ω) (U 0)).2.2) k = 0) ∧
      trV ((tot (L2V Ω) (L2M Ω) (L2M Ω) (U 0)).2.2) = 0 := by
    rw [hU0]
    exact ⟨(symm_trace_viol_of_TSD hE₀).1, (symm_trace_viol_of_TSD hE₀).2,
      (symm_trace_viol_of_TSD hB₀).1, (symm_trace_viol_of_TSD hB₀).2⟩
  have hv := hW.ae_viol_eq_zero hΩ h0 hr ht
  have hSΩ : {y | dist₂ y x < r - t} ⊆ Ω := fun y hy => hr y (by
    simp only [mem_ofPred_eq] at hy; linarith [ht.1])
  refine ⟨hσ t ht, hW.divE t ht, hW.divB t ht, ?_⟩
  have h1 := ae_symTF_of_viol _ hSΩ (hv.mono fun y hy => ⟨hy.1, hy.2.1⟩)
  have h2 := ae_symTF_of_viol _ hSΩ (hv.mono fun y hy => ⟨hy.2.2.1, hy.2.2.2⟩)
  filter_upwards [h1, h2] with y h1 h2 using ⟨h1, h2⟩

/-- The **domain of dependence** of `Ω` at time `t`: the points whose Euclidean distance to
`ℝ³ \ Ω` exceeds `t`. -/
def depDomain (Ω : Set R3) (t : ℝ) : Set R3 := {y | ∃ r, t < r ∧ ∀ z, dist₂ z y < r → z ∈ Ω}

theorem depDomain_subset {t : ℝ} (ht : 0 ≤ t) : depDomain Ω t ⊆ Ω := fun y ⟨r, htr, h⟩ =>
  h y (by rw [dist₂_self]; linarith)


/-- `depDomain Ω t` is the union of the cones `{|y - x| < r - t}` over the Euclidean balls
`{|z - x| < r} ⊆ Ω`. -/
theorem depDomain_eq_iUnion (t : ℝ) :
    depDomain Ω t = ⋃ p : {p : R3 × ℝ // ∀ z, dist₂ z p.1 < p.2 → z ∈ Ω},
      {y | dist₂ y p.1.1 < p.1.2 - t} := by
  ext y
  simp only [depDomain, mem_iUnion, mem_ofPred_eq, Subtype.exists, Prod.exists]
  constructor
  · rintro ⟨r, htr, h⟩
    exact ⟨y, r, h, by rw [dist₂_self]; linarith⟩
  · rintro ⟨q, r, h, hy⟩
    refine ⟨r - dist₂ y q, by linarith, fun z hz => h z ?_⟩
    linarith [dist₂_triangle z y q]

/-- **TSD on the domain of dependence.** Under the hypotheses of `thesisComplex_TSD_cone`, for
every `t ∈ [0, T]`, `E(t)` and `B(t)` are symmetric and trace-free a.e. on `depDomain Ω t`, the
set of points at Euclidean distance `> t` from `ℝ³ \ Ω` (and divergence-free, `σ(t) = 0`, on
all of `Ω`). -/
theorem thesisComplex_TSD_depDomain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {E₀ B₀ : L2M Ω}
    (hE₀ : E₀ ∈ TSD Ω) (hB₀ : B₀ ∈ TSD Ω) {T : ℝ} {U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω)}
    (hU : IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) E₀ B₀) 0 U)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᵐ y ∂volume.restrict (depDomain Ω t),
      SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1 y ∧
        SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2 y := by
  set s : {p : R3 × ℝ // ∀ z, dist₂ z p.1 < p.2 → z ∈ Ω} → Set R3 :=
    fun p => {y | dist₂ y p.1.1 < p.1.2 - t}
  obtain ⟨I, hI, hIU⟩ := TopologicalSpace.isOpen_iUnion_countable s
    fun p => isOpen_ball₂ _ _
  rw [depDomain_eq_iUnion, ← hIU, ae_restrict_biUnion_iff _ hI]
  intro p _
  exact (thesisComplex_TSD_cone hΩ hb hE₀ hB₀ hU p.2 ht).2.2.2

/-- **Existence form.** For TSD data `(0, E₀, B₀) ∈ D(L)` and every `T`, (4.14) has a solution on
`[0, T]` (Stone's theorem; Thm 4.6), unique among strong solutions, and it is TSD on the domain
of dependence `depDomain Ω t` for every `t ∈ [0, T]`. -/
theorem thesisComplex_TSD_depDomain_exists (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {E₀ B₀ : L2M Ω} (hE₀ : E₀ ∈ TSD Ω) (hB₀ : B₀ ∈ TSD Ω)
    (hD : ini (L2V Ω) E₀ B₀ ∈ (thesisComplex hΩ hb).domL) (T : ℝ) :
    ∃ U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω),
      IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) E₀ B₀) 0 U ∧
      (∀ U', IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) E₀ B₀) 0 U' →
        EqOn U' U (Icc 0 T)) ∧
      ∀ t ∈ Icc 0 T, ∀ᵐ y ∂volume.restrict (depDomain Ω t),
        SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1 y ∧
          SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2 y := by
  obtain ⟨U, hU, huniq, -⟩ := (thesisComplex hΩ hb).thm_4_6_unconditional T hD
  exact ⟨U, hU.toIsStrongSolution, huniq, fun t ht =>
    thesisComplex_TSD_depDomain hΩ hb hE₀ hB₀ hU.toIsStrongSolution ht⟩

/-- Converse direction: a.e. symmetric and trace-free on `Ω` plus weakly divergence-free gives
`L²(TSD)`. -/
theorem mem_TSD_of_ae_symTF {X : L2M Ω} (hX : ∀ᵐ y ∂volume.restrict Ω, SymTF X y)
    (hd : X ∈ HdivZero Ω) : X ∈ TSD Ω := by
  refine ⟨fun i j => Lp.ext ?_, ?_, hd⟩
  · filter_upwards [hX] with y hy using hy.1 i j
  · have e : ∑ i, X (i, i) = X (0, 0) + X (1, 1) + X (2, 2) := by simp [Fin.sum_univ_three]
    rw [e]
    refine Lp.ext ?_
    filter_upwards [hX, Lp.coeFn_add (X (0, 0) + X (1, 1)) (X (2, 2)),
      Lp.coeFn_add (X (0, 0)) (X (1, 1)), Lp.coeFn_zero ℝ 2 (volume.restrict Ω)]
      with y hy h1 h2 h3
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, Pi.zero_apply, ← hy.2, Fin.sum_univ_three]

/-- **The boundary obstruction lives in the boundary layer** (existential-datum form; see
`thesisComplex_beta_violation_boundary_layer` for the explicit `β`). On every nonempty bounded
open `Ω ⊆ ℝ³` there is TSD data `(0, 0, B₀) ∈ D(L)` such that for every `T > 0` (4.14) has a strong
solution on `[0, T]` (Stone's theorem), and every such solution
* is TSD on the domain of dependence `depDomain Ω t` for every `t ∈ [0, T]`
  (`thesisComplex_TSD_depDomain`), but
* fails to be symmetric and trace-free on a non-null subset of the boundary layer
  `Ω \ depDomain Ω t` (points within distance `t` of `∂Ω`) for some `t ∈ [0, T]`.

So the violation is excluded from the domain of dependence and is present in the layer of width
`t` at some `t ∈ [0, T]`. Correction: [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem thesisComplex_violation_boundary_layer (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    ∃ B₀ : L2M Ω, B₀ ∈ TSD Ω ∧ ini (L2V Ω) 0 B₀ ∈ (thesisComplex hΩ hb).domL ∧
      ∀ T > 0, (∃ U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω),
          IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) 0 B₀) 0 U) ∧
        ∀ U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω),
          IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) 0 B₀) 0 U →
            (∀ t ∈ Icc 0 T, ∀ᵐ y ∂volume.restrict (depDomain Ω t),
              SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1 y ∧
                SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2 y) ∧
            ∃ t ∈ Icc 0 T, ¬ ∀ᵐ y ∂volume.restrict (Ω \ depDomain Ω t),
              SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1 y ∧
                SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2 y := by
  obtain ⟨B₀, hB₀, hD, -, hall⟩ := thesisComplex_orbit_not_propagate_unconditional hΩ hb hne
  refine ⟨B₀, hB₀, hD, fun T hT => ⟨(hall T hT).1, fun U hU => ?_⟩⟩
  have h0 : (0 : L2M Ω) ∈ TSD Ω := Submodule.zero_mem _
  refine ⟨fun t ht => thesisComplex_TSD_depDomain hΩ hb h0 hB₀ hU ht, ?_⟩
  obtain ⟨t, ht, hnot⟩ := (hall T hT).2 U hU
  refine ⟨t, ht, fun hlayer => hnot ?_⟩
  have hdep := thesisComplex_TSD_depDomain hΩ hb h0 hB₀ hU ht
  have hall' : ∀ᵐ y ∂volume.restrict Ω, SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1 y ∧
      SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2 y := by
    have := (ae_restrict_union_iff _ _ _).2 ⟨hdep, hlayer⟩
    rwa [union_sdiff_cancel (depDomain_subset ht.1)] at this
  obtain ⟨hσ, hdE, hdB, -⟩ := thesisComplex_TSD_cone hΩ hb h0 hB₀ hU (x := 0) (r := 0)
    (fun z hz => absurd hz (not_lt.2 (Real.sqrt_nonneg _))) ht
  rw [mem_Kc]
  exact ⟨hσ, mem_TSD_of_ae_symTF (hall'.mono fun y hy => hy.1) hdE,
    mem_TSD_of_ae_symTF (hall'.mono fun y hy => hy.2) hdB⟩
end Main

/-! ## Arbitrary open domains, the whole space, and local forms -/

section Open

variable {Ω : Set R3} {T : ℝ} {E B : ℝ → L2M Ω}

/-- **Interior finite speed of propagation on an arbitrary open `Ω ⊆ ℝ³`** (bounded or not,
including `Ω = ℝ³`). Under `WeakEB` with vanishing initial violation, at time `t ∈ [0, T]` the
violations `a(E), τ(E), a(B), τ(B)` vanish a.e. on the domain of dependence `depDomain Ω t`. -/
theorem WeakEB.ae_viol_eq_zero_depDomain (hΩ : IsOpen Ω) (h : WeakEB Ω T E B)
    (h0 : (∀ k, axV (E 0) k = 0) ∧ trV (E 0) = 0 ∧ (∀ k, axV (B 0) k = 0) ∧ trV (B 0) = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᵐ y ∂volume.restrict (depDomain Ω t), (∀ k, axV (E t) k y = 0) ∧
      trV (E t) y = 0 ∧ (∀ k, axV (B t) k y = 0) ∧ trV (B t) y = 0 := by
  set s : {p : R3 × ℝ // ∀ z, dist₂ z p.1 < p.2 → z ∈ Ω} → Set R3 :=
    fun p => {y | dist₂ y p.1.1 < p.1.2 - t}
  obtain ⟨I, hI, hIU⟩ := TopologicalSpace.isOpen_iUnion_countable s
    fun p => isOpen_ball₂ _ _
  rw [depDomain_eq_iUnion, ← hIU, ae_restrict_biUnion_iff _ hI]
  intro p _
  exact h.ae_viol_eq_zero hΩ h0 p.2 ht

/-- The same, stated as pointwise symmetry and trace-freeness of the representatives. -/
theorem WeakEB.ae_symTF_depDomain (hΩ : IsOpen Ω) (h : WeakEB Ω T E B)
    (h0 : (∀ k, axV (E 0) k = 0) ∧ trV (E 0) = 0 ∧ (∀ k, axV (B 0) k = 0) ∧ trV (B 0) = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᵐ y ∂volume.restrict (depDomain Ω t), SymTF (E t) y ∧ SymTF (B t) y := by
  have hv := h.ae_viol_eq_zero_depDomain hΩ h0 ht
  have h1 := ae_symTF_of_viol _ (depDomain_subset ht.1) (hv.mono fun y hy => ⟨hy.1, hy.2.1⟩)
  have h2 := ae_symTF_of_viol _ (depDomain_subset ht.1) (hv.mono fun y hy => ⟨hy.2.2.1, hy.2.2.2⟩)
  filter_upwards [h1, h2] with y h1 h2 using ⟨h1, h2⟩

theorem depDomain_univ (t : ℝ) : depDomain (univ : Set R3) t = univ :=
  eq_univ_of_forall fun _ => ⟨t + 1, by linarith, fun _ _ => mem_univ _⟩

/-- **The whole space `ℝ³`.** With no boundary, the domain of dependence is all of `ℝ³`, so the
interior estimate gives global constraint propagation: if `E, B` satisfy `WeakEB` on `Ω = ℝ³`
and their violations vanish at `t = 0`, then `E(t)` and `B(t)` are symmetric and trace-free a.e.
on `ℝ³` for every `t ∈ [0, T]`. This is the TSD part of the conclusion of Prop 4.17 on `ℝ³`, by
the energy method instead of the projection hypothesis; the solution itself is assumed. -/
theorem WeakEB.ae_symTF_univ {E B : ℝ → L2M (univ : Set R3)} (h : WeakEB univ T E B)
    (h0 : (∀ k, axV (E 0) k = 0) ∧ trV (E 0) = 0 ∧ (∀ k, axV (B 0) k = 0) ∧ trV (B 0) = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᵐ y ∂volume.restrict (univ : Set R3), SymTF (E t) y ∧ SymTF (B t) y := by
  have := h.ae_symTF_depDomain isOpen_univ h0 ht
  rwa [depDomain_univ] at this

/-- On `ℝ³`, `WeakEB` with TSD data keeps `E(t)`, `B(t)` in `L²(TSD)` for all `t ∈ [0, T]`. -/
theorem WeakEB.mem_TSD_univ {E B : ℝ → L2M (univ : Set R3)} (h : WeakEB univ T E B)
    (hE₀ : E 0 ∈ TSD univ) (hB₀ : B 0 ∈ TSD univ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    E t ∈ TSD univ ∧ B t ∈ TSD univ := by
  have h0 : (∀ k, axV (E 0) k = 0) ∧ trV (E 0) = 0 ∧ (∀ k, axV (B 0) k = 0) ∧ trV (B 0) = 0 :=
    ⟨(symm_trace_viol_of_TSD hE₀).1, (symm_trace_viol_of_TSD hE₀).2,
      (symm_trace_viol_of_TSD hB₀).1, (symm_trace_viol_of_TSD hB₀).2⟩
  have hs := h.ae_symTF_univ h0 ht
  exact ⟨mem_TSD_of_ae_symTF (hs.mono fun y hy => hy.1) (h.divE t ht),
    mem_TSD_of_ae_symTF (hs.mono fun y hy => hy.2) (h.divB t ht)⟩

end Open

/-! ### Distributional and local `L²(TSD)` forms -/

section Local

variable {Ω : Set R3}

/-- If `V = 0` a.e. on a measurable `S`, then `∫_Ω V g = 0` for every `g` supported in `S`. -/
theorem integral_mul_eq_zero_of_ae {S : Set R3} (hS : MeasurableSet S) {V g : R3 → ℝ}
    (hV : ∀ᵐ y ∂volume.restrict S, V y = 0) (hg : Function.support g ⊆ S) :
    ∫ y, V y * g y ∂volume.restrict Ω = 0 := by
  refine integral_eq_zero_of_ae (ae_restrict_of_ae ?_)
  filter_upwards [(ae_restrict_iff' hS).1 hV] with y hy
  by_cases hyS : y ∈ S
  · simp [hy hyS]
  · simp [Function.notMem_support.1 fun h => hyS (hg h)]

theorem measurableSet_depDomain (t : ℝ) : MeasurableSet (depDomain Ω t) := by
  rw [depDomain_eq_iUnion]
  exact (isOpen_iUnion fun p => isOpen_ball₂ _ _).measurableSet

/-- Restriction `L²(Ω) → L²(S)` for `S ⊆ Ω`. -/
def resL2 {S : Set R3} (hS : S ⊆ Ω) (f : L2 Ω) : L2 S :=
  (Measure.restrict_restrict_of_subset (μ := volume) hS ▸ (Lp.memLp f).restrict S).toLp _

theorem coeFn_resL2 {S : Set R3} (hS : S ⊆ Ω) (f : L2 Ω) :
    (resL2 hS f : R3 → ℝ) =ᵐ[volume.restrict S] f :=
  MemLp.coeFn_toLp _

/-- Restriction `L²(Ω; ℝ³ˣ³) → L²(S; ℝ³ˣ³)`, componentwise. -/
def resM {S : Set R3} (hS : S ⊆ Ω) (X : L2M Ω) : L2M S := WithLp.toLp 2 fun ij => resL2 hS (X ij)

/-- **Local `L²(TSD)`.** If `X ∈ H(div, 0; Ω)` is symmetric and trace-free a.e. on `S ⊆ Ω`, its
restriction to `S` lies in `L²(TSD)(S)` (symmetric, trace-free, weakly divergence-free in `S`). -/
theorem resM_mem_TSD (hΩ : IsOpen Ω) {S : Set R3} (hS : S ⊆ Ω) {X : L2M Ω}
    (hX : X ∈ HdivZero Ω) (hsym : ∀ᵐ y ∂volume.restrict S, SymTF X y) : resM hS X ∈ TSD S := by
  have hc : ∀ ij, ((resM hS X) ij : R3 → ℝ) =ᵐ[volume.restrict S] X ij := fun ij =>
    coeFn_resL2 hS (X ij)
  refine mem_TSD_of_ae_symTF ?_ fun φ hφ => ?_
  · filter_upwards [hsym, ae_all_iff.2 hc] with y hy hcy
    refine ⟨fun i j => ?_, ?_⟩
    · rw [hcy, hcy, hy.1]
    · simp only [hcy]; exact hy.2
  · have hφΩ : ∀ i, IsTest Ω (φ i) := fun i =>
      ⟨(hφ i).contDiff, (hφ i).hasCompactSupport, (hφ i).tsupport_subset.trans hS⟩
    rw [← hX φ hφΩ]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [integral_congr_ae ((hc ij).mono fun y hy => by simp only; rw [hy]),
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet hS fun y hy => ?_]
    have : y ∉ tsupport (φ ij.1) := fun h => hy.2 ((hφ ij.1).tsupport_subset h)
    simp [pd, fderiv_of_notMem_tsupport (𝕜 := ℝ) this]

end Local


section ThesisLocal

variable {Ω : Set R3}

open Feec.HilbertComplex2 Feec.Constraints

/-- **Distributional form.** Under the hypotheses of `thesisComplex_TSD_cone`, at `t ∈ [0, T]`:
for every scalar `g` supported in the domain of dependence `depDomain Ω t` (in particular every
`g ∈ C_c^∞` with support in a cone `{|y - x| < r - t}`), `∫_Ω (E_{ij} - E_{ji}) g = 0` and
`∫_Ω (tr E) g = 0`, and likewise for `B`. -/
theorem thesisComplex_TSD_depDomain_distrib (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {E₀ B₀ : L2M Ω} (hE₀ : E₀ ∈ TSD Ω) (hB₀ : B₀ ∈ TSD Ω) {T : ℝ}
    {U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω)}
    (hU : IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) E₀ B₀) 0 U)
    {t : ℝ} (ht : t ∈ Icc 0 T) {g : R3 → ℝ} (hg : Function.support g ⊆ depDomain Ω t) :
    (∀ i j, ∫ y, ((tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1 (i, j) y -
        (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1 (j, i) y) * g y ∂volume.restrict Ω = 0) ∧
      ∫ y, (∑ i, (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1 (i, i) y) * g y
        ∂volume.restrict Ω = 0 ∧
      (∀ i j, ∫ y, ((tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2 (i, j) y -
        (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2 (j, i) y) * g y ∂volume.restrict Ω = 0) ∧
      ∫ y, (∑ i, (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2 (i, i) y) * g y
        ∂volume.restrict Ω = 0 := by
  have h := thesisComplex_TSD_depDomain hΩ hb hE₀ hB₀ hU ht
  have hm := measurableSet_depDomain (Ω := Ω) t
  refine ⟨fun i j => integral_mul_eq_zero_of_ae hm (h.mono fun y hy => ?_) hg,
    integral_mul_eq_zero_of_ae hm (h.mono fun y hy => hy.1.2) hg,
    fun i j => integral_mul_eq_zero_of_ae hm (h.mono fun y hy => ?_) hg,
    integral_mul_eq_zero_of_ae hm (h.mono fun y hy => hy.2.2) hg⟩
  · rw [hy.1.1 i j, sub_self]
  · rw [hy.2.1 i j, sub_self]

/-- **Local `L²(TSD)` form.** Under the hypotheses of `thesisComplex_TSD_cone`, at `t ∈ [0, T]`
the restrictions of `E(t)` and `B(t)` to the open set `depDomain Ω t` lie in
`L²(TSD)(depDomain Ω t)`: symmetric, trace-free and weakly divergence-free there. -/
theorem thesisComplex_TSD_depDomain_local (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {E₀ B₀ : L2M Ω} (hE₀ : E₀ ∈ TSD Ω) (hB₀ : B₀ ∈ TSD Ω) {T : ℝ}
    {U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω)}
    (hU : IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) E₀ B₀) 0 U)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    resM (depDomain_subset ht.1) (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1 ∈ TSD (depDomain Ω t) ∧
      resM (depDomain_subset ht.1) (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2 ∈
        TSD (depDomain Ω t) := by
  have h := thesisComplex_TSD_depDomain hΩ hb hE₀ hB₀ hU ht
  obtain ⟨-, hdE, hdB, -⟩ := thesisComplex_TSD_cone hΩ hb hE₀ hB₀ hU (x := 0) (r := 0)
    (fun z hz => absurd hz (not_lt.2 (Real.sqrt_nonneg _))) ht
  exact ⟨resM_mem_TSD hΩ _ hdE (h.mono fun y hy => hy.1),
    resM_mem_TSD hΩ _ hdB (h.mono fun y hy => hy.2)⟩

/-- The `L²` class of the explicit TSD field `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)` on `Ω`. -/
def betaL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : L2M Ω :=
  smoothField hΩ hb betaField (fun ij => (contDiff_betaField ij).continuous)

/-- For the explicit datum `(0, 0, β)`, every strong solution of (4.14) for `thesisComplex`
leaves `K = {0} × L²(TSD) × L²(TSD)` somewhere in `[0, T]`, `T > 0` (the argument of
`exists_data_not_propagate`, with `B₀ = β` pinned). -/
theorem beta_leaves_K (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {T : ℝ} (hT : 0 < T) {U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω)}
    (hU : IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) 0 (betaL2 hΩ hb)) 0 U) :
    ∃ t ∈ Icc 0 T, U t ∉ Kc (L2V Ω) (TSD Ω) (TSD Ω) := by
  set H := thesisComplex hΩ hb
  have hd1 := mem_closure_curlClosure hΩ hb
  have hβ : ∀ ij, ContDiff ℝ 1 (betaField ij) := fun ij => (contDiff_betaField ij).of_le (by simp)
  obtain ⟨hadj, hadj'⟩ := smoothField_mem_adjoint hΩ hb H hd1 hβ
  unfold betaL2 at hU
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  set K := constField hΩ hb diagA
  let ℓ : Tot (L2V Ω) (L2M Ω) (L2M Ω) →L[ℝ] ℝ := (innerSL ℝ K).comp
    ((ContinuousLinearMap.fst ℝ (L2M Ω) (L2M Ω)).comp ((ContinuousLinearMap.snd ℝ (L2V Ω) _).comp
      (Constraints.totL (W0 := L2V Ω) (W1 := L2M Ω) (W2 := L2M Ω)).toContinuousLinearMap))
  have hℓ : ∀ y, ℓ y = ⟪K, (tot (L2V Ω) (L2M Ω) (L2M Ω) y).2.1⟫ := fun y => rfl
  have hzero : ∀ t ∈ Icc 0 T, ℓ (U t) = 0 := by
    intro t ht
    have hD := (Feec.Constraints.mem_domL H).1 (hU.mem t ht)
    have hE : (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1 ∈ H.d1.domain :=
      (Submodule.mem_inf.1 hD.2.1).1
    rw [hℓ, real_inner_comm, inner_constField]
    refine Finset.sum_eq_zero fun ij _ => ?_
    rw [integral_eq_zero_of_mem_TSD_of_mem_HcurlZero hΩ hb ((mem_Kc).1 (hall t ht)).2.1
      ⟨_, hd1 ⟨_, hE⟩⟩, mul_zero]
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hd := ℓ.hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) (hU.deriv 0 h0)
  have hd0 : HasDerivWithinAt (ℓ ∘ U) 0 (Icc 0 T) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) (Icc 0 T) (0 : ℝ)).congr (fun t ht => hzero t ht)
      (hzero 0 h0)
  have heq := (uniqueDiffOn_Icc hT 0 h0).eq_deriv _ hd hd0
  have hp0 : H.pr0 ⟨U 0, hU.mem 0 h0⟩ = 0 := Subtype.ext (by simp [hU.init])
  have hp2 : H.prV2s ⟨U 0, hU.mem 0 h0⟩ =
      ⟨smoothField hΩ hb betaField (fun ij => (hβ ij).continuous), hadj⟩ :=
    Subtype.ext (by simp [hU.init])
  rw [Pi.zero_apply, add_zero, LinearPMap.neg_apply, _root_.map_neg, hℓ,
    Constraints.tot_waveOp] at heq
  simp only at heq
  rw [hp0, hp2, hadj', LinearPMap.map_zero, zero_add, real_inner_comm, inner_constField] at heq
  have hI : ∀ ij : Ix, ∫ x, smoothField hΩ hb (curlM betaField) (continuous_curlM hβ) ij x
      ∂volume.restrict Ω = volume.real Ω * -diagA ij.1 ij.2 := fun ij => by
    rw [integral_congr_ae (coeFn_smoothField hΩ hb _ _ ij)]
    simp only [curlM_betaField, integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
  simp only [hI] at heq
  have hpos : 0 < volume.real Ω := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hΩ.measure_pos volume hne).ne' hb.measure_lt_top.ne
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, diagA] at heq
  linarith

/-- **The boundary obstruction of the explicit datum `(0, 0, β)` lives in the boundary layer.**
On every nonempty bounded open `Ω ⊆ ℝ³`, `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)` is TSD, `(0, 0, β) ∈ D(L)`,
and for every `T > 0`, (4.14) has a strong solution on `[0, T]` (Stone's theorem), unique among
strong solutions; it is TSD a.e. on `depDomain Ω t` for every `t ∈ [0, T]`, but for some
`t ∈ [0, T]` it is not a.e. symmetric and trace-free on the boundary layer `Ω \ depDomain Ω t`.
Correction: [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem thesisComplex_beta_violation_boundary_layer (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    betaL2 hΩ hb ∈ TSD Ω ∧ ini (L2V Ω) 0 (betaL2 hΩ hb) ∈ (thesisComplex hΩ hb).domL ∧
      ∀ T > 0, ∃ U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω),
        IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) 0 (betaL2 hΩ hb)) 0 U ∧
        (∀ U', IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T
          (ini (L2V Ω) 0 (betaL2 hΩ hb)) 0 U' → EqOn U' U (Icc 0 T)) ∧
        (∀ t ∈ Icc 0 T, ∀ᵐ y ∂volume.restrict (depDomain Ω t),
          SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1 y ∧
            SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2 y) ∧
        ∃ t ∈ Icc 0 T, ¬ ∀ᵐ y ∂volume.restrict (Ω \ depDomain Ω t),
          SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1 y ∧
            SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2 y := by
  have hβ : ∀ ij, ContDiff ℝ 1 (betaField ij) := fun ij => (contDiff_betaField ij).of_le (by simp)
  have hB₀ : betaL2 hΩ hb ∈ TSD Ω := betaField_mem_TSD hΩ hb
  obtain ⟨hadj, -⟩ := smoothField_mem_adjoint hΩ hb (thesisComplex hΩ hb)
    (mem_closure_curlClosure hΩ hb) hβ
  have hD : ini (L2V Ω) 0 (betaL2 hΩ hb) ∈ (thesisComplex hΩ hb).domL := by
    rw [Feec.Constraints.mem_domL, tot_ini]
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, hadj⟩
  have h0 : (0 : L2M Ω) ∈ TSD Ω := Submodule.zero_mem _
  refine ⟨hB₀, hD, fun T hT => ?_⟩
  obtain ⟨U, hU, huniq, -⟩ := (thesisComplex hΩ hb).thm_4_6_unconditional T hD
  have hS := hU.toIsStrongSolution
  refine ⟨U, hS, huniq, fun t ht => thesisComplex_TSD_depDomain hΩ hb h0 hB₀ hS ht, ?_⟩
  obtain ⟨t, ht, hnot⟩ := beta_leaves_K hΩ hb hne hT hS
  refine ⟨t, ht, fun hlayer => hnot ?_⟩
  have hdep := thesisComplex_TSD_depDomain hΩ hb h0 hB₀ hS ht
  have hall' : ∀ᵐ y ∂volume.restrict Ω, SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1 y ∧
      SymTF (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2 y := by
    have := (ae_restrict_union_iff _ _ _).2 ⟨hdep, hlayer⟩
    rwa [union_sdiff_cancel (depDomain_subset ht.1)] at this
  obtain ⟨hσ, hdE, hdB, -⟩ := thesisComplex_TSD_cone hΩ hb h0 hB₀ hS (x := 0) (r := 0)
    (fun z hz => absurd hz (not_lt.2 (Real.sqrt_nonneg _))) ht
  rw [mem_Kc]
  exact ⟨hσ, mem_TSD_of_ae_symTF (hall'.mono fun y hy => hy.1) hdE,
    mem_TSD_of_ae_symTF (hall'.mono fun y hy => hy.2) hdB⟩

end ThesisLocal


end Feec.BoundedDomain
