module

public import Feec.FiniteElement.BrambleHilbert
public import Feec.FiniteElement.PolyInterpolation
public import Feec.FiniteElement.ShapeRegularInverse
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The `L²` Bramble–Hilbert lemma, Sobolev embedding and `L²` interpolation errors

`Feec.FiniteElement.BrambleHilbert` is the classical (`C^{r+1}`, sup-norm) form of the
Bramble–Hilbert lemma. This file proves its Sobolev (`L²`) form for smooth functions, with the
**averaged Taylor polynomial** `Q_m f (x) = ⨍_{y ∈ K} T_m f(y)(x)` (`avgTaylorPoly`; the Taylor
polynomial of degree `< m` at `y`, averaged uniformly over the base points `y ∈ K`), and derives
the Sobolev embedding and the `L²` interpolation error of the canonical interpolants of `P_rΛᵏ`
and `P_r⁻Λᵏ`. All statements are for functions of class `C^m` on an open neighbourhood of a
compact set (no Sobolev spaces): the seminorms are `∫_K ‖D^m f‖²`, `D^m` the iterated Fréchet
derivative. The averaged Taylor polynomial is the construction of Sobolev used by Brenner–Scott
(*The Mathematical Theory of Finite Element Methods*, Ch. 4), here averaged over `K` itself.

* **Polynomial part** (`avgTaylorPoly_mem_polyFunctions`, `avgTaylorPoly_eq_of_mem_polyFunctions`):
  `Q_{k+1} f ∈ P_k(ℝⁿ; G)` (expansion of `T_{k+1} f(y)(x)` in monomials of `x` with integrable
  coefficients in `y`, `avgTaylorPoly_eq_sum`), and `Q_{k+1} p = p` for `p ∈ P_k`.
* **Riesz-potential bound** (`enorm_sub_avgTaylorPoly_le_riesz`): for `K` compact convex with
  `|K| > 0`, `‖x - y‖ ≤ d` on `K` and `x ∈ K`,
  `‖f x - Q_{k+1} f (x)‖ ≤ dⁿ / (n k! |K|) ∫_K ‖D^{k+1} f(z)‖ ‖x - z‖^{k+1-n} dz`
  (`rieszKernel`). Proof: Taylor's formula with integral remainder along `[y, x]`
  (`sub_taylorPoly_eq_integral`), the change of variables `z = y + t (x - y)` at fixed `t`
  (Jacobian `(1 - t)⁻ⁿ`, `lintegral_comp_add_smul_sub`), `‖x - z‖ ≤ (1 - t) d`, Tonelli, and
  `∫₀¹ (1 - t)^{-(n+1)} 1[‖x - z‖ ≤ (1 - t) d] dt ≤ dⁿ / (n ‖x - z‖ⁿ)`
  (`lintegral_inv_one_sub_pow_indicator_le`).
* **Kernel integrals** (`lintegral_rieszKernel_pow_le`, `lintegral_closedBall_pow_div_pow`):
  `∫_K ‖x - z‖^{q(m-n)} dz ≤ n |B₁| d^{n + q(m-n)} / (n + q(m-n))` for `q n < q m + n`, by polar
  coordinates (`MeasureTheory.integral_fun_norm_addHaar`).
* **`L²` Bramble–Hilbert** (`lintegral_sub_avgTaylorPoly_sq_le`), for every order `k + 1 ≥ 1`:
  `∫_K ‖f - Q_{k+1} f‖² ≤ (dⁿ/(n k! |K|) · C₁)² ∫_K ‖D^{k+1} f‖²`, by a Schur test on the
  symmetric Riesz kernel (weighted Cauchy–Schwarz `lintegral_mul_sq_le`, Tonelli). The seminorms
  of order `j ≤ k` (`lintegral_iteratedFDeriv_sub_avgTaylorPoly_sq_le`) follow from
  `D (Q_{k+1} f) = Q_k (D f)` (`hasFDerivAt_avgTaylorPoly`, differentiation under the integral
  sign) by induction on `j`.
* **Sobolev embedding** (`enorm_sub_avgTaylorPoly_le_L2`), for `2(k + 1) > n`:
  `sup_K ‖f - Q_{k+1} f‖ ≤ dⁿ/(n k! |K|) · C₂^{1/2} (∫_K ‖D^{k+1} f‖²)^{1/2}` (Cauchy–Schwarz,
  `‖x - ·‖^{2(k+1-n)}` integrable).
* **Interpolation on `T̂`** (`IsRefInterpolant.lintegral_sub_sq_le_L2`): every reference
  interpolant `I` that is stable in `C⁰(T̂)` and reproduces `P_s`
  (`Feec.FiniteElement.IsRefInterpolant n s 0`) satisfies
  `∫_{T̂} ‖f - I f‖² ≤ K ∫_{T̂} ‖D^{s+1} f‖²` if `2(s + 1) > n` (`K = refL2Const n s C`), since
  `f - I f = (f - p) - I (f - p)` with `p = Q_{s+1} f` and the Sobolev embedding.
* **Transport** (`lintegral_sub_transportInterp_sq_le_L2`): on any `n`-simplex `T`,
  `∫_T ‖u - Π_T u‖² ≤ (‖Φ⁻¹‖ ‖Φ‖ ‖B_T‖^{s+1})² K ∫_T ‖D^{s+1} u‖²` (the Jacobians cancel), and on
  a shape-regular family with `‖B_T‖ ≤ C₀ h_T`
  (`lintegral_sub_transportInterp_sq_le_L2_of_isShapeRegular`). For differential forms on
  homothetic copies `T = t + h K` (`Feec.FiniteElement.transportInterp_polyRefInterp_eq`):
  `‖w - Π_T w‖²_{L²(T)} ≤ C h^{2(s+1)} ∫_T ‖D^{s+1} w‖²` for `P_rΛᵏ`, `s ≤ r`
  (`exists_formL2Sq_sub_polyInterp_le_L2`) and `P_r⁻Λᵏ`, `s ≤ r - 1`
  (`exists_formL2Sq_sub_polyMinusInterp_le_L2`), uniformly over finitely many reference simplices
  (`..._uniform`), and the graph-norm part `‖dw - d Π_T w‖²_{L²(T)}` through the commuting
  property (`exists_formL2Sq_extDeriv_sub_polyInterp_le_L2`,
  `exists_formL2Sq_extDeriv_sub_polyMinusInterp_le_L2`).
* **Non-vacuity** (`lintegral_sub_avgTaylorPoly_sq_nonvacuous`,
  `lintegral_sub_lagrangeP1_sq_nonvacuous`): for the monomial `x₀^{k+1}` both sides of the
  Bramble–Hilbert estimate are nonzero, and in dimensions `1 ≤ n ≤ 3` so are both sides of the
  reference interpolation estimate for `P₁` Lagrange interpolation and `x₀²`.

**The restriction `2(s + 1) > n`.** The Bramble–Hilbert part (`lintegral_sub_avgTaylorPoly_sq_le`
and its derivative versions) holds for every order `≥ 1` in every dimension. The interpolation
estimates need `2(s + 1) > n`: the moment degrees of freedom of `Π_T` (`∫_f tr_f ω ∧ η`, down
to vertex values) need point values, which `H^{s+1}` controls only through the Sobolev embedding
`H^{s+1} ⊂ C⁰` ([Evans2010], §5.6). In dimension `n ≤ 3` this is every `s ≥ 1`, and `s ≥ 0` for
`n = 1`. The dimension is assumed `n ≥ 1` (the time integral of the Riesz argument is `1/n`).

## Main definitions

* `Feec.FiniteElement.avgTaylorPoly K f m`: the averaged Taylor polynomial `Q_m f`.
* `Feec.FiniteElement.rieszKernel n m x z`: `‖x - z‖^m / ‖x - z‖ⁿ` in `ℝ≥0∞`.
* `Feec.FiniteElement.avgTaylorConst`, `Feec.FiniteElement.rieszConst`,
  `Feec.FiniteElement.refL2Const`, `Feec.FiniteElement.formTransportConst`: explicit constants.

## Main results

* `sub_taylorPoly_eq_integral`: Taylor's formula with integral remainder.
* `enorm_sub_avgTaylorPoly_le_riesz`: the Riesz-potential bound.
* `lintegral_sub_avgTaylorPoly_sq_le`, `lintegral_iteratedFDeriv_sub_avgTaylorPoly_sq_le`:
  **`L²` Bramble–Hilbert**.
* `enorm_sub_avgTaylorPoly_le_L2`: **Sobolev embedding** for `2(k + 1) > n`.
* `IsRefInterpolant.lintegral_sub_sq_le_L2`: the reference interpolation error in `L²`.
* `lintegral_sub_transportInterp_sq_le_L2`, `exists_formL2Sq_sub_polyInterp_le_L2`,
  `exists_formL2Sq_sub_polyMinusInterp_le_L2`, `exists_formL2Sq_extDeriv_sub_polyInterp_le_L2`,
  `exists_formL2Sq_extDeriv_sub_polyMinusInterp_le_L2`, `..._uniform`: physical simplices.

## References

* [J. H. Bramble, S. R. Hilbert, *Estimation of Linear Functionals on Sobolev Spaces with Application to Fourier Transforms and Spline Interpolation*][BrambleHilbert1970]
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1
  (Thm 3.1.1, polynomial approximation; Thm 3.1.4, interpolation error; Thm 3.1.5, regular
  families)
* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.6 (Sobolev inequalities),
  §5.8.1 (Poincaré inequalities)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Feec.FiniteElement

variable {n : ℕ} {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### The averaged Taylor polynomial -/

section AvgTaylor

/-- The **averaged Taylor polynomial** of order `m` (degree `< m`) of `f` over `K`:
`Q_m f (x) = ⨍_{y ∈ K} T_m f(y)(x)`, the Taylor polynomial at `y` averaged uniformly over the
base points `y ∈ K`. -/
def avgTaylorPoly [CompleteSpace G] (K : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → G) (m : ℕ)
    (x : Fin n → ℝ) : G :=
  ⨍ y in K, taylorPoly f y m x

/-- The coefficient of the monomial `∏_{l ∈ s} x_{σ l}` in the expansion of the `i`-th Taylor
term at `y`. -/
def taylorCoeff (f : (Fin n → ℝ) → G) (i : ℕ) (σ : Fin i → Fin n) (s : Finset (Fin i))
    (y : Fin n → ℝ) : G :=
  ((i.factorial : ℝ)⁻¹ * ∏ l ∈ sᶜ, (-y (σ l))) •
    iteratedFDeriv ℝ i f y (fun l => fun j => if σ l = j then (1 : ℝ) else 0)

/-- Expansion of the Taylor polynomial at `y` in monomials of `x`. -/
theorem taylorPoly_eq_sum_taylorCoeff (f : (Fin n → ℝ) → G) (y x : Fin n → ℝ) (m : ℕ) :
    taylorPoly f y m x = ∑ i ∈ Finset.range m, ∑ σ : Fin i → Fin n, ∑ s : Finset (Fin i),
      (∏ l ∈ s, x (σ l)) • taylorCoeff f i σ s y := by
  unfold taylorPoly
  refine Finset.sum_congr rfl fun i _ => ?_
  set A := iteratedFDeriv ℝ i f y
  have hx : x - y = ∑ j, (x - y) j • (fun k => if j = k then (1 : ℝ) else 0) :=
    pi_eq_sum_univ (x - y)
  rw [hx, A.map_sum (fun _ j => (x - y) j • (fun k => if j = k then (1 : ℝ) else 0)),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [A.map_smul_univ (fun l => (x - y) (σ l))
    (fun l => fun k => if σ l = k then (1 : ℝ) else 0)]
  have hprod : ∏ l, (x - y) (σ l) =
      ∑ s : Finset (Fin i), (∏ l ∈ s, x (σ l)) * ∏ l ∈ sᶜ, (-y (σ l)) := by
    simp_rw [Pi.sub_apply, sub_eq_add_neg]
    rw [Finset.prod_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.compl_eq_univ_sdiff]
  rw [hprod, Finset.sum_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [taylorCoeff, smul_smul]
  congr 1
  ring

/-- Continuity of the derivatives of a `C^N` function on an open set. -/
theorem continuousOn_iteratedFDeriv_of_isOpen {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {N : ℕ} {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U) {i : ℕ} (hi : i ≤ N) :
    ContinuousOn (iteratedFDeriv ℝ i f) U := fun y hy =>
  ((hf.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right (m := 0) (i := i)
    (by rw [zero_add]; exact_mod_cast hi)).continuousAt.continuousWithinAt

theorem continuousOn_taylorCoeff {r : ℕ} {f : (Fin n → ℝ) → G} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ r f U) {i : ℕ} (hi : i ≤ r) (σ : Fin i → Fin n)
    (s : Finset (Fin i)) : ContinuousOn (taylorCoeff f i σ s) U := by
  unfold taylorCoeff
  refine ContinuousOn.smul (continuousOn_const.mul (continuousOn_finsetProd _ fun l _ =>
    (continuous_apply (σ l)).continuousOn.neg)) ?_
  exact (continuous_eval_const _).comp_continuousOn (continuousOn_iteratedFDeriv_of_isOpen hU hf hi)

/-- The monomial `x ↦ (∏_{l ∈ s} x_{σ l}) • c` lies in `P_r` for `#s ≤ r`. -/
theorem prod_smul_mem_polyFunctions {i r : ℕ} (σ : Fin i → Fin n) (s : Finset (Fin i))
    (hs : s.card ≤ r) (c : G) :
    (fun x : Fin n → ℝ => (∏ l ∈ s, x (σ l)) • c) ∈ polyFunctions n r G := by
  refine Submodule.subset_span ⟨∏ l ∈ s, MvPolynomial.X (σ l), ?_, c, ?_⟩
  · refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    calc ∑ l ∈ s, (MvPolynomial.X (σ l) : MvPolynomial (Fin n) ℝ).totalDegree
        = ∑ _l ∈ s, 1 := Finset.sum_congr rfl fun l _ => MvPolynomial.totalDegree_X _
      _ ≤ r := by simpa using hs
  · funext x
    simp

/-- Expansion of the averaged Taylor polynomial in monomials of `x`. -/
theorem avgTaylorPoly_eq_sum [CompleteSpace G] {K U : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {r : ℕ} {f : (Fin n → ℝ) → G} (hf : ContDiffOn ℝ r f U)
    (x : Fin n → ℝ) :
    avgTaylorPoly K f (r + 1) x = ∑ i ∈ Finset.range (r + 1), ∑ σ : Fin i → Fin n,
      ∑ s : Finset (Fin i), (∏ l ∈ s, x (σ l)) • ⨍ y in K, taylorCoeff f i σ s y := by
  have hint : ∀ i ∈ Finset.range (r + 1), ∀ (σ : Fin i → Fin n) (s : Finset (Fin i)),
      IntegrableOn (taylorCoeff f i σ s) K := fun i hi σ s =>
    ((continuousOn_taylorCoeff hU hf (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) σ s).mono
      hKU).integrableOn_compact hK
  have hint' : ∀ i ∈ Finset.range (r + 1), ∀ (σ : Fin i → Fin n) (s : Finset (Fin i)),
      IntegrableOn (fun y => (∏ l ∈ s, x (σ l)) • taylorCoeff f i σ s y) K := fun i hi σ s =>
    (hint i hi σ s).smul _
  simp only [avgTaylorPoly, taylorPoly_eq_sum_taylorCoeff, setAverage_eq]
  rw [integral_finsetSum _ fun i hi => integrable_finsetSum _ fun σ _ =>
    integrable_finsetSum _ fun s _ => hint' i hi σ s, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ fun σ _ => integrable_finsetSum _ fun s _ => hint' i hi σ s,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_finsetSum _ fun s _ => hint' i hi σ s, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_smul, smul_comm]

/-- **The averaged Taylor polynomial of order `r + 1` lies in `P_r`** (for `f` of class `C^r` on
an open neighbourhood of the compact set `K`, so that the coefficients are integrable). -/
theorem avgTaylorPoly_mem_polyFunctions [CompleteSpace G] {K U : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {r : ℕ} {f : (Fin n → ℝ) → G}
    (hf : ContDiffOn ℝ r f U) : avgTaylorPoly K f (r + 1) ∈ polyFunctions n r G := by
  have : avgTaylorPoly K f (r + 1) = ∑ i ∈ Finset.range (r + 1), ∑ σ : Fin i → Fin n,
      ∑ s : Finset (Fin i), fun x : Fin n → ℝ =>
        (∏ l ∈ s, x (σ l)) • ⨍ y in K, taylorCoeff f i σ s y := by
    funext x
    simp only [Finset.sum_apply]
    exact avgTaylorPoly_eq_sum hK hU hKU hf x
  rw [this]
  refine Submodule.sum_mem _ fun i hi => Submodule.sum_mem _ fun σ _ =>
    Submodule.sum_mem _ fun s _ => prod_smul_mem_polyFunctions σ s ?_ _
  calc s.card ≤ (Finset.univ : Finset (Fin i)).card := Finset.card_le_univ s
    _ = i := by simp
    _ ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)

/-- **The averaged Taylor polynomial reproduces `P_r`**: `Q_{r+1} p = p` for `p ∈ P_r`, if
`0 < |K| < ∞`. -/
theorem avgTaylorPoly_eq_of_mem_polyFunctions [CompleteSpace G] {K : Set (Fin n → ℝ)}
    (hK0 : volume K ≠ 0) (hKt : volume K ≠ ∞) {r : ℕ} {p : (Fin n → ℝ) → G}
    (hp : p ∈ polyFunctions n r G) (x : Fin n → ℝ) : avgTaylorPoly K p (r + 1) x = p x := by
  simp only [avgTaylorPoly, taylorPoly_eq_of_mem_polyFunctions hp]
  exact setAverage_const hK0 hKt _

end AvgTaylor

/-! ### Taylor's formula with integral remainder -/

section Remainder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The Taylor sum along the segment `t ↦ y + t v`:
`∑_{i ≤ k} ((1 - t)^i / i!) D^i f(y + t v)(v, …, v)`. -/
def taylorSegment (f : E → F) (y v : E) (k : ℕ) (t : ℝ) : F :=
  ∑ i ∈ Finset.range (k + 1),
    ((1 - t) ^ i / i.factorial) • iteratedFDeriv ℝ i f (y + t • v) (fun _ => v)

theorem hasDerivAt_iteratedFDeriv_segment {N : ℕ} {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ N f U) {i : ℕ} (hi : i < N) {y v : E} {t : ℝ} (ht : y + t • v ∈ U) :
    HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ i f (y + t • v) (fun _ => v))
      (iteratedFDeriv ℝ (i + 1) f (y + t • v) (fun _ => v)) t := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ i f) (y + t • v) :=
    (hf.contDiffAt (hU.mem_nhds ht)).differentiableAt_iteratedFDeriv (by exact_mod_cast hi)
  have hγ : HasDerivAt (fun t : ℝ => y + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add y
  have h1 := hd.hasFDerivAt.comp_hasDerivAt t hγ
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => E) F
    (fun _ => v)).hasFDerivAt.comp_hasDerivAt t h1
  have e : iteratedFDeriv ℝ (i + 1) f (y + t • v) (fun _ => v) =
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => E) F (fun _ => v))
        (fderiv ℝ (iteratedFDeriv ℝ i f) (y + t • v) v) := by
    rw [iteratedFDeriv_succ_apply_left]; rfl
  rw [e]
  exact h2

theorem hasDerivAt_taylorSegment {N : ℕ} {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ N f U) {y v : E} {t : ℝ} (ht : y + t • v ∈ U) :
    ∀ k : ℕ, k < N → HasDerivAt (taylorSegment f y v k)
      (((1 - t) ^ k / k.factorial) • iteratedFDeriv ℝ (k + 1) f (y + t • v) (fun _ => v)) t := by
  have hc : ∀ i : ℕ, HasDerivAt (fun t : ℝ => (1 - t) ^ i / (i.factorial : ℝ))
      (((i : ℝ) * (1 - t) ^ (i - 1) * (-1)) / i.factorial) t := fun i => by
    have := (((hasDerivAt_id t).const_sub 1).pow i).div_const (i.factorial : ℝ)
    simpa using this
  intro k
  induction k with
  | zero =>
    intro hN
    have h := (hc 0).smul (hasDerivAt_iteratedFDeriv_segment hU hf hN ht)
    have he : taylorSegment f y v 0 = fun t : ℝ =>
        ((1 - t) ^ 0 / (Nat.factorial 0 : ℝ)) • iteratedFDeriv ℝ 0 f (y + t • v) (fun _ => v) := by
      funext t; simp [taylorSegment]
    rw [he]
    convert h using 1
    simp
  | succ k ih =>
    intro hN
    have h1 := ih (by omega)
    have h2 := (hc (k + 1)).smul (hasDerivAt_iteratedFDeriv_segment hU hf hN ht)
    have he : taylorSegment f y v (k + 1) = fun t : ℝ => taylorSegment f y v k t +
        ((1 - t) ^ (k + 1) / ((k + 1).factorial : ℝ)) •
          iteratedFDeriv ℝ (k + 1) f (y + t • v) (fun _ => v) := by
      funext t; rw [taylorSegment, Finset.sum_range_succ]; rfl
    rw [he]
    convert h1.add h2 using 1
    rw [add_comm (((1 - t) ^ (k + 1) / _) • _), ← add_assoc, ← add_smul]
    have : (1 - t) ^ k / (k.factorial : ℝ) +
        ((k + 1 : ℕ) : ℝ) * (1 - t) ^ (k + 1 - 1) * (-1) / ((k + 1).factorial : ℝ) = 0 := by
      rw [Nat.factorial_succ, Nat.add_sub_cancel]
      push_cast
      field_simp
      ring
    rw [this, zero_smul, zero_add]

/-- **Taylor's formula with integral remainder**: for `f` of class `C^{k+1}` on an open set
containing the segment `[y, x]`,
`f x - T_{k+1} f(y)(x) = ∫₀¹ ((1 - t)^k / k!) D^{k+1} f(y + t (x - y))(x - y, …, x - y) dt`. -/
theorem sub_taylorPoly_eq_integral [CompleteSpace F] {k : ℕ} {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (k + 1) f U) {x y : E}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, y + t • (x - y) ∈ U) :
    f x - taylorPoly f y (k + 1) x = ∫ t in (0 : ℝ)..1, ((1 - t) ^ k / k.factorial) •
      iteratedFDeriv ℝ (k + 1) f (y + t • (x - y)) (fun _ => x - y) := by
  have hseg' : ∀ t ∈ uIcc (0 : ℝ) 1, y + t • (x - y) ∈ U := fun t ht =>
    hseg t (by rwa [uIcc_of_le zero_le_one] at ht)
  have hcont : ContinuousOn (fun t : ℝ => ((1 - t) ^ k / k.factorial) •
      iteratedFDeriv ℝ (k + 1) f (y + t • (x - y)) (fun _ => x - y)) (uIcc 0 1) := by
    refine ContinuousOn.smul (by fun_prop) ?_
    refine (continuous_eval_const _).comp_continuousOn ?_
    refine (continuousOn_iteratedFDeriv_of_isOpen hU hf le_rfl).comp
      (by fun_prop) fun t ht => hseg' t ht
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_taylorSegment (N := k + 1) hU (by exact_mod_cast hf) (hseg' t ht) k
      (Nat.lt_succ_self k))
    (hcont.intervalIntegrable)]
  have h1 : taylorSegment f y (x - y) k 1 = f x := by
    rw [taylorSegment, Finset.sum_range_succ']
    simp only [sub_self, one_smul, add_sub_cancel, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, iteratedFDeriv_zero_apply]
    rw [Finset.sum_eq_zero fun i _ => by simp, zero_add]
  have h0 : taylorSegment f y (x - y) k 0 = taylorPoly f y (k + 1) x := by
    rw [taylorSegment, taylorPoly]
    simp
  rw [h1, h0]

/-- The integral remainder in `ℝ≥0∞`:
`‖f x - T_{k+1} f(y)(x)‖ ≤ ∫₀¹ ((1 - t)^k / k!) ‖D^{k+1} f(y + t (x - y))‖ ‖x - y‖^{k+1} dt`. -/
theorem enorm_sub_taylorPoly_le [CompleteSpace F] {k : ℕ} {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (k + 1) f U) {x y : E}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, y + t • (x - y) ∈ U) :
    ‖f x - taylorPoly f y (k + 1) x‖ₑ ≤ ∫⁻ t in Ioo (0 : ℝ) 1,
      ENNReal.ofReal ((1 - t) ^ k / k.factorial) *
        ‖iteratedFDeriv ℝ (k + 1) f (y + t • (x - y))‖ₑ * ‖x - y‖ₑ ^ (k + 1) := by
  rw [sub_taylorPoly_eq_integral hU hf hseg, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [setLIntegral_congr Ioo_ae_eq_Ioc.symm]
  refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
  have hc : 0 ≤ (1 - t) ^ k / (k.factorial : ℝ) := by
    have : 0 ≤ 1 - t := by linarith [ht.2]
    positivity
  rw [enorm_smul, Real.enorm_eq_ofReal hc, mul_assoc]
  gcongr
  have h := (iteratedFDeriv ℝ (k + 1) f (y + t • (x - y))).le_opNNNorm (fun _ => x - y)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  simpa [enorm, ← ENNReal.coe_pow, ← ENNReal.coe_mul] using ENNReal.coe_le_coe.2 h

end Remainder

/-! ### Two integrals -/

section Integrals

/-- `∫₀^b (1 - t)^{-(n+1)} dt = ((1 - b)^{-n} - 1) / n` for `b < 1`. -/
theorem integral_inv_one_sub_pow (hn : 0 < n) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1) :
    ∫ t in (0 : ℝ)..b, ((1 - t) ^ (n + 1))⁻¹ = (((1 - b) ^ n)⁻¹ - 1) / n := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) b, HasDerivAt (fun t : ℝ => ((1 - t) ^ n)⁻¹ / n)
      ((1 - t) ^ (n + 1))⁻¹ t := by
    intro t ht
    rw [uIcc_of_le hb0] at ht
    have h1 : (1 - t) ≠ 0 := by linarith [ht.2]
    have h2 : HasDerivAt (fun t : ℝ => (1 - t) ^ n) (n * (1 - t) ^ (n - 1) * (-1)) t := by
      have := (hasDerivAt_pow n (1 - t)).comp t ((hasDerivAt_id t).const_sub 1)
      convert this using 1
      exact funext fun _ => rfl
    have h := (h2.inv (pow_ne_zero n h1)).div_const (n : ℝ)
    convert h using 1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    field_simp
    ring
  have hcont : ContinuousOn (fun t : ℝ => ((1 - t) ^ (n + 1))⁻¹) (uIcc 0 b) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun t ht => ?_
    rw [uIcc_of_le hb0] at ht
    exact pow_ne_zero _ (by linarith [ht.2])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp [sub_div]

/-- The time integral of the Riesz-potential argument:
`∫₀¹ (1 - t)^{-(n+1)} 1[a ≤ (1 - t) d] dt ≤ dⁿ / (n aⁿ)` for `a > 0`. -/
theorem lintegral_inv_one_sub_pow_indicator_le (hn : 0 < n) {a d : ℝ} (ha : 0 < a) :
    ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) *
        {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t ≤ ENNReal.ofReal (d ^ n / (n * a ^ n)) := by
  rcases le_or_gt d a with hda | hda
  · -- the indicator vanishes on `(0, 1)`
    have h0 : ∀ t ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) *
        {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t = 0 := by
      intro t ht
      have : ¬ a ≤ (1 - t) * d := by
        rcases le_or_gt d 0 with hd | hd
        · nlinarith [ht.2]
        · nlinarith [ht.1]
      simp [Set.indicator_of_notMem (show t ∉ {t : ℝ | a ≤ (1 - t) * d} from this)]
    refine (setLIntegral_mono' measurableSet_Ioo fun t ht => (h0 t ht).le).trans ?_
    simp
  have hd : 0 < d := ha.trans hda
  set b := 1 - a / d with hb_def
  have hb0 : 0 ≤ b := by
    rw [hb_def, sub_nonneg, div_le_one hd]; exact hda.le
  have hb1 : b < 1 := by rw [hb_def]; have := div_pos ha hd; linarith
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) *
      {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t ≤
        (Ioc 0 b).indicator (fun t => ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹)) t := by
    intro t ht
    by_cases hmem : a ≤ (1 - t) * d
    · have htb : t ≤ b := by
        rw [hb_def, le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hd]; linarith
      rw [Set.indicator_of_mem (show t ∈ {t : ℝ | a ≤ (1 - t) * d} from hmem),
        Set.indicator_of_mem (show t ∈ Ioc 0 b from ⟨ht.1, htb⟩)]
      simp
    · rw [Set.indicator_of_notMem (show t ∉ {t : ℝ | a ≤ (1 - t) * d} from hmem)]
      simp
  have hcont : ContinuousOn (fun t : ℝ => ((1 - t) ^ (n + 1))⁻¹) (Icc 0 b) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun t ht => pow_ne_zero _ (by linarith [ht.2])
  have hint : IntegrableOn (fun t : ℝ => ((1 - t) ^ (n + 1))⁻¹) (Ioc 0 b) :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  calc ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) *
        {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t
      ≤ ∫⁻ t in Ioo (0 : ℝ) 1,
          (Ioc 0 b).indicator (fun t => ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹)) t :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ ≤ ∫⁻ t, (Ioc 0 b).indicator (fun t => ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹)) t :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ t in Ioc 0 b, ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) :=
        lintegral_indicator measurableSet_Ioc _
    _ = ENNReal.ofReal (∫ t in Ioc 0 b, ((1 - t) ^ (n + 1))⁻¹) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioc
          fun t ht => inv_nonneg.2 (pow_nonneg (by linarith [ht.2]) _))).symm
    _ ≤ ENNReal.ofReal (d ^ n / (n * a ^ n)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← intervalIntegral.integral_of_le hb0, integral_inv_one_sub_pow hn hb0 hb1, hb_def,
          sub_sub_cancel, div_pow, inv_div]
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rw [div_le_div_iff₀ hn' (by positivity), sub_mul, one_mul]
        have : d ^ n / a ^ n * (n * a ^ n) = d ^ n * n := by field_simp
        rw [this]
        have : 0 ≤ (n : ℝ) * a ^ n := by positivity
        linarith

/-- Lebesgue integrals under a dilation: `∫ g(r y) dy = |r⁻ⁿ| ∫ g`. -/
theorem lintegral_comp_smul_fin (g : (Fin n → ℝ) → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    ∫⁻ y, g (r • y) = ENNReal.ofReal |(r ^ n)⁻¹| * ∫⁻ z, g z := by
  let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) := (Homeomorph.smul (Units.mk0 r hr)).toMeasurableEquiv
  calc ∫⁻ y, g (r • y) = ∫⁻ y, g (e y) := rfl
    _ = ∫⁻ z, g z ∂(Measure.map e volume) := (lintegral_map_equiv g e).symm
    _ = ENNReal.ofReal |(r ^ n)⁻¹| * ∫⁻ z, g z := by
        have he : (e : (Fin n → ℝ) → (Fin n → ℝ)) = fun y => r • y := rfl
        rw [he, Measure.map_addHaar_smul volume hr, lintegral_smul_measure, Module.finrank_fin_fun]
        rfl

/-- The change of variables `z = y + t (x - y) = (1 - t) y + t x`, `t ≠ 1`:
`∫ g(y + t (x - y)) dy = |(1 - t)⁻ⁿ| ∫ g`. -/
theorem lintegral_comp_add_smul_sub (g : (Fin n → ℝ) → ℝ≥0∞) (x : Fin n → ℝ) {t : ℝ}
    (ht : t ≠ 1) :
    ∫⁻ y, g (y + t • (x - y)) = ENNReal.ofReal |((1 - t) ^ n)⁻¹| * ∫⁻ z, g z := by
  have hs : (1 - t) ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  have e : ∀ y : Fin n → ℝ, y + t • (x - y) = (1 - t) • y + t • x := fun y => by
    rw [smul_sub, sub_smul, one_smul]; abel
  simp_rw [e]
  rw [lintegral_comp_smul_fin (fun w => g (w + t • x)) hs,
    lintegral_add_right_eq_self (fun w => g w) (t • x)]

/-- The indicator of a function continuous on a closed set is measurable. -/
theorem measurable_indicator_of_continuousOn {s : Set (Fin n → ℝ)} (hs : IsClosed s)
    {g : (Fin n → ℝ) → ℝ≥0∞} (hg : ContinuousOn g s) : Measurable (s.indicator g) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact hg.measurable_piecewise continuousOn_const hs.measurableSet

end Integrals

/-! ### The Riesz-potential bound for the remainder -/

section Riesz

/-- The Riesz kernel `‖x - z‖^m / ‖x - z‖^n` in `ℝ≥0∞`: `‖x - z‖^{m-n}` off the diagonal, `0` on
the diagonal if `m ≥ 1`. -/
def rieszKernel (n m : ℕ) (x z : Fin n → ℝ) : ℝ≥0∞ := ‖x - z‖ₑ ^ m / ‖x - z‖ₑ ^ n

theorem measurable_rieszKernel (m : ℕ) :
    Measurable (Function.uncurry (rieszKernel n m)) := by
  change Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => rieszKernel n m p.1 p.2
  unfold rieszKernel
  have : Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => ‖p.1 - p.2‖ₑ :=
    (continuous_enorm.comp (continuous_fst.sub continuous_snd)).measurable
  exact (this.pow_const m).div (this.pow_const n)

theorem measurable_rieszKernel_right (m : ℕ) (x : Fin n → ℝ) :
    Measurable (rieszKernel n m x) :=
  (measurable_rieszKernel m).of_uncurry_left

theorem rieszKernel_comm (m : ℕ) (x z : Fin n → ℝ) : rieszKernel n m x z = rieszKernel n m z x := by
  simp only [rieszKernel, ← enorm_neg (x - z), neg_sub]

/-- The per-point time integral of the Riesz argument. -/
theorem lintegral_time_le (hn : 0 < n) (k : ℕ) {d : ℝ} (hd : 0 ≤ d) (x z : Fin n → ℝ) (c : ℝ≥0∞) :
    ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ k / k.factorial) *
        ENNReal.ofReal |((1 - t) ^ n)⁻¹| * (c * (ENNReal.ofReal (1 - t)⁻¹ * ‖x - z‖ₑ) ^ (k + 1) *
          {p : ℝ × (Fin n → ℝ) | ‖x - p.2‖ ≤ (1 - p.1) * d}.indicator 1 (t, z)) ≤
      ENNReal.ofReal (d ^ n / (n * k.factorial)) * (c * rieszKernel n (k + 1) x z) := by
  rcases eq_or_ne x z with rfl | hxz
  · simp
  have ha : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hxz)
  set a := ‖x - z‖ with ha_def
  set A := ‖x - z‖ₑ with hA_def
  have hAa : A = ENNReal.ofReal a := by rw [hA_def, ha_def, ofReal_norm]
  set Cst := c * A ^ (k + 1) * ENNReal.ofReal (k.factorial : ℝ)⁻¹
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ k / k.factorial) *
      ENNReal.ofReal |((1 - t) ^ n)⁻¹| * (c * (ENNReal.ofReal (1 - t)⁻¹ * A) ^ (k + 1) *
        {p : ℝ × (Fin n → ℝ) | ‖x - p.2‖ ≤ (1 - p.1) * d}.indicator 1 (t, z)) =
      Cst * (ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) * {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t) := by
    intro t ht
    have h1t : 0 < 1 - t := by linarith [ht.2]
    have hreal : (1 - t) ^ k / k.factorial * |((1 - t) ^ n)⁻¹| * ((1 - t)⁻¹) ^ (k + 1) =
        ((1 - t) ^ (n + 1))⁻¹ * (k.factorial : ℝ)⁻¹ := by
      rw [abs_of_pos (by positivity)]
      generalize 1 - t = u at h1t ⊢
      have hu : u ≠ 0 := h1t.ne'
      rw [inv_pow]
      field_simp
      ring
    have hind : {p : ℝ × (Fin n → ℝ) | ‖x - p.2‖ ≤ (1 - p.1) * d}.indicator
        (1 : ℝ × (Fin n → ℝ) → ℝ≥0∞) (t, z) =
        {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t := by
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, ha_def, Pi.one_apply]
    rw [hind, mul_pow, ← ENNReal.ofReal_pow (inv_nonneg.2 h1t.le)]
    calc ENNReal.ofReal ((1 - t) ^ k / k.factorial) * ENNReal.ofReal |((1 - t) ^ n)⁻¹| *
          (c * (ENNReal.ofReal ((1 - t)⁻¹ ^ (k + 1)) * A ^ (k + 1)) *
            {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t)
        = ENNReal.ofReal ((1 - t) ^ k / k.factorial * |((1 - t) ^ n)⁻¹| *
            ((1 - t)⁻¹) ^ (k + 1)) * (c * A ^ (k + 1)) *
            {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          ring
      _ = Cst * (ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) *
            {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t) := by
          rw [hreal, ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg h1t.le _))]
          ring
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) *
      {t : ℝ | a ≤ (1 - t) * d}.indicator (1 : ℝ → ℝ≥0∞) t :=
    (ENNReal.measurable_ofReal.comp ((measurable_id.const_sub (1 : ℝ)).pow_const (n + 1)).inv).mul
      (measurable_const.indicator (measurableSet_le measurable_const
        ((measurable_id.const_sub 1).mul measurable_const)))
  rw [setLIntegral_congr_fun measurableSet_Ioo hpt, lintegral_const_mul _ hmeas]
  calc Cst * ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) *
        {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t
      ≤ Cst * ENNReal.ofReal (d ^ n / (n * a ^ n)) :=
        mul_le_mul_right (lintegral_inv_one_sub_pow_indicator_le hn ha) _
    _ = ENNReal.ofReal (d ^ n / (n * k.factorial)) * (c * rieszKernel n (k + 1) x z) := by
        have hsplit : ENNReal.ofReal (k.factorial : ℝ)⁻¹ * ENNReal.ofReal (d ^ n / (n * a ^ n)) =
            ENNReal.ofReal (d ^ n / (n * k.factorial)) * (ENNReal.ofReal a ^ n)⁻¹ := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg _)), ← ENNReal.ofReal_pow ha.le,
            ← ENNReal.ofReal_inv_of_pos (pow_pos ha n),
            ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hd _) (by positivity))]
          congr 1
          field_simp
        simp only [Cst, rieszKernel, ← hA_def, ENNReal.div_eq_inv_mul]
        rw [hAa]
        calc c * ENNReal.ofReal a ^ (k + 1) * ENNReal.ofReal (k.factorial : ℝ)⁻¹ *
              ENNReal.ofReal (d ^ n / (n * a ^ n))
            = c * ENNReal.ofReal a ^ (k + 1) * (ENNReal.ofReal (k.factorial : ℝ)⁻¹ *
              ENNReal.ofReal (d ^ n / (n * a ^ n))) := by ring
          _ = _ := by rw [hsplit]; ring

theorem enorm_sub_avgTaylorPoly_le_riesz [CompleteSpace G] (hn : 0 < n) {K U : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKc : Convex ℝ K) (hK0 : volume K ≠ 0) (hU : IsOpen U) (hKU : K ⊆ U)
    {k : ℕ} {f : (Fin n → ℝ) → G} (hf : ContDiffOn ℝ (k + 1) f U) {d : ℝ}
    (hd : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ d) {x : Fin n → ℝ} (hx : x ∈ K) :
    ‖f x - avgTaylorPoly K f (k + 1) x‖ₑ ≤
      ENNReal.ofReal (d ^ n / (n * k.factorial)) / volume K *
        ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ * rieszKernel n (k + 1) x z := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hKt : volume K ≠ ∞ := hK.measure_lt_top.ne
  have hd0 : 0 ≤ d := by simpa using hd x hx x hx
  set F : (Fin n → ℝ) → ℝ≥0∞ := K.indicator fun z => ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ with hF_def
  have hFm : Measurable F := measurable_indicator_of_continuousOn hK.isClosed
    (continuous_enorm.comp_continuousOn
      ((continuousOn_iteratedFDeriv_of_isOpen hU hf le_rfl).mono hKU))
  set T : (Fin n → ℝ) → G := fun y => taylorPoly f y (k + 1) x
  have hTc : ContinuousOn T K := by
    have : T = fun y => ∑ i ∈ Finset.range (k + 1),
        ((i.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ i f y (fun _ => x - y)) := rfl
    rw [this]
    refine continuousOn_finsetSum _ fun i hi => ContinuousOn.const_smul ?_ _
    have hc := (continuousOn_iteratedFDeriv_of_isOpen hU hf
      (Nat.le_succ_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))).mono hKU
    exact continuous_eval.comp_continuousOn (hc.prodMk (by fun_prop))
  have hTint : IntegrableOn T K := hTc.integrableOn_compact hK
  -- the average of the remainder
  have h1 : ‖f x - avgTaylorPoly K f (k + 1) x‖ₑ ≤ (volume K)⁻¹ * ∫⁻ y in K, ‖f x - T y‖ₑ := by
    have hr : volume.real K ≠ 0 := by
      rw [measureReal_def]; exact ENNReal.toReal_ne_zero.2 ⟨hK0, hKt⟩
    have : f x - avgTaylorPoly K f (k + 1) x = (volume.real K)⁻¹ • ∫ y in K, (f x - T y) := by
      rw [integral_sub (integrableOn_const hKt) hTint, setIntegral_const, smul_sub, smul_smul,
        inv_mul_cancel₀ hr, one_smul, avgTaylorPoly, setAverage_eq]
    rw [this, enorm_smul]
    gcongr
    · rw [Real.enorm_eq_ofReal (inv_nonneg.2 measureReal_nonneg), ENNReal.ofReal_inv_of_pos
        (lt_of_le_of_ne measureReal_nonneg (Ne.symm hr)), measureReal_def,
        ENNReal.ofReal_toReal hKt]
    · exact enorm_integral_le_lintegral_enorm _
  -- the integral remainder at each base point
  have h2 : ∀ y ∈ K, ‖f x - T y‖ₑ ≤ ∫⁻ t in Ioo (0 : ℝ) 1,
      ENNReal.ofReal ((1 - t) ^ k / k.factorial) * F (y + t • (x - y)) * ‖x - y‖ₑ ^ (k + 1) := by
    intro y hy
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1, y + t • (x - y) ∈ K := fun t ht =>
      hKc.add_smul_sub_mem hy hx ht
    refine (enorm_sub_taylorPoly_le hU hf fun t ht => hKU (hseg t ht)).trans_eq ?_
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [hF_def, Set.indicator_of_mem (hseg t (Ioo_subset_Icc_self ht))]
  set S : Set (ℝ × (Fin n → ℝ)) := {p | ‖x - p.2‖ ≤ (1 - p.1) * d} with hS_def
  have hSm : MeasurableSet S := measurableSet_le (by fun_prop) (by fun_prop)
  set g : ℝ → (Fin n → ℝ) → ℝ≥0∞ := fun t z =>
    F z * (ENNReal.ofReal (1 - t)⁻¹ * ‖x - z‖ₑ) ^ (k + 1) * S.indicator 1 (t, z) with hg_def
  have hHm : Measurable fun p : (Fin n → ℝ) × ℝ =>
      ENNReal.ofReal ((1 - p.2) ^ k / k.factorial) * F (p.1 + p.2 • (x - p.1)) *
        ‖x - p.1‖ₑ ^ (k + 1) := by
    refine Measurable.mul (Measurable.mul ?_ ?_) ?_
    · exact ENNReal.measurable_ofReal.comp
        (by fun_prop : Continuous fun p : (Fin n → ℝ) × ℝ => (1 - p.2) ^ k / k.factorial).measurable
    · exact hFm.comp
        (by fun_prop : Continuous fun p : (Fin n → ℝ) × ℝ => p.1 + p.2 • (x - p.1)).measurable
    · exact (continuous_enorm.comp
        (by fun_prop : Continuous fun p : (Fin n → ℝ) × ℝ => x - p.1)).measurable.pow_const (k + 1)
  have hΨm : Measurable fun p : ℝ × (Fin n → ℝ) =>
      ENNReal.ofReal ((1 - p.1) ^ k / k.factorial) * ENNReal.ofReal |((1 - p.1) ^ n)⁻¹| *
        g p.1 p.2 := by
    have h1 : Measurable fun p : ℝ × (Fin n → ℝ) => ENNReal.ofReal ((1 - p.1) ^ k / k.factorial) :=
      ENNReal.measurable_ofReal.comp
        (by fun_prop : Continuous fun p : ℝ × (Fin n → ℝ) => (1 - p.1) ^ k / k.factorial).measurable
    have h2 : Measurable fun p : ℝ × (Fin n → ℝ) => ENNReal.ofReal |((1 - p.1) ^ n)⁻¹| :=
      ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
        (((measurable_fst (α := ℝ) (β := Fin n → ℝ)).const_sub (1 : ℝ)).pow_const n).inv)
    have h3 : Measurable fun p : ℝ × (Fin n → ℝ) => F p.2 := hFm.comp measurable_snd
    have h4 : Measurable fun p : ℝ × (Fin n → ℝ) =>
        (ENNReal.ofReal (1 - p.1)⁻¹ * ‖x - p.2‖ₑ) ^ (k + 1) :=
      ((ENNReal.measurable_ofReal.comp
        ((measurable_fst (α := ℝ) (β := Fin n → ℝ)).const_sub (1 : ℝ)).inv).mul
        (continuous_enorm.comp (by fun_prop :
          Continuous fun p : ℝ × (Fin n → ℝ) => x - p.2)).measurable).pow_const (k + 1)
    have h5 : Measurable fun p : ℝ × (Fin n → ℝ) =>
        S.indicator (1 : ℝ × (Fin n → ℝ) → ℝ≥0∞) (p.1, p.2) :=
      (measurable_const.indicator hSm).comp (measurable_fst.prodMk measurable_snd)
    exact (h1.mul h2).mul ((h3.mul h4).mul h5)
  -- the change of variables at fixed time
  have h4 : ∀ t ∈ Ioo (0 : ℝ) 1, ∫⁻ y in K, ENNReal.ofReal ((1 - t) ^ k / k.factorial) *
      F (y + t • (x - y)) * ‖x - y‖ₑ ^ (k + 1) ≤ ∫⁻ z, ENNReal.ofReal ((1 - t) ^ k /
        k.factorial) * ENNReal.ofReal |((1 - t) ^ n)⁻¹| * g t z := by
    intro t ht
    have h1t : 0 < 1 - t := by linarith [ht.2]
    have hpt : ∀ y ∈ K, ENNReal.ofReal ((1 - t) ^ k / k.factorial) * F (y + t • (x - y)) *
        ‖x - y‖ₑ ^ (k + 1) ≤ ENNReal.ofReal ((1 - t) ^ k / k.factorial) *
          g t (y + t • (x - y)) := by
      intro y hy
      have hxv : x - (y + t • (x - y)) = (1 - t) • (x - y) := by
        rw [sub_smul, one_smul]; abel
      have hn1 : ENNReal.ofReal (1 - t)⁻¹ * ‖x - (y + t • (x - y))‖ₑ = ‖x - y‖ₑ := by
        rw [hxv, enorm_smul, Real.enorm_eq_ofReal h1t.le, ← mul_assoc,
          ← ENNReal.ofReal_mul (inv_nonneg.2 h1t.le), inv_mul_cancel₀ h1t.ne', ENNReal.ofReal_one,
          one_mul]
      have hSmem : (t, y + t • (x - y)) ∈ S := by
        change ‖x - (y + t • (x - y))‖ ≤ (1 - t) * d
        rw [hxv, norm_smul, Real.norm_of_nonneg h1t.le]
        exact mul_le_mul_of_nonneg_left (hd x hx y hy) h1t.le
      rw [hg_def]
      simp only
      rw [hn1, Set.indicator_of_mem hSmem, Pi.one_apply, mul_one, mul_assoc]
    calc ∫⁻ y in K, ENNReal.ofReal ((1 - t) ^ k / k.factorial) * F (y + t • (x - y)) *
          ‖x - y‖ₑ ^ (k + 1)
        ≤ ∫⁻ y, ENNReal.ofReal ((1 - t) ^ k / k.factorial) * g t (y + t • (x - y)) :=
          (setLIntegral_mono' hKm hpt).trans (setLIntegral_le_lintegral _ _)
      _ = ENNReal.ofReal ((1 - t) ^ k / k.factorial) * ∫⁻ y, g t (y + t • (x - y)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal ((1 - t) ^ k / k.factorial) *
            (ENNReal.ofReal |((1 - t) ^ n)⁻¹| * ∫⁻ z, g t z) := by
          rw [lintegral_comp_add_smul_sub _ x (ne_of_lt ht.2)]
      _ = _ := by
          rw [← mul_assoc, ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            ENNReal.ofReal_ne_top)]
  calc ‖f x - avgTaylorPoly K f (k + 1) x‖ₑ ≤ (volume K)⁻¹ * ∫⁻ y in K, ‖f x - T y‖ₑ := h1
    _ ≤ (volume K)⁻¹ * ∫⁻ y in K, ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ k /
          k.factorial) * F (y + t • (x - y)) * ‖x - y‖ₑ ^ (k + 1) := by
        exact mul_le_mul_right (setLIntegral_mono' hKm h2) _
    _ = (volume K)⁻¹ * ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ y in K, ENNReal.ofReal ((1 - t) ^ k /
          k.factorial) * F (y + t • (x - y)) * ‖x - y‖ₑ ^ (k + 1) := by
        rw [lintegral_lintegral_swap hHm.aemeasurable]
    _ ≤ (volume K)⁻¹ * ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ z, ENNReal.ofReal ((1 - t) ^ k /
          k.factorial) * ENNReal.ofReal |((1 - t) ^ n)⁻¹| * g t z := by
        exact mul_le_mul_right (setLIntegral_mono' measurableSet_Ioo h4) _
    _ = (volume K)⁻¹ * ∫⁻ z, ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ k /
          k.factorial) * ENNReal.ofReal |((1 - t) ^ n)⁻¹| * g t z := by
        rw [lintegral_lintegral_swap hΨm.aemeasurable]
    _ ≤ (volume K)⁻¹ * ∫⁻ z, ENNReal.ofReal (d ^ n / (n * k.factorial)) *
          (F z * rieszKernel n (k + 1) x z) := by
        exact mul_le_mul_right (lintegral_mono fun z => lintegral_time_le hn k hd0 x z (F z)) _
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hF_def]
        simp_rw [← Set.indicator_mul_left]
        rw [lintegral_indicator hKm, ENNReal.div_eq_inv_mul]
        ring

end Riesz

/-! ### Integrals of the Riesz kernel -/

section KernelIntegral

/-- **Radial integral of a power** on a closed ball (polar coordinates,
`MeasureTheory.integral_fun_norm_addHaar`): for `b < a + n`,
`∫_{‖w‖ ≤ d} ‖w‖^a / ‖w‖^b dw = n |B₁| d^{n + a - b} / (n + a - b)`. -/
theorem lintegral_closedBall_pow_div_pow (hn : 0 < n) {a b : ℕ} (ha : 0 < a) (hab : b < a + n)
    {d : ℝ} (hd : 0 ≤ d) :
    ∫⁻ w in Metric.closedBall (0 : Fin n → ℝ) d, ‖w‖ₑ ^ a / ‖w‖ₑ ^ b =
      ENNReal.ofReal (n * volume.real (Metric.ball (0 : Fin n → ℝ) 1) *
        (d ^ ((n : ℝ) + a - b) / ((n : ℝ) + a - b))) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hγ : (-1 : ℝ) < (n : ℝ) - 1 + a - b := by
    have : (b : ℝ) < a + n := by exact_mod_cast hab
    linarith
  set h : ℝ → ℝ := (Iic d).indicator fun y => y ^ a / y ^ b with h_def
  -- the integrand as a radial function
  have hrad : ∀ w : Fin n → ℝ, (Metric.closedBall (0 : Fin n → ℝ) d).indicator
      (fun w => ‖w‖ₑ ^ a / ‖w‖ₑ ^ b) w = ENNReal.ofReal (h ‖w‖) := by
    intro w
    by_cases hw : w ∈ Metric.closedBall (0 : Fin n → ℝ) d
    · have hw' : ‖w‖ ∈ Iic d := by simpa using hw
      rw [Set.indicator_of_mem hw, h_def, Set.indicator_of_mem hw']
      rcases eq_or_ne w 0 with rfl | hw0
      · simp [zero_pow ha.ne']
      · have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
        rw [ENNReal.ofReal_div_of_pos (pow_pos hpos b), ENNReal.ofReal_pow hpos.le,
          ENNReal.ofReal_pow hpos.le, ofReal_norm]
    · have hw' : ‖w‖ ∉ Iic d := by simpa using hw
      rw [Set.indicator_of_notMem hw, h_def, Set.indicator_of_notMem hw', ENNReal.ofReal_zero]
  -- the radial profile
  have hprof : EqOn (fun y : ℝ => y ^ (Module.finrank ℝ (Fin n → ℝ) - 1) • h y)
      ((Ioc 0 d).indicator fun y => y ^ ((n : ℝ) - 1 + a - b)) (Ioi 0) := by
    intro y hy
    have hy : 0 < y := hy
    dsimp only
    rw [Module.finrank_fin_fun, smul_eq_mul, h_def]
    by_cases hyd : y ≤ d
    · rw [Set.indicator_of_mem (show y ∈ Iic d from hyd),
        Set.indicator_of_mem (show y ∈ Ioc 0 d from ⟨hy, hyd⟩)]
      rw [Real.rpow_sub hy, Real.rpow_add hy, Real.rpow_sub hy, Real.rpow_one, Real.rpow_natCast,
        Real.rpow_natCast, Real.rpow_natCast, ← pow_sub_one_mul (by omega : n ≠ 0) y] 
      field_simp
    · rw [Set.indicator_of_notMem (show y ∉ Iic d from hyd),
        Set.indicator_of_notMem (show y ∉ Ioc 0 d from fun h => hyd h.2), mul_zero]
  have hint1 : IntegrableOn (fun y : ℝ => y ^ ((n : ℝ) - 1 + a - b)) (Ioc 0 d) :=
    (intervalIntegral.intervalIntegrable_rpow' hγ).1
  have hint2 : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ (Fin n → ℝ) - 1) • h y)
      (Ioi 0) := by
    refine (integrableOn_congr_fun hprof measurableSet_Ioi).2 ?_
    exact (hint1.integrable_indicator measurableSet_Ioc).integrableOn
  have hint : Integrable (fun w : Fin n → ℝ => h ‖w‖) :=
    (integrable_fun_norm_addHaar volume (f := h)).2 hint2
  have hval : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ (Fin n → ℝ) - 1) • h y =
      d ^ ((n : ℝ) + a - b) / ((n : ℝ) + a - b) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hprof, setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.2 Ioc_subset_Ioi_self, ← intervalIntegral.integral_of_le hd,
      integral_rpow (Or.inl hγ)]
    have : (n : ℝ) - 1 + a - b + 1 = (n : ℝ) + a - b := by ring
    rw [this, Real.zero_rpow (by linarith), sub_zero]
  have hnonneg : 0 ≤ᵐ[volume] fun w : Fin n → ℝ => h ‖w‖ := by
    refine Eventually.of_forall fun w => ?_
    simp only [h_def, Pi.zero_apply]
    exact Set.indicator_nonneg (fun y _ => div_nonneg (pow_nonneg (norm_nonneg w) _)
      (pow_nonneg (norm_nonneg w) _)) _
  rw [← lintegral_indicator measurableSet_closedBall]
  simp_rw [hrad]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg, integral_fun_norm_addHaar volume h, hval,
    Module.finrank_fin_fun, nsmul_eq_mul, smul_eq_mul, mul_assoc]

/-- The explicit constant `n |B₁| d^{n + a - b} / (n + a - b)` of
`lintegral_closedBall_pow_div_pow`. -/
def rieszConst (n a b : ℕ) (d : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (n * volume.real (Metric.ball (0 : Fin n → ℝ) 1) *
    (d ^ ((n : ℝ) + a - b) / ((n : ℝ) + a - b)))

theorem rieszConst_ne_top (n a b : ℕ) (d : ℝ) : rieszConst n a b d ≠ ∞ := ENNReal.ofReal_ne_top

/-- **Integrability of the Riesz kernel**:
`∫_K k(x, z)^q dz ≤ n |B₁| d^{n + q(m - n)} / (n + q(m - n))`
for `x ∈ K`, `‖x - y‖ ≤ d` on `K`, `q m ≥ 1` and `q n < q m + n`. -/
theorem lintegral_rieszKernel_pow_le (hn : 0 < n) {K : Set (Fin n → ℝ)} (hKm : MeasurableSet K)
    {d : ℝ} (hd : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ d) {x : Fin n → ℝ} (hx : x ∈ K) {m q : ℕ}
    (hqm : 0 < q * m) (hq : q * n < q * m + n) :
    ∫⁻ z in K, rieszKernel n m x z ^ q ≤ rieszConst n (q * m) (q * n) d := by
  have hd0 : 0 ≤ d := by simpa using hd x hx x hx
  have hpt : ∀ z, K.indicator (fun z => rieszKernel n m x z ^ q) z ≤
      (Metric.closedBall (0 : Fin n → ℝ) d).indicator
        (fun w => ‖w‖ₑ ^ (q * m) / ‖w‖ₑ ^ (q * n)) (x - z) := by
    intro z
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (mem_closedBall_zero_iff.2 (hd x hx z hz)),
        rieszKernel]
      refine le_of_eq ?_
      simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow, ← pow_mul, mul_comm m q, mul_comm n q]
    · rw [Set.indicator_of_notMem hz]; exact zero_le
  calc ∫⁻ z in K, rieszKernel n m x z ^ q
      = ∫⁻ z, K.indicator (fun z => rieszKernel n m x z ^ q) z := (lintegral_indicator hKm _).symm
    _ ≤ ∫⁻ z, (Metric.closedBall (0 : Fin n → ℝ) d).indicator
          (fun w => ‖w‖ₑ ^ (q * m) / ‖w‖ₑ ^ (q * n)) (x - z) := lintegral_mono hpt
    _ = ∫⁻ w, (Metric.closedBall (0 : Fin n → ℝ) d).indicator
          (fun w => ‖w‖ₑ ^ (q * m) / ‖w‖ₑ ^ (q * n)) w := lintegral_sub_left_eq_self _ x
    _ = rieszConst n (q * m) (q * n) d := by
        rw [lintegral_indicator measurableSet_closedBall]
        exact lintegral_closedBall_pow_div_pow hn hqm hq hd0

/-- **Weighted Cauchy–Schwarz**: `(∫ F k)² ≤ (∫ k)(∫ F² k)`. -/
theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {F k : α → ℝ≥0∞} (hF : AEMeasurable F μ) (hk : AEMeasurable k μ) :
    (∫⁻ a, F a * k a ∂μ) ^ 2 ≤ (∫⁻ a, k a ∂μ) * ∫⁻ a, F a ^ 2 * k a ∂μ := by
  set g : α → ℝ≥0∞ := fun a => k a ^ (1 / 2 : ℝ)
  have hg : AEMeasurable g μ := hk.pow_const _
  have hsq : ∀ a, g a ^ (2 : ℝ) = k a := fun a => by
    rw [← ENNReal.rpow_mul]; norm_num
  have hfg : ∀ a, F a * k a = (F * g) a * g a := fun a => by
    simp only [Pi.mul_apply]
    rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two (hF.mul hg) hg
  simp only [Pi.mul_apply] at h
  rw [show (fun a => F a * k a) = fun a => F a * g a * g a from funext fun a => hfg a]
  have h1 : ∀ a, (F a * g a) ^ (2 : ℝ) = F a ^ 2 * k a := fun a => by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsq, ENNReal.rpow_two]
  simp_rw [h1, hsq] at h
  calc (∫⁻ a, F a * g a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, F a ^ 2 * k a ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, k a ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le h 2
    _ = (∫⁻ a, k a ∂μ) * ∫⁻ a, F a ^ 2 * k a ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num
        ring

end KernelIntegral

/-! ### `L²` Bramble–Hilbert and Sobolev embedding on a convex set -/

section ConvexSet

/-- The constant `dⁿ / (n k! |K|)` of the Riesz-potential bound. -/
def avgTaylorConst (n k : ℕ) (d : ℝ) (K : Set (Fin n → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (d ^ n / (n * k.factorial)) / volume K

theorem avgTaylorConst_ne_top {k : ℕ} {d : ℝ} {K : Set (Fin n → ℝ)} (hK0 : volume K ≠ 0) :
    avgTaylorConst n k d K ≠ ∞ :=
  ENNReal.div_ne_top ENNReal.ofReal_ne_top hK0

theorem measurable_indicator_enorm_iteratedFDeriv {K U : Set (Fin n → ℝ)} (hK : IsClosed K)
    (hU : IsOpen U) (hKU : K ⊆ U) {N : ℕ} {f : (Fin n → ℝ) → G} (hf : ContDiffOn ℝ N f U) :
    Measurable (K.indicator fun z => ‖iteratedFDeriv ℝ N f z‖ₑ) :=
  measurable_indicator_of_continuousOn hK (continuous_enorm.comp_continuousOn
    ((continuousOn_iteratedFDeriv_of_isOpen hU hf le_rfl).mono hKU))

/-- **`L²` Bramble–Hilbert lemma** on a compact convex set with nonempty interior (`|K| > 0`),
for every order `k + 1 ≥ 1` ([BrambleHilbert1970]; [Ciarlet2002], Thm 3.1.1): the averaged
Taylor polynomial `p = Q_{k+1} f ∈ P_k` satisfies
`∫_K ‖f - p‖² ≤ (dⁿ/(n k! |K|) · C₁)² ∫_K ‖D^{k+1} f‖²`, with
`C₁ = n |B₁| d^{k+1} / (k+1)` the bound of `∫_K ‖x - z‖^{k+1-n} dz` (Schur test on the Riesz
kernel). -/
theorem lintegral_sub_avgTaylorPoly_sq_le [CompleteSpace G] (hn : 0 < n) {K U : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKc : Convex ℝ K) (hK0 : volume K ≠ 0) (hU : IsOpen U) (hKU : K ⊆ U)
    {k : ℕ} {f : (Fin n → ℝ) → G} (hf : ContDiffOn ℝ (k + 1) f U) {d : ℝ}
    (hd : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ d) :
    ∫⁻ x in K, ‖f x - avgTaylorPoly K f (k + 1) x‖ₑ ^ 2 ≤
      (avgTaylorConst n k d K * rieszConst n (k + 1) n d) ^ 2 *
        ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ ^ 2 := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set A := avgTaylorConst n k d K
  set B := rieszConst n (k + 1) n d
  set F : (Fin n → ℝ) → ℝ≥0∞ := K.indicator fun z => ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ with hF_def
  have hFm : Measurable F := measurable_indicator_enorm_iteratedFDeriv hK.isClosed hU hKU
    (N := k + 1) (by exact_mod_cast hf)
  have hkm : ∀ x, Measurable fun z => rieszKernel n (k + 1) x z := fun x =>
    measurable_rieszKernel_right (k + 1) x
  have hB : ∀ x ∈ K, ∫⁻ z in K, rieszKernel n (k + 1) x z ≤ B := fun x hx => by
    have := lintegral_rieszKernel_pow_le hn hKm hd hx (m := k + 1) (q := 1) (by omega)
      (by omega)
    simp only [pow_one, one_mul] at this
    exact this
  have hFK : ∀ g : (Fin n → ℝ) → ℝ≥0∞, ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ * g z =
      ∫⁻ z in K, F z * g z := fun g =>
    setLIntegral_congr_fun hKm fun z hz => by rw [hF_def, Set.indicator_of_mem hz]
  have hpt : ∀ x ∈ K, ‖f x - avgTaylorPoly K f (k + 1) x‖ₑ ^ 2 ≤
      A ^ 2 * B * ∫⁻ z in K, F z ^ 2 * rieszKernel n (k + 1) x z := by
    intro x hx
    have h := enorm_sub_avgTaylorPoly_le_riesz hn hK hKc hK0 hU hKU hf hd hx
    rw [hFK] at h
    calc ‖f x - avgTaylorPoly K f (k + 1) x‖ₑ ^ 2
        ≤ (A * ∫⁻ z in K, F z * rieszKernel n (k + 1) x z) ^ 2 := pow_le_pow_left₀ zero_le h 2
      _ = A ^ 2 * (∫⁻ z in K, F z * rieszKernel n (k + 1) x z) ^ 2 := mul_pow _ _ _
      _ ≤ A ^ 2 * ((∫⁻ z in K, rieszKernel n (k + 1) x z) *
            ∫⁻ z in K, F z ^ 2 * rieszKernel n (k + 1) x z) :=
          mul_le_mul_right (lintegral_mul_sq_le _ hFm.aemeasurable (hkm x).aemeasurable) _
      _ ≤ A ^ 2 * (B * ∫⁻ z in K, F z ^ 2 * rieszKernel n (k + 1) x z) := by
          gcongr; exact hB x hx
      _ = _ := by ring
  have hAB : A ^ 2 * B ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (avgTaylorConst_ne_top hK0)) (rieszConst_ne_top _ _ _ _)
  have hjm : Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      F p.2 ^ 2 * rieszKernel n (k + 1) p.1 p.2 :=
    ((hFm.comp measurable_snd).pow_const 2).mul (measurable_rieszKernel (n := n) (k + 1))
  calc ∫⁻ x in K, ‖f x - avgTaylorPoly K f (k + 1) x‖ₑ ^ 2
      ≤ ∫⁻ x in K, A ^ 2 * B * ∫⁻ z in K, F z ^ 2 * rieszKernel n (k + 1) x z :=
        setLIntegral_mono' hKm hpt
    _ = A ^ 2 * B * ∫⁻ x in K, ∫⁻ z in K, F z ^ 2 * rieszKernel n (k + 1) x z :=
        lintegral_const_mul' _ _ hAB
    _ = A ^ 2 * B * ∫⁻ z in K, ∫⁻ x in K, F z ^ 2 * rieszKernel n (k + 1) x z := by
        rw [lintegral_lintegral_swap hjm.aemeasurable]
    _ = A ^ 2 * B * ∫⁻ z in K, F z ^ 2 * ∫⁻ x in K, rieszKernel n (k + 1) z x := by
        congr 1
        refine lintegral_congr fun z => ?_
        rw [← lintegral_const_mul _ (hkm z)]
        exact lintegral_congr fun x => by rw [rieszKernel_comm]
    _ ≤ A ^ 2 * B * ∫⁻ z in K, F z ^ 2 * B := by
        gcongr ?_ * ?_
        · exact le_rfl
        · exact setLIntegral_mono' hKm fun z hz => mul_le_mul_right (hB z hz) _
    _ = (A * B) ^ 2 * ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ ^ 2 := by
        rw [lintegral_mul_const' _ _ (rieszConst_ne_top _ _ _ _)]
        have : ∫⁻ z in K, F z ^ 2 = ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ ^ 2 :=
          setLIntegral_congr_fun hKm fun z hz => by rw [hF_def, Set.indicator_of_mem hz]
        rw [this]
        ring

/-- **Sobolev embedding** `H^{k+1}(K) ⊂ C(K)` for `2(k + 1) > n`, in the Bramble–Hilbert form:
`sup_K ‖f - Q_{k+1} f‖ ≤ dⁿ/(n k! |K|) · C₂^{1/2} (∫_K ‖D^{k+1} f‖²)^{1/2}` with
`C₂ = n |B₁| d^{2(k+1) - n} / (2(k+1) - n)` the bound of `∫_K ‖x - z‖^{2(k+1-n)} dz`
(Cauchy–Schwarz on the Riesz potential; [Evans2010], §5.6). -/
theorem enorm_sub_avgTaylorPoly_le_L2 [CompleteSpace G] (hn : 0 < n) {K U : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKc : Convex ℝ K) (hK0 : volume K ≠ 0) (hU : IsOpen U) (hKU : K ⊆ U)
    {k : ℕ} (hnk : n < 2 * (k + 1)) {f : (Fin n → ℝ) → G} (hf : ContDiffOn ℝ (k + 1) f U)
    {d : ℝ} (hd : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ d) {x : Fin n → ℝ} (hx : x ∈ K) :
    ‖f x - avgTaylorPoly K f (k + 1) x‖ₑ ≤
      avgTaylorConst n k d K * rieszConst n (2 * (k + 1)) (2 * n) d ^ (1 / 2 : ℝ) *
        (∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set F : (Fin n → ℝ) → ℝ≥0∞ := K.indicator fun z => ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ with hF_def
  have hFm : Measurable F := measurable_indicator_enorm_iteratedFDeriv hK.isClosed hU hKU
    (N := k + 1) (by exact_mod_cast hf)
  have hkm : Measurable fun z => rieszKernel n (k + 1) x z := measurable_rieszKernel_right _ x
  have h := enorm_sub_avgTaylorPoly_le_riesz hn hK hKc hK0 hU hKU hf hd hx
  have hFK : ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ * rieszKernel n (k + 1) x z =
      ∫⁻ z in K, (F * fun z => rieszKernel n (k + 1) x z) z :=
    setLIntegral_congr_fun hKm fun z hz => by
      simp only [Pi.mul_apply]; rw [hF_def, Set.indicator_of_mem hz]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict K) Real.HolderConjugate.two_two
    hFm.aemeasurable hkm.aemeasurable
  have hF2 : ∫⁻ z in K, F z ^ (2 : ℝ) = ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ ^ 2 :=
    setLIntegral_congr_fun hKm fun z hz => by
      rw [hF_def, Set.indicator_of_mem hz, ENNReal.rpow_two]
  have hk2 : ∫⁻ z in K, rieszKernel n (k + 1) x z ^ (2 : ℝ) ≤
      rieszConst n (2 * (k + 1)) (2 * n) d := by
    simp_rw [ENNReal.rpow_two]
    exact lintegral_rieszKernel_pow_le hn hKm hd hx (m := k + 1) (q := 2) (by omega) (by omega)
  rw [hFK] at h
  refine h.trans ?_
  rw [hF2] at hH
  calc avgTaylorConst n k d K * ∫⁻ z in K, (F * fun z => rieszKernel n (k + 1) x z) z
      ≤ avgTaylorConst n k d K * ((∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ ^ 2) ^ (1 / 2 : ℝ) *
          (∫⁻ z in K, rieszKernel n (k + 1) x z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_right hH _
    _ ≤ avgTaylorConst n k d K * ((∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ ^ 2) ^ (1 / 2 : ℝ) *
          rieszConst n (2 * (k + 1)) (2 * n) d ^ (1 / 2 : ℝ)) := by
        gcongr
    _ = _ := by ring

end ConvexSet

/-! ### Derivatives of the averaged Taylor polynomial -/

section Derivatives

/-- Joint continuity of `(y, x) ↦ T_k g(y)(x)` for `g` of class `C^N` on an open set,
`k ≤ N + 1`. -/
theorem continuousOn_taylorPoly_prod {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {N : ℕ} {g : E → F} {U : Set E} (hU : IsOpen U)
    (hg : ContDiffOn ℝ N g U) {k : ℕ} (hk : k ≤ N + 1) :
    ContinuousOn (fun p : E × E => taylorPoly g p.1 k p.2) (U ×ˢ univ) := by
  unfold taylorPoly
  refine continuousOn_finsetSum _ fun i hi => ContinuousOn.const_smul ?_ _
  have hi : i ≤ N := by have := Finset.mem_range.1 hi; omega
  have hc := (continuousOn_iteratedFDeriv_of_isOpen hU hg hi).comp
    (continuousOn_fst (s := U ×ˢ (univ : Set E))) (fun p hp => (Set.mem_prod.1 hp).1)
  have hv : Continuous fun p : E × E => (fun _ : Fin i => p.2 - p.1) :=
    continuous_pi fun _ => continuous_snd.sub continuous_fst
  exact continuous_eval.comp_continuousOn (hc.prodMk hv.continuousOn)

/-- Continuity of `y ↦ T_k g(y)(x)` for `g` of class `C^N` on an open set, `k ≤ N + 1`. -/
theorem continuousOn_taylorPoly_base {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {N : ℕ} {g : E → F} {U : Set E} (hU : IsOpen U)
    (hg : ContDiffOn ℝ N g U) {k : ℕ} (hk : k ≤ N + 1) (x : E) :
    ContinuousOn (fun y => taylorPoly g y k x) U := by
  unfold taylorPoly
  refine continuousOn_finsetSum _ fun i hi => ContinuousOn.const_smul ?_ _
  have hi : i ≤ N := by have := Finset.mem_range.1 hi; omega
  have hv : Continuous fun y : E => (fun _ : Fin i => x - y) :=
    continuous_pi fun _ => continuous_const.sub continuous_id
  exact continuous_eval.comp_continuousOn
    ((continuousOn_iteratedFDeriv_of_isOpen hU hg hi).prodMk hv.continuousOn)

/-- **`D (Q_{k+1} f) = Q_k (D f)`**: the averaged Taylor polynomial commutes with
differentiation (differentiation under the integral sign, `hasFDerivAt_taylorPoly`). -/
theorem hasFDerivAt_avgTaylorPoly [CompleteSpace G] {K U : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {k : ℕ} {f : (Fin n → ℝ) → G} (hf : ContDiffOn ℝ (k + 1) f U)
    (x₀ : Fin n → ℝ) :
    HasFDerivAt (avgTaylorPoly K f (k + 1)) (avgTaylorPoly K (fderiv ℝ f) k x₀) x₀ := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hdf : ContDiffOn ℝ k (fderiv ℝ f) U := hf.fderiv_of_isOpen hU le_rfl
  have hF := continuousOn_taylorPoly_prod hU (N := k + 1) (by exact_mod_cast hf)
    (k := k + 1) (by omega)
  have hF' := continuousOn_taylorPoly_prod hU hdf (k := k) (by omega)
  have hFy : ∀ x, ContinuousOn (fun y => taylorPoly f y (k + 1) x) K := fun x =>
    (continuousOn_taylorPoly_base hU (N := k + 1) (by exact_mod_cast hf) (k := k + 1) (by omega)
      x).mono hKU
  have hF'y : ∀ x, ContinuousOn (fun y => taylorPoly (fderiv ℝ f) y k x) K := fun x =>
    (continuousOn_taylorPoly_base hU hdf (k := k) (by omega) x).mono hKU
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn
    (hF'.mono (Set.prod_mono hKU (subset_univ _)))
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hint := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict K)
    (F := fun x y => taylorPoly f y (k + 1) x) (F' := fun x y => taylorPoly (fderiv ℝ f) y k x)
    (x₀ := x₀) (bound := fun _ => B) (Metric.closedBall_mem_nhds x₀ one_pos)
    (Eventually.of_forall fun x => (hFy x).aestronglyMeasurable hKm)
    ((hFy x₀).integrableOn_compact hK) ((hF'y x₀).aestronglyMeasurable hKm)
    ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun y hy x hx => hB (y, x) ⟨hy, hx⟩))
    (integrable_const B)
    ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun y hy x _ =>
      hasFDerivAt_taylorPoly ((hf.contDiffAt (hU.mem_nhds (hKU hy))).of_le
        le_self_add) x))
  have := hint.const_smul (volume.real K)⁻¹
  have hfun : avgTaylorPoly K f (k + 1) =
      (volume.real K)⁻¹ • fun x => ∫ y in K, taylorPoly f y (k + 1) x := by
    funext x; simp only [avgTaylorPoly, setAverage_eq, Pi.smul_apply]
  rw [hfun, avgTaylorPoly, setAverage_eq]
  exact this

theorem fderiv_avgTaylorPoly [CompleteSpace G] {K U : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {k : ℕ} {f : (Fin n → ℝ) → G} (hf : ContDiffOn ℝ (k + 1) f U) :
    fderiv ℝ (avgTaylorPoly K f (k + 1)) = avgTaylorPoly K (fderiv ℝ f) k :=
  funext fun x => (hasFDerivAt_avgTaylorPoly hK hU hKU hf x).fderiv

/-- **`L²` Bramble–Hilbert in the seminorms of order `j ≤ k`**: on a compact convex `K` with
`|K| > 0`, for `f` of class `C^{k+1}` near `K`,
`∫_K ‖D^j (f - Q_{k+1} f)‖² ≤ (dⁿ/(n (k-j)! |K|) · C₁)² ∫_K ‖D^{k+1} f‖²`, with the constant of
the order-`(k + 1 - j)` estimate. Proof: `D (f - Q_{k+1} f) = D f - Q_k (D f)`
(`fderiv_avgTaylorPoly`) and induction on `j`. -/
theorem lintegral_iteratedFDeriv_sub_avgTaylorPoly_sq_le (hn : 0 < n) {K U : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKc : Convex ℝ K) (hK0 : volume K ≠ 0) (hU : IsOpen U) (hKU : K ⊆ U)
    {d : ℝ} (hd : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ d) (j : ℕ) :
    ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {k : ℕ}
      {f : (Fin n → ℝ) → G}, j ≤ k → ContDiffOn ℝ (k + 1) f U →
      ∫⁻ x in K, ‖iteratedFDeriv ℝ j (fun y => f y - avgTaylorPoly K f (k + 1) y) x‖ₑ ^ 2 ≤
        (avgTaylorConst n (k - j) d K * rieszConst n (k + 1 - j) n d) ^ 2 *
          ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ ^ 2 := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  induction j with
  | zero =>
    intro G _ _ _ k f _ hf
    simp only [Nat.sub_zero]
    have h := lintegral_sub_avgTaylorPoly_sq_le hn hK hKc hK0 hU hKU hf hd
    refine le_of_eq_of_le (setLIntegral_congr_fun hKm fun x _ => ?_) h
    rw [← enorm_norm, norm_iteratedFDeriv_zero, enorm_norm]
  | succ j ih =>
    intro G _ _ _ k f hjk hf
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hdf : ContDiffOn ℝ (k + 1) (fderiv ℝ f) U :=
      hf.fderiv_of_isOpen hU (by push_cast; exact le_rfl)
    have h := ih (G := (Fin n → ℝ) →L[ℝ] G) (k := k) (f := fderiv ℝ f) (by omega) hdf
    have heq : ∀ x ∈ K, ‖iteratedFDeriv ℝ (j + 1)
        (fun y => f y - avgTaylorPoly K f (k + 1 + 1) y) x‖ₑ ^ 2 =
        ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ f y - avgTaylorPoly K (fderiv ℝ f) (k + 1) y)
          x‖ₑ ^ 2 := by
      intro x hx
      have hloc : fderiv ℝ (fun y => f y - avgTaylorPoly K f (k + 1 + 1) y) =ᶠ[𝓝 x]
          fun y => fderiv ℝ f y - avgTaylorPoly K (fderiv ℝ f) (k + 1) y := by
        filter_upwards [hU.mem_nhds (hKU hx)] with y hy
        exact ((((hf.differentiableOn (by simp)) y hy).differentiableAt
          (hU.mem_nhds hy)).hasFDerivAt.sub (hasFDerivAt_avgTaylorPoly hK hU hKU hf y)).fderiv
      rw [← enorm_norm, ← norm_iteratedFDeriv_fderiv, (hloc.iteratedFDeriv ℝ j).eq_of_nhds,
        enorm_norm]
    have hD : ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) (fderiv ℝ f) z‖ₑ ^ 2 =
        ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1 + 1) f z‖ₑ ^ 2 :=
      lintegral_congr fun z => by rw [← enorm_norm, norm_iteratedFDeriv_fderiv, enorm_norm]
    rw [setLIntegral_congr_fun hKm heq]
    refine h.trans_eq ?_
    rw [hD, show k + 1 - (j + 1) = k - j by omega, show k + 1 + 1 - (j + 1) = k + 1 - j by omega]

end Derivatives

/-! ### The reference simplex: interpolation error in `L²` -/

section RefSimplex

open Feec.Mesh

theorem setLIntegral_enorm_sq_lt_top {E : Type*} [NormedAddCommGroup E] {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) {g : (Fin n → ℝ) → E} (hg : ContinuousOn g K) :
    ∫⁻ x in K, ‖g x‖ₑ ^ 2 < ∞ := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hg
  calc ∫⁻ x in K, ‖g x‖ₑ ^ 2 ≤ ∫⁻ _x in K, ENNReal.ofReal M ^ 2 :=
        setLIntegral_mono' hK.isClosed.measurableSet fun x hx => pow_le_pow_left₀ zero_le
          (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hM x hx)) 2
    _ = ENNReal.ofReal M ^ 2 * volume K := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hK.measure_lt_top

theorem volume_closedInterior_ne_zero (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    volume T.closedInterior ≠ 0 :=
  (isOpen_interior.measure_pos volume (interior_closedInterior_nonempty T)).ne'.symm ∘
    fun h => le_antisymm ((measure_mono interior_subset).trans h.le) zero_le |>.symm

/-- The constant of the reference `L²` interpolation estimate
`|T̂| (1 + C)² (avgTaylorConst)² C₂`. -/
def refL2Const (n s : ℕ) (C : ℝ) : ℝ≥0∞ :=
  volume (Feec.Mesh.refSimplex n).closedInterior * ENNReal.ofReal (1 + C) ^ 2 *
    (avgTaylorConst n s 1 (Feec.Mesh.refSimplex n).closedInterior ^ 2 *
      rieszConst n (2 * (s + 1)) (2 * n) 1)

theorem refL2Const_ne_top (n s : ℕ) (C : ℝ) : refL2Const n s C ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (Feec.Mesh.refSimplex n).isCompact_closedInterior.measure_lt_top.ne
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (avgTaylorConst_ne_top (volume_closedInterior_ne_zero _)))
      (rieszConst_ne_top _ _ _ _))

/-- **`L²(T̂)` interpolation error from `L²` derivatives** ([Ciarlet2002], Thm 3.1.4, Sobolev
form): for every reference interpolant `I` that is stable in `C⁰(T̂)` and reproduces `P_s`
(`IsRefInterpolant n s 0`, e.g. the canonical interpolants of `P_rΛ`, `s ≤ r`, and `P_r⁻Λ`,
`s ≤ r - 1`), and every `f` of class `C^{s+1}` near `T̂`, if `2(s + 1) > n`:
`∫_{T̂} ‖f - I f‖² ≤ K ∫_{T̂} ‖D^{s+1} f‖²`, `K = refL2Const n s C`. The restriction
`2(s + 1) > n` is that of the Sobolev embedding `H^{s+1} ⊂ C⁰`: the moment degrees of freedom
need point values (traces on faces). -/
theorem IsRefInterpolant.lintegral_sub_sq_le_L2 [CompleteSpace G] (hn : 0 < n) {s : ℕ}
    (hns : n < 2 * (s + 1)) {I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G} {C : ℝ} (hC : 0 ≤ C)
    (hI : IsRefInterpolant n s 0 G I C) {f : (Fin n → ℝ) → G} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hTU : (Feec.Mesh.refSimplex n).closedInterior ⊆ U)
    (hf : ContDiffOn ℝ (s + 1) f U) :
    ∫⁻ x in (Feec.Mesh.refSimplex n).closedInterior, ‖f x - I f x‖ₑ ^ 2 ≤
      refL2Const n s C * ∫⁻ x in (Feec.Mesh.refSimplex n).closedInterior,
        ‖iteratedFDeriv ℝ (s + 1) f x‖ₑ ^ 2 := by
  set K := (Feec.Mesh.refSimplex n).closedInterior with hK_def
  have hK : IsCompact K := (Feec.Mesh.refSimplex n).isCompact_closedInterior
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hK0 : volume K ≠ 0 := volume_closedInterior_ne_zero _
  have hd : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ 1 := fun x hx y hy =>
    norm_sub_le_one_of_mem_refSimplex hx hy
  set p := avgTaylorPoly K f (s + 1) with hp_def
  have hp : p ∈ polyFunctions n s G :=
    avgTaylorPoly_mem_polyFunctions hK hU hTU (hf.of_le (by exact_mod_cast Nat.le_succ s))
  have hpc : ContDiffOn ℝ (s + 1) p U := (contDiff_of_mem_polyFunctions hp).contDiffOn
  set J := ∫⁻ x in K, ‖iteratedFDeriv ℝ (s + 1) f x‖ₑ ^ 2
  have hJ : J ≠ ∞ := (setLIntegral_enorm_sq_lt_top hK
    ((continuousOn_iteratedFDeriv_of_isOpen hU (N := s + 1) (by exact_mod_cast hf)
      le_rfl).mono hTU)).ne
  set A := avgTaylorConst n s 1 K
  set B := rieszConst n (2 * (s + 1)) (2 * n) 1
  set S := A * B ^ (1 / 2 : ℝ) * J ^ (1 / 2 : ℝ)
  have hS : S ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (avgTaylorConst_ne_top hK0)
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (rieszConst_ne_top _ _ _ _)))
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hJ)
  have hsob : ∀ y ∈ K, ‖f y - p y‖ ≤ S.toReal := fun y hy => by
    have h := enorm_sub_avgTaylorPoly_le_L2 hn hK (convex_closedInterior _) hK0 hU hTU hns hf hd hy
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_le_iff_le_toReal hS).1 h
  have hpt : ∀ x ∈ K, ‖f x - I f x‖ ≤ (1 + C) * S.toReal := by
    intro x hx
    have hsub := hI.map_sub U hU hTU f p hf hpc x hx
    rw [hI.apply_eq p hp x hx] at hsub
    have hstab := hI.norm_le U hU hTU (f - p) (hf.sub hpc) (fun _ => S.toReal)
      (fun j hj y hy => by
        obtain rfl : j = 0 := Nat.le_zero.1 hj
        rw [norm_iteratedFDeriv_zero]; exact hsob y hy) x hx
    rw [Finset.sum_range_one] at hstab
    have : f x - I f x = (f x - p x) - I (f - p) x := by rw [hsub]; abel
    rw [this]
    calc ‖f x - p x - I (f - p) x‖ ≤ ‖f x - p x‖ + ‖I (f - p) x‖ := _root_.norm_sub_le _ _
      _ ≤ S.toReal + C * S.toReal := add_le_add (hsob x hx) hstab
      _ = (1 + C) * S.toReal := by ring
  calc ∫⁻ x in K, ‖f x - I f x‖ₑ ^ 2 ≤ ∫⁻ _x in K, ENNReal.ofReal ((1 + C) * S.toReal) ^ 2 :=
        setLIntegral_mono' hKm fun x hx => pow_le_pow_left₀ zero_le
          (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hpt x hx)) 2
    _ = volume K * ENNReal.ofReal (1 + C) ^ 2 * S ^ 2 := by
        rw [setLIntegral_const, ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_toReal hS]
        ring
    _ = refL2Const n s C * J := by
        have hS2 : S ^ 2 = A ^ 2 * B * J := by
          simp only [S, mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
        rw [hS2, refL2Const]
        ring

end RefSimplex

/-! ### Transport to a physical simplex -/

section Transport

open Feec.Mesh

/-- **`L²(T)` interpolation error on an `n`-simplex `T`**, by transport from `T̂`
(`Feec.FiniteElement.transportInterp`, `Π_T u = Φ⁻¹ ∘ I (Φ ∘ u ∘ F_T) ∘ F_T⁻¹`): for
`2(s + 1) > n`,
`∫_T ‖u - Π_T u‖² ≤ (‖Φ⁻¹‖ ‖Φ‖ ‖B_T‖^{s+1})² K ∫_T ‖D^{s+1} u‖²`. The Jacobians `|det B_T|` of
the two changes of variables cancel. -/
theorem lintegral_sub_transportInterp_sq_le_L2 [CompleteSpace G] (hn : 0 < n) {s : ℕ}
    (hns : n < 2 * (s + 1)) {I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G} {C : ℝ} (hC : 0 ≤ C)
    (hI : IsRefInterpolant n s 0 G I C) (T : Affine.Simplex ℝ (Fin n → ℝ) n) (Φ : G ≃L[ℝ] G)
    {u : (Fin n → ℝ) → G} {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hTU : T.closedInterior ⊆ U)
    (hu : ContDiffOn ℝ (s + 1) u U) :
    ∫⁻ x in T.closedInterior, ‖u x - transportInterp T Φ I u x‖ₑ ^ 2 ≤
      ENNReal.ofReal ((‖(Φ.symm : G →L[ℝ] G)‖ * (‖(Φ : G →L[ℝ] G)‖ *
        ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (s + 1))) ^ 2) * refL2Const n s C *
        ∫⁻ x in T.closedInterior, ‖iteratedFDeriv ℝ (s + 1) u x‖ₑ ^ 2 := by
  set a := ‖(Φ.symm : G →L[ℝ] G)‖
  set b := ‖(Φ : G →L[ℝ] G)‖ * ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (s + 1)
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := by positivity
  set û := refPullback T Φ u
  have hmem : ∀ y ∈ (Feec.Mesh.refSimplex n).closedInterior, T.refMap y ∈ T.closedInterior :=
    fun y hy => by rw [T.closedInterior_eq_image_refMap]; exact mem_image_of_mem _ hy
  have hTU' : (Feec.Mesh.refSimplex n).closedInterior ⊆ T.refMap ⁻¹' U := fun y hy =>
    hTU (hmem y hy)
  have hU' : IsOpen (T.refMap ⁻¹' U) := hU.preimage (contDiff_refMap T (N := 0)).continuous
  have href := hI.lintegral_sub_sq_le_L2 hn hns hC hU' hTU' (contDiffOn_refPullback T Φ hu)
  have hpt : ∀ y, ‖u (T.refMap y) - transportInterp T Φ I u (T.refMap y)‖ₑ ^ 2 ≤
      ENNReal.ofReal (a ^ 2) * ‖û y - I û y‖ₑ ^ 2 := by
    intro y
    have he : u (T.refMap y) - transportInterp T Φ I u (T.refMap y) = Φ.symm (û y - I û y) := by
      simp [transportInterp, û, refPullback, map_sub]
    rw [he, ENNReal.ofReal_pow ha, ← mul_pow]
    refine pow_le_pow_left₀ zero_le ?_ 2
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul ha]
    exact ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm (Φ.symm : G →L[ℝ] G) _)
  have hD : ∀ y, ‖iteratedFDeriv ℝ (s + 1) û y‖ₑ ^ 2 ≤
      ENNReal.ofReal (b ^ 2) * ‖iteratedFDeriv ℝ (s + 1) u (T.refMap y)‖ₑ ^ 2 := by
    intro y
    rw [ENNReal.ofReal_pow hb, ← mul_pow]
    refine pow_le_pow_left₀ zero_le ?_ 2
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hb]
    exact ENNReal.ofReal_le_ofReal (norm_iteratedFDeriv_refPullback_le T Φ u _ y)
  set D := ENNReal.ofReal |LinearMap.det T.linearPart|
  calc ∫⁻ x in T.closedInterior, ‖u x - transportInterp T Φ I u x‖ₑ ^ 2
      = D * ∫⁻ y in (Feec.Mesh.refSimplex n).closedInterior,
          ‖u (T.refMap y) - transportInterp T Φ I u (T.refMap y)‖ₑ ^ 2 :=
        lintegral_closedInterior_eq T _
    _ ≤ D * ∫⁻ y in (Feec.Mesh.refSimplex n).closedInterior,
          ENNReal.ofReal (a ^ 2) * ‖û y - I û y‖ₑ ^ 2 := by
        gcongr with y; exact hpt y
    _ = D * (ENNReal.ofReal (a ^ 2) * ∫⁻ y in (Feec.Mesh.refSimplex n).closedInterior,
          ‖û y - I û y‖ₑ ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ D * (ENNReal.ofReal (a ^ 2) * (refL2Const n s C *
          ∫⁻ y in (Feec.Mesh.refSimplex n).closedInterior,
            ‖iteratedFDeriv ℝ (s + 1) û y‖ₑ ^ 2)) := by
        gcongr
    _ ≤ D * (ENNReal.ofReal (a ^ 2) * (refL2Const n s C *
          ∫⁻ y in (Feec.Mesh.refSimplex n).closedInterior,
            ENNReal.ofReal (b ^ 2) * ‖iteratedFDeriv ℝ (s + 1) u (T.refMap y)‖ₑ ^ 2)) := by
        gcongr with y; exact hD y
    _ = ENNReal.ofReal ((a * b) ^ 2) * refL2Const n s C * (D *
          ∫⁻ y in (Feec.Mesh.refSimplex n).closedInterior,
            ‖iteratedFDeriv ℝ (s + 1) u (T.refMap y)‖ₑ ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_pow a b 2,
          ENNReal.ofReal_mul (sq_nonneg a)]
        ring
    _ = _ := by
        rw [lintegral_closedInterior_eq T (fun x => ‖iteratedFDeriv ℝ (s + 1) u x‖ₑ ^ 2)]

/-- **`L²(T)` interpolation error on a shape-regular family** (`Feec.Mesh.IsShapeRegular`:
`‖B_T‖ ≤ C₀ h_T`, `‖B_T⁻¹‖ ≤ C₀ / h_T`) with a fibre map scaling like a `k`-form pullback
(`‖Φ_T‖ ≤ A ‖B_T‖^k`, `‖Φ_T⁻¹‖ ≤ A ‖B_T⁻¹‖^k`):
`∫_T ‖u - Π_T u‖² ≤ (A² C₀^{2k} (C₀ h_T)^{s+1})² K ∫_T ‖D^{s+1} u‖²` for `2(s + 1) > n`
([Ciarlet2002], Thm 3.1.5, Sobolev form). -/
theorem lintegral_sub_transportInterp_sq_le_L2_of_isShapeRegular [CompleteSpace G] (hn : 0 < n)
    {s : ℕ} (hns : n < 2 * (s + 1)) {I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G} {C : ℝ}
    (hC : 0 ≤ C) (hI : IsRefInterpolant n s 0 G I C) {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}
    {C₀ c : ℝ} (hS : IsShapeRegular S C₀ c) {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ S)
    (Φ : G ≃L[ℝ] G) {A : ℝ} {k : ℕ}
    (hΦ : ‖(Φ : G →L[ℝ] G)‖ ≤ A * ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ k)
    (hΦs : ‖(Φ.symm : G →L[ℝ] G)‖ ≤
      A * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ k)
    {u : (Fin n → ℝ) → G} {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hTU : T.closedInterior ⊆ U)
    (hu : ContDiffOn ℝ (s + 1) u U) :
    ∫⁻ x in T.closedInterior, ‖u x - transportInterp T Φ I u x‖ₑ ^ 2 ≤
      ENNReal.ofReal ((A ^ 2 * C₀ ^ (2 * k) * (C₀ * diam T) ^ (s + 1)) ^ 2) * refL2Const n s C *
        ∫⁻ x in T.closedInterior, ‖iteratedFDeriv ℝ (s + 1) u x‖ₑ ^ 2 := by
  refine (lintegral_sub_transportInterp_sq_le_L2 hn hns hC hI T Φ hU hTU hu).trans ?_
  refine mul_le_mul_left (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _) _
  obtain ⟨hB, -, -⟩ := hS T hT
  have hΦΦ := norm_symm_mul_norm_le_of_isShapeRegular hS hT Φ hΦ hΦs
  have h0 : 0 ≤ ‖(Φ.symm : G →L[ℝ] G)‖ * (‖(Φ : G →L[ℝ] G)‖ *
      ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (s + 1)) := by positivity
  refine pow_le_pow_left₀ h0 ?_ 2
  rw [← mul_assoc]
  exact mul_le_mul hΦΦ (pow_le_pow_left₀ (norm_nonneg _) hB _) (by positivity)
    ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hΦΦ)

end Transport

/-! ### Differential forms on homothetic simplices -/

section Forms

open Feec.Mesh ExteriorFibre

variable {r k : ℕ}

/-- `‖u‖²_{L²(S)} ≤ #Λ ∫_S ‖u‖²` (sup norm on the fibre), if the right side is finite. -/
theorem formL2Sq_le_card_mul_lintegral {S : Set (Fin n → ℝ)} {u : FormField n}
    (hfin : ∫⁻ x in S, ‖u x‖ₑ ^ 2 ≠ ∞) :
    formL2Sq S u ≤ Fintype.card (Finset (Fin n)) * (∫⁻ x in S, ‖u x‖ₑ ^ 2).toReal := by
  have h1 : ∀ t : Finset (Fin n), ∫ x in S, (u x t) ^ 2 ≤ (∫⁻ x in S, ‖u x‖ₑ ^ 2).toReal := by
    intro t
    by_cases hi : Integrable (fun x => (u x t) ^ 2) (volume.restrict S)
    · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
        hi.aestronglyMeasurable]
      refine ENNReal.toReal_mono hfin (lintegral_mono fun x => ?_)
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hle : |u x t| ≤ ‖u x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm (u x) t
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    · rw [integral_undef hi]; exact ENNReal.toReal_nonneg
  calc formL2Sq S u = ∑ t, ∫ x in S, (u x t) ^ 2 := rfl
    _ ≤ ∑ _t : Finset (Fin n), (∫⁻ x in S, ‖u x‖ₑ ^ 2).toReal := Finset.sum_le_sum fun t _ => h1 t
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem integral_norm_sq_eq_toReal_lintegral {E : Type*} [NormedAddCommGroup E]
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) {g : (Fin n → ℝ) → E} (hg : ContinuousOn g S) :
    ∫ x in S, ‖g x‖ ^ 2 = (∫⁻ x in S, ‖g x‖ₑ ^ 2).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
    ((hg.norm.pow 2).aestronglyMeasurable hS)]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The constant `(‖Φ_K⁻¹‖ ‖Φ_K‖ ‖B_K‖^{s+1})²` of a reference simplex `K` with the fibre map
`Φ_K = B_K^*`. -/
def formTransportConst (K : Affine.Simplex ℝ (Fin n → ℝ) n) (s : ℕ) : ℝ :=
  (‖((fibrePullbackEquiv K.points (isUnit_det_edgeMatrix K)).symm :
      (Finset (Fin n) → ℝ) →L[ℝ] (Finset (Fin n) → ℝ))‖ *
    (‖(fibrePullbackEquiv K.points (isUnit_det_edgeMatrix K) :
      (Finset (Fin n) → ℝ) →L[ℝ] (Finset (Fin n) → ℝ))‖ *
      ‖(K.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (s + 1))) ^ 2

/-- The common core of the form estimates: a reference interpolant transported to `T = t + h K`
with `Φ_K`, compared with a field `P` that it equals. -/
theorem formL2Sq_sub_le_of_transportInterp_eq (K : Affine.Simplex ℝ (Fin n → ℝ) n) (hn : 0 < n)
    {s : ℕ} (hns : n < 2 * (s + 1)) {I : FormField n → FormField n} {CI : ℝ} (hCI : 0 ≤ CI)
    (hI : IsRefInterpolant n s 0 (Finset (Fin n) → ℝ) I CI) {h : ℝ} (hh : 0 < h)
    (t : Fin n → ℝ) {w P : FormField n} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hTU : (mapEquiv (boxMap t h hh.ne') K).closedInterior ⊆ U) (hw : ContDiffOn ℝ (s + 1) w U)
    (hP : ∀ x, transportInterp (mapEquiv (boxMap t h hh.ne') K)
      (fibrePullbackEquiv K.points (isUnit_det_edgeMatrix K)) I w x = P x) :
    formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior (w - P) ≤
      Fintype.card (Finset (Fin n)) * formTransportConst K s * (refL2Const n s CI).toReal *
        h ^ (2 * (s + 1)) * ∫ y in (mapEquiv (boxMap t h hh.ne') K).closedInterior,
          ‖iteratedFDeriv ℝ (s + 1) w y‖ ^ 2 := by
  set T := mapEquiv (boxMap t h hh.ne') K
  set Φ := fibrePullbackEquiv K.points (isUnit_det_edgeMatrix K)
  have hL := lintegral_sub_transportInterp_sq_le_L2 hn hns hCI hI T Φ hU hTU hw
  rw [norm_linearEquiv_mapEquiv_boxMap K t hh] at hL
  simp_rw [hP] at hL
  have hTc : IsCompact T.closedInterior := T.isCompact_closedInterior
  have hTm : MeasurableSet T.closedInterior := hTc.isClosed.measurableSet
  have hDc : ContinuousOn (iteratedFDeriv ℝ (s + 1) w) T.closedInterior :=
    (continuousOn_iteratedFDeriv_of_isOpen hU (N := s + 1) (by exact_mod_cast hw) le_rfl).mono hTU
  have hJ := (setLIntegral_enorm_sq_lt_top hTc hDc).ne
  have hc : (‖(Φ.symm : (Finset (Fin n) → ℝ) →L[ℝ] (Finset (Fin n) → ℝ))‖ *
      (‖(Φ : (Finset (Fin n) → ℝ) →L[ℝ] (Finset (Fin n) → ℝ))‖ *
        (h * ‖(K.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖) ^ (s + 1))) ^ 2 =
      formTransportConst K s * h ^ (2 * (s + 1)) := by
    simp only [formTransportConst, Φ]; ring
  rw [hc] at hL
  have hfin : ∫⁻ x in T.closedInterior, ‖(w - P) x‖ₑ ^ 2 ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (refL2Const_ne_top _ _ _)) hJ) (by simpa only [Pi.sub_apply] using hL)
  have hnn : 0 ≤ formTransportConst K s * h ^ (2 * (s + 1)) := by
    unfold formTransportConst; positivity
  calc formL2Sq T.closedInterior (w - P)
      ≤ Fintype.card (Finset (Fin n)) * (∫⁻ x in T.closedInterior, ‖(w - P) x‖ₑ ^ 2).toReal :=
        formL2Sq_le_card_mul_lintegral hfin
    _ ≤ Fintype.card (Finset (Fin n)) * (ENNReal.ofReal (formTransportConst K s *
          h ^ (2 * (s + 1))) * refL2Const n s CI * ∫⁻ x in T.closedInterior,
            ‖iteratedFDeriv ℝ (s + 1) w x‖ₑ ^ 2).toReal := by
        gcongr
        · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (refL2Const_ne_top _ _ _)) hJ
        · simpa only [Pi.sub_apply] using hL
    _ = _ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn,
          ← integral_norm_sq_eq_toReal_lintegral hTm hDc]
        ring

/-- **`L²(T)` interpolation error of `Π_T` for `P_rΛᵏ` from `L²` derivatives** on
`T = t + h K`, `s ≤ r`, `2(s + 1) > n`:
`‖w - Π_T w‖²_{L²(T)} ≤ C h^{2(s+1)} ∫_T ‖D^{s+1} w‖²`, `C` depending only on `K`, `n`, `r`,
`s` (the Sobolev form of `Feec.FiniteElement.exists_formL2Sq_sub_polyInterp_le`; full order
`h^{2(r+1)}` for `s = r`). -/
theorem exists_formL2Sq_sub_polyInterp_le_L2 (K : Affine.Simplex ℝ (Fin n → ℝ) n) (hn : 0 < n)
    (hr : 1 ≤ r) (hk : k ≤ n) {s : ℕ} (hs : s ≤ r) (hns : n < 2 * (s + 1)) :
    ∃ C, 0 ≤ C ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {w : FormField n} (hwc : Continuous w)
      (hwk : ∀ x, IsDeg k (w x)) {U : Set (Fin n → ℝ)}, IsOpen U →
      (mapEquiv (boxMap t h hh.ne') K).closedInterior ⊆ U → ContDiffOn ℝ (s + 1) w U →
      formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior
        (w - (polyInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) hr hk
          ⟨w, mem_contDegForms hwc hwk⟩ : FormField n)) ≤
        C * h ^ (2 * (s + 1)) * ∫ y in (mapEquiv (boxMap t h hh.ne') K).closedInterior,
          ‖iteratedFDeriv ℝ (s + 1) w y‖ ^ 2 := by
  obtain ⟨CI, hCI0, hI⟩ := exists_isRefInterpolant_polyRefInterp (n := n) hr hs
  refine ⟨Fintype.card (Finset (Fin n)) * formTransportConst K s * (refL2Const n s CI).toReal,
    by unfold formTransportConst; positivity, fun {h} hh t w hwc hwk U hU hTU hw => ?_⟩
  exact formL2Sq_sub_le_of_transportInterp_eq K hn hns hCI0 hI hh t hU hTU hw
    (transportInterp_polyRefInterp_eq K hr hk hh t hwc hwk)

/-- **`L²(T)` interpolation error of `Π_T` for `P_r⁻Λᵏ` from `L²` derivatives** on
`T = t + h K`, `s ≤ r - 1`, `2(s + 1) > n`. -/
theorem exists_formL2Sq_sub_polyMinusInterp_le_L2 (K : Affine.Simplex ℝ (Fin n → ℝ) n)
    (hn : 0 < n) (hr : 1 ≤ r) (hk : k ≤ n) {s : ℕ} (hs : s + 1 ≤ r) (hns : n < 2 * (s + 1)) :
    ∃ C, 0 ≤ C ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {w : FormField n} (hwc : Continuous w)
      (hwk : ∀ x, IsDeg k (w x)) {U : Set (Fin n → ℝ)}, IsOpen U →
      (mapEquiv (boxMap t h hh.ne') K).closedInterior ⊆ U → ContDiffOn ℝ (s + 1) w U →
      formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior
        (w - (polyMinusInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) hr hk
          ⟨w, mem_contDegForms hwc hwk⟩ : FormField n)) ≤
        C * h ^ (2 * (s + 1)) * ∫ y in (mapEquiv (boxMap t h hh.ne') K).closedInterior,
          ‖iteratedFDeriv ℝ (s + 1) w y‖ ^ 2 := by
  obtain ⟨CI, hCI0, hI⟩ := exists_isRefInterpolant_polyMinusRefInterp (n := n) hr hs
  refine ⟨Fintype.card (Finset (Fin n)) * formTransportConst K s * (refL2Const n s CI).toReal,
    by unfold formTransportConst; positivity, fun {h} hh t w hwc hwk U hU hTU hw => ?_⟩
  exact formL2Sq_sub_le_of_transportInterp_eq K hn hns hCI0 hI hh t hU hTU hw
    (transportInterp_polyMinusRefInterp_eq K hr hk hh t hwc hwk)

/-- **`L²(T)` error of `d Π_T` for the `P` family** (graph-norm part, Sobolev form): with
`Π_T : C⁰Λᵏ → P_{r+1}Λᵏ(T)` and the commuting property `d Π_T w = Π_T dw`
(`Feec.FiniteElement.polyInterp_extDeriv`),
`‖dw - d Π_T w‖²_{L²(T)} ≤ C h^{2(s+1)} ∫_T ‖D^{s+1} dw‖²` for `s ≤ r`, `2(s + 1) > n`, `w ∈ C¹`
of class `C^{s+2}` on an open `U ⊇ T`. -/
theorem exists_formL2Sq_extDeriv_sub_polyInterp_le_L2 (K : Affine.Simplex ℝ (Fin n → ℝ) n)
    (hn : 0 < n) (hr : 1 ≤ r) (hk : k + 1 ≤ n) {s : ℕ} (hs : s ≤ r) (hns : n < 2 * (s + 1)) :
    ∃ C, 0 ≤ C ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {w : FormField n}
      (hw1 : ContDiff ℝ 1 w) (hwk : ∀ x, IsDeg k (w x)) {U : Set (Fin n → ℝ)}, IsOpen U →
      (mapEquiv (boxMap t h hh.ne') K).closedInterior ⊆ U → ContDiffOn ℝ (s + 1 + 1) w U →
      formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior
        (extDeriv w - extDeriv (polyInterp
          (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K))
          (Nat.le_add_left 1 r) (by omega : k ≤ n) ⟨w, mem_contDegForms hw1.continuous hwk⟩ :
            FormField n)) ≤
        C * h ^ (2 * (s + 1)) * ∫ y in (mapEquiv (boxMap t h hh.ne') K).closedInterior,
          ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_formL2Sq_sub_polyInterp_le_L2 K hn hr hk hs hns
  refine ⟨C, hC0, fun {h} hh t w hw1 hwk U hU hTU hw => ?_⟩
  have hw1' : ContDiff ℝ ((0 : ℕ) + 1) w := by simpa using hw1
  have hdw := contDiff_extDeriv hw1'
  have hcomm := polyInterp_extDeriv (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) hr hk
    ⟨w, mem_c1DegForms_of_contDiff hw1' hwk⟩
  have e := congrArg (fun ω : localPolySpace (mapEquiv (boxMap t h hh.ne') K).points r (k + 1) =>
    (ω : FormField n)) hcomm
  have h1 := hC hh t hdw.continuous (fun x => IsDeg.extDeriv hwk x) hU hTU
    (contDiffOn_extDeriv hU hw)
  convert h1 using 3
  exact e.symm

/-- **`L²(T)` error of `d Π_T` for the `P⁻` family** (`s ≤ r - 1`, `2(s + 1) > n`). -/
theorem exists_formL2Sq_extDeriv_sub_polyMinusInterp_le_L2 (K : Affine.Simplex ℝ (Fin n → ℝ) n)
    (hn : 0 < n) (hr : 1 ≤ r) (hk : k + 1 ≤ n) {s : ℕ} (hs : s + 1 ≤ r)
    (hns : n < 2 * (s + 1)) :
    ∃ C, 0 ≤ C ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {w : FormField n}
      (hw1 : ContDiff ℝ 1 w) (hwk : ∀ x, IsDeg k (w x)) {U : Set (Fin n → ℝ)}, IsOpen U →
      (mapEquiv (boxMap t h hh.ne') K).closedInterior ⊆ U → ContDiffOn ℝ (s + 1 + 1) w U →
      formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior
        (extDeriv w - extDeriv (polyMinusInterp
          (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) hr (by omega : k ≤ n)
            ⟨w, mem_contDegForms hw1.continuous hwk⟩ : FormField n)) ≤
        C * h ^ (2 * (s + 1)) * ∫ y in (mapEquiv (boxMap t h hh.ne') K).closedInterior,
          ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_formL2Sq_sub_polyMinusInterp_le_L2 K hn hr hk hs hns
  refine ⟨C, hC0, fun {h} hh t w hw1 hwk U hU hTU hw => ?_⟩
  have hw1' : ContDiff ℝ ((0 : ℕ) + 1) w := by simpa using hw1
  have hdw := contDiff_extDeriv hw1'
  have hcomm := polyMinusInterp_extDeriv (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K))
    hr hk ⟨w, mem_c1DegForms_of_contDiff hw1' hwk⟩
  have e := congrArg (fun ω : localPolyMinusSpace (mapEquiv (boxMap t h hh.ne') K).points r
    (k + 1) => (ω : FormField n)) hcomm
  have h1 := hC hh t hdw.continuous (fun x => IsDeg.extDeriv hwk x) hU hTU
    (contDiffOn_extDeriv hU hw)
  convert h1 using 3
  exact e.symm

/-! #### Finitely many reference simplices -/

/-- `exists_formL2Sq_sub_polyInterp_le_L2` with one constant for a finite family of reference
simplices `K i` (the Kuhn simplices of a Freudenthal mesh). -/
theorem exists_formL2Sq_sub_polyInterp_le_L2_uniform {ι : Type*} [Finite ι]
    (K : ι → Affine.Simplex ℝ (Fin n → ℝ) n) (hn : 0 < n) (hr : 1 ≤ r) (hk : k ≤ n) {s : ℕ}
    (hs : s ≤ r) (hns : n < 2 * (s + 1)) :
    ∃ C, 0 ≤ C ∧ ∀ i, ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {w : FormField n}
      (hwc : Continuous w) (hwk : ∀ x, IsDeg k (w x)) {U : Set (Fin n → ℝ)}, IsOpen U →
      (mapEquiv (boxMap t h hh.ne') (K i)).closedInterior ⊆ U → ContDiffOn ℝ (s + 1) w U →
      formL2Sq (mapEquiv (boxMap t h hh.ne') (K i)).closedInterior
        (w - (polyInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') (K i))) hr hk
          ⟨w, mem_contDegForms hwc hwk⟩ : FormField n)) ≤
        C * h ^ (2 * (s + 1)) * ∫ y in (mapEquiv (boxMap t h hh.ne') (K i)).closedInterior,
          ‖iteratedFDeriv ℝ (s + 1) w y‖ ^ 2 := by
  classical
  have := Fintype.ofFinite ι
  choose C hC0 hC using fun i => exists_formL2Sq_sub_polyInterp_le_L2 (K i) hn hr hk hs hns
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC0 i,
    fun i {h} hh t w hwc hwk U hU hTU hw => (hC i hh t hwc hwk hU hTU hw).trans ?_⟩
  have hCi : C i ≤ ∑ j, C j :=
    Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_univ i)
  have hJ : 0 ≤ ∫ y in (mapEquiv (boxMap t h hh.ne') (K i)).closedInterior,
      ‖iteratedFDeriv ℝ (s + 1) w y‖ ^ 2 := setIntegral_nonneg_of_ae (Eventually.of_forall
        fun _ => sq_nonneg _)
  gcongr

/-- `exists_formL2Sq_sub_polyMinusInterp_le_L2` with one constant for a finite family of
reference simplices. -/
theorem exists_formL2Sq_sub_polyMinusInterp_le_L2_uniform {ι : Type*} [Finite ι]
    (K : ι → Affine.Simplex ℝ (Fin n → ℝ) n) (hn : 0 < n) (hr : 1 ≤ r) (hk : k ≤ n) {s : ℕ}
    (hs : s + 1 ≤ r) (hns : n < 2 * (s + 1)) :
    ∃ C, 0 ≤ C ∧ ∀ i, ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {w : FormField n}
      (hwc : Continuous w) (hwk : ∀ x, IsDeg k (w x)) {U : Set (Fin n → ℝ)}, IsOpen U →
      (mapEquiv (boxMap t h hh.ne') (K i)).closedInterior ⊆ U → ContDiffOn ℝ (s + 1) w U →
      formL2Sq (mapEquiv (boxMap t h hh.ne') (K i)).closedInterior
        (w - (polyMinusInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') (K i))) hr
          hk ⟨w, mem_contDegForms hwc hwk⟩ : FormField n)) ≤
        C * h ^ (2 * (s + 1)) * ∫ y in (mapEquiv (boxMap t h hh.ne') (K i)).closedInterior,
          ‖iteratedFDeriv ℝ (s + 1) w y‖ ^ 2 := by
  classical
  have := Fintype.ofFinite ι
  choose C hC0 hC using fun i => exists_formL2Sq_sub_polyMinusInterp_le_L2 (K i) hn hr hk hs hns
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC0 i,
    fun i {h} hh t w hwc hwk U hU hTU hw => (hC i hh t hwc hwk hU hTU hw).trans ?_⟩
  have hCi : C i ≤ ∑ j, C j :=
    Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_univ i)
  have hJ : 0 ≤ ∫ y in (mapEquiv (boxMap t h hh.ne') (K i)).closedInterior,
      ‖iteratedFDeriv ℝ (s + 1) w y‖ ^ 2 := setIntegral_nonneg_of_ae (Eventually.of_forall
        fun _ => sq_nonneg _)
  gcongr

end Forms

/-! ### Non-vacuity -/

section NonVacuity

open Feec.Mesh

/-- A function continuous and nonzero at an interior point of `K` has `∫_K ‖g‖² > 0`. -/
theorem setLIntegral_enorm_sq_ne_zero {E : Type*} [NormedAddCommGroup E] {K : Set (Fin n → ℝ)}
    {g : (Fin n → ℝ) → E} {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ interior K) (hg : ContinuousAt g x₀)
    (hne : g x₀ ≠ 0) : ∫⁻ x in K, ‖g x‖ₑ ^ 2 ≠ 0 := by
  have hpos : 0 < ‖g x₀‖ := norm_pos_iff.2 hne
  have hev : ∀ᶠ x in 𝓝 x₀, ‖g x₀‖ / 2 < ‖g x‖ ∧ x ∈ interior K :=
    (hg.norm.eventually (lt_mem_nhds (half_lt_self hpos))).and (isOpen_interior.mem_nhds hx₀)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hev
  have hlow : ENNReal.ofReal ((‖g x₀‖ / 2) ^ 2) * volume (Metric.ball x₀ ε) ≤
      ∫⁻ x in K, ‖g x‖ₑ ^ 2 := by
    calc ENNReal.ofReal ((‖g x₀‖ / 2) ^ 2) * volume (Metric.ball x₀ ε)
        = ∫⁻ _x in Metric.ball x₀ ε, ENNReal.ofReal ((‖g x₀‖ / 2) ^ 2) :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in Metric.ball x₀ ε, ‖g x‖ₑ ^ 2 :=
          setLIntegral_mono' measurableSet_ball fun x hx => by
            rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
            exact ENNReal.ofReal_le_ofReal
              (pow_le_pow_left₀ (by positivity) (hball hx).1.le 2)
      _ ≤ ∫⁻ x in K, ‖g x‖ₑ ^ 2 := lintegral_mono_set fun x hx => interior_subset (hball hx).2
  have h0 : 0 < ENNReal.ofReal ((‖g x₀‖ / 2) ^ 2) * volume (Metric.ball x₀ ε) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne' (Metric.measure_ball_pos _ _ hε).ne'
  exact (h0.trans_le hlow).ne'

/-- If `D^{r+1} f` does not vanish at an interior point of `K`, then no `p ∈ P_r` has
`∫_K ‖f - p‖² = 0`: the left side of the Bramble–Hilbert estimate is positive. -/
theorem lintegral_sub_sq_ne_zero_of_iteratedFDeriv_ne_zero {K U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hKU : K ⊆ U) {r : ℕ} {f p : (Fin n → ℝ) → G}
    (hf : ContDiffOn ℝ (r + 1) f U) (hp : p ∈ polyFunctions n r G) {x₀ : Fin n → ℝ}
    (hx₀ : x₀ ∈ interior K) (hD : iteratedFDeriv ℝ (r + 1) f x₀ ≠ 0) :
    ∫⁻ x in K, ‖f x - p x‖ₑ ^ 2 ≠ 0 := by
  by_cases h : ∃ x₁ ∈ interior K, f x₁ ≠ p x₁
  · obtain ⟨x₁, hx₁, hne⟩ := h
    exact setLIntegral_enorm_sq_ne_zero hx₁
      ((hf.continuousOn.continuousAt (hU.mem_nhds (hKU (interior_subset hx₁)))).sub
        (contDiff_of_mem_polyFunctions hp (N := 0)).continuous.continuousAt) (sub_ne_zero.2 hne)
  · push Not at h
    have heq : f =ᶠ[𝓝 x₀] p := Filter.eventually_of_mem (isOpen_interior.mem_nhds hx₀) h
    exact (hD (((heq.iteratedFDeriv ℝ (r + 1)).eq_of_nhds).trans
      (iteratedFDeriv_eq_zero_of_mem_polyFunctions r hp x₀))).elim

/-- The `m`-th derivative of the monomial `x ↦ x_{i₀}^m` never vanishes (it is `m!` on
`(e_{i₀}, …, e_{i₀})`). -/
theorem iteratedFDeriv_coord_pow_ne_zero (i₀ : Fin n) (m : ℕ) (x : Fin n → ℝ) :
    iteratedFDeriv ℝ m (fun y : Fin n → ℝ => y i₀ ^ m) x ≠ 0 := by
  intro h
  have h1 := congrArg (fun A => A (fun _ => (Pi.single i₀ (1 : ℝ) : Fin n → ℝ))) h
  have hL : (fun y : Fin n → ℝ => y i₀ ^ m) = (fun t : ℝ => t ^ m) ∘
      (ContinuousLinearMap.proj i₀ : (Fin n → ℝ) →L[ℝ] ℝ) := rfl
  have hpow : ContDiff ℝ m (fun t : ℝ => t ^ m) := contDiff_id.pow m
  simp only [hL] at h1
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hpow x le_rfl,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_pow] at h1
  simp [Nat.descFactorial_self, Nat.factorial_ne_zero] at h1

/-- **Non-vacuity of the `L²` Bramble–Hilbert lemma** on `T̂` (`n ≥ 1`): for the monomial
`f(x) = x₀^{k+1}` of degree `k + 1`, both sides of `lintegral_sub_avgTaylorPoly_sq_le` are
nonzero. -/
theorem lintegral_sub_avgTaylorPoly_sq_nonvacuous (hn : 0 < n) (k : ℕ) :
    ∫⁻ x in (Feec.Mesh.refSimplex n).closedInterior,
        ‖x ⟨0, hn⟩ ^ (k + 1) - avgTaylorPoly (Feec.Mesh.refSimplex n).closedInterior
          (fun y : Fin n → ℝ => y ⟨0, hn⟩ ^ (k + 1)) (k + 1) x‖ₑ ^ 2 ≠ 0 ∧
      ∫⁻ x in (Feec.Mesh.refSimplex n).closedInterior,
        ‖iteratedFDeriv ℝ (k + 1) (fun y : Fin n → ℝ => y ⟨0, hn⟩ ^ (k + 1)) x‖ₑ ^ 2 ≠ 0 := by
  obtain ⟨x₀, hx₀⟩ := interior_closedInterior_nonempty (Feec.Mesh.refSimplex n)
  have hc : ContDiff ℝ (k + 1) (fun y : Fin n → ℝ => y ⟨0, hn⟩ ^ (k + 1)) := by fun_prop
  have hf : ContDiffOn ℝ (k + 1) (fun y : Fin n → ℝ => y ⟨0, hn⟩ ^ (k + 1)) univ := hc.contDiffOn
  refine ⟨lintegral_sub_sq_ne_zero_of_iteratedFDeriv_ne_zero isOpen_univ (subset_univ _) hf
    (avgTaylorPoly_mem_polyFunctions (Feec.Mesh.refSimplex n).isCompact_closedInterior
      isOpen_univ (subset_univ _) (hf.of_le (by exact_mod_cast Nat.le_succ k))) hx₀
    (iteratedFDeriv_coord_pow_ne_zero _ _ _), ?_⟩
  exact setLIntegral_enorm_sq_ne_zero hx₀
    (hc.continuous_iteratedFDeriv (m := k + 1) (by exact_mod_cast le_rfl)).continuousAt
    (iteratedFDeriv_coord_pow_ne_zero _ _ _)

/-- `P₁` Lagrange interpolation takes values in `P₁`. -/
theorem lagrangeP1_mem_polyFunctions (g : (Fin n → ℝ) → G) :
    lagrangeP1 g ∈ polyFunctions n 1 G := by
  have : lagrangeP1 g = ∑ i, fun x => refBaryCoord x i • g (refPoints n i) := by
    funext x; simp [lagrangeP1, Finset.sum_apply]
  rw [this]
  refine Submodule.sum_mem _ fun i _ => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · refine Submodule.subset_span ⟨1 - ∑ j, MvPolynomial.X j, ?_, g (refPoints n 0), ?_⟩
    · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) ?_)
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
      simp
    · funext x; simp [refBaryCoord]
  · refine Submodule.subset_span ⟨MvPolynomial.X j, by simp, g (refPoints n j.succ), ?_⟩
    funext x; simp [refBaryCoord]

/-- **Non-vacuity of `IsRefInterpolant.lintegral_sub_sq_le_L2`**: in dimensions `1 ≤ n ≤ 3`,
`P₁` Lagrange interpolation (`IsRefInterpolant n 1 0`, `2 (1 + 1) > n`) and the quadratic
`f(x) = x₀²` give nonzero values to both sides of the estimate. -/
theorem lintegral_sub_lagrangeP1_sq_nonvacuous (hn : 0 < n) (hn3 : n ≤ 3) :
    IsRefInterpolant n 1 0 ℝ lagrangeP1 1 ∧ n < 2 * (1 + 1) ∧
      ∫⁻ x in (Feec.Mesh.refSimplex n).closedInterior,
        ‖x ⟨0, hn⟩ ^ 2 - lagrangeP1 (fun y : Fin n → ℝ => y ⟨0, hn⟩ ^ 2) x‖ₑ ^ 2 ≠ 0 ∧
      ∫⁻ x in (Feec.Mesh.refSimplex n).closedInterior,
        ‖iteratedFDeriv ℝ (1 + 1) (fun y : Fin n → ℝ => y ⟨0, hn⟩ ^ 2) x‖ₑ ^ 2 ≠ 0 := by
  obtain ⟨x₀, hx₀⟩ := interior_closedInterior_nonempty (Feec.Mesh.refSimplex n)
  have hc : ContDiff ℝ (1 + 1) (fun y : Fin n → ℝ => y ⟨0, hn⟩ ^ 2) := by fun_prop
  have hf : ContDiffOn ℝ (1 + 1) (fun y : Fin n → ℝ => y ⟨0, hn⟩ ^ 2) univ := hc.contDiffOn
  refine ⟨isRefInterpolant_lagrangeP1 n ℝ, by omega, ?_, ?_⟩
  · exact lintegral_sub_sq_ne_zero_of_iteratedFDeriv_ne_zero (r := 1) isOpen_univ
      (subset_univ _) hf (lagrangeP1_mem_polyFunctions _) hx₀
      (iteratedFDeriv_coord_pow_ne_zero _ 2 _)
  · exact setLIntegral_enorm_sq_ne_zero hx₀
      (hc.continuous_iteratedFDeriv (m := 1 + 1) (by exact_mod_cast le_rfl)).continuousAt
      (iteratedFDeriv_coord_pow_ne_zero _ 2 _)

end NonVacuity

end Feec.FiniteElement
