module

public import Feec.TimeStepping.Rational
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Runge–Kutta methods

The stability function `det(1 - z A + z 𝟙 bᵀ)/det(1 - z A)` of a Runge–Kutta method, its rational
scheme, and the midpoint rule and two-stage Gauss–Legendre, Radau IIA and SDIRK methods.

## References

* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996],
  §IV.3, §IV.5, §IV.6

Bibliography: [references.bib](../../docs/references.bib)
-/

open Polynomial Matrix

@[expose] public noncomputable section

namespace Feec.TimeStepping

/-- A Butcher tableau: `s` stages, coefficients `A`, weights `b`. [HairerWanner1996], §IV.3 -/
structure ButcherTableau (s : ℕ) where
  /-- the coefficients -/
  A : Matrix (Fin s) (Fin s) ℝ
  /-- the weights -/
  b : Fin s → ℝ

namespace ButcherTableau

variable {s : ℕ} (T : ButcherTableau s)

/-- The denominator `det(1 - X A)` of the stability function. -/
def stabilityDen : ℝ[X] := ((1 : Matrix (Fin s) (Fin s) ℝ[X]) - (X : ℝ[X]) • T.A.map C).det

/-- The numerator `det(1 - X A + X 𝟙 bᵀ)` of the stability function. -/
def stabilityNum : ℝ[X] :=
  ((1 : Matrix (Fin s) (Fin s) ℝ[X]) - (X : ℝ[X]) • (T.A - vecMulVec (fun _ => 1) T.b).map C).det

private theorem map_one_sub_smul {K : Type*} [CommRing K] [Algebra ℝ K] (f : ℝ[X] →ₐ[ℝ] K)
    (B : Matrix (Fin s) (Fin s) ℝ) :
    f.mapMatrix ((1 : Matrix (Fin s) (Fin s) ℝ[X]) - (X : ℝ[X]) • B.map C) =
      1 - f X • B.map (algebraMap ℝ K) := by
  have hC : ∀ r, f (C r) = algebraMap ℝ K r := fun r => f.commutes r
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, map_sub, map_mul, hC]
  congr 1
  by_cases h : i = j <;> simp [one_apply, h]

theorem aeval_stabilityDen {K : Type*} [CommRing K] [Algebra ℝ K] (z : K) :
    aeval z T.stabilityDen = (1 - z • T.A.map (algebraMap ℝ K)).det := by
  rw [stabilityDen, AlgHom.map_det, map_one_sub_smul, aeval_X]

theorem aeval_stabilityNum {K : Type*} [CommRing K] [Algebra ℝ K] (z : K) :
    aeval z T.stabilityNum = ((1 : Matrix (Fin s) (Fin s) K) -
      z • (T.A - vecMulVec (fun _ => 1) T.b).map (algebraMap ℝ K)).det := by
  rw [stabilityNum, AlgHom.map_det, map_one_sub_smul, aeval_X]

theorem eval_stabilityDen (x : ℝ) : T.stabilityDen.eval x = (1 - x • T.A).det := by
  rw [← coe_aeval_eq_eval, aeval_stabilityDen]; simp

theorem eval_stabilityNum (x : ℝ) :
    T.stabilityNum.eval x = (1 - x • (T.A - vecMulVec (fun _ => 1) T.b)).det := by
  rw [← coe_aeval_eq_eval, aeval_stabilityNum]; simp

/-- **The stability function**: `1 + z bᵀ (1 - z A)⁻¹ 𝟙 = det(1 - z A + z 𝟙 bᵀ)/det(1 - z A)`
wherever `det(1 - z A) ≠ 0`. [HairerWanner1996], §IV.3, Prop 3.2 -/
theorem stabilityFunction_eq (z : ℂ) (hz : (1 - z • T.A.map (algebraMap ℝ ℂ)).det ≠ 0) :
    1 + z * ((fun i => (T.b i : ℂ)) ⬝ᵥ ((1 - z • T.A.map (algebraMap ℝ ℂ))⁻¹ *ᵥ fun _ => 1)) =
      aeval z T.stabilityNum / aeval z T.stabilityDen := by
  set M := 1 - z • T.A.map (algebraMap ℝ ℂ)
  rw [aeval_stabilityNum, aeval_stabilityDen, eq_div_iff hz]
  have e : 1 - z • (T.A - vecMulVec (fun _ => 1) T.b).map (algebraMap ℝ ℂ) =
      M + replicateCol Unit (fun _ => (1 : ℂ)) * replicateRow Unit (z • fun j => (T.b j : ℂ)) := by
    ext i j
    simp [M, replicateCol, replicateRow, Matrix.mul_apply, vecMulVec_apply]
    ring
  rw [e, det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.2 hz), det_unique (n := Unit)]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateCol_apply,
    replicateRow_apply, Pi.smul_apply, smul_eq_mul, mul_one, dotProduct, mulVec,
    Finset.mul_sum]
  rw [mul_comm]
  congr 2
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- The rational scheme of a method with `deg n ≤ deg d` and no pole for `re z ≤ 0`. -/
def toRationalScheme (hdeg : T.stabilityNum.natDegree ≤ T.stabilityDen.natDegree)
    (hden : ∀ z : ℂ, z.re ≤ 0 → aeval z T.stabilityDen ≠ 0) : RationalScheme :=
  ⟨T.stabilityNum, T.stabilityDen, hdeg, hden⟩

/-! ### Auxiliary bounds for the instances -/

theorem quadratic_ne_zero {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) {z : ℂ} (hz : z.re ≤ 0) :
    (1 : ℂ) - a * z + b * z ^ 2 ≠ 0 := fun h => by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re, Complex.add_im,
    Complex.sub_im, Complex.one_im, Complex.mul_im, add_zero, zero_sub, Complex.zero_im] at h1 h2
  have hy : z.im = 0 := by
    have : z.im * (2 * b * z.re - a) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · nlinarith
  rw [hy] at h1
  nlinarith

theorem norm_sq_quadratic (a b y : ℝ) :
    ‖(1 : ℂ) + a * (y * Complex.I) + b * (y * Complex.I) ^ 2‖ ^ 2 =
      (1 - b * y ^ 2) ^ 2 + (a * y) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [pow_two]
  ring

theorem norm_div_le_one_of_sq {n d : ℂ} (hd : d ≠ 0) (h : ‖n‖ ^ 2 ≤ ‖d‖ ^ 2) : ‖n / d‖ ≤ 1 := by
  rw [norm_div, div_le_one (norm_pos_iff.2 hd)]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-! ### The implicit midpoint rule -/

/-- **The implicit midpoint rule**, the one-stage Gauss method. [HairerWanner1996], §IV.5 -/
def implicitMidpoint : ButcherTableau 1 := ⟨!![1 / 2], ![1]⟩

theorem implicitMidpoint_stability :
    implicitMidpoint.stabilityNum = (RationalScheme.theta (1 / 2) (by norm_num)).num ∧
      implicitMidpoint.stabilityDen = (RationalScheme.theta (1 / 2) (by norm_num)).den :=
  ⟨Polynomial.funext fun x => by
    rw [eval_stabilityNum, det_fin_one]; simp [implicitMidpoint, RationalScheme.theta]; ring,
   Polynomial.funext fun x => by
    rw [eval_stabilityDen, det_fin_one]; simp [implicitMidpoint, RationalScheme.theta]; ring⟩

/-! ### The two-stage Gauss–Legendre method -/

/-- **The two-stage Gauss–Legendre method.** [HairerWanner1996], §IV.5 -/
def gaussLegendre2 : ButcherTableau 2 :=
  ⟨!![1 / 4, 1 / 4 - √3 / 6; 1 / 4 + √3 / 6, 1 / 4], ![1 / 2, 1 / 2]⟩

theorem gaussLegendre2_stabilityNum :
    gaussLegendre2.stabilityNum = 1 + C (1 / 2) * X + C (1 / 12) * X ^ 2 :=
  Polynomial.funext fun x => by
    have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [eval_stabilityNum, det_fin_two]
    simp [gaussLegendre2, vecMulVec, vecHead, vecTail]
    linear_combination (x ^ 2 / 36) * h3

theorem gaussLegendre2_stabilityDen :
    gaussLegendre2.stabilityDen = 1 - C (1 / 2) * X + C (1 / 12) * X ^ 2 :=
  Polynomial.funext fun x => by
    have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [eval_stabilityDen, det_fin_two]
    simp [gaussLegendre2]
    linear_combination (x ^ 2 / 36) * h3

/-! ### The two-stage Radau IIA method -/

/-- **The two-stage Radau IIA method.** [HairerWanner1996], §IV.5 -/
def radauIIA2 : ButcherTableau 2 := ⟨!![5 / 12, -1 / 12; 3 / 4, 1 / 4], ![3 / 4, 1 / 4]⟩

theorem radauIIA2_stabilityNum : radauIIA2.stabilityNum = 1 + C (1 / 3) * X :=
  Polynomial.funext fun x => by
    rw [eval_stabilityNum, det_fin_two]
    simp [radauIIA2, vecMulVec, vecHead, vecTail]
    ring

theorem radauIIA2_stabilityDen :
    radauIIA2.stabilityDen = 1 - C (2 / 3) * X + C (1 / 6) * X ^ 2 :=
  Polynomial.funext fun x => by
    rw [eval_stabilityDen, det_fin_two]
    simp [radauIIA2]
    ring

theorem natDegree_radauIIA2_stabilityDen : radauIIA2.stabilityDen.natDegree = 2 := by
  rw [radauIIA2_stabilityDen, show (1 - C (2 / 3 : ℝ) * X + C (1 / 6) * X ^ 2) =
    C (1 / 6) * X ^ 2 + C (-(2 / 3)) * X + C 1 by rw [C_neg, C_1]; ring]
  exact natDegree_quadratic (by norm_num)

/-! ### The two-stage SDIRK method -/

/-- The diagonal coefficient `γ = 1 - √2/2` of `sdirk2`. -/
def sdirk2Coeff : ℝ := 1 - √2 / 2

theorem sdirk2Coeff_sq : sdirk2Coeff ^ 2 = 2 * sdirk2Coeff - 1 / 2 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold sdirk2Coeff
  linear_combination (1 / 4) * h2

theorem sdirk2Coeff_pos : 0 < sdirk2Coeff := by
  have : √2 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  unfold sdirk2Coeff; linarith

/-- **The two-stage SDIRK method** with `γ = 1 - √2/2`. [HairerWanner1996], §IV.6 -/
def sdirk2 : ButcherTableau 2 :=
  ⟨!![sdirk2Coeff, 0; 1 - sdirk2Coeff, sdirk2Coeff], ![1 - sdirk2Coeff, sdirk2Coeff]⟩

theorem sdirk2_stabilityNum : sdirk2.stabilityNum = 1 + C (1 - 2 * sdirk2Coeff) * X :=
  Polynomial.funext fun x => by
    rw [eval_stabilityNum, det_fin_two]
    simp [sdirk2, vecMulVec, vecHead, vecTail]
    ring

theorem sdirk2_stabilityDen :
    sdirk2.stabilityDen = 1 - C (2 * sdirk2Coeff) * X + C (sdirk2Coeff ^ 2) * X ^ 2 :=
  Polynomial.funext fun x => by
    rw [eval_stabilityDen, det_fin_two]
    simp [sdirk2]
    ring

theorem natDegree_sdirk2_stabilityDen : sdirk2.stabilityDen.natDegree = 2 := by
  rw [sdirk2_stabilityDen, show (1 - C (2 * sdirk2Coeff) * X + C (sdirk2Coeff ^ 2) * X ^ 2) =
    C (sdirk2Coeff ^ 2) * X ^ 2 + C (-(2 * sdirk2Coeff)) * X + C 1 by rw [C_neg, C_1]; ring]
  exact natDegree_quadratic (pow_pos sdirk2Coeff_pos 2).ne'

end ButcherTableau

open ButcherTableau

namespace RationalScheme

/-- The rational scheme `(1 + z/2)/(1 - z/2)` of the implicit midpoint rule (Crank–Nicolson). -/
def implicitMidpoint : RationalScheme :=
  ButcherTableau.implicitMidpoint.toRationalScheme
    (by rw [implicitMidpoint_stability.1, implicitMidpoint_stability.2]
        exact (RationalScheme.theta (1 / 2) (by norm_num)).natDegree_num_le)
    (by rw [implicitMidpoint_stability.2]
        exact (RationalScheme.theta (1 / 2) (by norm_num)).aeval_den_ne_zero)

theorem implicitMidpoint_eq_theta : implicitMidpoint = theta (1 / 2) (by norm_num) :=
  RationalScheme.ext implicitMidpoint_stability.1 implicitMidpoint_stability.2

/-- The rational scheme `(1 + z/2 + z²/12)/(1 - z/2 + z²/12)` of two-stage Gauss–Legendre. -/
def gaussLegendre2 : RationalScheme :=
  ButcherTableau.gaussLegendre2.toRationalScheme
    (by
      rw [gaussLegendre2_stabilityNum, gaussLegendre2_stabilityDen]
      have : (1 - C (1 / 2 : ℝ) * X + C (1 / 12) * X ^ 2).natDegree = 2 := by
        rw [show (1 - C (1 / 2 : ℝ) * X + C (1 / 12) * X ^ 2) =
          C (1 / 12) * X ^ 2 + C (-(1 / 2)) * X + C 1 by rw [C_neg, C_1]; ring]
        exact natDegree_quadratic (by norm_num)
      rw [this]; compute_degree!)
    (by
      rw [gaussLegendre2_stabilityDen]
      intro z hz
      convert quadratic_ne_zero (a := 1 / 2) (b := 1 / 12) (by norm_num) (by norm_num) hz using 1
      simp)

theorem isSymmetric_implicitMidpoint : implicitMidpoint.IsSymmetric := by
  rw [implicitMidpoint_eq_theta]; exact isSymmetric_theta_half

theorem hasOrder_implicitMidpoint : implicitMidpoint.HasOrder 2 := by
  rw [implicitMidpoint_eq_theta]; exact hasOrder_theta_half

theorem isSymmetric_gaussLegendre2 : gaussLegendre2.IsSymmetric := by
  change ButcherTableau.gaussLegendre2.stabilityNum =
    ButcherTableau.gaussLegendre2.stabilityDen.comp (-X)
  rw [gaussLegendre2_stabilityNum, gaussLegendre2_stabilityDen]
  exact Polynomial.funext fun x => by simp

/-- **The Gauss–Legendre method has order `4`**. [HairerWanner1996], §IV.5 -/
theorem hasOrder_gaussLegendre2 : gaussLegendre2.HasOrder 4 := by
  change X ^ 5 ∣ ButcherTableau.gaussLegendre2.stabilityNum -
    ButcherTableau.gaussLegendre2.stabilityDen * expTaylor 4
  rw [gaussLegendre2_stabilityNum, gaussLegendre2_stabilityDen]
  exact ⟨C (1 / 144) - C (1 / 288) * X, Polynomial.funext fun x => by
    simp [expTaylor, Finset.sum_range_succ, Nat.factorial]; ring⟩

/-- The rational scheme of the two-stage Radau IIA method, `r(z) = (1 + z/3)/(1 - 2z/3 + z²/6)`. -/
def radauIIA2 : RationalScheme :=
  ButcherTableau.radauIIA2.toRationalScheme
    (by rw [natDegree_radauIIA2_stabilityDen, radauIIA2_stabilityNum]; compute_degree!)
    (by
      rw [radauIIA2_stabilityDen]
      intro z hz
      convert quadratic_ne_zero (a := 2 / 3) (b := 1 / 6) (by norm_num) (by norm_num) hz using 1
      simp)

theorem isAStable_radauIIA2 : radauIIA2.IsAStable := fun y => by
  have hd := radauIIA2.aeval_den_ne_zero (y * Complex.I) (by simp)
  change ‖aeval _ ButcherTableau.radauIIA2.stabilityNum /
    aeval _ ButcherTableau.radauIIA2.stabilityDen‖ ≤ 1
  change aeval _ ButcherTableau.radauIIA2.stabilityDen ≠ 0 at hd
  rw [radauIIA2_stabilityNum, radauIIA2_stabilityDen] at *
  refine norm_div_le_one_of_sq hd ?_
  have e1 : aeval ((y : ℂ) * Complex.I) (1 + C (1 / 3 : ℝ) * X) =
      1 + ((1 / 3 : ℝ) : ℂ) * (y * Complex.I) + ((0 : ℝ) : ℂ) * (y * Complex.I) ^ 2 := by simp
  have e2 : aeval ((y : ℂ) * Complex.I) (1 - C (2 / 3 : ℝ) * X + C (1 / 6) * X ^ 2) =
      1 + ((-(2 / 3) : ℝ) : ℂ) * (y * Complex.I) + ((1 / 6 : ℝ) : ℂ) * (y * Complex.I) ^ 2 := by
    simp; ring
  rw [e1, e2, norm_sq_quadratic, norm_sq_quadratic]
  nlinarith [sq_nonneg (y ^ 2)]

theorem isLStable_radauIIA2 : radauIIA2.IsLStable := by
  refine ⟨isAStable_radauIIA2, degree_lt_degree ?_⟩
  change ButcherTableau.radauIIA2.stabilityNum.natDegree <
    ButcherTableau.radauIIA2.stabilityDen.natDegree
  rw [natDegree_radauIIA2_stabilityDen, radauIIA2_stabilityNum]
  exact lt_of_le_of_lt (b := 1) (by compute_degree!) one_lt_two

/-- **The Radau IIA method has order `3`**. [HairerWanner1996], §IV.5 -/
theorem hasOrder_radauIIA2 : radauIIA2.HasOrder 3 := by
  change X ^ 4 ∣ ButcherTableau.radauIIA2.stabilityNum -
    ButcherTableau.radauIIA2.stabilityDen * expTaylor 3
  rw [radauIIA2_stabilityNum, radauIIA2_stabilityDen]
  exact ⟨C (1 / 36) - C (1 / 36) * X, Polynomial.funext fun x => by
    simp [expTaylor, Finset.sum_range_succ, Nat.factorial]; ring⟩

/-- The rational scheme of `sdirk2`, `r(z) = (1 + (1 - 2γ) z)/(1 - γ z)²`. -/
def sdirk2 : RationalScheme :=
  ButcherTableau.sdirk2.toRationalScheme
    (by rw [natDegree_sdirk2_stabilityDen, sdirk2_stabilityNum]; compute_degree!)
    (by
      rw [sdirk2_stabilityDen]
      intro z hz
      have hγ := sdirk2Coeff_pos
      convert quadratic_ne_zero (a := 2 * sdirk2Coeff) (b := sdirk2Coeff ^ 2) (by positivity)
        (by positivity) hz using 1
      simp)

theorem isAStable_sdirk2 : sdirk2.IsAStable := fun y => by
  have hd := sdirk2.aeval_den_ne_zero (y * Complex.I) (by simp)
  change ‖aeval _ ButcherTableau.sdirk2.stabilityNum /
    aeval _ ButcherTableau.sdirk2.stabilityDen‖ ≤ 1
  change aeval _ ButcherTableau.sdirk2.stabilityDen ≠ 0 at hd
  rw [sdirk2_stabilityNum, sdirk2_stabilityDen] at *
  refine norm_div_le_one_of_sq hd ?_
  have e1 : aeval ((y : ℂ) * Complex.I) (1 + C (1 - 2 * sdirk2Coeff) * X) =
      1 + ((1 - 2 * sdirk2Coeff : ℝ) : ℂ) * (y * Complex.I) +
        ((0 : ℝ) : ℂ) * (y * Complex.I) ^ 2 := by simp
  have e2 : aeval ((y : ℂ) * Complex.I)
      (1 - C (2 * sdirk2Coeff) * X + C (sdirk2Coeff ^ 2) * X ^ 2) =
      1 + ((-(2 * sdirk2Coeff)) : ℝ) * (y * Complex.I) +
        ((sdirk2Coeff ^ 2 : ℝ) : ℂ) * (y * Complex.I) ^ 2 := by
    simp; ring
  rw [e1, e2, norm_sq_quadratic, norm_sq_quadratic]
  have hγ := sdirk2Coeff_sq
  nlinarith [sq_nonneg (sdirk2Coeff ^ 2 * y ^ 2)]

theorem isLStable_sdirk2 : sdirk2.IsLStable := by
  refine ⟨isAStable_sdirk2, degree_lt_degree ?_⟩
  change ButcherTableau.sdirk2.stabilityNum.natDegree < ButcherTableau.sdirk2.stabilityDen.natDegree
  rw [natDegree_sdirk2_stabilityDen, sdirk2_stabilityNum]
  exact lt_of_le_of_lt (b := 1) (by compute_degree!) one_lt_two

/-- **`sdirk2` has order `2`**. [HairerWanner1996], §IV.6 -/
theorem hasOrder_sdirk2 : sdirk2.HasOrder 2 := by
  change X ^ 3 ∣ ButcherTableau.sdirk2.stabilityNum -
    ButcherTableau.sdirk2.stabilityDen * expTaylor 2
  rw [sdirk2_stabilityNum, sdirk2_stabilityDen]
  have hγ := sdirk2Coeff_sq
  exact ⟨C (sdirk2Coeff - sdirk2Coeff ^ 2) - C (sdirk2Coeff ^ 2 / 2) * X,
    Polynomial.funext fun x => by
      simp [expTaylor, Finset.sum_range_succ, Nat.factorial]
      linear_combination (-x ^ 2) * hγ⟩

end RationalScheme

end Feec.TimeStepping
