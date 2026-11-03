module

public import Feec.Models.BoundedDomain.MovingTSD
public import Feec.Counterexamples.BallSymTSD
public import Feec.Models.Box.EigenDense
public import Feec.Domain.Rellich
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# TSD eigenfields on the unit ball

For the thesis' complex `H̊¹(Ω; ℝ³) → H̊(curl, Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)` (`gradCurl`) and
`K = {0} × L²(TSD) × L²(TSD)`, whether the invariant core `K*` contains a moving datum reduces
(`Feec.Models.BoundedDomain.not_coreSub_le_stationary_iff`, under a complete set of eigenvectors
of `L²`) to the existence of a nonzero **TSD eigenfield**: `u ∈ L²(TSD) ∩ H̊(curl)` with
`curl u ∈ H(curl)`, `curl† curl u = ξ² u`, `ξ > 0`, necessarily with `curl u ∉ H̊(curl)`. This
file decides the question on the unit ball `B = {|x| < 1}` (`Feec.Counterexamples.BallSymTSD.ball3`)
in the class of fields that are `C²` up to the boundary, and isolates what remains.

## Decision

**No TSD eigenfield exists on the ball in the smooth class** (alternative (b)): a TSD eigenfield
with a representative `C²` on a neighbourhood of the closed ball vanishes
(`eq_zero_of_isEigenfield_of_contDiff_ball`). Evidence before the proof: for the separated ansatz
`Uᵢⱼ(x) = jₗ(ξ|x|) |x|⁻ˡ Pᵢⱼ(x)` with `Pᵢⱼ` homogeneous harmonic polynomials of degree `l`
(`jₗ(ξ) = 0`, the Dirichlet condition forced on symmetric trace-free fields with normal rows),
the divergence condition splits by degree into `P(x) x = 0`, and a symmetric, trace-free,
harmonic `P` with `P(x) x = 0` restricts to a transverse-traceless tensor on `S²`, hence vanishes;
an exact rank computation (outside the formalization) finds no nonzero solution for `l ≤ 6`.
Mixed eigenspaces cannot help, since the recurrence `jₗ₋₁ + jₗ₊₁ = (2l + 1) jₗ / z` forbids
common zeros of `jₗ` and `jₗ₊₂`, the only degrees the divergence couples. The separated fields
are entire, so the smooth-class theorem covers them; spherical Bessel functions are not
formalized.

## Proof of the smooth-class theorem

Let `U` be a `C²` representative (cut off to `ℝ³`, `exists_contDiff_eq_on_closedBall3`).
1. **Interior equations** (`pointwise_of_mem_tsd`, `eigen_data`): `U` is symmetric, trace-free and
   divergence-free in `B`, `curl curl U = ξ² U` in `B`, and Green's formula holds against every
   `ψ ∈ C_c^∞(ℝ³)` (no boundary condition on `ψ`).
2. **Trace** (`crossF_eq_zero_of_green`): the radial cut-offs `χₙ(x) = ηₙ(|x|²)` turn Green's
   formula into `∫_{S²} Σᵢₖ ψᵢₖ (x × Uᵢ)ₖ dσ = 0` (`integral_sphere_eq_zero_of_integral_div`,
   through polar coordinates `integral_eq_integral_sphere` and the approximate identity
   `κₙ = -d/dr ηₙ(r²)`, `tendsto_integral_deriv_eta_mul`), so `x × Uᵢ(x) = 0` on `S²`; being
   symmetric and trace-free, `U = 0` on `S²` (`eq_zero_of_symm_of_trace_of_cross`).
3. **The boundary layer** `V = (x · ∇) U` (`isSphereTT_radDeriv`): tangential derivatives of `U`
   vanish on `S²` and `∂ₜ² U = |t|² V` for `t ⊥ x` (`tangential_derivs`, along great circles);
   with `div U = 0` and `ΔU = ∇ div U - curl curl U = 0` on `S²`, `V` is symmetric, trace-free,
   tangential and surface-divergence-free: the TT layer.
4. **No TT tensors on the round sphere** (`eq_zero_of_isSphereTT`): in the stereographic chart
   `σ(x, y) = (2x, 2y, x² + y² - 1)/(1 + x² + y²)`, `F = σₓᵀ V σₓ - i σₓᵀ V σ_y` satisfies the
   Cauchy–Riemann equations (`ttAx_add_ttBy`, `ttA'y_sub_ttB'x`, polynomial identities) and
   `|F| = O(|z|⁻⁴)`, so `F = 0` by Liouville; `F = 0` forces `V = 0` (genus zero: no holomorphic
   quadratic differentials). Hence `∇U = 0` and `curl U = 0` on `S²`.
5. **Conclusion**: `curl U` is `C¹` and vanishes on `S²`, so `curl u ∈ H̊(curl)`
   (`smoothField_mem_minimal_of_eq_zero_sphere`, cut-offs with `|curl U| = O(1 - |x|²)`), and
   `u = 0` by `Feec.Models.BoundedDomain.eq_zero_of_isEigenfield_of_mem_minimal`.

## What remains

Whether every TSD eigenfield on `B` is `C²` up to `∂B` is elliptic boundary regularity, absent
from Mathlib. It is isolated as the standard row-wise statement `MaxwellEigenfieldRegularity`:
weakly divergence-free vector fields `w ∈ H̊(curl, B)` with `curl curl w = ξ² w` are `C²` up to
`∂B`. This involves no symmetry or trace, is not equivalent to the absence of eigenfields, and
implies the TSD form `TSDEigenfieldRegularity` (`tsdEigenfieldRegularity_of_maxwell`: the rows
of a TSD eigenfield are such fields, `isDivFree_rowF`, `isMaxwellEigenfield_rowF`). On the ball
the TSD form alone is *equivalent* to the absence of TSD eigenfields
(`tsdEigenfieldRegularity_ball_iff`), so it only restates the open question; the Maxwell form is
the genuine missing theorem. With it and a complete set of eigenvectors of `L²` (`EigenDense`,
from compactness on the ball), `K*` is stationary on the ball
(`coreSub_le_stationary_ball_of_maxwellRegularity`, `coreSub_le_stationary_ball_of_regularity`).
Without `EigenDense`, a TSD eigenfield always produces a moving datum of `K*` on every open `Ω`,
with the explicit orbit `cos(ξt) u + (sin(ξt)/ξ) L u` (`not_coreSub_le_stationary_of_eigenfield`).

## Non-vacuity

The hypotheses of the smooth-class theorem without the electric boundary condition are met by
the nonzero smooth TSD shear wave `cos(ξ x₁)(e₂e₃ᵀ + e₃e₂ᵀ)`, which therefore lies outside
`H̊(curl)` (`shearWaveL2_spec`). The zero field has a smooth representative (`hasC2Rep_zero`), so
`TSDEigenfieldRegularity` holds wherever TSD eigenfields vanish
(`tsdEigenfieldRegularity_of_forall_eq_zero`), concretely on every box
(`tsdEigenfieldRegularity_box`); `MaxwellEigenfieldRegularity` holds on `∅`
(`maxwellEigenfieldRegularity_empty`). On boxes and on the ball it is a genuine statement:
nonzero smooth electric Maxwell eigenfields exist there (e.g. `sin x₁ sin x₂ e₃` on `(0, π)³`,
and the toroidal fields below on the ball; not formalized). Dropping symmetry instead,
`u = e₃ ⊗ T` with the toroidal field `T = j₁(k|x|)/|x| (x₂, -x₁, 0)`, `j₁(k) = 0`, is a nonzero
trace-free, divergence-free eigenfield in `H̊(curl)` (not formalized: it needs `j₁`).

## Layering

The file lives in `Counterexamples` because it uses the ball geometry (`rho`, `ball3`, the radial
cut-offs `eta`, `chi`) of `Feec.Counterexamples.BallSymTSD`; `Models` files do not import
`Counterexamples`.

## Main results

* **`not_coreSub_le_stationary_of_eigenfield`**: a nonzero TSD eigenfield gives a non-stationary
  datum of `K*`, on every open `Ω`, without `EigenDense`.
* **`eq_zero_of_isSphereTT`**: transverse-traceless `C¹` tensors on `S²` vanish.
* **`crossF_eq_zero_of_green`**: Green's formula forces the tangential trace to vanish pointwise.
* **`eq_zero_of_isEigenfield_of_contDiff_ball`**: TSD eigenfields `C²` up to `∂B` vanish.
* **`tsdEigenfieldRegularity_of_maxwell`**: row-wise Maxwell regularity implies TSD regularity.
* **`coreSub_le_stationary_ball_of_maxwellRegularity`**,
  `coreSub_le_stationary_ball_of_regularity`, `tsdEigenfieldRegularity_ball_iff`.
* `shearWaveL2_spec`, `hasC2Rep_zero`, `tsdEigenfieldRegularity_box`,
  `maxwellEigenfieldRegularity_empty`: non-vacuity.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17)
* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.5 (traces), §5.6, §6.3 (boundary
  regularity)
* [V. Girault, P.-A. Raviart, *Finite Element Methods for Navier–Stokes Equations*][GiraultRaviart1986],
  Ch. I, §3 (`H(curl) ∩ H(div)`)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace LinearPMap ContDiff
open MeasureTheory Set Filter Topology Feec.Domain Feec.Models.BoundedDomain

namespace Feec.Counterexamples.BallEigenfields

-- Over `ℝ` the generic real structure on the window spaces duplicates the inner-product one.
attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-! ### Sufficiency: an eigenfield moves `K*` (no spectral hypothesis) -/

section Sufficiency

variable {Ω : Set R3}

/-- **A TSD eigenfield gives a moving datum of `K*`, without `EigenDense`**: on every open
`Ω ⊆ ℝ³` (bounded or not), if `u ≠ 0` lies in `L²(TSD) ∩ H̊(curl)` with `curl u ∈ H(curl)` and
`curl† curl u = ξ² u`, `ξ > 0`, then `x = (0, u, 0)` lies in `K*`, is not stationary, and its
orbit is `e^{tL} x = cos(ξt) x + (sin(ξt)/ξ) L x`
(`Feec.C0Group.IsIsometric.S_eq_of_isEigenSq`). So `K*` is not stationary. This is the
sufficiency half of `Feec.Models.BoundedDomain.gradCurl_coreSub_spectral` (part 3), which needs
no spectral hypothesis (`Feec.ShortHilbertComplex.eigenfield_mem_invariantCore₁`). -/
theorem not_coreSub_le_stationary_of_eigenfield (hΩ : IsOpen Ω)
    {ξ : ℝ} (hξ : 0 < ξ) {v : L2F ℝ Ω Ix} (hv0 : v ≠ 0) (hv : v ∈ tsd Ω)
    (hE : (gradCurl ℝ hΩ).IsEigenfield ξ v) :
    ShortHilbertComplex.inj₁ (𝕜 := ℝ) (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix) v ∈
        (gradCurl ℝ hΩ).coreSub (tsd Ω) (tsd Ω) ∧
      ShortHilbertComplex.inj₁ (𝕜 := ℝ) (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix) v ∉
        (gradCurl ℝ hΩ).stationary ∧
      (∃ h : ShortHilbertComplex.inj₁ (𝕜 := ℝ) (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix) v ∈
          (gradCurl ℝ hΩ).wave.domain, ∀ t : ℝ,
        (gradCurl ℝ hΩ).toHilbertComplex.waveGroup.S t
            (ShortHilbertComplex.inj₁ (𝕜 := ℝ) (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix) v) =
          Real.cos (ξ * t) •
              ShortHilbertComplex.inj₁ (𝕜 := ℝ) (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix) v +
            (Real.sin (ξ * t) / ξ) • (gradCurl ℝ hΩ).wave ⟨_, h⟩) ∧
      ¬ (gradCurl ℝ hΩ).coreSub (tsd Ω) (tsd Ω) ≤ (gradCurl ℝ hΩ).stationary := by
  obtain ⟨hv1, hv3, e⟩ := hE
  obtain ⟨h2, e2⟩ := LinearPMap.exists_apply_eq_zero_of_mem_ker (tsd_le_ker_gradCurl hΩ hv)
  obtain ⟨hES, hm, hns⟩ := ShortHilbertComplex.eigenfield_mem_invariantCore₁
    (S := gradCurl ℝ hΩ) (S₂ := tsd Ω) hξ hv hv1 h2 e2 hv3
    (minimal_curl_mem_tsd hΩ ⟨v, hv1⟩ hv) e
  obtain ⟨hD, hD2, hLL⟩ := hES
  have horbit : ∀ t : ℝ, (gradCurl ℝ hΩ).toHilbertComplex.waveGroup.S t
      (ShortHilbertComplex.inj₁ (𝕜 := ℝ) (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix) v) =
        Real.cos (ξ * t) •
            ShortHilbertComplex.inj₁ (𝕜 := ℝ) (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix) v +
          (Real.sin (ξ * t) / ξ) • (gradCurl ℝ hΩ).wave ⟨_, hD⟩ := by
    have key : ∀ (A : _ →ₗ.[ℝ] _) (_ : (gradCurl ℝ hΩ).toHilbertComplex.waveGroup.generator = A)
        (h : ShortHilbertComplex.inj₁ (𝕜 := ℝ) (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix) v ∈
          A.domain) (h' : A ⟨_, h⟩ ∈ A.domain) (_ : A ⟨A ⟨_, h⟩, h'⟩ = -(ξ ^ 2) •
          ShortHilbertComplex.inj₁ (𝕜 := ℝ) (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix) v),
        ∀ t : ℝ, (gradCurl ℝ hΩ).toHilbertComplex.waveGroup.S t
          (ShortHilbertComplex.inj₁ (𝕜 := ℝ) (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix) v) =
          Real.cos (ξ * t) •
            ShortHilbertComplex.inj₁ (𝕜 := ℝ) (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix) v +
            (Real.sin (ξ * t) / ξ) • A ⟨_, h⟩ := by
      rintro A rfl h h' e t
      exact (gradCurl ℝ hΩ).toHilbertComplex.isIsometric_waveGroup.S_eq_of_isEigenSq hξ h h' e t
    exact key _ (gradCurl ℝ hΩ).toHilbertComplex.generator_waveGroup hD hD2 hLL
  exact ⟨hm, hns hv0, ⟨hD, horbit⟩, fun hle => hns hv0 (hle hm)⟩

end Sufficiency

section Stereographic

open Complex
open Feec.Counterexamples.BallSymTSD (rho)

/-! ### Stereographic coordinates on the unit sphere -/

/-- `q(x, y) = 1 + x² + y²`. -/
def stQ (x y : ℝ) : ℝ := 1 + x ^ 2 + y ^ 2

theorem stQ_pos (x y : ℝ) : 0 < stQ x y := by unfold stQ; positivity

theorem stQ_ne_zero (x y : ℝ) : stQ x y ≠ 0 := (stQ_pos x y).ne'

/-- The numerator `N = (2x, 2y, x² + y² - 1)` of the inverse stereographic map `σ = N / q`. -/
def stN (x y : ℝ) : R3 := ![2 * x, 2 * y, x ^ 2 + y ^ 2 - 1]
/-- `X = (1 + x² + y²)² ∂ₓσ`. -/
def stX (x y : ℝ) : R3 := ![-2 * (x ^ 2 - y ^ 2 - 1), -4 * x * y, 4 * x]
/-- `Y = (1 + x² + y²)² ∂_y σ`. -/
def stY (x y : ℝ) : R3 := ![-4 * x * y, 2 * (x ^ 2 - y ^ 2 + 1), 4 * y]
/-- `(1 + x² + y²)³ ∂ₓ² σ`. -/
def stXX (x y : ℝ) : R3 :=
  ![4 * x * (x ^ 2 - 3 * y ^ 2 - 3), 4 * y * (3 * x ^ 2 - y ^ 2 - 1), -4 * (3 * x ^ 2 - y ^ 2 - 1)]
/-- `(1 + x² + y²)³ ∂ₓ∂_y σ`. -/
def stXY (x y : ℝ) : R3 :=
  ![4 * y * (3 * x ^ 2 - y ^ 2 - 1), -4 * x * (x ^ 2 - 3 * y ^ 2 + 1), -16 * x * y]
/-- `(1 + x² + y²)³ ∂_y² σ`. -/
def stYY (x y : ℝ) : R3 :=
  ![-4 * x * (x ^ 2 - 3 * y ^ 2 + 1), -4 * y * (3 * x ^ 2 - y ^ 2 + 3), 4 * (x ^ 2 - 3 * y ^ 2 + 1)]

/-- The inverse stereographic projection `σ(x, y) = (2x, 2y, x² + y² - 1) / (1 + x² + y²)`
from the north pole. -/
def stSig (x y : ℝ) : R3 := fun k => stN x y k * (stQ x y)⁻¹
/-- `∂ₓσ`. -/
def stSx (x y : ℝ) : R3 := fun k => stX x y k * (stQ x y)⁻¹ ^ 2
/-- `∂_y σ`. -/
def stSy (x y : ℝ) : R3 := fun k => stY x y k * (stQ x y)⁻¹ ^ 2
/-- `∂ₓ² σ`. -/
def stSxx (x y : ℝ) : R3 := fun k => stXX x y k * (stQ x y)⁻¹ ^ 3
/-- `∂ₓ∂_y σ`. -/
def stSxy (x y : ℝ) : R3 := fun k => stXY x y k * (stQ x y)⁻¹ ^ 3
/-- `∂_y² σ`. -/
def stSyy (x y : ℝ) : R3 := fun k => stYY x y k * (stQ x y)⁻¹ ^ 3

theorem rho_stSig (x y : ℝ) : rho (stSig x y) = 1 := by
  have := stQ_ne_zero x y
  simp only [rho, stSig, stN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  field_simp
  unfold stQ
  ring

private theorem hasDerivAt_mul_inv_pow {P Q : ℝ → ℝ} {P' Q' x : ℝ} (hP : HasDerivAt P P' x)
    (hQ : HasDerivAt Q Q' x) (hQ0 : Q x ≠ 0) (m : ℕ) :
    HasDerivAt (fun t => P t * (Q t)⁻¹ ^ m)
      (P' * (Q x)⁻¹ ^ m - m * P x * Q' * (Q x)⁻¹ ^ (m + 1)) x := by
  have h2 : HasDerivAt (fun t => (Q t)⁻¹ ^ m)
      ((m : ℝ) * (Q x)⁻¹ ^ (m - 1) * (-Q' / Q x ^ 2)) x := (hQ.inv hQ0).fun_pow m
  have h := hP.mul h2
  convert h using 1
  rcases m with _ | m
  · simp
  · simp only [Nat.add_sub_cancel, div_eq_mul_inv, ← inv_pow]
    push_cast
    ring

private theorem hasDerivAt_stQ_x (x y : ℝ) : HasDerivAt (fun t => stQ t y) (2 * x) x := by
  have h := ((hasDerivAt_pow 2 x).const_add 1).add_const (y ^ 2)
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at h
  exact h.congr_deriv (by ring)

private theorem hasDerivAt_stQ_y (x y : ℝ) : HasDerivAt (fun t => stQ x t) (2 * y) y := by
  have h := (hasDerivAt_pow 2 y).const_add (1 + x ^ 2)
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at h
  exact (h.congr_deriv (by ring)).congr_of_eventuallyEq
    (Eventually.of_forall fun t => by simp only [stQ])

private theorem hasDerivAt_mul_inv_pow' {P Q : ℝ → ℝ} {P' Q' x : ℝ} (hP : HasDerivAt P P' x)
    (hQ : HasDerivAt Q Q' x) (hQ0 : Q x ≠ 0) (m : ℕ) {R : ℝ}
    (hR : P' * Q x - m * P x * Q' = R) :
    HasDerivAt (fun t => P t * (Q t)⁻¹ ^ m) (R * (Q x)⁻¹ ^ (m + 1)) x := by
  refine (hasDerivAt_mul_inv_pow hP hQ hQ0 m).congr_deriv ?_
  have hr : Q x * (Q x)⁻¹ = 1 := mul_inv_cancel₀ hQ0
  rw [← hR]
  linear_combination (-(P' * (Q x)⁻¹ ^ m)) * hr

/-- `∂ₓ N`. -/
def stNx (x : ℝ) : R3 := ![2, 0, 2 * x]
/-- `∂_y N`. -/
def stNy (y : ℝ) : R3 := ![0, 2, 2 * y]
/-- `∂ₓ X`, also `∂_y Y`. -/
def stXx (x y : ℝ) : R3 := ![-4 * x, -4 * y, 4]
/-- `∂_y X`. -/
def stXy (x y : ℝ) : R3 := ![4 * y, -4 * x, 0]
/-- `∂ₓ Y`. -/
def stYx (x y : ℝ) : R3 := ![-4 * y, 4 * x, 0]

private theorem hasDerivAt_stN_x (x y : ℝ) (k : Fin 3) :
    HasDerivAt (fun t => stN t y k) (stNx x k) x := by
  fin_cases k <;> simp only [stN, stNx, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  · exact ((hasDerivAt_id x).const_mul 2).congr_deriv (by simp)
  · exact hasDerivAt_const x _
  · exact (((hasDerivAt_pow 2 x).add_const (y ^ 2)).sub_const 1).congr_deriv (by simp)

private theorem hasDerivAt_stN_y (x y : ℝ) (k : Fin 3) :
    HasDerivAt (fun t => stN x t k) (stNy y k) y := by
  fin_cases k <;> simp only [stN, stNy, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  · exact hasDerivAt_const y _
  · exact ((hasDerivAt_id y).const_mul 2).congr_deriv (by simp)
  · exact (((hasDerivAt_pow 2 y).const_add (x ^ 2)).sub_const 1).congr_deriv (by simp)

private theorem hasDerivAt_stX_x (x y : ℝ) (k : Fin 3) :
    HasDerivAt (fun t => stX t y k) (stXx x y k) x := by
  fin_cases k <;> simp only [stX, stXx, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  · exact ((((hasDerivAt_pow 2 x).sub_const (y ^ 2)).sub_const 1).const_mul (-2)).congr_deriv
      (by simp; ring)
  · exact (((hasDerivAt_id x).const_mul (-4)).mul_const y).congr_deriv (by simp)
  · exact ((hasDerivAt_id x).const_mul 4).congr_deriv (by simp)

private theorem hasDerivAt_stX_y (x y : ℝ) (k : Fin 3) :
    HasDerivAt (fun t => stX x t k) (stXy x y k) y := by
  fin_cases k <;> simp only [stX, stXy, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  · exact ((((hasDerivAt_pow 2 y).const_sub (x ^ 2)).sub_const 1).const_mul (-2)).congr_deriv
      (by simp; ring)
  · exact ((hasDerivAt_id y).const_mul (-4 * x)).congr_deriv (by simp)
  · exact hasDerivAt_const y _

private theorem hasDerivAt_stY_x (x y : ℝ) (k : Fin 3) :
    HasDerivAt (fun t => stY t y k) (stYx x y k) x := by
  fin_cases k <;> simp only [stY, stYx, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  · exact (((hasDerivAt_id x).const_mul (-4)).mul_const y).congr_deriv (by simp)
  · exact ((((hasDerivAt_pow 2 x).sub_const (y ^ 2)).add_const 1).const_mul 2).congr_deriv
      (by simp; ring)
  · exact hasDerivAt_const x _

private theorem hasDerivAt_stY_y (x y : ℝ) (k : Fin 3) :
    HasDerivAt (fun t => stY x t k) (stXx x y k) y := by
  fin_cases k <;> simp only [stY, stXx, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  · exact ((hasDerivAt_id y).const_mul (-4 * x)).congr_deriv (by simp)
  · exact ((((hasDerivAt_pow 2 y).const_sub (x ^ 2)).add_const 1).const_mul 2).congr_deriv
      (by simp; ring)
  · exact ((hasDerivAt_id y).const_mul 4).congr_deriv (by simp)

theorem hasDerivAt_stSig_x (x y : ℝ) (k : Fin 3) :
    HasDerivAt (fun t => stSig t y k) (stSx x y k) x := by
  have h := hasDerivAt_mul_inv_pow' (hasDerivAt_stN_x x y k) (hasDerivAt_stQ_x x y)
    (stQ_ne_zero x y) 1 (R := stX x y k) (by
      fin_cases k <;> simp [stN, stNx, stX, stQ] <;> ring)
  simpa only [pow_one, stSig, stSx, stSy, Nat.reduceAdd] using h

theorem hasDerivAt_stSig_y (x y : ℝ) (k : Fin 3) :
    HasDerivAt (fun t => stSig x t k) (stSy x y k) y := by
  have h := hasDerivAt_mul_inv_pow' (hasDerivAt_stN_y x y k) (hasDerivAt_stQ_y x y)
    (stQ_ne_zero x y) 1 (R := stY x y k) (by
      fin_cases k <;> simp [stN, stNy, stY, stQ] <;> ring)
  simpa only [pow_one, stSig, stSx, stSy, Nat.reduceAdd] using h

theorem hasDerivAt_stSx_x (x y : ℝ) (k : Fin 3) :
    HasDerivAt (fun t => stSx t y k) (stSxx x y k) x :=
  hasDerivAt_mul_inv_pow' (hasDerivAt_stX_x x y k) (hasDerivAt_stQ_x x y)
    (stQ_ne_zero x y) 2 (R := stXX x y k) (by
      fin_cases k <;> simp [stX, stXx, stXX, stQ] <;> ring)

theorem hasDerivAt_stSx_y (x y : ℝ) (k : Fin 3) :
    HasDerivAt (fun t => stSx x t k) (stSxy x y k) y :=
  hasDerivAt_mul_inv_pow' (hasDerivAt_stX_y x y k) (hasDerivAt_stQ_y x y)
    (stQ_ne_zero x y) 2 (R := stXY x y k) (by
      fin_cases k <;> simp [stX, stXy, stXY, stQ] <;> ring)

theorem hasDerivAt_stSy_x (x y : ℝ) (k : Fin 3) :
    HasDerivAt (fun t => stSy t y k) (stSxy x y k) x :=
  hasDerivAt_mul_inv_pow' (hasDerivAt_stY_x x y k) (hasDerivAt_stQ_x x y)
    (stQ_ne_zero x y) 2 (R := stXY x y k) (by
      fin_cases k <;> simp [stY, stYx, stXY, stQ] <;> ring)

theorem hasDerivAt_stSy_y (x y : ℝ) (k : Fin 3) :
    HasDerivAt (fun t => stSy x t k) (stSyy x y k) y :=
  hasDerivAt_mul_inv_pow' (hasDerivAt_stY_y x y k) (hasDerivAt_stQ_y x y)
    (stQ_ne_zero x y) 2 (R := stYY x y k) (by
      fin_cases k <;> simp [stY, stXx, stYY, stQ] <;> ring)

/-! ### Calculus along the chart -/

theorem clm_apply_eq_sum (L : R3 →L[ℝ] ℝ) (v : R3) : L v = ∑ k, v k * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (Pi.single k (v k) : R3) = v k • Pi.single k 1 by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

theorem hasDerivAt_comp_stSig_x {f : R3 → ℝ} (hf : Differentiable ℝ f) (x y : ℝ) :
    HasDerivAt (fun t => f (stSig t y)) (∑ k, stSx x y k * partialDeriv k f (stSig x y)) x := by
  have hσ : HasDerivAt (fun t => stSig t y) (stSx x y) x :=
    hasDerivAt_pi.2 fun k => hasDerivAt_stSig_x x y k
  have h := (hf (stSig x y)).hasFDerivAt.comp_hasDerivAt x hσ
  rw [clm_apply_eq_sum] at h
  exact h

theorem hasDerivAt_comp_stSig_y {f : R3 → ℝ} (hf : Differentiable ℝ f) (x y : ℝ) :
    HasDerivAt (fun t => f (stSig x t)) (∑ k, stSy x y k * partialDeriv k f (stSig x y)) y := by
  have hσ : HasDerivAt (fun t => stSig x t) (stSy x y) y :=
    hasDerivAt_pi.2 fun k => hasDerivAt_stSig_y x y k
  have h := (hf (stSig x y)).hasFDerivAt.comp_hasDerivAt y hσ
  rw [clm_apply_eq_sum] at h
  exact h

/-- Derivative of a bilinear expression `Σᵢⱼ aᵢ Mᵢⱼ bⱼ` along a parameter. -/
theorem hasDerivAt_quad {a b : ℝ → R3} {M : Ix → ℝ → ℝ} {a' b' : R3} {M' : Ix → ℝ} {t : ℝ}
    (ha : ∀ i, HasDerivAt (fun s => a s i) (a' i) t)
    (hb : ∀ j, HasDerivAt (fun s => b s j) (b' j) t)
    (hM : ∀ ij, HasDerivAt (M ij) (M' ij) t) :
    HasDerivAt (fun s => ∑ i, ∑ j, a s i * M (i, j) s * b s j)
      (∑ i, ∑ j, (a' i * M (i, j) t * b t j + a t i * M' (i, j) * b t j +
        a t i * M (i, j) t * b' j)) t := by
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  exact (((ha i).mul (hM _)).mul (hb j)).congr_deriv (by simp only [Pi.mul_apply]; ring)

/-! ### Transverse-traceless tensors on the unit sphere -/

/-- `V` is **transverse-traceless on the unit sphere** `S² = {|x| = 1}`: at every `x ∈ S²`,
`V(x)` is symmetric, trace-free and tangential (`V(x) x = 0`), and `V` has zero tangential
divergence `Σⱼₖ (δⱼₖ - xⱼ xₖ) ∂ₖ Vᵢⱼ(x) = 0` (the surface divergence of a tangential tensor). -/
def IsSphereTT (V : Ix → R3 → ℝ) : Prop :=
  ∀ x : R3, rho x = 1 → (∀ i j, V (i, j) x = V (j, i) x) ∧ ∑ i, V (i, i) x = 0 ∧
    (∀ i, ∑ j, V (i, j) x * x j = 0) ∧
    ∀ i, ∑ j, ∑ k, ((if j = k then 1 else 0) - x j * x k) * partialDeriv k (V (i, j)) x = 0

/-- The real part `A = σₓᵀ V σₓ` of the pulled-back quadratic differential `F = A - i B`. -/
def ttA (V : Ix → R3 → ℝ) (x y : ℝ) : ℝ :=
  ∑ i, ∑ j, stSx x y i * V (i, j) (stSig x y) * stSx x y j
/-- `B = σₓᵀ V σ_y`. -/
def ttB (V : Ix → R3 → ℝ) (x y : ℝ) : ℝ :=
  ∑ i, ∑ j, stSx x y i * V (i, j) (stSig x y) * stSy x y j
/-- `A' = -σ_yᵀ V σ_y` (equal to `A` on `S²`, `ttA_eq_ttA'`). -/
def ttA' (V : Ix → R3 → ℝ) (x y : ℝ) : ℝ :=
  -∑ i, ∑ j, stSy x y i * V (i, j) (stSig x y) * stSy x y j
/-- `B' = σ_yᵀ V σₓ` (equal to `B` on `S²`, `ttB_eq_ttB'`). -/
def ttB' (V : Ix → R3 → ℝ) (x y : ℝ) : ℝ :=
  ∑ i, ∑ j, stSy x y i * V (i, j) (stSig x y) * stSx x y j

section TT

variable {V : Ix → R3 → ℝ}

/-- The tangency condition in numerator form: `Σⱼ Vᵢⱼ(σ) Nⱼ = 0`. -/
theorem sum_mul_stN_eq_zero (hV : IsSphereTT V) (x y : ℝ) (i : Fin 3) :
    ∑ j, V (i, j) (stSig x y) * stN x y j = 0 := by
  have h := (hV _ (rho_stSig x y)).2.2.1 i
  have hr : (stQ x y)⁻¹ ≠ 0 := inv_ne_zero (stQ_ne_zero x y)
  have e : ∑ j, V (i, j) (stSig x y) * stSig x y j =
      (∑ j, V (i, j) (stSig x y) * stN x y j) * (stQ x y)⁻¹ := by
    simp only [stSig, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e] at h
  exact (mul_eq_zero.1 h).resolve_right hr

/-- The divergence condition in numerator form. -/
theorem sum_tdiv_stN_eq_zero (hV : IsSphereTT V) (x y : ℝ) (i : Fin 3) :
    ∑ j, ∑ k, (stQ x y ^ 2 * (if j = k then 1 else 0) - stN x y j * stN x y k) *
      partialDeriv k (V (i, j)) (stSig x y) = 0 := by
  have h := (hV _ (rho_stSig x y)).2.2.2 i
  have hq := stQ_ne_zero x y
  have e : ∑ j, ∑ k, (stQ x y ^ 2 * (if j = k then 1 else 0) - stN x y j * stN x y k) *
      partialDeriv k (V (i, j)) (stSig x y) = stQ x y ^ 2 * ∑ j, ∑ k,
        ((if j = k then 1 else 0) - stSig x y j * stSig x y k) *
          partialDeriv k (V (i, j)) (stSig x y) := by
    simp only [Finset.mul_sum, stSig]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [e, h, mul_zero]

/-- `∂ₓ A`, as produced by `hasDerivAt_quad`. -/
def ttAx (V : Ix → R3 → ℝ) (x y : ℝ) : ℝ :=
  ∑ i, ∑ j, (stSxx x y i * V (i, j) (stSig x y) * stSx x y j +
    stSx x y i * (∑ k, stSx x y k * partialDeriv k (V (i, j)) (stSig x y)) * stSx x y j +
    stSx x y i * V (i, j) (stSig x y) * stSxx x y j)
/-- `∂_y B`. -/
def ttBy (V : Ix → R3 → ℝ) (x y : ℝ) : ℝ :=
  ∑ i, ∑ j, (stSxy x y i * V (i, j) (stSig x y) * stSy x y j +
    stSx x y i * (∑ k, stSy x y k * partialDeriv k (V (i, j)) (stSig x y)) * stSy x y j +
    stSx x y i * V (i, j) (stSig x y) * stSyy x y j)
/-- `∂_y A'`. -/
def ttA'y (V : Ix → R3 → ℝ) (x y : ℝ) : ℝ :=
  -∑ i, ∑ j, (stSyy x y i * V (i, j) (stSig x y) * stSy x y j +
    stSy x y i * (∑ k, stSy x y k * partialDeriv k (V (i, j)) (stSig x y)) * stSy x y j +
    stSy x y i * V (i, j) (stSig x y) * stSyy x y j)
/-- `∂ₓ B'`. -/
def ttB'x (V : Ix → R3 → ℝ) (x y : ℝ) : ℝ :=
  ∑ i, ∑ j, (stSxy x y i * V (i, j) (stSig x y) * stSx x y j +
    stSy x y i * (∑ k, stSx x y k * partialDeriv k (V (i, j)) (stSig x y)) * stSx x y j +
    stSy x y i * V (i, j) (stSig x y) * stSxx x y j)

/-- The constraints at `σ(x, y)` in polynomial form. -/
private theorem tt_constraints (hV : IsSphereTT V) (x y : ℝ) :
    V (1, 0) (stSig x y) = V (0, 1) (stSig x y) ∧ V (2, 0) (stSig x y) = V (0, 2) (stSig x y) ∧
    V (2, 1) (stSig x y) = V (1, 2) (stSig x y) ∧
    V (0, 0) (stSig x y) + V (1, 1) (stSig x y) + V (2, 2) (stSig x y) = 0 := by
  obtain ⟨hs, htr, -, -⟩ := hV _ (rho_stSig x y)
  refine ⟨hs 1 0, hs 2 0, hs 2 1, ?_⟩
  simpa [Fin.sum_univ_three] using htr

theorem ttA_eq_ttA' (hV : IsSphereTT V) (x y : ℝ) : ttA V x y = ttA' V x y := by
  obtain ⟨h10, h20, h21, htr⟩ := tt_constraints hV x y
  have hC0 := sum_mul_stN_eq_zero hV x y 0
  have hC1 := sum_mul_stN_eq_zero hV x y 1
  have hC2 := sum_mul_stN_eq_zero hV x y 2
  simp only [ttA, ttA', stSx, stSy, Fin.sum_univ_three] at *
  set r := (stQ x y)⁻¹
  simp only [stX, stY, stN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, h10, h20, h21] at *
  linear_combination (r ^ 4 * (-8 * x)) * hC0 + (r ^ 4 * (-8 * y)) * hC1 +
    (r ^ 4 * (-4 * (x ^ 2 + y ^ 2 - 1))) * hC2 + (r ^ 4 * (4 * (x ^ 2 + y ^ 2 + 1) ^ 2)) * htr

theorem ttB_eq_ttB' (hV : IsSphereTT V) (x y : ℝ) : ttB V x y = ttB' V x y := by
  obtain ⟨h10, h20, h21, -⟩ := tt_constraints hV x y
  simp only [ttB, ttB', Fin.sum_univ_three, h10, h20, h21]
  ring

/-- **First Cauchy–Riemann equation** `∂ₓA + ∂_y B = 0`. -/
theorem ttAx_add_ttBy (hV : IsSphereTT V) (x y : ℝ) : ttAx V x y + ttBy V x y = 0 := by
  obtain ⟨h10, h20, h21, htr⟩ := tt_constraints hV x y
  have hC0 := sum_mul_stN_eq_zero hV x y 0
  have hC1 := sum_mul_stN_eq_zero hV x y 1
  have hC2 := sum_mul_stN_eq_zero hV x y 2
  have hT0 := sum_tdiv_stN_eq_zero hV x y 0
  have hT1 := sum_tdiv_stN_eq_zero hV x y 1
  have hT2 := sum_tdiv_stN_eq_zero hV x y 2
  simp only [ttAx, ttBy, stSx, stSy, stSxx, stSxy, stSyy, Fin.sum_univ_three] at *
  set r := (stQ x y)⁻¹
  simp only [stX, stY, stN, stXX, stXY, stYY, stQ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h10, h20, h21, ite_true, ite_false,
    Fin.reduceEq, one_ne_zero, zero_ne_one] at *
  linear_combination (r ^ 5 * (8 * (5 * x ^ 2 - 3 * y ^ 2 - 3))) * hC0 +
    (r ^ 5 * (64 * x * y)) * hC1 + (r ^ 5 * (8 * x * (x ^ 2 + y ^ 2 - 7))) * hC2 +
    (r ^ 5 * (-8 * x * (x ^ 2 + y ^ 2 + 1) ^ 2)) * htr +
    (4 * r ^ 6 * (-2 * (x ^ 2 - y ^ 2 - 1))) * hT0 + (4 * r ^ 6 * (-4 * x * y)) * hT1 +
    (4 * r ^ 6 * (4 * x)) * hT2

/-- **Second Cauchy–Riemann equation** `∂_y A' - ∂ₓB' = 0`. -/
theorem ttA'y_sub_ttB'x (hV : IsSphereTT V) (x y : ℝ) : ttA'y V x y - ttB'x V x y = 0 := by
  obtain ⟨h10, h20, h21, htr⟩ := tt_constraints hV x y
  have hC0 := sum_mul_stN_eq_zero hV x y 0
  have hC1 := sum_mul_stN_eq_zero hV x y 1
  have hC2 := sum_mul_stN_eq_zero hV x y 2
  have hT0 := sum_tdiv_stN_eq_zero hV x y 0
  have hT1 := sum_tdiv_stN_eq_zero hV x y 1
  have hT2 := sum_tdiv_stN_eq_zero hV x y 2
  simp only [ttA'y, ttB'x, stSx, stSy, stSxx, stSxy, stSyy, Fin.sum_univ_three] at *
  set r := (stQ x y)⁻¹
  simp only [stX, stY, stN, stXX, stXY, stYY, stQ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h10, h20, h21, ite_true, ite_false,
    Fin.reduceEq, one_ne_zero, zero_ne_one] at *
  linear_combination (-(r ^ 5 * (64 * x * y))) * hC0 +
    (-(r ^ 5 * (-8 * (3 * x ^ 2 - 5 * y ^ 2 + 3)))) * hC1 +
    (-(r ^ 5 * (8 * y * (x ^ 2 + y ^ 2 - 7)))) * hC2 +
    (-(r ^ 5 * (-8 * y * (x ^ 2 + y ^ 2 + 1) ^ 2))) * htr + (-(4 * r ^ 6 * (-4 * x * y))) * hT0 +
    (-(4 * r ^ 6 * (2 * (x ^ 2 - y ^ 2 + 1)))) * hT1 + (-(4 * r ^ 6 * (4 * y))) * hT2

theorem hasDerivAt_ttA_x (hV' : ∀ ij, Differentiable ℝ (V ij)) (x y : ℝ) :
    HasDerivAt (fun t => ttA V t y) (ttAx V x y) x := by
  have hM : ∀ ij : Ix, HasDerivAt (fun t => V ij (stSig t y))
      (∑ k, stSx x y k * partialDeriv k (V ij) (stSig x y)) x := fun ij =>
    hasDerivAt_comp_stSig_x (hV' ij) x y
  have h := hasDerivAt_quad (a := fun t => stSx t y) (b := fun t => stSx t y)
    (M := fun ij t => V ij (stSig t y)) (M' := fun ij => ∑ k,
      stSx x y k * partialDeriv k (V ij) (stSig x y))
    (t := x) (fun i => hasDerivAt_stSx_x x y i) (fun j => hasDerivAt_stSx_x x y j) hM
  exact h

theorem hasDerivAt_ttB_y (hV' : ∀ ij, Differentiable ℝ (V ij)) (x y : ℝ) :
    HasDerivAt (fun t => ttB V x t) (ttBy V x y) y := by
  have hM : ∀ ij : Ix, HasDerivAt (fun t => V ij (stSig x t))
      (∑ k, stSy x y k * partialDeriv k (V ij) (stSig x y)) y := fun ij =>
    hasDerivAt_comp_stSig_y (hV' ij) x y
  have h := hasDerivAt_quad (a := fun t => stSx x t) (b := fun t => stSy x t)
    (M := fun ij t => V ij (stSig x t)) (M' := fun ij => ∑ k,
      stSy x y k * partialDeriv k (V ij) (stSig x y))
    (t := y) (fun i => hasDerivAt_stSx_y x y i) (fun j => hasDerivAt_stSy_y x y j) hM
  exact h

theorem hasDerivAt_ttA_y (hV : IsSphereTT V) (hV' : ∀ ij, Differentiable ℝ (V ij)) (x y : ℝ) :
    HasDerivAt (fun t => ttA V x t) (ttA'y V x y) y := by
  have e : (fun t => ttA V x t) = fun t => ttA' V x t := funext fun t => ttA_eq_ttA' hV x t
  rw [e]
  have hM : ∀ ij : Ix, HasDerivAt (fun t => V ij (stSig x t))
      (∑ k, stSy x y k * partialDeriv k (V ij) (stSig x y)) y := fun ij =>
    hasDerivAt_comp_stSig_y (hV' ij) x y
  have h := hasDerivAt_quad (a := fun t => stSy x t) (b := fun t => stSy x t)
    (M := fun ij t => V ij (stSig x t)) (M' := fun ij => ∑ k,
      stSy x y k * partialDeriv k (V ij) (stSig x y))
    (t := y) (fun i => hasDerivAt_stSy_y x y i) (fun j => hasDerivAt_stSy_y x y j) hM
  exact h.neg

theorem hasDerivAt_ttB_x (hV : IsSphereTT V) (hV' : ∀ ij, Differentiable ℝ (V ij)) (x y : ℝ) :
    HasDerivAt (fun t => ttB V t y) (ttB'x V x y) x := by
  have e : (fun t => ttB V t y) = fun t => ttB' V t y := funext fun t => ttB_eq_ttB' hV t y
  rw [e]
  have hM : ∀ ij : Ix, HasDerivAt (fun t => V ij (stSig t y))
      (∑ k, stSx x y k * partialDeriv k (V ij) (stSig x y)) x := fun ij =>
    hasDerivAt_comp_stSig_x (hV' ij) x y
  have h := hasDerivAt_quad (a := fun t => stSy t y) (b := fun t => stSx t y)
    (M := fun ij t => V ij (stSig t y)) (M' := fun ij => ∑ k,
      stSx x y k * partialDeriv k (V ij) (stSig x y))
    (t := x) (fun i => hasDerivAt_stSy_x x y i) (fun j => hasDerivAt_stSx_x x y j) hM
  exact h

/-- The pulled-back quadratic differential `F = A - i B` on `ℂ`. -/
def ttF (V : Ix → R3 → ℝ) (z : ℂ) : ℂ := (ttA V z.re z.im : ℂ) - I * (ttB V z.re z.im : ℂ)

theorem differentiable_stSig : Differentiable ℝ (fun z : ℂ => stSig z.re z.im) := by
  refine differentiable_pi.2 fun k => ?_
  have hq : ∀ z : ℂ, (1 + z.re ^ 2 + z.im ^ 2) ≠ 0 := fun z => stQ_ne_zero z.re z.im
  fin_cases k <;> simp only [stSig, stN, stQ, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] <;> fun_prop (disch := exact hq _)

theorem differentiable_stSx : Differentiable ℝ (fun z : ℂ => stSx z.re z.im) := by
  refine differentiable_pi.2 fun k => ?_
  have hq : ∀ z : ℂ, (1 + z.re ^ 2 + z.im ^ 2) ≠ 0 := fun z => stQ_ne_zero z.re z.im
  fin_cases k <;> simp only [stSx, stX, stQ, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] <;> fun_prop (disch := exact hq _)

theorem differentiable_stSy : Differentiable ℝ (fun z : ℂ => stSy z.re z.im) := by
  refine differentiable_pi.2 fun k => ?_
  have hq : ∀ z : ℂ, (1 + z.re ^ 2 + z.im ^ 2) ≠ 0 := fun z => stQ_ne_zero z.re z.im
  fin_cases k <;> simp only [stSy, stY, stQ, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] <;> fun_prop (disch := exact hq _)

theorem differentiable_ttF (hV' : ∀ ij, Differentiable ℝ (V ij)) :
    Differentiable ℝ (ttF V) := by
  have hσ := differentiable_stSig
  have hx := differentiable_stSx
  have hy := differentiable_stSy
  have hW : ∀ ij, Differentiable ℝ (fun z : ℂ => V ij (stSig z.re z.im)) := fun ij =>
    (hV' ij).comp hσ
  have hA : Differentiable ℝ (fun z : ℂ => ttA V z.re z.im) := by
    unfold ttA
    refine Differentiable.fun_sum fun i _ => Differentiable.fun_sum fun j _ => ?_
    exact (((differentiable_pi.1 hx i).mul (hW _)).mul (differentiable_pi.1 hx j))
  have hB : Differentiable ℝ (fun z : ℂ => ttB V z.re z.im) := by
    unfold ttB
    refine Differentiable.fun_sum fun i _ => Differentiable.fun_sum fun j _ => ?_
    exact (((differentiable_pi.1 hx i).mul (hW _)).mul (differentiable_pi.1 hy j))
  unfold ttF
  exact (ofRealCLM.differentiable.comp hA).sub
    ((differentiable_const I).mul (ofRealCLM.differentiable.comp hB))

/-! ### Holomorphy and Liouville -/

theorem hasFDerivAt_ttF_one (hV : IsSphereTT V) (hV' : ∀ ij, Differentiable ℝ (V ij)) (z : ℂ) :
    fderiv ℝ (ttF V) z 1 = (ttAx V z.re z.im : ℂ) - I * (ttB'x V z.re z.im : ℂ) := by
  have hF := (differentiable_ttF hV' z).hasFDerivAt
  have hγ : HasDerivAt (fun t : ℝ => (t : ℂ) + (z.im : ℂ) * I) 1 z.re := by
    simpa using (ofRealCLM.hasDerivAt (x := z.re)).add_const ((z.im : ℂ) * I)
  have h1 := hF.comp_hasDerivAt_of_eq z.re hγ (by simp [re_add_im])
  have h2 : HasDerivAt (fun t : ℝ => ttF V ((t : ℂ) + (z.im : ℂ) * I))
      ((ttAx V z.re z.im : ℂ) - I * (ttB'x V z.re z.im : ℂ)) z.re := by
    have e : (fun t : ℝ => ttF V ((t : ℂ) + (z.im : ℂ) * I)) =
        fun t => (ttA V t z.im : ℂ) - I * (ttB V t z.im : ℂ) := by
      funext t; simp [ttF]
    rw [e]
    exact (hasDerivAt_ttA_x hV' z.re z.im).ofReal_comp.sub
      ((hasDerivAt_ttB_x hV hV' z.re z.im).ofReal_comp.const_mul I)
  exact h1.unique h2

theorem hasFDerivAt_ttF_I (hV : IsSphereTT V) (hV' : ∀ ij, Differentiable ℝ (V ij)) (z : ℂ) :
    fderiv ℝ (ttF V) z I = (ttA'y V z.re z.im : ℂ) - I * (ttBy V z.re z.im : ℂ) := by
  have hF := (differentiable_ttF hV' z).hasFDerivAt
  have hγ : HasDerivAt (fun t : ℝ => (z.re : ℂ) + (t : ℂ) * I) I z.im := by
    simpa using ((ofRealCLM.hasDerivAt (x := z.im)).mul_const I).const_add (z.re : ℂ)
  have h1 := hF.comp_hasDerivAt_of_eq z.im hγ (by simp [re_add_im])
  have h2 : HasDerivAt (fun t : ℝ => ttF V ((z.re : ℂ) + (t : ℂ) * I))
      ((ttA'y V z.re z.im : ℂ) - I * (ttBy V z.re z.im : ℂ)) z.im := by
    have e : (fun t : ℝ => ttF V ((z.re : ℂ) + (t : ℂ) * I)) =
        fun t => (ttA V z.re t : ℂ) - I * (ttB V z.re t : ℂ) := by
      funext t; simp [ttF]
    rw [e]
    exact (hasDerivAt_ttA_y hV hV' z.re z.im).ofReal_comp.sub
      ((hasDerivAt_ttB_y hV' z.re z.im).ofReal_comp.const_mul I)
  exact h1.unique h2

/-- **The pulled-back quadratic differential is holomorphic** (Cauchy–Riemann). -/
theorem differentiable_complex_ttF (hV : IsSphereTT V) (hV' : ∀ ij, Differentiable ℝ (V ij)) :
    Differentiable ℂ (ttF V) := fun z => by
  refine differentiableAt_complex_iff_differentiableAt_real.2
    ⟨differentiable_ttF hV' z, ?_⟩
  rw [hasFDerivAt_ttF_I hV hV' z, hasFDerivAt_ttF_one hV hV' z]
  have e1 : ttA'y V z.re z.im = ttB'x V z.re z.im := sub_eq_zero.1 (ttA'y_sub_ttB'x hV _ _)
  have e2 : ttBy V z.re z.im = -ttAx V z.re z.im := eq_neg_of_add_eq_zero_right
    (ttAx_add_ttBy hV _ _)
  rw [e1, e2, smul_eq_mul]
  push_cast
  linear_combination (ttB'x V z.re z.im : ℂ) * I_sq

private theorem abs_stX_le (x y : ℝ) (i : Fin 3) : |stX x y i| ≤ 2 * stQ x y := by
  fin_cases i <;> simp only [stX, stQ, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] <;> rw [abs_le] <;> constructor <;>
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 1), sq_nonneg (x + 1),
      sq_nonneg x, sq_nonneg y]

private theorem abs_stY_le (x y : ℝ) (i : Fin 3) : |stY x y i| ≤ 2 * stQ x y := by
  fin_cases i <;> simp only [stY, stQ, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] <;> rw [abs_le] <;> constructor <;>
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (y - 1), sq_nonneg (y + 1),
      sq_nonneg x, sq_nonneg y]

private theorem abs_stSx_le (x y : ℝ) (i : Fin 3) : |stSx x y i| ≤ 2 * (stQ x y)⁻¹ := by
  have hq := stQ_pos x y
  rw [stSx, abs_mul, abs_of_pos (pow_pos (inv_pos.2 hq) 2)]
  calc |stX x y i| * (stQ x y)⁻¹ ^ 2 ≤ 2 * stQ x y * (stQ x y)⁻¹ ^ 2 := by
        gcongr; exact abs_stX_le x y i
    _ = 2 * (stQ x y)⁻¹ := by field_simp

private theorem abs_stSy_le (x y : ℝ) (i : Fin 3) : |stSy x y i| ≤ 2 * (stQ x y)⁻¹ := by
  have hq := stQ_pos x y
  rw [stSy, abs_mul, abs_of_pos (pow_pos (inv_pos.2 hq) 2)]
  calc |stY x y i| * (stQ x y)⁻¹ ^ 2 ≤ 2 * stQ x y * (stQ x y)⁻¹ ^ 2 := by
        gcongr; exact abs_stY_le x y i
    _ = 2 * (stQ x y)⁻¹ := by field_simp

private theorem abs_quad_le {a b : R3} {M : Ix → ℝ} {α β C : ℝ} (ha : ∀ i, |a i| ≤ α)
    (hb : ∀ j, |b j| ≤ β) (hM : ∀ ij, |M ij| ≤ C) :
    |∑ i, ∑ j, a i * M (i, j) * b j| ≤ 9 * (α * C * β) := by
  have hα : 0 ≤ α := (abs_nonneg _).trans (ha 0)
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hb 0)
  have hC : 0 ≤ C := (abs_nonneg _).trans (hM (0, 0))
  calc |∑ i, ∑ j, a i * M (i, j) * b j| ≤ ∑ i : Fin 3, ∑ j : Fin 3, α * C * β := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul (ha i) (hM _) (abs_nonneg _) hα) (hb j) (abs_nonneg _)
          (mul_nonneg hα hC)
    _ = 9 * (α * C * β) := by simp; ring

/-- `F → 0` at infinity: `|F| ≤ 72 M / (1 + |z|²)²`. -/
theorem tendsto_ttF (hV' : ∀ ij, Continuous (V ij)) :
    Tendsto (ttF V) (cocompact ℂ) (𝓝 0) := by
  have hK : IsCompact {x : R3 | rho x = 1} :=
    Metric.isCompact_of_isClosed_isBounded
      (isClosed_eq Feec.Counterexamples.BallSymTSD.continuous_rho continuous_const)
      ((Metric.isBounded_closedBall (x := (0 : R3)) (r := 1)).subset fun x hx => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact Feec.Counterexamples.BallSymTSD.norm_le_one_of_rho_le (le_of_eq hx))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (f := fun x => ∑ ij, |V ij x|) (continuous_finsetSum _ fun ij _ => (hV' ij).abs).continuousOn
  have hCij : ∀ x : R3, rho x = 1 → ∀ ij, |V ij x| ≤ C := fun x hx ij => by
    have h := hC x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at h
    exact (Finset.single_le_sum (f := fun ij => |V ij x|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ ij)).trans h
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hCij _ (rho_stSig 0 0) (0, 0))
  have hbound : ∀ z : ℂ, ‖ttF V z‖ ≤ 72 * C * (1 + ‖z‖ ^ 2)⁻¹ := by
    intro z
    have hq : stQ z.re z.im = 1 + ‖z‖ ^ 2 := by
      rw [stQ, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have hr : 0 < (stQ z.re z.im)⁻¹ := inv_pos.2 (stQ_pos _ _)
    have hr1 : (stQ z.re z.im)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
      unfold stQ; nlinarith [sq_nonneg z.re, sq_nonneg z.im])
    have hA := abs_quad_le (fun i => abs_stSx_le z.re z.im i) (fun j => abs_stSx_le z.re z.im j)
      (fun ij => hCij _ (rho_stSig z.re z.im) ij)
    have hB := abs_quad_le (fun i => abs_stSx_le z.re z.im i) (fun j => abs_stSy_le z.re z.im j)
      (fun ij => hCij _ (rho_stSig z.re z.im) ij)
    calc ‖ttF V z‖ ≤ |ttA V z.re z.im| + |ttB V z.re z.im| := by
          unfold ttF
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 9 * (2 * (stQ z.re z.im)⁻¹ * C * (2 * (stQ z.re z.im)⁻¹)) +
            9 * (2 * (stQ z.re z.im)⁻¹ * C * (2 * (stQ z.re z.im)⁻¹)) := add_le_add hA hB
      _ = 72 * C * (stQ z.re z.im)⁻¹ * (stQ z.re z.im)⁻¹ := by ring
      _ ≤ 72 * C * (stQ z.re z.im)⁻¹ * 1 := by gcongr
      _ = 72 * C * (1 + ‖z‖ ^ 2)⁻¹ := by rw [hq, mul_one]
  have hlim : Tendsto (fun z : ℂ => 72 * C * (1 + ‖z‖ ^ 2)⁻¹) (cocompact ℂ) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℂ => 1 + ‖z‖ ^ 2) (cocompact ℂ) atTop :=
      tendsto_atTop_add_const_left _ _
        ((tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop)
    simpa using (tendsto_inv_atTop_zero.comp h1).const_mul (72 * C)
  exact squeeze_zero_norm hbound hlim

/-- `A = B = 0` on the whole chart (Liouville). -/
theorem ttA_eq_zero_and_ttB_eq_zero (hV : IsSphereTT V) (hV' : ∀ ij, ContDiff ℝ 1 (V ij))
    (x y : ℝ) : ttA V x y = 0 ∧ ttB V x y = 0 := by
  have hd : ∀ ij, Differentiable ℝ (V ij) := fun ij => (hV' ij).differentiable one_ne_zero
  have h := (differentiable_complex_ttF hV hd).eq_const_of_tendsto_cocompact
    (tendsto_ttF fun ij => (hV' ij).continuous)
  have hz := congrFun h ((x : ℂ) + (y : ℂ) * I)
  simp only [ttF, Function.const_apply] at hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp at hre him
  exact ⟨hre, him⟩

/-- The numerator `Xᵀ V X` of `A`. -/
def ttAn (V : Ix → R3 → ℝ) (x y : ℝ) : ℝ :=
  ∑ i, ∑ j, stX x y i * V (i, j) (stSig x y) * stX x y j
/-- The numerator `Xᵀ V Y` of `B`. -/
def ttBn (V : Ix → R3 → ℝ) (x y : ℝ) : ℝ :=
  ∑ i, ∑ j, stX x y i * V (i, j) (stSig x y) * stY x y j

theorem ttA_eq_mul (x y : ℝ) : ttA V x y = (stQ x y)⁻¹ ^ 4 * ttAn V x y := by
  simp only [ttA, ttAn, stSx, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem ttB_eq_mul (x y : ℝ) : ttB V x y = (stQ x y)⁻¹ ^ 4 * ttBn V x y := by
  simp only [ttB, ttBn, stSx, stSy, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- A tangential, symmetric, trace-free tensor with `A = B = 0` vanishes (`σ, σₓ, σ_y` is a
basis). -/
theorem apply_stSig_eq_zero (hV : IsSphereTT V) {x y : ℝ} (hA : ttA V x y = 0)
    (hB : ttB V x y = 0) (ij : Ix) : V ij (stSig x y) = 0 := by
  have hr : (stQ x y)⁻¹ ^ 4 ≠ 0 := pow_ne_zero _ (inv_ne_zero (stQ_ne_zero x y))
  have hAn : ttAn V x y = 0 := by
    rw [ttA_eq_mul] at hA; exact (mul_eq_zero.1 hA).resolve_left hr
  have hBn : ttBn V x y = 0 := by
    rw [ttB_eq_mul] at hB; exact (mul_eq_zero.1 hB).resolve_left hr
  obtain ⟨h10, h20, h21, htr⟩ := tt_constraints hV x y
  have hC0 := sum_mul_stN_eq_zero hV x y 0
  have hC1 := sum_mul_stN_eq_zero hV x y 1
  have hC2 := sum_mul_stN_eq_zero hV x y 2
  have hq4 : (1 + x ^ 2 + y ^ 2) ^ 4 ≠ 0 := pow_ne_zero _ (stQ_ne_zero x y)
  simp only [ttAn, ttBn, Fin.sum_univ_three, stX, stY, stN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h10, h20,
    h21] at hAn hBn hC0 hC1 hC2
  have e00 : (1 + x ^ 2 + y ^ 2) ^ 4 * V (0, 0) (stSig x y) = 0 := by
    linear_combination (4 * x * (x ^ 4 + y ^ 4 + 2 * y ^ 2 + 1)) * hC0 +
      (-8 * x ^ 2 * y * (y ^ 2 + 1)) * hC1 +
      (-4 * x ^ 2 * (y ^ 2 + 1) * (x ^ 2 + y ^ 2 - 1)) * hC2 +
      (4 * x ^ 2 * y ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2) * htr +
      ((x ^ 2 - 2 * x * y - y ^ 2 - 1) * (x ^ 2 + 2 * x * y - y ^ 2 - 1)/4) * hAn +
      (x * y * (x ^ 2 - y ^ 2 - 1)) * hBn
  have e01 : (1 + x ^ 2 + y ^ 2) ^ 4 * V (0, 1) (stSig x y) = 0 := by
    linear_combination (2 * y * (3 * x ^ 4 + y ^ 4 + 2 * y ^ 2 + 1)) * hC0 +
      (2 * x * (x ^ 4 + 4 * x ^ 2 * y ^ 2 + 2 * x ^ 2 - y ^ 4 + 1)) * hC1 +
      (2 * x * y * (x ^ 2 - y ^ 2 - 1) * (x ^ 2 + y ^ 2 - 1)) * hC2 +
      (-2 * x * y * (x ^ 2 - y ^ 2 + 1) * (x ^ 2 + y ^ 2 + 1) ^ 2) * htr +
      (x * y * (x - y) * (x + y)) * hAn + (-(x ^ 4 - 6 * x ^ 2 * y ^ 2 + y ^ 4 - 1)/4) * hBn
  have e02 : (1 + x ^ 2 + y ^ 2) ^ 4 * V (0, 2) (stSig x y) = 0 := by
    linear_combination (x ^ 6 + 3 * x ^ 4 * y ^ 2 - 3 * x ^ 4 + 3 * x ^ 2 * y ^ 4 + 6 * x ^ 2 *
        y ^ 2 + 3 * x ^ 2 + y ^ 6 + y ^ 4 - y ^ 2 - 1) * hC0 +
      (-4 * x * y * (x ^ 2 - y ^ 2 - 1)) * hC1 +
      (4 * x * (x ^ 2 * y ^ 2 + 2 * x ^ 2 + y ^ 4 + y ^ 2)) * hC2 +
      (-4 * x * y ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2) * htr + (-x * (x ^ 2 - 3 * y ^ 2 - 1)/2) * hAn +
      (-y * (3 * x ^ 2 - y ^ 2 - 1)/2) * hBn
  have e11 : (1 + x ^ 2 + y ^ 2) ^ 4 * V (1, 1) (stSig x y) = 0 := by
    linear_combination (-2 * x * (x ^ 2 - 2 * x * y + y ^ 2 + 1) * (x ^ 2 + 2 * x * y + y ^ 2 +
        1)) * hC0 +
      (2 * y * (x ^ 4 + 6 * x ^ 2 * y ^ 2 + 2 * x ^ 2 + y ^ 4 + 2 * y ^ 2 + 1)) * hC1 +
      (-(x ^ 2 + y ^ 2 - 1) * (x ^ 2 - 2 * x * y + y ^ 2 + 1) * (x ^ 2 + 2 * x * y + y ^ 2 +
        1)) * hC2 + ((x ^ 2 - y ^ 2 + 1) ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2) * htr +
      (-(x ^ 2 - 2 * x * y - y ^ 2 + 1) * (x ^ 2 + 2 * x * y - y ^ 2 + 1)/4) * hAn +
      (-x * y * (x ^ 2 - y ^ 2 + 1)) * hBn
  have e12 : (1 + x ^ 2 + y ^ 2) ^ 4 * V (1, 2) (stSig x y) = 0 := by
    linear_combination (-8 * x ^ 3 * y) * hC0 +
      (x ^ 6 + 3 * x ^ 4 * y ^ 2 + x ^ 4 + 3 * x ^ 2 * y ^ 4 - 6 * x ^ 2 * y ^ 2 - x ^ 2 +
        y ^ 6 + y ^ 4 - y ^ 2 - 1) * hC1 +
      (-2 * y * (x ^ 4 - 4 * x ^ 2 - y ^ 4 - 2 * y ^ 2 - 1)) * hC2 +
      (2 * y * (x ^ 2 - y ^ 2 + 1) * (x ^ 2 + y ^ 2 + 1) ^ 2) * htr +
      (-y * (3 * x ^ 2 - y ^ 2 + 1)/2) * hAn + (x * (x ^ 2 - 3 * y ^ 2 + 1)/2) * hBn
  have e22 : (1 + x ^ 2 + y ^ 2) ^ 4 * V (2, 2) (stSig x y) = 0 := by
    linear_combination (-2 * x * (x ^ 2 - 2 * x + y ^ 2 + 1) * (x ^ 2 + 2 * x + y ^ 2 + 1)) * hC0 +
      (-2 * y * (x ^ 2 - 2 * x + y ^ 2 + 1) * (x ^ 2 + 2 * x + y ^ 2 + 1)) * hC1 +
      ((x ^ 2 + y ^ 2 - 1) * (x ^ 4 + 2 * x ^ 2 * y ^ 2 + 6 * x ^ 2 + y ^ 4 + 2 * y ^ 2 + 1)) *
        hC2 + (4 * y ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2) * htr + ((x - y) * (x + y)) * hAn +
      (2 * x * y) * hBn
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · exact (mul_eq_zero.1 e00).resolve_left hq4
  · exact (mul_eq_zero.1 e01).resolve_left hq4
  · exact (mul_eq_zero.1 e02).resolve_left hq4
  · rw [h10]; exact (mul_eq_zero.1 e01).resolve_left hq4
  · exact (mul_eq_zero.1 e11).resolve_left hq4
  · exact (mul_eq_zero.1 e12).resolve_left hq4
  · rw [h20]; exact (mul_eq_zero.1 e02).resolve_left hq4
  · rw [h21]; exact (mul_eq_zero.1 e12).resolve_left hq4
  · exact (mul_eq_zero.1 e22).resolve_left hq4

/-- Every point of `S²` other than the north pole is in the chart. -/
theorem stSig_inv {p : R3} (hp : rho p = 1) (h2 : p 2 ≠ 1) :
    stSig (p 0 / (1 - p 2)) (p 1 / (1 - p 2)) = p := by
  have h : 1 - p 2 ≠ 0 := sub_ne_zero.2 (Ne.symm h2)
  have hρ : p 0 * p 0 + p 1 * p 1 + p 2 * p 2 = 1 := hp
  have hq : stQ (p 0 / (1 - p 2)) (p 1 / (1 - p 2)) = 2 / (1 - p 2) := by
    unfold stQ
    field_simp
    linear_combination hρ
  funext k
  fin_cases k <;> simp only [stSig, stN, hq, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  · field_simp
  · field_simp
  · field_simp
    linear_combination hρ

/-- **No transverse-traceless tensors on the round sphere**: a `C¹` field that is symmetric,
trace-free, tangential and surface-divergence-free on `S²` vanishes on `S²`. In the
stereographic chart `σ`, `F = σₓᵀ V σₓ - i σₓᵀ V σ_y` satisfies the Cauchy–Riemann equations
(`ttAx_add_ttBy`, `ttA'y_sub_ttB'x`) and decays like `|z|⁻⁴`, so it vanishes (Liouville); `F = 0`
forces `V = 0` on the chart (`apply_stSig_eq_zero`), and at the north pole by continuity. This
is the genus-zero case of the absence of holomorphic quadratic differentials. -/
theorem eq_zero_of_isSphereTT (hV : IsSphereTT V) (hV' : ∀ ij, ContDiff ℝ 1 (V ij)) {p : R3}
    (hp : rho p = 1) (ij : Ix) : V ij p = 0 := by
  have hchart : ∀ q : R3, rho q = 1 → q 2 ≠ 1 → V ij q = 0 := fun q hq h2 => by
    rw [← stSig_inv hq h2]
    obtain ⟨hA, hB⟩ := ttA_eq_zero_and_ttB_eq_zero hV hV' (q 0 / (1 - q 2)) (q 1 / (1 - q 2))
    exact apply_stSig_eq_zero hV hA hB ij
  by_cases h2 : p 2 = 1
  swap
  · exact hchart p hp h2
  -- the north pole: approach it along `g(s) = (2s, 0, 1 - s²) / (1 + s²)`
  have hρ : p 0 * p 0 + p 1 * p 1 + p 2 * p 2 = 1 := hp
  have h0 : p 0 = 0 := by rw [h2] at hρ; nlinarith [mul_self_nonneg (p 0), mul_self_nonneg (p 1)]
  have h1 : p 1 = 0 := by rw [h2] at hρ; nlinarith [mul_self_nonneg (p 0), mul_self_nonneg (p 1)]
  set g : ℝ → R3 := fun s => ![2 * s / (1 + s ^ 2), 0, (1 - s ^ 2) / (1 + s ^ 2)]
  have hs : ∀ s : ℝ, 1 + s ^ 2 ≠ 0 := fun s => by positivity
  have hg : Continuous g := by
    refine continuous_pi fun k => ?_
    fin_cases k <;> simp only [g, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] <;> fun_prop (disch := exact hs _)
  have hg0 : g 0 = p := by
    funext k
    fin_cases k <;> simp [g, h0, h1, h2]
  have hgS : ∀ s, rho (g s) = 1 := fun s => by
    simp only [rho, g, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    field_simp
    ring
  have hg2 : ∀ s, s ≠ 0 → g s 2 ≠ 1 := fun s hs0 h => by
    simp only [g, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
    rw [div_eq_one_iff_eq (hs s)] at h
    exact hs0 (by nlinarith [sq_nonneg s])
  have hcont : ContinuousAt (fun s => V ij (g s)) 0 := ((hV' ij).continuous.comp hg).continuousAt
  have hlim : Tendsto (fun s => V ij (g s)) (𝓝[≠] 0) (𝓝 (V ij (g 0))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev : (fun s => V ij (g s)) =ᶠ[𝓝[≠] 0] fun _ => 0 :=
    eventually_nhdsWithin_of_forall fun s hs0 => hchart (g s) (hgS s) (hg2 s hs0)
  rw [← hg0]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)

end TT

end Stereographic

section Tangential

open Feec.Counterexamples.BallSymTSD (rho ball3 continuous_rho)

/-- Chain rule along a curve: `(f ∘ γ)' = Σₖ γₖ' ∂ₖ f(γ)`. -/
theorem hasDerivAt_comp_curve {f : R3 → ℝ} (hf : Differentiable ℝ f) {γ : ℝ → R3} {γ' : R3}
    {s : ℝ} (hγ : ∀ k, HasDerivAt (fun s => γ s k) (γ' k) s) :
    HasDerivAt (fun s => f (γ s)) (∑ k, γ' k * partialDeriv k f (γ s)) s := by
  have h := (hf (γ s)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_pi.2 hγ)
  rw [clm_apply_eq_sum] at h
  exact h

/-! ### Tangential derivatives of fields vanishing on the unit sphere -/

/-- **Tangential derivatives of a `C²` function vanishing on `S²`**: at `x ∈ S²` and for `t ⊥ x`,
`∂_t f(x) = 0` and `∂_t² f(x) = |t|² ∂_x f(x)` (differentiate `f` twice along the great circle
`s ↦ cos(λs) x + sin(λs)/λ t`, `λ = |t|`). -/
theorem tangential_derivs {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (hf0 : ∀ y, rho y = 1 → f y = 0)
    {x t : R3} (hx : rho x = 1) (ht : ∑ k, t k * x k = 0) :
    ∑ k, t k * partialDeriv k f x = 0 ∧
      ∑ k, ∑ m, t k * t m * partialDeriv m (partialDeriv k f) x =
        (∑ k, t k * t k) * ∑ k, x k * partialDeriv k f x := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdk : ∀ k, Differentiable ℝ (partialDeriv k f) := fun k =>
    (hf.partialDeriv (m := 1) (by norm_num) k).differentiable one_ne_zero
  by_cases ht0 : ∑ k, t k * t k = 0
  · have hz : ∀ k, t k = 0 := by
      intro k
      have := Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_self_nonneg (t k)) |>.1 ht0 k
        (Finset.mem_univ k)
      exact mul_self_eq_zero.1 this
    simp [hz]
  set l := Real.sqrt (∑ k, t k * t k)
  have hl : 0 < l := Real.sqrt_pos.2 (lt_of_le_of_ne
    (Finset.sum_nonneg fun k _ => mul_self_nonneg (t k)) (Ne.symm ht0))
  have hl2 : l ^ 2 = ∑ k, t k * t k :=
    Real.sq_sqrt (Finset.sum_nonneg fun k _ => mul_self_nonneg (t k))
  set γ : ℝ → R3 := fun s k => Real.cos (l * s) * x k + Real.sin (l * s) / l * t k
  set γ1 : ℝ → R3 := fun s k => -(l * Real.sin (l * s)) * x k + Real.cos (l * s) * t k
  set γ2 : ℝ → R3 := fun s k => -(l ^ 2 * Real.cos (l * s)) * x k - l * Real.sin (l * s) * t k
  have hγ : ∀ s k, HasDerivAt (fun s => γ s k) (γ1 s k) s := fun s k => by
    have hc := (Real.hasDerivAt_cos (l * s)).comp s ((hasDerivAt_id s).const_mul l)
    have hs := (Real.hasDerivAt_sin (l * s)).comp s ((hasDerivAt_id s).const_mul l)
    refine ((hc.mul_const (x k)).add ((hs.div_const l).mul_const (t k))).congr_deriv ?_
    simp only [γ1, mul_one]
    field_simp
  have hγ1 : ∀ s k, HasDerivAt (fun s => γ1 s k) (γ2 s k) s := fun s k => by
    have hc := (Real.hasDerivAt_cos (l * s)).comp s ((hasDerivAt_id s).const_mul l)
    have hs := (Real.hasDerivAt_sin (l * s)).comp s ((hasDerivAt_id s).const_mul l)
    refine (((hs.const_mul l).neg.mul_const (x k)).add (hc.mul_const (t k))).congr_deriv ?_
    simp only [γ2, mul_one]
    ring
  have hγS : ∀ s, rho (γ s) = 1 := fun s => by
    have hxt : t 0 * x 0 + t 1 * x 1 + t 2 * x 2 = 0 := by simpa [Fin.sum_univ_three] using ht
    have hx' : x 0 * x 0 + x 1 * x 1 + x 2 * x 2 = 1 := hx
    have hl2' : l ^ 2 = t 0 * t 0 + t 1 * t 1 + t 2 * t 2 := by
      simpa [Fin.sum_univ_three] using hl2
    have hcs := Real.cos_sq_add_sin_sq (l * s)
    simp only [rho, γ]
    field_simp
    linear_combination (l ^ 2 * Real.cos (l * s) ^ 2) * hx' +
      (2 * l * Real.cos (l * s) * Real.sin (l * s)) * hxt + (-(Real.sin (l * s) ^ 2)) * hl2' +
      l ^ 2 * hcs
  have hγ0 : γ 0 = x := by funext k; simp [γ]
  have hγ10 : γ1 0 = t := by funext k; simp [γ1]
  -- `f ∘ γ ≡ 0`
  have hG : ∀ s, ∑ k, γ1 s k * partialDeriv k f (γ s) = 0 := fun s => by
    have h1 := hasDerivAt_comp_curve hd (hγ s)
    have e : (fun s => f (γ s)) = fun _ => 0 := funext fun s => hf0 _ (hγS s)
    rw [e] at h1
    exact h1.unique (hasDerivAt_const s 0)
  refine ⟨by simpa [hγ0, hγ10] using hG 0, ?_⟩
  have hG' : HasDerivAt (fun s => ∑ k, γ1 s k * partialDeriv k f (γ s))
      (∑ k, (γ2 0 k * partialDeriv k f (γ 0) + γ1 0 k * ∑ m,
        γ1 0 m * partialDeriv m (partialDeriv k f) (γ 0))) 0 :=
    HasDerivAt.fun_sum fun k _ => (hγ1 0 k).mul (hasDerivAt_comp_curve (hdk k) (hγ 0))
  have e : (fun s => ∑ k, γ1 s k * partialDeriv k f (γ s)) = fun _ => 0 := funext hG
  rw [e] at hG'
  have h0 := hG'.unique (hasDerivAt_const 0 0)
  simp only [hγ0, hγ10, γ2, mul_zero, Real.cos_zero, Real.sin_zero, mul_one, zero_mul,
    sub_zero] at h0
  rw [← hl2]
  have e2 : ∑ k, ∑ m, t k * t m * partialDeriv m (partialDeriv k f) x =
    ∑ k, t k * ∑ m, t m * partialDeriv m (partialDeriv k f) x := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [e2]
  have e3 : ∑ k, (-l ^ 2 * x k * partialDeriv k f x + t k * ∑ m,
    t m * partialDeriv m (partialDeriv k f) x) =
      -l ^ 2 * ∑ k, x k * partialDeriv k f x + ∑ k, t k * ∑ m,
        t m * partialDeriv m (partialDeriv k f) x := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have : ∑ k, (-l ^ 2 * x k * partialDeriv k f x + t k * ∑ m,
    t m * partialDeriv m (partialDeriv k f) x) = 0 := by
    rw [← h0]
  linarith [e3]

/-- The tangential projection `pₖ = eₖ - xₖ x` of the `k`-th basis vector. -/
def tanProj (x : R3) (k : Fin 3) : R3 := fun m => (if m = k then 1 else 0) - x k * x m

theorem sum_tanProj_mul (x : R3) (hx : rho x = 1) (k : Fin 3) :
    ∑ m, tanProj x k m * x m = 0 := by
  have hx' : x 0 * x 0 + x 1 * x 1 + x 2 * x 2 = 1 := hx
  fin_cases k <;> simp [tanProj, Fin.sum_univ_three] <;> linear_combination (-x _) * hx'

/-- **Trace of a Hessian with umbilic tangential part**: if `h(pₖ, pₖ) = |pₖ|² v` for the three
tangential projections and `tr h = 0`, then `h(x, x) = -2 v` (on `|x| = 1`). -/
theorem hess_eq_of_tangential (x : R3) (hx : rho x = 1) (h : Fin 3 → Fin 3 → ℝ) (v : ℝ)
    (hk : ∀ k, ∑ a, ∑ b, tanProj x k a * tanProj x k b * h b a =
      (∑ a, tanProj x k a * tanProj x k a) * v)
    (htr : ∑ k, h k k = 0) :
    ∑ k, ∑ m, x k * x m * h m k = -2 * v := by
  have hx' : x 0 * x 0 + x 1 * x 1 + x 2 * x 2 = 1 := hx
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  simp only [tanProj, Fin.sum_univ_three, Fin.isValue] at h0 h1 h2 htr ⊢
  norm_num at h0 h1 h2
  linear_combination (-1) * h0 + (-1) * h1 + (-1) * h2 + htr +
    ((x 0 * x 0 * h 0 0 + x 0 * x 1 * h 1 0 + x 0 * x 2 * h 2 0 + x 1 * x 0 * h 0 1 + x 1 *
      x 1 * h 1 1 + x 1 * x 2 * h 2 1 + x 2 * x 0 * h 0 2 + x 2 * x 1 * h 1 2 + x 2 * x 2 *
      h 2 2) - (x 0 * x 0 + x 1 * x 1 + x 2 * x 2 - 1) * v) * hx'

/-! ### Fields on the closed ball -/

theorem mem_closure_ball3 {x : R3} (hx : rho x ≤ 1) : x ∈ closure ball3 := by
  have hlim : Tendsto (fun t : ℝ => t • x) (𝓝[<] 1) (𝓝 x) := by
    have : Tendsto (fun t : ℝ => t • x) (𝓝 1) (𝓝 ((1 : ℝ) • x)) :=
      (continuous_id.smul continuous_const).tendsto 1
    rw [one_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim ?_
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 < t ∧ t < 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht using ht
  filter_upwards [hev] with t ht
  show rho (t • x) < 1
  have e : rho (t • x) = t ^ 2 * rho x := by
    simp only [rho, Pi.smul_apply, smul_eq_mul]; ring
  rw [e]
  have h0 := Feec.Counterexamples.BallSymTSD.rho_nonneg x
  have : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
  nlinarith

theorem eq_zero_of_ball3 {f : R3 → ℝ} (hf : Continuous f) (h : ∀ x ∈ ball3, f x = 0) {x : R3}
    (hx : rho x ≤ 1) : f x = 0 := by
  have hEq : EqOn f (fun _ => (0 : ℝ)) (closure ball3) :=
    EqOn.closure (fun y hy => h y hy) hf continuous_const
  exact hEq (mem_closure_ball3 hx)

theorem pd_eq_zero_of_ball3 {f : R3 → ℝ} (h : ∀ x ∈ ball3, f x = 0) {x : R3} (hx : x ∈ ball3)
    (k : Fin 3) : partialDeriv k f x = 0 := by
  have hev : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (Feec.Counterexamples.BallSymTSD.isOpen_ball3.mem_nhds hx) h
  rw [partialDeriv, hev.fderiv_eq]
  simp

end Tangential

/-! ### The boundary layer `(x · ∇) U` is transverse-traceless -/

section BoundaryLayer

open Feec.Counterexamples.BallSymTSD (rho ball3 continuous_rho)

/-- The radial derivative `(x · ∇) U` of a matrix field. -/
def radDeriv (U : Ix → R3 → ℝ) : Ix → R3 → ℝ := fun ij x => ∑ k, x k * partialDeriv k (U ij) x

theorem contDiff_radDeriv {U : Ix → R3 → ℝ} (hU : ∀ ij, ContDiff ℝ 2 (U ij)) (ij : Ix) :
    ContDiff ℝ 1 (radDeriv U ij) := by
  unfold radDeriv
  exact ContDiff.sum fun k _ => (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) k).mul
    ((hU ij).partialDeriv (m := 1) (by norm_num) k)

/-- `∂ₖ (x · ∇ f) = ∂ₖ f + Σₘ xₘ ∂ₖ∂ₘ f`. -/
theorem pd_radDeriv {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (k : Fin 3) (x : R3) :
    partialDeriv k (fun y => ∑ m, y m * partialDeriv m f y) x =
      partialDeriv k f x + ∑ m, x m * partialDeriv k (partialDeriv m f) x := by
  have hdm : ∀ m, Differentiable ℝ (partialDeriv m f) := fun m =>
    (hf.partialDeriv (m := 1) (by norm_num) m).differentiable one_ne_zero
  rw [partialDeriv_sum (f := fun m y => y m * partialDeriv m f y) Finset.univ
    (fun m _ => ((differentiable_apply m).mul (hdm m)) x) k]
  have e : ∀ m, partialDeriv k (fun y => y m * partialDeriv m f y) x =
      (if k = m then partialDeriv m f x else 0) + x m *
        partialDeriv k (partialDeriv m f) x := fun m => by
    rw [partialDeriv_mul (differentiable_apply m x) ((hdm m) x), partialDeriv_apply_coord]
    split_ifs <;> ring
  simp only [e, Finset.sum_add_distrib]
  congr 1
  simp

/-- **The boundary layer of a TSD field vanishing on `S²` is transverse-traceless**: let `U` be
`C²`, symmetric, trace-free and divergence-free in the ball, vanishing on `S²`, with `ΔU = 0` on
`S²`. Then on `S²` the gradient is normal, `∂ₖ Uᵢⱼ = xₖ Vᵢⱼ` with `V = (x · ∇) U`, and `V` is
transverse-traceless (`IsSphereTT`). -/
theorem isSphereTT_radDeriv {U : Ix → R3 → ℝ} (hU : ∀ ij, ContDiff ℝ 2 (U ij))
    (hsym : ∀ x ∈ ball3, ∀ i j, U (i, j) x = U (j, i) x)
    (htr : ∀ x ∈ ball3, ∑ i, U (i, i) x = 0)
    (hdiv : ∀ x ∈ ball3, ∀ i, ∑ j, partialDeriv j (U (i, j)) x = 0)
    (hlap : ∀ x, rho x = 1 → ∀ ij, laplacian (U ij) x = 0)
    (hU0 : ∀ x, rho x = 1 → ∀ ij, U ij x = 0) :
    IsSphereTT (radDeriv U) ∧
      ∀ x, rho x = 1 → ∀ ij k, partialDeriv k (U ij) x = x k * radDeriv U ij x := by
  have hd : ∀ ij, Differentiable ℝ (U ij) := fun ij => (hU ij).differentiable (by norm_num)
  have hc1 : ∀ ij k, ContDiff ℝ 1 (partialDeriv k (U ij)) := fun ij k =>
    (hU ij).partialDeriv (m := 1) (by norm_num) k
  have hdk : ∀ ij k, Differentiable ℝ (partialDeriv k (U ij)) := fun ij k =>
    (hc1 ij k).differentiable one_ne_zero
  -- the normal gradient
  have hnorm : ∀ x, rho x = 1 → ∀ ij k, partialDeriv k (U ij) x = x k * radDeriv U ij x := by
    intro x hx ij k
    have h := (tangential_derivs (hU ij) (fun y hy => hU0 y hy ij) hx
      (sum_tanProj_mul x hx k)).1
    simp only [tanProj, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_assoc, ← Finset.mul_sum] at h
    unfold radDeriv
    linarith
  -- the divergence vanishes with its derivatives on the closed ball
  have hdivC : ∀ i, Continuous (fun y => ∑ j, partialDeriv j (U (i, j)) y) := fun i =>
    continuous_finsetSum _ fun j _ => (hc1 _ _).continuous
  have hdivS : ∀ x, rho x = 1 → ∀ i, ∑ j, partialDeriv j (U (i, j)) x = 0 := fun x hx i =>
    eq_zero_of_ball3 (hdivC i) (fun y hy => hdiv y hy i) hx.le
  have hdiv1 : ∀ x, rho x = 1 → ∀ i m, partialDeriv m (fun y => ∑ j,
    partialDeriv j (U (i, j)) y) x = 0 := by
    intro x hx i m
    have hC : ContDiff ℝ 1 (fun y => ∑ j, partialDeriv j (U (i, j)) y) :=
      ContDiff.sum fun j _ => hc1 _ _
    exact eq_zero_of_ball3 (hC.continuous_partialDeriv m)
      (fun y hy => pd_eq_zero_of_ball3 (fun z hz => hdiv z hz i) hy m) hx.le
  -- tangency: `V x = div U = 0`
  have hVx : ∀ x, rho x = 1 → ∀ i, ∑ j, radDeriv U (i, j) x * x j = 0 := fun x hx i => by
    rw [← hdivS x hx i]
    exact Finset.sum_congr rfl fun j _ => by rw [hnorm x hx]; ring
  refine ⟨fun x hx => ⟨fun i j => ?_, ?_, hVx x hx, fun i => ?_⟩, hnorm⟩
  · -- symmetry
    unfold radDeriv
    refine Finset.sum_congr rfl fun k _ => ?_
    have hC : ContDiff ℝ 1 (fun y => U (i, j) y - U (j, i) y) := (hU _).of_le (by norm_num) |>.sub
      ((hU _).of_le (by norm_num))
    have h0 := eq_zero_of_ball3 (hC.continuous_partialDeriv k)
      (fun y hy => pd_eq_zero_of_ball3 (fun z hz => by rw [hsym z hz i j, sub_self]) hy k) hx.le
    rw [partialDeriv_sub (hd _ _) (hd _ _)] at h0
    rw [sub_eq_zero.1 h0]
  · -- trace
    have hC : ContDiff ℝ 1 (fun y => ∑ i, U (i, i) y) :=
      ContDiff.sum fun i _ => (hU _).of_le (by norm_num)
    have h0 : ∀ k, partialDeriv k (fun y => ∑ i, U (i, i) y) x = 0 := fun k =>
      eq_zero_of_ball3 (hC.continuous_partialDeriv k)
        (fun y hy => pd_eq_zero_of_ball3 (fun z hz => htr z hz) hy k) hx.le
    simp only [radDeriv]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.mul_sum, ← partialDeriv_sum Finset.univ (fun i _ => hd _ x) k, h0 k, mul_zero]
  · -- tangential divergence
    have hV : ∀ j k, partialDeriv k (radDeriv U (i, j)) x =
        partialDeriv k (U (i, j)) x + ∑ m, x m * partialDeriv k
          (partialDeriv m (U (i, j))) x := fun j k =>
      pd_radDeriv (hU _) k x
    simp only [hV]
    -- the Hessian identity `H[x, x] = -2 V`
    have hH : ∀ j, ∑ k, ∑ m, x k * x m * partialDeriv m (partialDeriv k (U (i, j))) x =
      -2 * radDeriv U (i, j) x := by
      intro j
      refine hess_eq_of_tangential x hx (fun a b => partialDeriv a (partialDeriv b (U (i, j))) x)
        _ (fun k => ?_)
        (hlap x hx (i, j))
      have h := (tangential_derivs (hU (i, j)) (fun y hy => hU0 y hy (i, j)) hx
        (sum_tanProj_mul x hx k)).2
      rw [h]
      rfl
    have hcomm : ∀ j k m, partialDeriv k (partialDeriv m (U (i, j))) x =
      partialDeriv m (partialDeriv k (U (i, j))) x := fun j k m =>
      partialDeriv_comm (hU _) k m x
    -- expand
    have e1 : ∑ j, ∑ k, ((if j = k then 1 else 0) - x j * x k) *
        (partialDeriv k (U (i, j)) x + ∑ m, x m * partialDeriv k (partialDeriv m (U (i, j))) x) =
        (∑ j, partialDeriv j (U (i, j)) x + ∑ m, x m *
          partialDeriv m (fun y => ∑ j, partialDeriv j (U (i, j)) y) x) -
          ∑ j, x j * (∑ k, x k * partialDeriv k (U (i, j)) x +
            ∑ k, ∑ m, x k * x m * partialDeriv m (partialDeriv k (U (i, j))) x) := by
      rw [show (∑ m, x m * partialDeriv m (fun y => ∑ j, partialDeriv j (U (i, j)) y) x) =
          ∑ m, x m * ∑ j, partialDeriv m (partialDeriv j (U (i, j))) x from
        Finset.sum_congr rfl fun m _ => by rw [partialDeriv_sum Finset.univ
          (fun j _ => hdk _ _ x) m]]
      simp only [Fin.sum_univ_three, Fin.isValue]
      norm_num
      simp only [hcomm _ _ _]
      ring
    rw [e1]
    simp only [hdivS x hx i, hdiv1 x hx i, mul_zero, Finset.sum_const_zero, add_zero, zero_sub,
      hH]
    have e2 : ∑ j, x j * (radDeriv U (i, j) x + -2 * radDeriv U (i, j) x) =
        -∑ j, radDeriv U (i, j) x * x j := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hVx := hVx x hx i
    simp only [radDeriv] at e2 hVx ⊢
    rw [e2, hVx, neg_zero, neg_zero]

end BoundaryLayer

/-! ### Fields vanishing on `S²` lie in `H̊(curl, B)` -/

section Cutoff

open Feec.Counterexamples.BallSymTSD (rho ball3 continuous_rho isOpen_ball3 isBounded_ball3 chi eta
  contDiff_chi differentiable_chi pd_chi isTest_chi eventually_eta_eq_one abs_mul_deriv_eta_le
  eta_nonneg eta_le_one tendsto_toLp_of_bound rho_nonneg)

theorem isCompact_closedBall3 : IsCompact {x : R3 | rho x ≤ 1} :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_rho continuous_const)
    ((Metric.isBounded_closedBall (x := (0 : R3)) (r := 1)).subset fun x hx => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact Feec.Counterexamples.BallSymTSD.norm_le_one_of_rho_le hx)

theorem exists_bound_closedBall3 {g : R3 → ℝ} (hg : Continuous g) :
    ∃ C, 0 ≤ C ∧ ∀ x, rho x ≤ 1 → |g x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_closedBall3.exists_bound_of_continuousOn hg.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx => (by simpa [Real.norm_eq_abs] using hC x hx :
    |g x| ≤ C).trans (le_max_left _ _)⟩

/-- **A `C¹` function vanishing on `S²` is `O(1 - |x|²)` in the ball** (mean value theorem along
the ray through `x`). -/
theorem exists_abs_le_mul_one_sub_rho {w : R3 → ℝ} (hw : ContDiff ℝ 1 w)
    (hw0 : ∀ x, rho x = 1 → w x = 0) : ∃ L, 0 ≤ L ∧ ∀ x ∈ ball3, |w x| ≤ L * (1 - rho x) := by
  obtain ⟨M0, hM0, hM0b⟩ := exists_bound_closedBall3 hw.continuous
  obtain ⟨M, hM, hMb⟩ := exists_bound_closedBall3 (g := fun y => ∑ k, |partialDeriv k w y|)
    (continuous_finsetSum _ fun k _ => (hw.continuous_partialDeriv k).abs)
  have hpd : ∀ y, rho y ≤ 1 → ∀ k, |partialDeriv k w y| ≤ M := fun y hy k => by
    have h := hMb y hy
    rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at h
    exact (Finset.single_le_sum (f := fun k => |partialDeriv k w y|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)).trans h
  have hd : Differentiable ℝ w := hw.differentiable one_ne_zero
  refine ⟨max (6 * M) (4 / 3 * M0), le_max_of_le_left (by positivity), fun x hx => ?_⟩
  have hx1 : rho x < 1 := hx
  have hρ0 := rho_nonneg x
  by_cases hsmall : rho x ≤ 1 / 4
  · calc |w x| ≤ M0 := hM0b x hx1.le
      _ ≤ 4 / 3 * M0 * (1 - rho x) := by nlinarith
      _ ≤ max (6 * M) (4 / 3 * M0) * (1 - rho x) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  rw [not_le] at hsmall
  set r := Real.sqrt (rho x)
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hr2 : r ^ 2 = rho x := Real.sq_sqrt hρ0
  have hr1 : r < 1 := by nlinarith
  have hrh : 1 / 2 < r := by nlinarith
  set s₀ := r⁻¹
  have hs₀ : 1 < s₀ := by rw [lt_inv_comm₀ one_pos hr]; simpa using hr1
  have hsx : ∀ s, rho (s • x) = s ^ 2 * rho x := fun s => by
    simp only [rho, Pi.smul_apply, smul_eq_mul]; ring
  have hs₀r : s₀ ^ 2 * rho x = 1 := by
    rw [← hr2, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
  have hg0 : w (s₀ • x) = 0 := hw0 _ (by rw [hsx, hs₀r])
  -- mean value theorem for `g(s) = w(s x)` on `[1, s₀]`
  have hgd : ∀ s, HasDerivAt (fun s => w (s • x)) (∑ k, x k * partialDeriv k w (s • x)) s :=
    fun s => hasDerivAt_comp_curve hd (γ := fun s => s • x) fun k => by
      simpa using (hasDerivAt_id s).mul_const (x k)
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope (fun s => w (s • x))
    (fun s => ∑ k, x k * partialDeriv k w (s • x)) hs₀
    (fun s _ => (hgd s).continuousAt.continuousWithinAt) (fun s _ => hgd s)
  have hcρ : rho (c • x) ≤ 1 := by
    rw [hsx]
    have : c ^ 2 ≤ s₀ ^ 2 := by nlinarith [hc.1, hc.2]
    calc c ^ 2 * rho x ≤ s₀ ^ 2 * rho x := by gcongr
      _ = 1 := hs₀r
  have hxk : ∀ k, |x k| ≤ 1 := Feec.Counterexamples.BallSymTSD.abs_le_one_of_rho_le hx1.le
  have hder : |∑ k, x k * partialDeriv k w (c • x)| ≤ 3 * M := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |x k * partialDeriv k w (c • x)| ≤ ∑ _k : Fin 3, M := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          exact (mul_le_mul (hxk k) (hpd _ hcρ k) (abs_nonneg _) zero_le_one).trans (by simp)
      _ = 3 * M := by simp
  simp only [one_smul, hg0] at hcs
  have hw1 : |w x| = |∑ k, x k * partialDeriv k w (c • x)| * (s₀ - 1) := by
    rw [hcs, abs_div, zero_sub, abs_neg, abs_of_pos (by linarith : 0 < s₀ - 1)]
    field_simp
  have hs1 : s₀ - 1 ≤ 2 * (1 - rho x) := by
    have e : s₀ - 1 = (1 - r) / r := by simp only [s₀]; field_simp
    rw [e, div_le_iff₀ hr, ← hr2]
    nlinarith
  calc |w x| = |∑ k, x k * partialDeriv k w (c • x)| * (s₀ - 1) := hw1
    _ ≤ 3 * M * (2 * (1 - rho x)) := by
        gcongr
    _ = 6 * M * (1 - rho x) := by ring
    _ ≤ max (6 * M) (4 / 3 * M0) * (1 - rho x) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)

/-- Componentwise `L²` convergence of `toL2F`. -/
theorem tendsto_toL2F_of_forall {ι : Type*} [Fintype ι] {Ω : Set R3} {F : ℕ → ι → R3 → ℝ}
    {f : ι → R3 → ℝ} (hF : ∀ n i, MemLp (F n i) 2 (volume.restrict Ω))
    (hf : ∀ i, MemLp (f i) 2 (volume.restrict Ω))
    (h : ∀ i, Tendsto (fun n => (hF n i).toLp (F n i)) atTop (𝓝 ((hf i).toLp (f i)))) :
    Tendsto (fun n => toL2F (hF n)) atTop (𝓝 (toL2F hf)) :=
  ((PiLp.continuous_toLp 2 _).tendsto _).comp (tendsto_pi_nhds.2 h)

/-- **A `C¹` field vanishing on `S²` lies in `H̊(curl, B)`**: the cut-offs `χₙ W` are compactly
supported in `B`, hence in `D(curl_min)`, and converge to `W` in the graph norm because
`|∇χₙ| |W| ≲ |ηₙ'(|x|²)| (1 - |x|²)` stays bounded (`exists_abs_le_mul_one_sub_rho`). -/
theorem smoothField_mem_minimal_of_eq_zero_sphere {W : Ix → R3 → ℝ} (hW : ∀ ij, ContDiff ℝ 1 (W ij))
    (hW0 : ∀ x, rho x = 1 → ∀ ij, W ij x = 0) :
    smoothField isOpen_ball3 isBounded_ball3 W (fun ij => (hW ij).continuous) ∈
      ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal ball3).domain := by
  have hΩm := isOpen_ball3.measurableSet
  set Wn : ℕ → Ix → R3 → ℝ := fun n ij x => chi n x * W ij x
  have hWn : ∀ n ij, ContDiff ℝ 1 (Wn n ij) := fun n ij =>
    ((contDiff_chi n).of_le (by simp)).mul (hW ij)
  have hm : ∀ n ij, MemLp (Wn n ij) 2 (volume.restrict ball3) := fun n ij =>
    memLp_of_continuous hΩm isBounded_ball3 (hWn n ij).continuous
  have hcm : ∀ n ij, MemLp ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).apply (Wn n) ij) 2
      (volume.restrict ball3) := fun n ij => by
    rw [← curlM_eq_apply]
    exact memLp_of_continuous hΩm isBounded_ball3 (continuous_curlM (hWn n) ij)
  have hmW : ∀ ij, MemLp (W ij) 2 (volume.restrict ball3) := fun ij =>
    memLp_of_continuous hΩm isBounded_ball3 (hW ij).continuous
  have hcW : ∀ ij, MemLp ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).apply W ij) 2
      (volume.restrict ball3) := fun ij => by
    rw [← curlM_eq_apply]
    exact memLp_of_continuous hΩm isBounded_ball3 (continuous_curlM hW ij)
  -- each cut-off lies in the graph of `curl_min`
  have hgraph : ∀ n, (toL2F (hm n), toL2F (hcm n)) ∈
      ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal ball3).graph := by
    intro n
    obtain ⟨hmax, hval⟩ := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).smooth_mem_maximal_domain
      isOpen_ball3 curlOp_isOrderLE (hWn n) (hm n) (hcm n)
    obtain ⟨hmin, hval'⟩ :=
      (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).mem_minimal_of_maximal_of_support_subset
      isOpen_ball3 (isTest_chi n).hasCompactSupport (isTest_chi n).tsupport_subset ⟨_, hmax⟩
      (fun ij => by
        filter_upwards [(hm n ij).coeFn_toLp] with x hx hxK
        rw [show (toL2F (hm n) ij : R3 → ℝ) = (hm n ij).toLp (Wn n ij) from rfl, hx]
        simp only [Wn, image_eq_zero_of_notMem_tsupport hxK, zero_mul])
    have := LinearPMap.mem_graph _ ⟨_, hmin⟩
    rwa [hval', hval] at this
  -- convergence in the graph norm
  obtain ⟨D, hD⟩ := exists_abs_dχ_le
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hL : ∀ ij, ∃ L, 0 ≤ L ∧ ∀ x ∈ ball3, |W ij x| ≤ L * (1 - rho x) := fun ij =>
    exists_abs_le_mul_one_sub_rho (hW ij) (fun x hx => hW0 x hx ij)
  choose L hL0 hLb using hL
  have hlim1 : Tendsto (fun n => toL2F (hm n)) atTop (𝓝 (toL2F hmW)) := by
    refine tendsto_toL2F_of_forall _ _ fun ij => ?_
    obtain ⟨C, -, hC⟩ := exists_bound_closedBall3 (hW ij).continuous
    refine tendsto_toLp_of_bound hΩm isBounded_ball3.measure_lt_top.ne _ _ (C := C)
      (fun n x hx => ?_) (fun x hx => ?_)
    · have h1 : |chi n x - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> simp only [chi] <;>
          linarith [eta_nonneg n (rho x), eta_le_one n (rho x)]
      rw [show Wn n ij x - W ij x = (chi n x - 1) * W ij x by simp only [Wn]; ring, abs_mul]
      simpa using mul_le_mul h1 (hC x (le_of_lt hx)) (abs_nonneg _) zero_le_one
    · refine tendsto_const_nhds.congr' ((eventually_eta_eq_one hx).mono fun n hn => ?_)
      simp only [Wn, chi, hn.1, one_mul]
  have hlim2 : Tendsto (fun n => toL2F (hcm n)) atTop (𝓝 (toL2F hcW)) := by
    refine tendsto_toL2F_of_forall _ _ fun ij => ?_
    obtain ⟨i, k⟩ := ij
    obtain ⟨C, -, hC⟩ := exists_bound_closedBall3 (continuous_curlM hW (i, k))
    have hpdW : ∀ n ij a x, partialDeriv a (Wn n ij) x = chi n x * partialDeriv a (W ij) x +
        W ij x * (deriv (eta n) (rho x) * (2 * x a)) := fun n ij a x => by
      simp only [Wn]
      rw [partialDeriv_mul (differentiable_chi n x) ((hW ij).differentiable one_ne_zero x), pd_chi]
      ring
    have hform : ∀ n x, (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).apply (Wn n) (i, k) x -
        (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).apply W (i, k) x =
        (chi n x - 1) * curlM W (i, k) x +
          (W (i, k + 2) x * (deriv (eta n) (rho x) * (2 * x (k + 1))) -
            W (i, k + 1) x * (deriv (eta n) (rho x) * (2 * x (k + 2)))) := fun n x => by
      rw [← curlM_eq_apply, ← curlM_eq_apply]
      simp only [curlM, hpdW]
      ring
    refine tendsto_toLp_of_bound hΩm isBounded_ball3.measure_lt_top.ne _ _
      (C := C + 8 * D * (L (i, k + 2) + L (i, k + 1))) (fun n x hx => ?_) (fun x hx => ?_)
    · rw [hform]
      have hx1 : rho x ≤ 1 := le_of_lt hx
      have hxa := Feec.Counterexamples.BallSymTSD.abs_le_one_of_rho_le hx1
      have hη := abs_mul_deriv_eta_le hD n (rho x)
      have hb : ∀ ij a, |W ij x * (deriv (eta n) (rho x) * (2 * x a))| ≤ 4 * D * L ij := by
        intro ij a
        have hW1 := hLb ij x hx
        calc |W ij x * (deriv (eta n) (rho x) * (2 * x a))|
            = |W ij x| * |deriv (eta n) (rho x)| * (2 * |x a|) := by
              rw [abs_mul, abs_mul, abs_mul, abs_two]; ring
          _ ≤ L ij * (1 - rho x) * |deriv (eta n) (rho x)| * (2 * 1) := by
              have : 0 ≤ L ij * (1 - rho x) * |deriv (eta n) (rho x)| :=
                mul_nonneg (mul_nonneg (hL0 ij) (by linarith)) (abs_nonneg _)
              gcongr
              exact hxa a
          _ = 2 * L ij * |(1 - rho x) * deriv (eta n) (rho x)| := by
              rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - rho x)]; ring
          _ ≤ 2 * L ij * (2 * D) := by gcongr; linarith [hL0 ij]
          _ = 4 * D * L ij := by ring
      have hc1 : |(chi n x - 1) * curlM W (i, k) x| ≤ C := by
        have h1 : |chi n x - 1| ≤ 1 := by
          rw [abs_le]; constructor <;> simp only [chi] <;>
            linarith [eta_nonneg n (rho x), eta_le_one n (rho x)]
        rw [abs_mul]
        simpa using mul_le_mul h1 (hC x hx1) (abs_nonneg _) zero_le_one
      refine ((abs_add_le _ _).trans (add_le_add hc1 ((abs_sub _ _).trans
        (add_le_add (hb _ _) (hb _ _))))).trans ?_
      nlinarith [hL0 (i, k + 2), hL0 (i, k + 1)]
    · refine tendsto_const_nhds.congr' ((eventually_eta_eq_one hx).mono fun n hn => ?_)
      have h := hform n x
      simp only [chi, hn.1, hn.2, sub_self, zero_mul, mul_zero, zero_add] at h
      linarith
  have hcl := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isClosed_minimal isOpen_ball3
  have hmem : (toL2F hmW, toL2F hcW) ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal ball3).graph :=
    hcl.mem_of_tendsto (hlim1.prodMk_nhds hlim2) (Eventually.of_forall hgraph)
  exact LinearPMap.mem_domain_of_mem_graph hmem

end Cutoff

/-! ### Polar coordinates -/

section Surface

section Polar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Polar coordinates**: `∫_E g = ∫_{S} ∫_{(0, ∞)} g(r u) r^{d-1} dr dσ(u)`, with
`σ = μ.toSphere`. -/
theorem integral_eq_integral_sphere {g : E → ℝ} (hg : Integrable g μ) :
    ∫ x, g x ∂μ = ∫ u : Metric.sphere (0 : E) 1, ∫ r : Ioi (0 : ℝ), g (r.1 • u.1)
      ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) ∂μ.toSphere := by
  have hmp := μ.measurePreserving_homeomorphUnitSphereProd
  have e1 : ∫ x, g x ∂μ = ∫ x : ({(0 : E)}ᶜ : Set E), g x.1 ∂(μ.comap (↑)) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl g, restrict_compl_singleton]
  have e2 : ∫ x : ({(0 : E)}ᶜ : Set E), g x.1 ∂(μ.comap (↑)) =
      ∫ p, g (p.2.1 • p.1.1)
        ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
    rw [← hmp.integral_comp (Homeomorph.measurableEmbedding _)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    congr 1
    have := (homeomorphUnitSphereProd E).symm_apply_apply x
    rw [← congrArg Subtype.val this, homeomorphUnitSphereProd_symm_apply_coe]
  have hint : Integrable (fun p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) => g (p.2.1 • p.1.1))
      (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
    have h1 : Integrable (g ∘ (↑) : ({(0 : E)}ᶜ : Set E) → ℝ) (μ.comap (↑)) :=
      (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).1 hg.integrableOn
    have h2 := (hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)
      (g := fun p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) => g (p.2.1 • p.1.1))).1
    refine h2 (h1.congr (Eventually.of_forall fun x => ?_))
    simp only [Function.comp_apply]
    congr 1
    have := (homeomorphUnitSphereProd E).symm_apply_apply x
    rw [← congrArg Subtype.val this, homeomorphUnitSphereProd_symm_apply_coe]
  rw [e1, e2, integral_prod _ hint]

/-- The radial measure `r^n dr` on `(0, ∞)`. -/
theorem integral_volumeIoiPow (n : ℕ) (f : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), f r.1 ∂(Measure.volumeIoiPow n) = ∫ r in Ioi (0 : ℝ), r ^ n * f r := by
  simp only [Measure.volumeIoiPow]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (Eventually.of_forall fun _ =>
      ENNReal.ofReal_lt_top),
    integral_subtype_comap measurableSet_Ioi (fun r => (ENNReal.ofReal (r ^ n)).toReal • f r)]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hr) _)]

end Polar

/-! ### The radial kernel of the cut-offs -/

section Kernel

open Feec.Counterexamples.BallSymTSD (eta deriv_eta differentiable_eta differentiable_deriv_eta
  eta_eq_one eta_eq_zero deriv_eta_eq_zero two_le_mul)

/-- `κₙ(r) = -d/dr ηₙ(r²) = -2 r ηₙ'(r²)`: a nonnegative kernel of mass one concentrating at
`r = 1`. -/
def kap (n : ℕ) (r : ℝ) : ℝ := -(2 * r * deriv (eta n) (r ^ 2))

theorem hasDerivAt_neg_eta_sq (n : ℕ) (r : ℝ) :
    HasDerivAt (fun r => -eta n (r ^ 2)) (kap n r) r := by
  have h := ((differentiable_eta n) (r ^ 2)).hasDerivAt.comp r (hasDerivAt_pow 2 r)
  refine h.neg.congr_deriv ?_
  simp only [kap, Nat.cast_ofNat]
  ring

theorem continuous_kap (n : ℕ) : Continuous (kap n) := by
  unfold kap
  have := (differentiable_deriv_eta n).continuous
  fun_prop

theorem deriv_eta_nonpos (n : ℕ) (s : ℝ) : deriv (eta n) s ≤ 0 := by
  rw [deriv_eta]
  have := dχ_nonneg (((n : ℝ) + 2) * (1 - s) - 1)
  have := two_le_mul n
  nlinarith

theorem kap_nonneg (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ kap n r := by
  unfold kap
  have := deriv_eta_nonpos n (r ^ 2)
  nlinarith

theorem kap_eq_zero_of_one_le (n : ℕ) {r : ℝ} (hr : 1 ≤ r) : kap n r = 0 := by
  unfold kap
  rw [deriv_eta, dχ_eq_zero_of_nonpos]
  · ring
  · have := two_le_mul n
    have : 1 ≤ r ^ 2 := by nlinarith
    nlinarith

theorem kap_eq_zero_of_le (n : ℕ) {r : ℝ} (h : 2 ≤ ((n : ℝ) + 2) * (1 - r ^ 2)) : kap n r = 0 := by
  unfold kap
  rw [deriv_eta_eq_zero h]
  ring

theorem integral_kap (n : ℕ) : ∫ r in (0 : ℝ)..1, kap n r = 1 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hasDerivAt_neg_eta_sq n r)
    ((continuous_kap n).intervalIntegrable 0 1)]
  have h0 : eta n ((0 : ℝ) ^ 2) = 1 := eta_eq_one (by simp)
  have h1 : eta n ((1 : ℝ) ^ 2) = 0 := eta_eq_zero (by simp)
  simp only [h0, h1]
  norm_num

theorem setIntegral_Ioi_kap_mul (n : ℕ) (h : ℝ → ℝ) :
    ∫ r in Ioi (0 : ℝ), kap n r * h r = ∫ r in (0 : ℝ)..1, kap n r * h r := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    fun r hr => ?_
  have : 1 ≤ r := by
    by_contra hlt
    exact hr.2 ⟨hr.1, le_of_lt (not_le.1 hlt)⟩
  rw [kap_eq_zero_of_one_le n this, zero_mul]

theorem abs_setIntegral_kap_mul_le (n : ℕ) {h : ℝ → ℝ} {C : ℝ}
    (hC : ∀ r ∈ Icc (0 : ℝ) 1, |h r| ≤ C) :
    |∫ r in Ioi (0 : ℝ), kap n r * h r| ≤ C := by
  rw [setIntegral_Ioi_kap_mul]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := 1)
    (f := fun r => kap n r * h r) (g := fun r => C * kap n r) zero_le_one
    (Eventually.of_forall fun r hr => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kap_nonneg n hr.1.le), mul_comm]
      exact mul_le_mul_of_nonneg_right (hC r ⟨hr.1.le, hr.2⟩) (kap_nonneg n hr.1.le))
    ((continuous_const.mul (continuous_kap n)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul, integral_kap, mul_one] at hb
  simpa [Real.norm_eq_abs] using hb

/-- **`κₙ` is an approximate identity at `r = 1`**: `∫₀^∞ κₙ h → h(1)`. -/
theorem tendsto_setIntegral_kap_mul {h : ℝ → ℝ} (hh : Continuous h) :
    Tendsto (fun n => ∫ r in Ioi (0 : ℝ), kap n r * h r) atTop (𝓝 (h 1)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδh⟩ := Metric.continuous_iff.1 hh 1 (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, setIntegral_Ioi_kap_mul]
  have e : (∫ r in (0 : ℝ)..1, kap n r * h r) - h 1 =
      ∫ r in (0 : ℝ)..1, kap n r * (h r - h 1) := by
    rw [show (fun r => kap n r * (h r - h 1)) = fun r => kap n r * h r - h 1 * kap n r from
      funext fun r => by ring, intervalIntegral.integral_sub (f := fun r => kap n r * h r)
      (g := fun r => h 1 * kap n r)
      (((continuous_kap n).mul hh).intervalIntegrable 0 1)
      ((continuous_const.mul (continuous_kap n)).intervalIntegrable 0 1),
      intervalIntegral.integral_const_mul, integral_kap, mul_one]
  rw [e]
  have hnδ : 2 / ((n : ℝ) + 2) < δ := by
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : 2 / δ < (n : ℝ) + 2 := by linarith
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at h2
    linarith
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := 1)
    (f := fun r => kap n r * (h r - h 1)) (g := fun r => ε / 2 * kap n r) zero_le_one
    (Eventually.of_forall fun r hr => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kap_nonneg n hr.1.le), mul_comm]
      by_cases hk : kap n r = 0
      · rw [hk, mul_zero, mul_zero]
      refine mul_le_mul_of_nonneg_right ?_ (kap_nonneg n hr.1.le)
      -- on the support of `κₙ`, `1 - r ≤ 1 - r² < 2/(n+2) < δ`
      have hr2 : ((n : ℝ) + 2) * (1 - r ^ 2) < 2 := by
        by_contra hge
        exact hk (kap_eq_zero_of_le n (not_lt.1 hge))
      have h1r : 1 - r < δ := by
        have : 1 - r ^ 2 < 2 / ((n : ℝ) + 2) := by
          rw [lt_div_iff₀ (by positivity)]; linarith
        nlinarith [hr.1, hr.2]
      have := hδh r (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.2])
      rw [Real.dist_eq] at this
      exact this.le)
    ((continuous_const.mul (continuous_kap n)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul, integral_kap, mul_one, Real.norm_eq_abs] at hb
  linarith

end Kernel

/-! ### The surface limit of the cut-off gradients -/

section SurfaceLimit

open Feec.Counterexamples.BallSymTSD (eta rho deriv_eta deriv_eta_eq_zero two_le_mul)

/-- `ℝ³` with the Euclidean norm, where the polar decomposition `Measure.toSphere` lives. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem rho_ofLp (y : E3) : rho (WithLp.ofLp y) = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  simp [rho, Fin.sum_univ_three, sq]

theorem deriv_eta_eq_zero_of_one_le (n : ℕ) {s : ℝ} (hs : 1 ≤ s) : deriv (eta n) s = 0 := by
  rw [deriv_eta, dχ_eq_zero_of_nonpos]
  · ring
  · have := two_le_mul n
    nlinarith

/-- **The cut-off gradients converge to the surface measure**: for continuous `H` on `ℝ³`,
`∫ -2 ηₙ'(|x|²) H(x) dx → ∫_{S²} H dσ` (`σ = volume.toSphere` on `EuclideanSpace ℝ (Fin 3)`). -/
theorem tendsto_integral_deriv_eta_mul {H : R3 → ℝ} (hH : Continuous H) :
    Tendsto (fun n => ∫ x, -2 * deriv (eta n) (rho x) * H x) atTop
      (𝓝 (∫ u : Metric.sphere (0 : E3) 1, H (WithLp.ofLp u.1)
        ∂(volume : Measure E3).toSphere)) := by
  have hdim : Module.finrank ℝ E3 - 1 = 2 := by simp
  set g : ℕ → E3 → ℝ := fun n y => -2 * deriv (eta n) (rho (WithLp.ofLp y)) * H (WithLp.ofLp y)
  have hcont : ∀ n, Continuous (g n) := fun n => by
    have := (Feec.Counterexamples.BallSymTSD.differentiable_deriv_eta n).continuous
    have hr := Feec.Counterexamples.BallSymTSD.continuous_rho
    have ho : Continuous (WithLp.ofLp : E3 → R3) := PiLp.continuous_ofLp 2 _
    exact (continuous_const.mul (this.comp (hr.comp ho))).mul (hH.comp ho)
  have hsupp : ∀ n, HasCompactSupport (g n) := fun n =>
    HasCompactSupport.intro (isCompact_closedBall (0 : E3) 1) fun y hy => by
      have : 1 ≤ ‖y‖ ^ 2 := by
        have := not_le.1 (fun h => hy (Metric.mem_closedBall.2 (by simpa using h)))
        nlinarith
      simp only [g, rho_ofLp, deriv_eta_eq_zero_of_one_le n this, mul_zero, zero_mul]
  have hint : ∀ n, Integrable (g n) := fun n => (hcont n).integrable_of_hasCompactSupport (hsupp n)
  -- transfer to `EuclideanSpace` and polar coordinates
  have e1 : ∀ n, ∫ x, -2 * deriv (eta n) (rho x) * H x = ∫ y, g n y := fun n =>
    ((PiLp.volume_preserving_ofLp (Fin 3)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding _).symm
  set J : ℕ → Metric.sphere (0 : E3) 1 → ℝ := fun n u =>
    ∫ r in Ioi (0 : ℝ), kap n r * (r * H (WithLp.ofLp (r • u.1)))
  have e2 : ∀ n, ∫ y, g n y = ∫ u, J n u ∂(volume : Measure E3).toSphere := fun n => by
    rw [integral_eq_integral_sphere _ (hint n)]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hdim]
    rw [integral_volumeIoiPow 2 (fun r => g n (r • u.1))]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hu : ‖u.1‖ = 1 := by simp
    have hn : rho (WithLp.ofLp (r • u.1)) = r ^ 2 := by
      rw [rho_ofLp, norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
    simp only [g, kap, hn]
    ring
  have hmeas : ∀ n, AEStronglyMeasurable (J n) (volume : Measure E3).toSphere := fun n => by
    have hmp := (volume : Measure E3).measurePreserving_homeomorphUnitSphereProd
    have h1 : Integrable (g n ∘ (↑) : ({(0 : E3)}ᶜ : Set E3) → ℝ)
        ((volume : Measure E3).comap (Subtype.val : ({(0 : E3)}ᶜ : Set E3) → E3)) :=
      (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).1 (hint n).integrableOn
    have h2 := (hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)
      (g := fun p : Metric.sphere (0 : E3) 1 × Ioi (0 : ℝ) => g n (p.2.1 • p.1.1))).1
      (h1.congr (Eventually.of_forall fun x => by
        simp only [Function.comp_apply]
        congr 1
        have := (homeomorphUnitSphereProd E3).symm_apply_apply x
        rw [← congrArg Subtype.val this, homeomorphUnitSphereProd_symm_apply_coe]))
    refine h2.integral_prod_left.aestronglyMeasurable.congr (Eventually.of_forall fun u => ?_)
    simp only [hdim]
    rw [integral_volumeIoiPow 2 (fun r => g n (r • u.1))]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hu : ‖u.1‖ = 1 := by simp
    have hn : rho (WithLp.ofLp (r • u.1)) = r ^ 2 := by
      rw [rho_ofLp, norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
    simp only [g, kap, hn]
    ring
  -- dominated convergence on the sphere
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E3) 1).exists_bound_of_continuousOn
    (f := fun y => H (WithLp.ofLp y)) (hH.comp (PiLp.continuous_ofLp 2 _)).continuousOn
  have hhu : ∀ u : Metric.sphere (0 : E3) 1,
      Continuous fun r : ℝ => r * H (WithLp.ofLp (r • u.1)) :=
    fun u => continuous_id.mul (hH.comp ((PiLp.continuous_ofLp 2 _).comp
      (continuous_id.smul continuous_const)))
  simp only [e1, e2]
  refine tendsto_integral_of_dominated_convergence (fun _ => C) hmeas (integrable_const C)
    (fun n => Eventually.of_forall fun u => ?_) (Eventually.of_forall fun u => ?_)
  · rw [Real.norm_eq_abs]
    refine abs_setIntegral_kap_mul_le n fun r hr => ?_
    have hu : ‖u.1‖ = 1 := by simp
    have h := hC (r • u.1) (by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hu, mul_one, Real.norm_eq_abs,
        abs_of_nonneg hr.1]
      exact hr.2)
    rw [abs_mul, abs_of_nonneg hr.1]
    rw [Real.norm_eq_abs] at h
    calc r * |H (WithLp.ofLp (r • u.1))| ≤ 1 * C := mul_le_mul hr.2 h (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  · have := tendsto_setIntegral_kap_mul (hhu u)
    simp only [one_mul, one_smul] at this
    exact this

end SurfaceLimit

end Surface

/-! ### The tangential trace from Green's formula -/

section TangentialTrace

open Feec.Counterexamples.BallSymTSD (rho ball3 isOpen_ball3 isBounded_ball3 chi eta isTest_chi
  pd_chi tendsto_chi eta_nonneg eta_le_one integrable_ball3 continuous_rho)

section Trace

variable {U ψ : Ix → R3 → ℝ}

/-- The rows of `x × U`: `(x × Uᵢ)ₖ = x_{k+1} U_{i,k+2} - x_{k+2} U_{i,k+1}`. -/
def crossF (U : Ix → R3 → ℝ) (ik : Ix) (x : R3) : ℝ :=
  x (ik.2 + 1) * U (ik.1, ik.2 + 2) x - x (ik.2 + 2) * U (ik.1, ik.2 + 1) x

/-- The flux `G = Σᵢ Uᵢ × ψᵢ`, whose divergence is `Σ (curl U : ψ - U : curl ψ)`. -/
def fluxG (U ψ : Ix → R3 → ℝ) (m : Fin 3) (x : R3) : ℝ :=
  ∑ i, (U (i, m + 1) x * ψ (i, m + 2) x - U (i, m + 2) x * ψ (i, m + 1) x)

theorem contDiff_fluxG (hU : ∀ ij, ContDiff ℝ 1 (U ij)) (hψ : ∀ ij, ContDiff ℝ 1 (ψ ij))
    (m : Fin 3) : ContDiff ℝ 1 (fluxG U ψ m) :=
  ContDiff.sum fun _ _ => ((hU _).mul (hψ _)).sub ((hU _).mul (hψ _))

/-- `div (Σᵢ Uᵢ × ψᵢ) = Σ (curl U : ψ - U : curl ψ)`. -/
theorem sum_pd_fluxG (hU : ∀ ij, Differentiable ℝ (U ij)) (hψ : ∀ ij, Differentiable ℝ (ψ ij))
    (x : R3) : ∑ m, partialDeriv m (fluxG U ψ m) x =
      ∑ ij, (curlM U ij x * ψ ij x - U ij x * curlM ψ ij x) := by
  have hprod : ∀ a b, Differentiable ℝ (fun y => U a y * ψ b y) := fun a b => (hU a).mul (hψ b)
  have e : ∀ m, partialDeriv m (fluxG U ψ m) x = ∑ i,
    ((U (i, m + 1) x * partialDeriv m (ψ (i, m + 2)) x +
      ψ (i, m + 2) x * partialDeriv m (U (i, m + 1)) x) -
        (U (i, m + 2) x * partialDeriv m (ψ (i, m + 1)) x +
      ψ (i, m + 1) x * partialDeriv m (U (i, m + 2)) x)) := fun m => by
    unfold fluxG
    rw [partialDeriv_sum
      (f := fun i y => U (i, m + 1) y * ψ (i, m + 2) y - U (i, m + 2) y * ψ (i, m + 1) y)
      Finset.univ (fun i _ => ((hprod _ _).sub (hprod _ _)) x) m]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [partialDeriv_sub (hprod _ _ x) (hprod _ _ x), partialDeriv_mul ((hU _) x) ((hψ _) x),
      partialDeriv_mul ((hU _) x) ((hψ _) x)]
    ring
  simp only [e, curlM, Fintype.sum_prod_type, Fin.sum_univ_three]
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  ring

/-- `x · G = Σᵢₖ ψᵢₖ (x × Uᵢ)ₖ`. -/
theorem sum_mul_fluxG (x : R3) :
    ∑ m, x m * fluxG U ψ m x = ∑ ik, ψ ik x * crossF U ik x := by
  simp only [fluxG, crossF, Fintype.sum_prod_type, Fin.sum_univ_three]
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  ring

/-- **Green's formula on the ball as a surface integral**: if `∫_B div G = 0`, then the flux
`∫_{S²} x · G dσ` vanishes. -/
theorem integral_sphere_eq_zero_of_integral_div {G : Fin 3 → R3 → ℝ}
    (hG : ∀ m, ContDiff ℝ 1 (G m)) (h0 : ∫ x in ball3, ∑ m, partialDeriv m (G m) x = 0) :
    ∫ u : Metric.sphere (0 : E3) 1, ∑ m, (WithLp.ofLp u.1) m * G m (WithLp.ofLp u.1)
      ∂(volume : Measure E3).toSphere = 0 := by
  set D : R3 → ℝ := fun x => ∑ m, partialDeriv m (G m) x
  have hD : Continuous D := continuous_finsetSum _ fun m _ => (hG m).continuous_partialDeriv m
  set H : R3 → ℝ := fun x => ∑ m, x m * G m x
  have hH : Continuous H := continuous_finsetSum _ fun m _ =>
    (continuous_apply m).mul (hG m).continuous
  -- `∫_B χₙ div G → ∫_B div G`
  have hlim1 : Tendsto (fun n => ∫ x in ball3, chi n x * D x) atTop (𝓝 (∫ x in ball3, D x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |D x|)
      (fun n => ((Feec.Counterexamples.BallSymTSD.contDiff_chi n).continuous.mul
        hD).aestronglyMeasurable) (integrable_ball3 hD.abs)
      (fun n => Eventually.of_forall fun x => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul]
      have h1 := eta_nonneg n (rho x)
      have h2 := eta_le_one n (rho x)
      rw [abs_of_nonneg (show 0 ≤ chi n x from h1)]
      exact mul_le_of_le_one_left (abs_nonneg _) h2
    · filter_upwards [ae_restrict_mem isOpen_ball3.measurableSet] with x hx
      simpa using (tendsto_chi hx).mul_const (D x)
  -- `∫_B χₙ div G = ∫ -2 ηₙ'(|x|²) x · G`
  have e : ∀ n, ∫ x in ball3, chi n x * D x = ∫ x, -2 * deriv (eta n) (rho x) * H x := by
    intro n
    have hT := isTest_chi n
    have hint : ∀ m, Integrable (fun x => chi n x * partialDeriv m (G m) x)
      (volume.restrict ball3) :=
      fun m => integrable_ball3 (hT.continuous.mul ((hG m).continuous_partialDeriv m))
    have hint' : ∀ m, Integrable (fun x => partialDeriv m (chi n) x * G m x)
      (volume.restrict ball3) :=
      fun m => integrable_ball3 (((hT.contDiff.of_le (by simp)).continuous_partialDeriv m).mul
        (hG m).continuous)
    calc ∫ x in ball3, chi n x * D x = ∑ m, ∫ x in ball3, chi n x * partialDeriv m (G m) x := by
          rw [← integral_finsetSum _ fun m _ => hint m]
          exact integral_congr_ae (Eventually.of_forall fun x => by simp [D, Finset.mul_sum])
      _ = ∑ m, -∫ x in ball3, partialDeriv m (chi n) x * G m x := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [integral_pd_mul hT (hG m) m, neg_neg]
      _ = ∫ x in ball3, -2 * deriv (eta n) (rho x) * H x := by
          simp only [← integral_neg]
          rw [← integral_finsetSum (f := fun m x => -(partialDeriv m (chi n) x * G m x)) _
            fun m _ => (hint' m).neg]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [pd_chi, H, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          ring
      _ = ∫ x, -2 * deriv (eta n) (rho x) * H x := by
          refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
          have : 1 ≤ rho x := not_lt.1 hx
          rw [deriv_eta_eq_zero_of_one_le n this, mul_zero, zero_mul]
  have hlim2 := tendsto_integral_deriv_eta_mul hH
  simp only [← e] at hlim2
  rw [← tendsto_nhds_unique hlim1 hlim2, h0]

/-- **The tangential trace of an `H̊(curl)` field vanishes pointwise**: if the `C¹` field `U`
satisfies Green's formula `Σ ∫_B curl U : ψ = Σ ∫_B U : curl ψ` against every `ψ ∈ C_c^∞(ℝ³)`
(no boundary condition on `ψ`), then `x × Uᵢ(x) = 0` on `S²`. -/
theorem crossF_eq_zero_of_green (hU : ∀ ij, ContDiff ℝ 1 (U ij))
    (hG : ∀ ψ : Ix → R3 → ℝ, IsTestField (univ : Set R3) ψ →
      ∑ ij, ∫ x in ball3, curlM U ij x * ψ ij x = ∑ ij, ∫ x in ball3, U ij x * curlM ψ ij x)
    {x₀ : R3} (hx₀ : rho x₀ = 1) (ik : Ix) : crossF U ik x₀ = 0 := by
  -- the surface identity
  have hsurf : ∀ ψ : Ix → R3 → ℝ, IsTestField (univ : Set R3) ψ →
      ∫ u : Metric.sphere (0 : E3) 1, ∑ jl, ψ jl (WithLp.ofLp u.1) * crossF U jl (WithLp.ofLp u.1)
        ∂(volume : Measure E3).toSphere = 0 := by
    intro ψ hψ
    have hψ1 : ∀ ij, ContDiff ℝ 1 (ψ ij) := fun ij => (hψ ij).contDiff.of_le (by simp)
    have h0 : ∫ x in ball3, ∑ m, partialDeriv m (fluxG U ψ m) x = 0 := by
      have hc : ∀ ij, Integrable (fun x => curlM U ij x * ψ ij x) (volume.restrict ball3) :=
        fun ij => integrable_ball3 ((continuous_curlM hU ij).mul (hψ ij).continuous)
      have hd : ∀ ij, Integrable (fun x => U ij x * curlM ψ ij x) (volume.restrict ball3) :=
        fun ij => integrable_ball3 ((hU ij).continuous.mul (continuous_curlM hψ1 ij))
      rw [integral_congr_ae (Eventually.of_forall fun x => sum_pd_fluxG
          (fun ij => (hU ij).differentiable one_ne_zero)
          (fun ij => (hψ1 ij).differentiable one_ne_zero) x),
        integral_finsetSum (f := fun ij x => curlM U ij x * ψ ij x - U ij x * curlM ψ ij x) _
          fun ij _ => (hc ij).sub (hd ij)]
      simp only [integral_sub (hc _) (hd _), Finset.sum_sub_distrib, hG ψ hψ, sub_self]
    have := integral_sphere_eq_zero_of_integral_div (contDiff_fluxG hU hψ1) h0
    simpa only [sum_mul_fluxG] using this
  -- localize with a bump
  by_contra hne
  set c : Ix → ℝ := fun jl => crossF U jl x₀
  set f : R3 → ℝ := fun x => ∑ jl, c jl * crossF U jl x
  have hfc : Continuous f := continuous_finsetSum _ fun jl _ => continuous_const.mul
    (((continuous_apply _).mul (hU _).continuous).sub ((continuous_apply _).mul (hU _).continuous))
  have hf0 : 0 < f x₀ := by
    have : 0 < c ik * c ik := mul_self_pos.2 hne
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun jl => c jl * c jl)
      (fun jl _ => mul_self_nonneg _) (Finset.mem_univ ik))
  obtain ⟨δ, hδ, hδf⟩ := Metric.isOpen_iff.1 (isOpen_lt continuous_const hfc) x₀ hf0
  let ζ : ContDiffBump x₀ := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  set ψ : Ix → R3 → ℝ := fun jl x => ζ x * c jl
  have hψ : IsTestField (univ : Set R3) ψ := fun jl =>
    ⟨ζ.contDiff.mul contDiff_const, ζ.hasCompactSupport.mul_right, subset_univ _⟩
  have hkey : ∀ x, ∑ jl, ψ jl x * crossF U jl x = ζ x * f x := fun x => by
    simp only [ψ, f, Finset.mul_sum]
    exact Finset.sum_congr rfl fun jl _ => by ring
  have hpos : 0 < ∫ u : Metric.sphere (0 : E3) 1, ∑ jl, ψ jl (WithLp.ofLp u.1) *
      crossF U jl (WithLp.ofLp u.1) ∂(volume : Measure E3).toSphere := by
    simp only [hkey]
    have hcont : Continuous fun u : Metric.sphere (0 : E3) 1 =>
        ζ (WithLp.ofLp u.1) * f (WithLp.ofLp u.1) :=
      (ζ.continuous.mul hfc).comp ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val)
    have hu₀ : WithLp.toLp 2 x₀ ∈ Metric.sphere (0 : E3) 1 := by
      have h := rho_ofLp (WithLp.toLp 2 x₀)
      simp only [hx₀] at h
      rw [mem_sphere_zero_iff_norm]
      nlinarith [norm_nonneg (WithLp.toLp 2 x₀ : E3)]
    refine hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun u => ?_) (x := ⟨_, hu₀⟩) ?_
    · show 0 ≤ ζ (WithLp.ofLp u.1) * f (WithLp.ofLp u.1)
      by_cases hz : ζ (WithLp.ofLp u.1) = 0
      · rw [hz, zero_mul]
      · refine mul_nonneg ζ.nonneg (le_of_lt (hδf ?_))
        have : WithLp.ofLp u.1 ∈ Function.support ζ := hz
        rwa [ζ.support_eq] at this
    · simp only [ζ.one_of_mem_closedBall (Metric.mem_closedBall_self
        (half_pos hδ).le), one_mul]
      exact hf0.ne'
  rw [hsurf ψ hψ] at hpos
  exact lt_irrefl _ hpos

end Trace

end TangentialTrace

/-! ### The smooth-class theorem -/

section SmoothClass

open Feec.Counterexamples.BallSymTSD (rho ball3 isOpen_ball3 isBounded_ball3 integrable_ball3
  continuous_rho)


section Assembly

variable {U : Ix → R3 → ℝ}

/-- The fundamental lemma on the ball, for continuous functions. -/
theorem eqOn_zero_of_integral_mul {f : R3 → ℝ} (hf : Continuous f)
    (h : ∀ g : R3 → ℝ, IsTest ball3 g → ∫ x in ball3, f x * g x = 0) : ∀ x ∈ ball3, f x = 0 := by
  have hae := isOpen_ball3.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) (f := f)
    (hf.locallyIntegrable.locallyIntegrableOn ball3) fun g hg hgc hgs => by
      have := h g ⟨hg, hgc, hgs⟩
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball3) fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hgs h)), zero_smul]]
      simpa [smul_eq_mul, mul_comm] using this
  have hae' : f =ᵐ[volume.restrict ball3] fun _ => (0 : ℝ) :=
    (ae_restrict_iff' isOpen_ball3.measurableSet).2 hae
  exact fun x hx => Measure.eqOn_open_of_ae_eq hae' isOpen_ball3 hf.continuousOn
    continuousOn_const hx

theorem eqOn_of_ae_ball3 {f g : R3 → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[volume.restrict ball3] g) : ∀ x ∈ ball3, f x = g x := fun _ hx =>
  Measure.eqOn_open_of_ae_eq h isOpen_ball3 hf.continuousOn hg.continuousOn hx

/-- **TSD in the pointwise sense**: a `C¹` field in `L²(TSD)` is symmetric, trace-free and
divergence-free at every point of the ball. -/
theorem pointwise_of_mem_tsd (hU : ∀ ij, ContDiff ℝ 1 (U ij))
    (hv : smoothField isOpen_ball3 isBounded_ball3 U (fun ij => (hU ij).continuous) ∈ tsd ball3) :
    (∀ x ∈ ball3, ∀ i j, U (i, j) x = U (j, i) x) ∧ (∀ x ∈ ball3, ∑ i, U (i, i) x = 0) ∧
      ∀ x ∈ ball3, ∀ i, ∑ j, partialDeriv j (U (i, j)) x = 0 := by
  set v := smoothField isOpen_ball3 isBounded_ball3 U (fun ij => (hU ij).continuous)
  have hc := coeFn_smoothField isOpen_ball3 isBounded_ball3 U (fun ij => (hU ij).continuous)
  obtain ⟨hs, htr, hdiv⟩ := hv
  refine ⟨fun x hx i j => ?_, fun x hx => ?_, fun x hx i => ?_⟩
  · refine eqOn_of_ae_ball3 (hU _).continuous (hU _).continuous ?_ x hx
    filter_upwards [hc (i, j), hc (j, i)] with y h1 h2
    rw [← h1, ← h2, hs i j]
  · refine eqOn_of_ae_ball3 (continuous_finsetSum _ fun i _ => (hU _).continuous)
      continuous_const ?_ x hx
    simp only [Fin.sum_univ_three] at htr ⊢
    filter_upwards [hc (0, 0), hc (1, 1), hc (2, 2), Lp.coeFn_add (v (0, 0) + v (1, 1)) (v (2, 2)),
      Lp.coeFn_add (v (0, 0)) (v (1, 1)), Lp.coeFn_zero ℝ 2 (volume.restrict ball3)]
      with y h1 h2 h3 h4 h5 h6
    rw [← h1, ← h2, ← h3, ← Pi.add_apply, ← h5, ← Pi.add_apply, ← h4, htr, h6]
    rfl
  · refine eqOn_zero_of_integral_mul (continuous_finsetSum _ fun j _ =>
      (hU _).continuous_partialDeriv j)
      (fun g hg => ?_) x hx
    set φ : Fin 3 → R3 → ℝ := fun i' => if i' = i then g else 0
    have hφ : IsTestField ball3 φ := fun i' => by
      by_cases h : i' = i
      · simp only [φ, h, ite_true]; exact hg
      · simp only [φ, h, ite_false]; exact IsTest.zero
    have h0 := hdiv φ hφ
    rw [inner_grad_testField _ hφ] at h0
    have h1 : ∀ ij : Ix, ∫ y, v ij y * partialDeriv ij.2 (φ ij.1) y ∂volume.restrict ball3 =
        -∫ y, φ ij.1 y * partialDeriv ij.2 (U ij) y ∂volume.restrict ball3 := fun ij => by
      rw [integral_congr_ae (g := fun y => partialDeriv ij.2 (φ ij.1) y * U ij y)
        ((hc ij).mono fun y hy => by simp only; rw [hy, mul_comm]),
        integral_pd_mul (hφ ij.1) (hU ij) ij.2]
    simp only [h1, Fintype.sum_prod_type, Finset.sum_neg_distrib, neg_eq_zero] at h0
    have h2 : ∑ i', ∑ j, ∫ y, φ i' y * partialDeriv j (U (i', j)) y ∂volume.restrict ball3 =
        ∑ j, ∫ y, g y * partialDeriv j (U (i, j)) y ∂volume.restrict ball3 := by
      rw [Finset.sum_eq_single i (fun b _ hb => by simp [φ, hb]) (by simp)]
      simp [φ]
    rw [h2, ← integral_finsetSum (f := fun j y => g y * partialDeriv j (U (i, j)) y) _
      fun j _ => integrable_ball3 (hg.continuous.mul ((hU _).continuous_partialDeriv j))] at h0
    rw [← h0]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem contDiff_curlM {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, ContDiff ℝ 2 (Ψ ij)) (ij : Ix) :
    ContDiff ℝ 1 (curlM Ψ ij) :=
  ((hΨ _).partialDeriv (m := 1) (by norm_num) _).sub
    ((hΨ _).partialDeriv (m := 1) (by norm_num) _)

/-- **An electric eigenfield with a `C²` representative**, pointwise: `curl_min u = curl U`,
`curl curl U = ξ² U` in the ball, and Green's formula against all of `C_c^∞(ℝ³)` (the weak form
of the electric boundary condition). -/
theorem eigen_data (hU : ∀ ij, ContDiff ℝ 2 (U ij)) {ξ : ℝ}
    (hE : (gradCurl ℝ isOpen_ball3).IsEigenfield ξ
      (smoothField isOpen_ball3 isBounded_ball3 U (fun ij => (hU ij).continuous))) :
    (∀ h1 : smoothField isOpen_ball3 isBounded_ball3 U (fun ij => (hU ij).continuous) ∈
        (gradCurl ℝ isOpen_ball3).d₁.domain,
      (gradCurl ℝ isOpen_ball3).d₁ ⟨_, h1⟩ =
        smoothField isOpen_ball3 isBounded_ball3 (curlM U)
          (fun ij => (contDiff_curlM hU ij).continuous)) ∧
    (∀ x ∈ ball3, ∀ ij, curlM (curlM U) ij x = ξ ^ 2 * U ij x) ∧
    ∀ ψ : Ix → R3 → ℝ, IsTestField (univ : Set R3) ψ →
      ∑ ij, ∫ x in ball3, curlM U ij x * ψ ij x = ∑ ij, ∫ x in ball3, U ij x * curlM ψ ij x := by
  have hU1 : ∀ ij, ContDiff ℝ 1 (U ij) := fun ij => (hU ij).of_le (by norm_num)
  set v := smoothField isOpen_ball3 isBounded_ball3 U (fun ij => (hU ij).continuous)
  set W := smoothField isOpen_ball3 isBounded_ball3 (curlM U)
    (fun ij => (contDiff_curlM hU ij).continuous)
  obtain ⟨hmem, hval⟩ := smoothField_mem_adjoint isOpen_ball3 isBounded_ball3
    (gradCurl ℝ isOpen_ball3) le_rfl hU1
  have hcurl : ∀ h1 : v ∈ (gradCurl ℝ isOpen_ball3).d₁.domain,
      (gradCurl ℝ isOpen_ball3).d₁ ⟨_, h1⟩ = W := fun h1 => by
    rw [show (gradCurl ℝ isOpen_ball3).d₁ ⟨_, h1⟩ =
      (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal ball3 ⟨_, h1⟩ from rfl,
      minimal_curl_eq_adjoint isOpen_ball3 ⟨_, h1⟩ hmem]
    exact hval
  obtain ⟨h1, h3, e⟩ := hE
  refine ⟨hcurl, ?_, ?_⟩
  · obtain ⟨hmem2, hval2⟩ := smoothField_mem_adjoint isOpen_ball3 isBounded_ball3
      (gradCurl ℝ isOpen_ball3) le_rfl (contDiff_curlM hU)
    have hq : (⟨(gradCurl ℝ isOpen_ball3).d₁ ⟨_, h1⟩, h3⟩ : (gradCurl ℝ isOpen_ball3).d₁†.domain) =
        ⟨W, hmem2⟩ := Subtype.ext (hcurl h1)
    rw [hq, hval2] at e
    simp only [RCLike.ofReal_real_eq_id, id_eq] at e
    intro x hx ij
    have hc2 := coeFn_smoothField isOpen_ball3 isBounded_ball3 (curlM (curlM U))
      (continuous_curlM (contDiff_curlM hU)) ij
    have hc1 := coeFn_smoothField isOpen_ball3 isBounded_ball3 U (fun ij => (hU ij).continuous) ij
    refine eqOn_of_ae_ball3 (continuous_curlM (contDiff_curlM hU) ij)
      (continuous_const.mul (hU ij).continuous) ?_ x hx
    filter_upwards [hc2, hc1, Lp.coeFn_smul (ξ ^ 2 : ℝ) (v ij)] with y h2 h1' h3'
    rw [← h2, e]
    simp only [PiLp.smul_apply] at h3' ⊢
    rw [h3', Pi.smul_apply, h1', smul_eq_mul, Pi.mul_apply]
  · intro ψ hψ
    have hψ1 : ∀ ij, ContDiff ℝ 1 (ψ ij) := fun ij => (hψ ij).contDiff.of_le (by simp)
    have hg := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal_green isOpen_ball3 curlOp_isOrderLE
      ⟨v, h1⟩ hψ1 (fun j => (memLp_of_isTest (hψ j)).restrict ball3)
      (fun i => (memLp_of_isTest
        ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.isTestField_apply hψ i)).restrict ball3)
    rw [show (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal ball3 ⟨v, h1⟩ = W from hcurl h1,
      inner_toL2F_eq, inner_toL2F_eq] at hg
    have hcW := coeFn_smoothField isOpen_ball3 isBounded_ball3 (curlM U)
      (fun ij => (contDiff_curlM hU ij).continuous)
    have hcv := coeFn_smoothField isOpen_ball3 isBounded_ball3 U (fun ij => (hU ij).continuous)
    have e1 : ∀ ij, ∫ x in ball3, W ij x * ψ ij x = ∫ x in ball3, curlM U ij x * ψ ij x :=
      fun ij => integral_congr_ae ((hcW ij).mono fun x hx => by simp only; rw [hx])
    have e2 : ∀ ij, ∫ x in ball3, v ij x *
        (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.apply ψ ij x =
          ∫ x in ball3, U ij x * curlM ψ ij x := fun ij =>
      integral_congr_ae ((hcv ij).mono fun x hx => by
        simp only; rw [hx, ← curlM_eq_formalAdj_apply])
    simp only [e1, e2] at hg
    exact hg

/-- **No TSD eigenfield on the ball with a `C²` representative on `ℝ³`** (core form). -/
theorem eq_zero_of_isEigenfield_of_contDiff_two {ξ : ℝ} (hξ : ξ ≠ 0)
    (hU : ∀ ij, ContDiff ℝ 2 (U ij))
    (hv : smoothField isOpen_ball3 isBounded_ball3 U (fun ij => (hU ij).continuous) ∈ tsd ball3)
    (hE : (gradCurl ℝ isOpen_ball3).IsEigenfield ξ
      (smoothField isOpen_ball3 isBounded_ball3 U (fun ij => (hU ij).continuous))) :
    smoothField isOpen_ball3 isBounded_ball3 U (fun ij => (hU ij).continuous) = 0 := by
  have hU1 : ∀ ij, ContDiff ℝ 1 (U ij) := fun ij => (hU ij).of_le (by norm_num)
  obtain ⟨hsym, htr, hdiv⟩ := pointwise_of_mem_tsd hU1 hv
  obtain ⟨hcurl, hcc, hgreen⟩ := eigen_data hU hE
  -- the electric boundary condition, pointwise: `x × Uᵢ = 0` on `S²`
  have hcross := fun x (hx : rho x = 1) ik => crossF_eq_zero_of_green hU1 hgreen hx ik
  -- `U = 0` on `S²` (symmetric, trace-free, normal rows)
  have hU0 : ∀ x, rho x = 1 → ∀ ij, U ij x = 0 := by
    intro x hx ij
    have hs : ∀ i j, U (i, j) x = U (j, i) x := fun i j => by
      have := eq_zero_of_ball3 ((hU (i, j)).continuous.sub (hU (j, i)).continuous)
        (fun y hy => sub_eq_zero.2 (hsym y hy i j)) hx.le
      exact sub_eq_zero.1 this
    have ht : ∑ i, U (i, i) x = 0 :=
      eq_zero_of_ball3 (continuous_finsetSum _ fun i _ => (hU _).continuous) htr hx.le
    have hM := eq_zero_of_symm_of_trace_of_cross (Matrix.of fun i j => U (i, j) x) x
      (by simpa [dotProduct, Fin.sum_univ_three, rho] using hx)
      (by ext i j; simp [hs i j]) (by simpa [Matrix.trace] using ht)
      (fun i => by
        funext k
        have h0 := hcross x hx (i, 0)
        have h1 := hcross x hx (i, 1)
        have h2 := hcross x hx (i, 2)
        simp only [crossF] at h0 h1 h2
        fin_cases k <;> simp [cross_apply] <;> assumption)
    have := congrFun (congrFun hM ij.1) ij.2
    simpa using this
  -- `ΔU = 0` on `S²`
  have hlap : ∀ x, rho x = 1 → ∀ ij, laplacian (U ij) x = 0 := by
    intro x hx ij
    obtain ⟨i, k⟩ := ij
    have hdivC : ContDiff ℝ 1 (fun y => ∑ l, partialDeriv l (U (i, l)) y) :=
      ContDiff.sum fun l _ => (hU _).partialDeriv (m := 1) (by norm_num) l
    have h1 : partialDeriv k (fun y => ∑ l, partialDeriv l (U (i, l)) y) x = 0 :=
      eq_zero_of_ball3 (hdivC.continuous_partialDeriv k)
        (fun y hy => pd_eq_zero_of_ball3 (fun z hz => hdiv z hz i) hy k) hx.le
    have h2 : curlM (curlM U) (i, k) x = 0 := by
      have := eq_zero_of_ball3 ((continuous_curlM (contDiff_curlM hU) (i, k)).sub
        (continuous_const.mul (hU (i, k)).continuous))
        (fun y hy => sub_eq_zero.2 (hcc y hy (i, k))) hx.le
      simp only [Pi.sub_apply, Pi.mul_apply, hU0 x hx (i, k), mul_zero, sub_zero] at this
      exact this
    have := curlM_curlM_eq hU i k x
    rw [h2, h1] at this
    linarith
  -- the boundary layer is transverse-traceless, hence zero (no TT tensors on `S²`)
  obtain ⟨hTT, hnorm⟩ := isSphereTT_radDeriv hU hsym htr hdiv hlap hU0
  have hV0 := fun x (hx : rho x = 1) ij =>
    eq_zero_of_isSphereTT hTT (contDiff_radDeriv hU) hx ij
  -- so `∇U = 0` and `curl U = 0` on `S²`
  have hW0 : ∀ x, rho x = 1 → ∀ ij, curlM U ij x = 0 := fun x hx ij => by
    simp only [curlM, hnorm x hx, hV0 x hx, mul_zero, sub_zero]
  -- `curl u ∈ H̊(curl)`, and the eigenfield vanishes
  have hm := smoothField_mem_minimal_of_eq_zero_sphere (contDiff_curlM hU) hW0
  exact eq_zero_of_isEigenfield_of_mem_minimal isOpen_ball3 isBounded_ball3 hξ hE
    fun h1 => by rw [hcurl h1]; exact hm

end Assembly

end SmoothClass

/-! ### Neighbourhoods of the closed ball -/

section Ball

open Feec.Counterexamples.BallSymTSD (rho ball3 isOpen_ball3 isBounded_ball3 continuous_rho)


/-- **Cut-off to `ℝ³`**: a field `C²` on a neighbourhood `O` of the closed ball agrees on a
neighbourhood of the closed ball with a field `C²` on `ℝ³`. -/
theorem exists_contDiff_eq_on_closedBall3 {O : Set R3} (hO : IsOpen O)
    (hBO : {x : R3 | rho x ≤ 1} ⊆ O) {U : Ix → R3 → ℝ} (hU : ∀ ij, ContDiffOn ℝ 2 (U ij) O) :
    ∃ U' : Ix → R3 → ℝ, (∀ ij, ContDiff ℝ 2 (U' ij)) ∧
      ∀ ij, ∀ x, rho x ≤ 1 → U' ij x = U ij x := by
  obtain ⟨δ, hδ, hδO⟩ := isCompact_closedBall3.exists_cthickening_subset_open hO hBO
  obtain ⟨ζ, hζs, -, hζsupp, hζ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (Metric.isOpen_thickening (δ := δ) (E := {x : R3 | rho x ≤ 1}))
    (isClosed_le continuous_rho continuous_const) (Metric.self_subset_thickening hδ _)
  have hts : tsupport ζ ⊆ O := by
    rw [tsupport, hζsupp]
    exact (Metric.closure_thickening_subset_cthickening δ _).trans hδO
  refine ⟨fun ij x => ζ x * U ij x, fun ij => ?_, fun ij x hx => ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ O
    · exact ((hζs.of_le (by simp)).contDiffAt).mul ((hU ij).contDiffAt (hO.mem_nhds hx))
    · have hev : (fun y => ζ y * U ij y) =ᶠ[𝓝 x] fun _ => 0 := by
        have : x ∉ tsupport ζ := fun h => hx (hts h)
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 this] with y hy
        simp only [Pi.zero_apply] at hy
        rw [hy, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · simp only [(hζ1 x).1 hx, one_mul]

/-- **TSD eigenfields on the unit ball that are `C²` up to the boundary vanish**: on
`B = {|x| < 1}`, let `ξ ≠ 0` and `u ∈ L²(TSD) ∩ H̊(curl)` with `curl† curl u = ξ² u`, and assume
`u` has a representative that is `C²` on a neighbourhood of the closed ball. Then `u = 0`. -/
theorem eq_zero_of_isEigenfield_of_contDiff_ball {ξ : ℝ} (hξ : ξ ≠ 0) {v : L2F ℝ ball3 Ix}
    (hv : v ∈ tsd ball3) (hE : (gradCurl ℝ isOpen_ball3).IsEigenfield ξ v) {O : Set R3}
    (hO : IsOpen O) (hBO : {x : R3 | rho x ≤ 1} ⊆ O) {U : Ix → R3 → ℝ}
    (hU : ∀ ij, ContDiffOn ℝ 2 (U ij) O) (hvU : ∀ ij, v ij =ᵐ[volume.restrict ball3] U ij) :
    v = 0 := by
  obtain ⟨U', hU', hUU'⟩ := exists_contDiff_eq_on_closedBall3 hO hBO hU
  have hveq : v = smoothField isOpen_ball3 isBounded_ball3 U' (fun ij => (hU' ij).continuous) := by
    refine (WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_)
    filter_upwards [hvU ij, coeFn_smoothField isOpen_ball3 isBounded_ball3 U'
      (fun ij => (hU' ij).continuous) ij, ae_restrict_mem isOpen_ball3.measurableSet]
      with x h1 h2 hx
    rw [h1, h2, hUU' ij x (le_of_lt hx)]
  subst hveq
  exact eq_zero_of_isEigenfield_of_contDiff_two hξ hU' hv hE

/-! ### The conditional result: regularity implies stationarity -/

section Regularity

variable {Ω : Set R3}

/-- `v` has a representative that is `C²` on a neighbourhood of `cl Ω`. -/
def HasC2Rep {ι : Type*} [Fintype ι] (Ω : Set R3) (v : L2F ℝ Ω ι) : Prop :=
  ∃ O : Set R3, IsOpen O ∧ closure Ω ⊆ O ∧ ∃ U : ι → R3 → ℝ,
    (∀ ij, ContDiffOn ℝ 2 (U ij) O) ∧ ∀ ij, v ij =ᵐ[volume.restrict Ω] U ij

/-- **Boundary regularity of TSD eigenfields** (hypothesis, absent from Mathlib): every TSD
eigenfield `u ∈ L²(TSD) ∩ H̊(curl)`, `curl† curl u = ξ² u`, `ξ > 0`, on `Ω` is `C²` up to `∂Ω`.
It follows from the row-wise Maxwell regularity `MaxwellEigenfieldRegularity`
(`tsdEigenfieldRegularity_of_maxwell`). -/
def TSDEigenfieldRegularity (Ω : Set R3) (hΩ : IsOpen Ω) : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ∀ v : L2F ℝ Ω Ix, v ∈ tsd Ω → (gradCurl ℝ hΩ).IsEigenfield ξ v → HasC2Rep Ω v

theorem hasC2Rep_zero {ι : Type*} [Fintype ι] : HasC2Rep Ω (0 : L2F ℝ Ω ι) :=
  ⟨univ, isOpen_univ, subset_univ _, fun _ _ => 0, fun _ => contDiffOn_const, fun ij =>
    (Lp.coeFn_zero ℝ 2 (volume.restrict Ω)).mono fun x hx => by
      rw [show (0 : L2F ℝ Ω ι) ij = 0 from rfl, hx]; rfl⟩

/-- The regularity hypothesis holds whenever every TSD eigenfield vanishes (the zero field has a
smooth representative). -/
theorem tsdEigenfieldRegularity_of_forall_eq_zero (hΩ : IsOpen Ω)
    (h : ∀ ξ : ℝ, 0 < ξ → ∀ v : L2F ℝ Ω Ix, v ∈ tsd Ω → (gradCurl ℝ hΩ).IsEigenfield ξ v →
      v = 0) : TSDEigenfieldRegularity Ω hΩ := fun ξ hξ v hv hE => by
  rw [h ξ hξ v hv hE]; exact hasC2Rep_zero

/-- **A concrete instance**: on every box `∏ (aᵢ, aᵢ + ℓᵢ)` the regularity hypothesis holds,
since there are no TSD eigenfields (`Feec.Models.Box.not_exists_tsd_eigenfield_box`). -/
theorem tsdEigenfieldRegularity_box {a ℓ : R3} (hℓ : ∀ i, 0 < ℓ i) :
    TSDEigenfieldRegularity (Models.Box.openBox a ℓ) (Models.Box.isOpen_openBox a ℓ) :=
  tsdEigenfieldRegularity_of_forall_eq_zero _ fun ξ hξ v hv hE => by
    by_contra hv0
    exact Models.Box.not_exists_tsd_eigenfield_box hℓ ⟨ξ, hξ, v, hv0, hv, hE⟩

/-- **On the ball, regularity is equivalent to the absence of TSD eigenfields**: the smooth-class
theorem `eq_zero_of_isEigenfield_of_contDiff_ball` kills every regular eigenfield. So, as a
hypothesis on the ball, `TSDEigenfieldRegularity` restates the open question O3; the standard
regularity statement it follows from is `MaxwellEigenfieldRegularity`. -/
theorem tsdEigenfieldRegularity_ball_iff :
    TSDEigenfieldRegularity ball3 isOpen_ball3 ↔
      ∀ ξ : ℝ, 0 < ξ → ∀ v : L2F ℝ ball3 Ix, v ∈ tsd ball3 →
        (gradCurl ℝ isOpen_ball3).IsEigenfield ξ v → v = 0 := by
  refine ⟨fun hR ξ hξ v hv hE => ?_, tsdEigenfieldRegularity_of_forall_eq_zero isOpen_ball3⟩
  obtain ⟨O, hO, hcl, U, hU, hvU⟩ := hR ξ hξ v hv hE
  exact eq_zero_of_isEigenfield_of_contDiff_ball hξ.ne' hv hE hO
    (fun x hx => hcl (mem_closure_ball3 hx)) hU hvU

/-- **`K*` is stationary on the ball under regularity**: for the thesis' complex on the unit ball
and `K = {0} × L²(TSD) × L²(TSD)`, if the eigenvectors of `L²` are complete (`hD`) and TSD
eigenfields are `C²` up to the boundary (`hR`), every datum of `K*` is stationary. -/
theorem coreSub_le_stationary_ball_of_regularity (hD : (gradCurl ℝ isOpen_ball3).EigenDense)
    (hR : TSDEigenfieldRegularity ball3 isOpen_ball3) :
    (gradCurl ℝ isOpen_ball3).coreSub (tsd ball3) (tsd ball3) ≤
      (gradCurl ℝ isOpen_ball3).stationary := by
  by_contra h
  obtain ⟨ξ, hξ, v, hv0, hv, hE, -⟩ :=
    (not_coreSub_le_stationary_iff isOpen_ball3 isBounded_ball3 hD).1 h
  exact hv0 (tsdEigenfieldRegularity_ball_iff.1 hR ξ hξ v hv hE)

end Regularity

/-! ### Row-wise Maxwell regularity -/

section Maxwell

variable {Ω : Set R3}

/-- Row `i` of a matrix field, as a vector field (index `Fin 1 × Fin 3`, the index of
`Feec.Domain.curlOp 1`, the row-wise curl of a single row). -/
def rowF (i : Fin 3) : L2F ℝ Ω Ix →L[ℝ] L2F ℝ Ω (Fin 1 × Fin 3) :=
  compF fun p : Fin 1 × Fin 3 => (i, p.2)

theorem rowF_apply (i : Fin 3) (v : L2F ℝ Ω Ix) (p : Fin 1 × Fin 3) :
    rowF i v p = v (i, p.2) := rfl

/-- A vector field placed in row `i` of a matrix field (the adjoint of `rowF i`). -/
def rowEmb (i : Fin 3) : L2F ℝ Ω (Fin 1 × Fin 3) →L[ℝ] L2F ℝ Ω Ix :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Ix => L2 ℝ Ω)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun jk : Ix =>
      if jk.1 = i then PiLp.proj 2 (fun _ : Fin 1 × Fin 3 => L2 ℝ Ω) (0, jk.2) else 0

theorem rowEmb_apply (i : Fin 3) (w : L2F ℝ Ω (Fin 1 × Fin 3)) (jk : Ix) :
    rowEmb i w jk = if jk.1 = i then w (0, jk.2) else 0 := by
  by_cases h : jk.1 = i <;> simp [rowEmb, h]

theorem inner_rowEmb (i : Fin 3) (u : L2F ℝ Ω Ix) (w : L2F ℝ Ω (Fin 1 × Fin 3)) :
    ⟪u, rowEmb i w⟫_ℝ = ⟪rowF i u, w⟫_ℝ := by
  simp only [PiLp.inner_apply, rowEmb_apply, rowF_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp [Fin.fin_one_eq_zero]

/-- The vector test field `ψ` placed in row `i`. -/
def rowTest (i : Fin 3) (ψ : Fin 1 × Fin 3 → R3 → ℝ) : Ix → R3 → ℝ :=
  fun jk => if jk.1 = i then ψ (0, jk.2) else 0

theorem isTestField_rowTest (i : Fin 3) {ψ : Fin 1 × Fin 3 → R3 → ℝ} (hψ : IsTestField Ω ψ) :
    IsTestField Ω (rowTest i ψ) := fun jk => by
  unfold rowTest
  split_ifs
  exacts [hψ _, IsTest.zero]

theorem rowEmb_testField (i : Fin 3) {ψ : Fin 1 × Fin 3 → R3 → ℝ} (hψ : IsTestField Ω ψ) :
    rowEmb i (testField hψ) = testField (isTestField_rowTest i hψ) := by
  refine PiLp.ext fun jk => ?_
  rw [rowEmb_apply, testField_apply, testField_apply]
  by_cases h : jk.1 = i
  · simp only [h, ↓reduceIte]
    exact toL2_congr _ _ (by simp [rowTest, h])
  · simp only [h, ↓reduceIte]
    exact ((toL2_congr _ IsTest.zero (by simp [rowTest, h])).trans toL2_zero).symm

theorem curlOp_rowTest (i : Fin 3) (ψ : Fin 1 × Fin 3 → R3 → ℝ) :
    (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).apply (rowTest i ψ) =
      rowTest i ((curlOp 1 : ConstCoeffOp R3 ℝ _ _).apply ψ) := by
  funext ⟨j, k⟩ x
  rw [curlOp_apply]
  by_cases h : j = i
  · subst h
    simp [rowTest, curlOp_apply]
  · simp [rowTest, h]

theorem curlOp_row (i : Fin 3) (φ : Ix → R3 → ℝ) :
    (curlOp 1 : ConstCoeffOp R3 ℝ _ _).apply (fun p : Fin 1 × Fin 3 => φ (i, p.2)) =
      fun p => (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).apply φ (i, p.2) := by
  funext ⟨a, k⟩ x
  rw [curlOp_apply, curlOp_apply]

theorem gradOp_rowTest (i : Fin 3) (φ : Fin 1 → R3 → ℝ) :
    (gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).apply (fun j => if j = i then φ 0 else 0) =
      rowTest i ((gradOp 3 1 : ConstCoeffOp R3 ℝ _ _).apply φ) := by
  funext ⟨j, k⟩ x
  rw [gradOp_apply]
  by_cases h : j = i
  · subst h
    simp [rowTest, gradOp_apply]
  · simp [rowTest, h]

/-- A vector field `w` is **weakly divergence-free** in `Ω`: `∫ w · ∇φ = 0` for all
`φ ∈ C_c^∞(Ω)` (no boundary condition). -/
def IsDivFree (w : L2F ℝ Ω (Fin 1 × Fin 3)) : Prop :=
  ∀ φ : Fin 1 → R3 → ℝ, ∀ hφ : IsTestField Ω φ,
    ⟪w, testField ((gradOp 3 1 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hφ)⟫_ℝ = 0

/-- `w` is an **electric (perfectly conducting) Maxwell eigenfield** with frequency `ξ`:
`w ∈ H̊(curl, Ω)`, `curl w ∈ H(curl, Ω)` and `curl curl w = ξ² w`, where the second curl is the
weak one, `(curl_min)†` (`Feec.Domain.ConstCoeffOp.adjoint_minimal`). -/
def IsMaxwellEigenfield (ξ : ℝ) (w : L2F ℝ Ω (Fin 1 × Fin 3)) : Prop :=
  ∃ (h1 : w ∈ ((curlOp 1 : ConstCoeffOp R3 ℝ _ _).minimal Ω).domain)
    (h2 : (curlOp 1 : ConstCoeffOp R3 ℝ _ _).minimal Ω ⟨w, h1⟩ ∈
      ((curlOp 1 : ConstCoeffOp R3 ℝ _ _).minimal Ω)†.domain),
    ((curlOp 1 : ConstCoeffOp R3 ℝ _ _).minimal Ω)† ⟨_, h2⟩ = (ξ ^ 2 : ℝ) • w

/-- **Boundary regularity of Maxwell eigenfields** (hypothesis, absent from Mathlib): every
weakly divergence-free vector field `w ∈ H̊(curl, Ω)` with `curl curl w = ξ² w`, `ξ > 0`, has a
representative `C²` on a neighbourhood of `cl Ω`. This is the textbook statement for the
electric Maxwell eigenproblem on a smooth bounded domain: `H̊(curl) ∩ H(div) ↪ H¹` with
`H^{s+1}` regularity from `curl curl w`, `div w ∈ H^s` ([GiraultRaviart1986], Ch. I, §3), then
bootstrapping and Sobolev embedding ([Evans2010], §5.6, §6.3 for the scalar model). It involves
no symmetry or trace condition, and it is not a restatement of the absence of eigenfields:
nonzero smooth Maxwell eigenfields exist on every box and on the ball (for instance the toroidal
fields `j₁(k|x|)/|x| (x₂, -x₁, 0)`, `j₁(k) = 0`; not formalized). -/
def MaxwellEigenfieldRegularity (Ω : Set R3) : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ∀ w : L2F ℝ Ω (Fin 1 × Fin 3), IsDivFree w → IsMaxwellEigenfield ξ w →
    HasC2Rep Ω w

/-- The hypothesis is satisfiable: it holds trivially on `∅`, where `L²` is zero. -/
theorem maxwellEigenfieldRegularity_empty : MaxwellEigenfieldRegularity (∅ : Set R3) :=
  fun _ _ _ _ _ => ⟨univ, isOpen_univ, subset_univ _, fun _ _ => 0, fun _ => contDiffOn_const,
    fun _ => ae_iff.2 (by simp)⟩

/-- The rows of a TSD field are weakly divergence-free. -/
theorem isDivFree_rowF {v : L2F ℝ Ω Ix} (hv : v ∈ tsd Ω) (i : Fin 3) : IsDivFree (rowF i v) := by
  intro φ hφ
  have hφ' : IsTestField Ω (fun j => if j = i then φ 0 else 0) := fun j => by
    dsimp only
    split_ifs
    exacts [hφ 0, IsTest.zero]
  have h0 := hv.2.2 _ hφ'
  rw [testField_congr _
      (isTestField_rowTest i ((gradOp 3 1 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hφ))
      (gradOp_rowTest i φ), ← rowEmb_testField, inner_rowEmb] at h0
  exact h0

theorem rowF_mem_testGraph (i : Fin 3) {φ : Ix → R3 → ℝ} (hφ : IsTestField Ω φ) :
    (rowF i (testField hφ),
        rowF i (testField ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply hφ))) ∈
      (curlOp 1 : ConstCoeffOp R3 ℝ _ _).testGraph Ω := by
  refine ⟨fun p => φ (i, p.2), fun p => hφ _, ?_⟩
  rw [rowF, compF_testField, compF_testField]
  exact Prod.ext rfl (testField_congr _ _ (curlOp_row i φ).symm)

/-- Rows of `H̊(curl)` matrix fields lie in `H̊(curl)`, with the row of the curl as curl. -/
theorem rowF_mem_minimal (hΩ : IsOpen Ω) (i : Fin 3)
    (u : ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain) :
    ∃ h : rowF i (u : L2F ℝ Ω Ix) ∈ ((curlOp 1 : ConstCoeffOp R3 ℝ _ _).minimal Ω).domain,
      (curlOp 1 : ConstCoeffOp R3 ℝ _ _).minimal Ω ⟨_, h⟩ =
        rowF i ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω u) :=
  (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).mem_minimal_of_mapsTo_testGraph hΩ hΩ (rowF i) (rowF i)
    (fun _ hφ => rowF_mem_testGraph i hφ) u

/-- Rows of `H(curl)` matrix fields lie in `H(curl)`, with the row of the weak curl as weak
curl. -/
theorem rowF_mem_adjoint (hΩ : IsOpen Ω) (i : Fin 3)
    (c : ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω)†.domain) :
    ∃ h : rowF i (c : L2F ℝ Ω Ix) ∈ ((curlOp 1 : ConstCoeffOp R3 ℝ _ _).minimal Ω)†.domain,
      ((curlOp 1 : ConstCoeffOp R3 ℝ _ _).minimal Ω)† ⟨_, h⟩ =
        rowF i (((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω)† c) := by
  have hid : ∀ ψ : Fin 1 × Fin 3 → R3 → ℝ, ∀ hψ : IsTestField Ω ψ,
      ⟪rowF i (((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω)† c), testField hψ⟫_ℝ =
        ⟪rowF i (c : L2F ℝ Ω Ix),
          testField ((curlOp 1 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hψ)⟫_ℝ := by
    intro ψ hψ
    rw [← inner_rowEmb, rowEmb_testField, ← inner_rowEmb, rowEmb_testField,
      (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).adjoint_minimal_inner_testField hΩ c
        (isTestField_rowTest i hψ)]
    exact congrArg _ (testField_congr _ _ (curlOp_rowTest i ψ))
  have hmem := ((curlOp 1 : ConstCoeffOp R3 ℝ _ _).mem_adjoint_minimal_domain_iff hΩ).2 ⟨_, hid⟩
  exact ⟨hmem, (curlOp 1 : ConstCoeffOp R3 ℝ _ _).adjoint_minimal_apply_eq hΩ ⟨_, hmem⟩ hid⟩

/-- **The rows of an electric eigenfield of the thesis' complex are electric Maxwell eigenfields**
(the curl acts row-wise). -/
theorem isMaxwellEigenfield_rowF (hΩ : IsOpen Ω) {ξ : ℝ} {v : L2F ℝ Ω Ix}
    (hE : (gradCurl ℝ hΩ).IsEigenfield ξ v) (i : Fin 3) : IsMaxwellEigenfield ξ (rowF i v) := by
  obtain ⟨h1, h3, e⟩ := hE
  obtain ⟨hr1, er1⟩ := rowF_mem_minimal hΩ i ⟨v, h1⟩
  obtain ⟨hr3, er3⟩ := rowF_mem_adjoint hΩ i ⟨_, h3⟩
  have key : ∀ (y : L2F ℝ Ω (Fin 1 × Fin 3))
      (hy : y ∈ ((curlOp 1 : ConstCoeffOp R3 ℝ _ _).minimal Ω)†.domain),
      y = rowF i ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω ⟨v, h1⟩) →
      ((curlOp 1 : ConstCoeffOp R3 ℝ _ _).minimal Ω)† ⟨y, hy⟩ = (ξ ^ 2 : ℝ) • rowF i v := by
    rintro y hy rfl
    refine er3.trans ?_
    rw [← map_smul]
    exact congrArg (rowF i) e
  exact ⟨hr1, er1 ▸ hr3, key _ _ er1⟩

/-- Componentwise assembly of `C²` representatives. -/
theorem hasC2Rep_of_rowF {v : L2F ℝ Ω Ix} (h : ∀ i, HasC2Rep Ω (rowF i v)) : HasC2Rep Ω v := by
  choose O hO hcl U hU hvU using h
  refine ⟨⋂ i, O i, isOpen_iInter_of_finite hO, subset_iInter hcl, fun jk => U jk.1 (0, jk.2),
    fun jk => (hU jk.1 (0, jk.2)).mono (iInter_subset _ _), fun jk => ?_⟩
  simpa only [rowF_apply] using hvU jk.1 (0, jk.2)

/-- **Maxwell regularity implies TSD regularity**: a TSD eigenfield is, row by row, a weakly
divergence-free electric Maxwell eigenfield. -/
theorem tsdEigenfieldRegularity_of_maxwell (hΩ : IsOpen Ω) (h : MaxwellEigenfieldRegularity Ω) :
    TSDEigenfieldRegularity Ω hΩ := fun ξ hξ _ hv hE =>
  hasC2Rep_of_rowF fun i => h ξ hξ _ (isDivFree_rowF hv i) (isMaxwellEigenfield_rowF hΩ hE i)

/-- **`K*` is stationary on the ball under Maxwell regularity**: for the thesis' complex on the
unit ball and `K = {0} × L²(TSD) × L²(TSD)`, if the eigenvectors of `L²` are complete (`hD`) and
electric Maxwell eigenfields on the ball are `C²` up to the boundary (`hM`, the standard elliptic
regularity statement, absent from Mathlib), every datum of `K*` is stationary. -/
theorem coreSub_le_stationary_ball_of_maxwellRegularity
    (hD : (gradCurl ℝ isOpen_ball3).EigenDense) (hM : MaxwellEigenfieldRegularity ball3) :
    (gradCurl ℝ isOpen_ball3).coreSub (tsd ball3) (tsd ball3) ≤
      (gradCurl ℝ isOpen_ball3).stationary :=
  coreSub_le_stationary_ball_of_regularity hD (tsdEigenfieldRegularity_of_maxwell isOpen_ball3 hM)

end Maxwell

/-! ### Non-vacuity: the boundary condition is the operative hypothesis -/

section ShearWave

/-- The constant symmetric trace-free matrix `M = e₂ e₃ᵀ + e₃ e₂ᵀ`, with `M e₁ = 0`. -/
def shearMat (ij : Ix) : ℝ := if ij = (1, 2) ∨ ij = (2, 1) then 1 else 0

/-- **The transverse plane wave** `P(x) = cos(ξ x₁) M`: symmetric, trace-free, divergence-free
(`M e₁ = 0`) and `curl curl P = ξ² P`, smooth on `ℝ³`, but with nonzero tangential trace. -/
def shearWave (ξ : ℝ) : Ix → R3 → ℝ := fun ij x => shearMat ij * Real.cos (ξ * x 0)

theorem contDiff_shearWave (ξ : ℝ) (ij : Ix) : ContDiff ℝ ∞ (shearWave ξ ij) := by
  unfold shearWave; fun_prop

private theorem pd_cos (ξ : ℝ) (k : Fin 3) (x : R3) :
    partialDeriv k (fun y : R3 => Real.cos (ξ * y 0)) x =
      if k = 0 then -(ξ * Real.sin (ξ * x 0)) else 0 := by
  have h : HasFDerivAt (fun y : R3 => Real.cos (ξ * y 0)) _ x :=
    ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 x).const_mul ξ).cos
  rw [HasFDerivAt.partialDeriv_eq h]
  by_cases hk : k = 0
  · subst hk; simp; ring
  · simp [Ne.symm hk, hk]

private theorem pd_sin (ξ : ℝ) (k : Fin 3) (x : R3) :
    partialDeriv k (fun y : R3 => Real.sin (ξ * y 0)) x =
      if k = 0 then ξ * Real.cos (ξ * x 0) else 0 := by
  have h : HasFDerivAt (fun y : R3 => Real.sin (ξ * y 0)) _ x :=
    ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 x).const_mul ξ).sin
  rw [HasFDerivAt.partialDeriv_eq h]
  by_cases hk : k = 0
  · subst hk; simp; ring
  · simp [Ne.symm hk, hk]

theorem pd_shearWave (ξ : ℝ) (ij : Ix) (k : Fin 3) (x : R3) :
    partialDeriv k (shearWave ξ ij) x = shearMat ij *
      (if k = 0 then -(ξ * Real.sin (ξ * x 0)) else 0) := by
  rw [show shearWave ξ ij = fun y => shearMat ij * Real.cos (ξ * y 0) from rfl,
    partialDeriv_const_mul (by fun_prop), pd_cos]

theorem pd_pd_shearWave (ξ : ℝ) (ij : Ix) (j k : Fin 3) (x : R3) :
    partialDeriv j (partialDeriv k (shearWave ξ ij)) x =
      shearMat ij *
        (if k = 0 then (if j = 0 then -(ξ ^ 2 * Real.cos (ξ * x 0)) else 0) else 0) := by
  have e : partialDeriv k (shearWave ξ ij) = fun y => (-(shearMat ij * (if k = 0 then ξ else 0))) *
      Real.sin (ξ * y 0) := funext fun y => by
    rw [pd_shearWave]; split_ifs <;> ring
  rw [e, partialDeriv_const_mul (by fun_prop), pd_sin]
  split_ifs <;> ring

theorem shearWave_symm (ξ : ℝ) (i j : Fin 3) (x : R3) :
    shearWave ξ (i, j) x = shearWave ξ (j, i) x := by
  simp only [shearWave, shearMat]
  fin_cases i <;> fin_cases j <;> simp

theorem shearWave_trace (ξ : ℝ) (x : R3) : ∑ i, shearWave ξ (i, i) x = 0 := by
  simp [shearWave, shearMat, Fin.sum_univ_three]

theorem shearWave_div (ξ : ℝ) (i : Fin 3) (x : R3) :
    ∑ j, partialDeriv j (shearWave ξ (i, j)) x = 0 := by
  simp only [pd_shearWave, Fin.sum_univ_three, shearMat]
  fin_cases i <;> simp

theorem curlM_curlM_shearWave (ξ : ℝ) (ij : Ix) (x : R3) :
    curlM (curlM (shearWave ξ)) ij x = ξ ^ 2 * shearWave ξ ij x := by
  obtain ⟨i, k⟩ := ij
  rw [curlM_curlM_eq (fun ij => (contDiff_shearWave ξ ij).of_le (by simp)) i k x]
  have hdiv : (fun y => ∑ l, partialDeriv l (shearWave ξ (i, l)) y) = 0 :=
    funext fun y => shearWave_div ξ i y
  rw [hdiv, partialDeriv_zero]
  simp only [laplacian, pd_pd_shearWave, Fin.sum_univ_three, shearWave]
  fin_cases k <;> simp <;> ring

/-- The plane wave as an element of `L²(B)`. -/
def shearWaveL2 (ξ : ℝ) : L2F ℝ ball3 Ix :=
  smoothField isOpen_ball3 isBounded_ball3 (shearWave ξ)
    fun ij => (contDiff_shearWave ξ ij).continuous

/-- **Non-vacuity of the smooth-class theorem**: for every `ξ ≠ 0` the plane wave
`P = cos(ξ x₁) (e₂ e₃ᵀ + e₃ e₂ᵀ)` is a nonzero smooth TSD field on the ball with
`curl curl P = ξ² P` in `H(curl)` (all hypotheses of `eq_zero_of_isEigenfield_of_contDiff_ball`
but the electric boundary condition); hence it is **not** in `H̊(curl, B)`. -/
theorem shearWaveL2_spec {ξ : ℝ} (hξ : ξ ≠ 0) :
    shearWaveL2 ξ ≠ 0 ∧ shearWaveL2 ξ ∈ tsd ball3 ∧ HasC2Rep ball3 (shearWaveL2 ξ) ∧
      (∃ h : shearWaveL2 ξ ∈ (gradCurl ℝ isOpen_ball3).d₁†.domain,
        ∃ h' : (gradCurl ℝ isOpen_ball3).d₁† ⟨_, h⟩ ∈ (gradCurl ℝ isOpen_ball3).d₁†.domain,
          (gradCurl ℝ isOpen_ball3).d₁† ⟨_, h'⟩ = (ξ ^ 2 : ℝ) • shearWaveL2 ξ) ∧
      shearWaveL2 ξ ∉ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal ball3).domain := by
  unfold shearWaveL2
  have hP2 : ∀ ij, ContDiff ℝ 2 (shearWave ξ ij) := fun ij =>
    (contDiff_shearWave ξ ij).of_le (by simp)
  have hP1 : ∀ ij, ContDiff ℝ 1 (shearWave ξ ij) := fun ij =>
    (contDiff_shearWave ξ ij).of_le (by simp)
  -- nonzero: `P₂₃(0) = 1`
  have h0 : smoothField isOpen_ball3 isBounded_ball3 (shearWave ξ)
      (fun ij => (contDiff_shearWave ξ ij).continuous) ≠ 0 := fun h => by
    have := eqOn_zero_of_smoothField_eq_zero isOpen_ball3 isBounded_ball3 _ h (1, 2) 0
      Feec.Counterexamples.BallSymTSD.zero_mem_ball3
    simp [shearWave, shearMat] at this
  set v := smoothField isOpen_ball3 isBounded_ball3 (shearWave ξ)
    (fun ij => (contDiff_shearWave ξ ij).continuous)
  have htsd : v ∈ tsd ball3 :=
    smoothField_mem_tsd isOpen_ball3 isBounded_ball3 hP1 (fun i j x _ => shearWave_symm ξ i j x)
      (fun x _ => shearWave_trace ξ x) (fun j x _ => shearWave_div ξ j x)
  have hreg : HasC2Rep ball3 v :=
    ⟨univ, isOpen_univ, subset_univ _, shearWave ξ, fun ij => (hP2 ij).contDiffOn,
      coeFn_smoothField isOpen_ball3 isBounded_ball3 _ _⟩
  obtain ⟨hm1, hv1⟩ := smoothField_mem_adjoint isOpen_ball3 isBounded_ball3
    (gradCurl ℝ isOpen_ball3) le_rfl hP1
  obtain ⟨hm2, hv2⟩ := smoothField_mem_adjoint isOpen_ball3 isBounded_ball3
    (gradCurl ℝ isOpen_ball3) le_rfl (contDiff_curlM hP2)
  have hcc : smoothField isOpen_ball3 isBounded_ball3 (curlM (curlM (shearWave ξ)))
      (continuous_curlM (contDiff_curlM hP2)) = (ξ ^ 2 : ℝ) • v := by
    refine (WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_)
    filter_upwards [coeFn_smoothField isOpen_ball3 isBounded_ball3 _
      (continuous_curlM (contDiff_curlM hP2)) ij,
      coeFn_smoothField isOpen_ball3 isBounded_ball3 (shearWave ξ)
        (fun ij => (contDiff_shearWave ξ ij).continuous) ij,
      Lp.coeFn_smul (ξ ^ 2 : ℝ) (v ij)] with x h1 h2 h3
    simp only [PiLp.smul_apply] at h3 ⊢
    rw [h1, h3, Pi.smul_apply, h2, curlM_curlM_shearWave, smul_eq_mul]
  have heig : ∃ h : v ∈ (gradCurl ℝ isOpen_ball3).d₁†.domain,
      ∃ h' : (gradCurl ℝ isOpen_ball3).d₁† ⟨_, h⟩ ∈ (gradCurl ℝ isOpen_ball3).d₁†.domain,
        (gradCurl ℝ isOpen_ball3).d₁† ⟨_, h'⟩ = (ξ ^ 2 : ℝ) • v := by
    refine ⟨hm1, hv1 ▸ hm2, ?_⟩
    have hq : (⟨(gradCurl ℝ isOpen_ball3).d₁† ⟨_, hm1⟩, hv1 ▸ hm2⟩ :
        (gradCurl ℝ isOpen_ball3).d₁†.domain) = ⟨_, hm2⟩ := Subtype.ext hv1
    rw [hq, hv2, hcc]
  refine ⟨h0, htsd, hreg, heig, fun hmin => h0 ?_⟩
  -- with the boundary condition the plane wave would be an electric eigenfield
  obtain ⟨hm1', hm2', e⟩ := heig
  have hd : (gradCurl ℝ isOpen_ball3).d₁ ⟨_, hmin⟩ = (gradCurl ℝ isOpen_ball3).d₁† ⟨_, hm1'⟩ :=
    minimal_curl_eq_adjoint isOpen_ball3 ⟨_, hmin⟩ hm1'
  have hE : (gradCurl ℝ isOpen_ball3).IsEigenfield ξ v := by
    refine ⟨hmin, hd ▸ hm2', ?_⟩
    have hq : (⟨(gradCurl ℝ isOpen_ball3).d₁ ⟨_, hmin⟩, hd ▸ hm2'⟩ :
        (gradCurl ℝ isOpen_ball3).d₁†.domain) = ⟨_, hm2'⟩ := Subtype.ext hd
    rw [hq, e]
    rfl
  exact eq_zero_of_isEigenfield_of_contDiff_two hξ hP2 htsd hE

end ShearWave

end Ball

end Feec.Counterexamples.BallEigenfields
