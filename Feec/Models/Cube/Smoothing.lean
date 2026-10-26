module

public import Feec.Models.Cube.DeRham

/-!
# Even Fourier multipliers on the cube (method of images)

On the torus `𝕋ⁿ` convolution with a kernel `ρ` is the Fourier multiplier `û(q) ↦ ρ̂(q) û(q)`.
For a real kernel even in every variable (`ρ(…, -x_j, …) = ρ(x)`), `ρ̂` is real and invariant under
every frequency reflection `q ↦ flip_j q`; for a probability density `|ρ̂| ≤ 1`. This file records
such **even multipliers** (`EvenMultiplier`) for the parity model of the de Rham complex of the
cube `Q = (0, ½)ⁿ` (`Feec.Models.Cube.DeRham`), their fibre symbols (`EvenMultiplier.symbol`), the
frequency boxes `‖q‖_∞ ≤ K` (`box`, `mem_box`), and the summability of `‖v q‖²` for `v ∈ ℓ²`
(`summable_norm_sq_count`).

The smoothers used by the finite element method on cube meshes are the dilated mollification of
`Feec.Domain.StarShapedSmoothing` (`Feec.Models.Cube.SmoothingEstimates`) and the parity smoother
of `Feec.Models.Cube.ParitySmoother`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.5 (smoothing operators commuting with `d`)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (the cube by the method of images)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  Ch. 4 (convolution and mollifiers)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory LinearPMap Set Filter Topology Feec.Fourier Feec.Fourier.Exterior

namespace Feec.Models.Cube.DeRham

open Feec.Models.Torus.DeRham (window windowSymbol)

variable {d : Type*} [Fintype d] [LinearOrder d]

variable (d) in
/-- An **even multiplier**: a real symbol `ρ̂ : ℤⁿ → ℝ` with `|ρ̂| ≤ 1`, invariant under every
frequency reflection. The Fourier coefficients of a real, even kernel of total variation `≤ 1`
(e.g. an even probability density) are such a symbol; only these two properties are used. -/
structure EvenMultiplier where
  /-- the symbol -/
  ρ : (d → ℤ) → ℝ
  abs_le_one : ∀ q, |ρ q| ≤ 1
  flipAt_invariant : ∀ j q, ρ (flipAt j q) = ρ q

namespace EvenMultiplier

variable (m : EvenMultiplier d)

/-- The fibre symbol `ρ̂(q) · id`. -/
def symbol (k : ℕ) (q : d → ℤ) : Form ℂ d k →L[ℂ] Form ℂ d k :=
  ((m.ρ q : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (Form ℂ d k)

end EvenMultiplier

omit [LinearOrder d] in
theorem summable_norm_sq_count {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : Lp E 2 (Measure.count : Measure (d → ℤ))) : Summable fun q => ‖v q‖ ^ 2 := by
  have h := (lp.memℓp_count (d → ℤ) E 2 v).summable (by norm_num)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

variable (d) in
/-- The frequency box `‖q‖_∞ ≤ K`. -/
def box (K : ℕ) : Finset (d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(K : ℤ)) K

theorem mem_box {K : ℕ} {q : d → ℤ} : q ∈ box d K ↔ ∀ a, |q a| ≤ K := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

end Feec.Models.Cube.DeRham
