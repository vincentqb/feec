module

public import Solution.CrankNicolson
public import Feec.Numerics.PlaneWaveCubeError

/-!
# The plane wave as a smooth row solution

`Feec`'s row solutions are the challenge's (`RowSolution.ofFeec`, the converse of
`RowSolution.toFeec`), and row `0` of the plane wave of [QuennevilleBelair2015], Ch. 7
(`Feec.Numerics.PlaneWaveCube.planeWaveRows` with `A₊ = 1`, `Aₓ = 0`, `ω = 1`) has the
coefficient `E_{dx₀}(t, y) = -sin (y₂ - t)`, with time derivative `cos (y₂ - t)`: both are nonzero
at some point of the cube at every time.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set

@[expose] public noncomputable section

namespace TimeStepping

open Feec.Numerics.PlaneWaveCube Feec.Numerics.CrankNicolson

/-- A `Feec` row solution as a smooth row solution of the challenge. -/
def RowSolution.ofFeec {T L : ℝ} (X : Feec.Models.Cube.Inhomogeneous.RowSolution T L) :
    TimeStepping.RowSolution T L where
  u := X.u
  u₁ := X.u₁
  u₂ := X.u₂
  u₃ := X.u₃
  isDeg t i y s hs := X.isDeg t i y s hs
  contDiff := X.contDiff
  continuous₁ := X.continuous₁
  continuous₂ := X.continuous₂
  continuous₃ := X.continuous₃
  hasDerivAt₁ := X.hasDerivAt₁
  hasDerivAt₂ := X.hasDerivAt₂
  hasDerivAt₃ := X.hasDerivAt₃
  pde₀ := X.pde₀
  pde₁ := X.pde₁
  pde₂ := X.pde₂
  bound := X.bound
  lipschitz := X.lipschitz
  bound₃ := X.bound₃

/-- The `dx₀` coefficient of the electric field of row `0` of the plane wave. -/
theorem planeWaveRows_apply (T t : ℝ) (y : Fin 3 → ℝ) :
    (planeWaveRows 1 0 1 T 0).u t 1 y {0} = -Real.sin (y 2 - t) := by
  change Feec.Models.Cube.Inhomogeneous.oneForm (fun j => (planeWaveTSD 1 0 1).E t (0, j)) y {0} =
    _
  rw [Feec.Models.Cube.Inhomogeneous.oneForm_apply_singleton]
  simp [planeWaveTSD, planeWave_apply, amplitudeE]

/-- The time derivative of the `dx₀` coefficient of the electric field of row `0` of the plane
wave. -/
theorem planeWaveRows_u₁_apply (T t : ℝ) (y : Fin 3 → ℝ) :
    (planeWaveRows 1 0 1 T 0).u₁ t 1 y {0} = Real.cos (y 2 - t) := by
  have h := ((hasDerivAt_id t).const_sub (y 2)).sin.neg
  simp only [id, mul_neg, mul_one, neg_neg] at h
  refine ((planeWaveRows 1 0 1 T 0).hasDerivAt₁ t 1 y {0}).unique ?_
  simpa only [planeWaveRows_apply, Pi.neg_def] using h

/-- At every time some `y₂ ∈ {1/8, 1/4}` has `sin (2 (y₂ - t)) ≠ 0`: the two arguments differ by
`1/4 ∈ (0, π)`. -/
theorem exists_sin_two_mul_ne_zero (t : ℝ) :
    ∃ a ∈ Ioo (0 : ℝ) (1 / 2), Real.sin (2 * (a - t)) ≠ 0 := by
  by_contra! h
  have h1 := h (1 / 8) ⟨by norm_num, by norm_num⟩
  have h2 := h (1 / 4) ⟨by norm_num, by norm_num⟩
  have hs : 0 < Real.sin (1 / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.two_le_pi])
  have hc : Real.cos (2 * (1 / 8 - t)) ≠ 0 := fun hc => by
    have := Real.sin_sq_add_cos_sq (2 * (1 / 8 - t))
    rw [h1, hc] at this; norm_num at this
  rw [show 2 * ((1 / 4 : ℝ) - t) = 2 * (1 / 8 - t) + 1 / 4 by ring, Real.sin_add, h1, zero_mul,
    zero_add] at h2
  exact mul_ne_zero hc hs.ne' h2

/-- Row `0` of the plane wave is a smooth row solution whose electric field `E` and its time
derivative are nonzero at some point of the cube at every time. -/
theorem exists_rowSolution (T : ℝ) :
    ∃ L, ∃ X : TimeStepping.RowSolution T L, ∀ t, ∃ y ∈ cube 3, X.u t 1 y ≠ 0 ∧ X.u₁ t 1 y ≠ 0 := by
  refine ⟨_, RowSolution.ofFeec (planeWaveRows 1 0 1 T 0), fun t => ?_⟩
  obtain ⟨a, ha, hsin⟩ := exists_sin_two_mul_ne_zero t
  rw [Real.sin_two_mul] at hsin
  refine ⟨fun _ => a, fun i _ => ha, fun h => hsin ?_, fun h => hsin ?_⟩
  · have := congrFun h {0}
    change (planeWaveRows 1 0 1 T 0).u t 1 (fun _ => a) {0} = 0 at this
    rw [planeWaveRows_apply] at this
    have hs : Real.sin (a - t) = 0 := by simpa using this
    simp [hs]
  · have := congrFun h {0}
    change (planeWaveRows 1 0 1 T 0).u₁ t 1 (fun _ => a) {0} = 0 at this
    rw [planeWaveRows_u₁_apply] at this
    have hc : Real.cos (a - t) = 0 := by simpa using this
    simp [hc]

end TimeStepping
