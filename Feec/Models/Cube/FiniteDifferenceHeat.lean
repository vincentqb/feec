module

public import Feec.ForMathlib.Analysis.FiniteDifference
public import Feec.Models.Cube.MaxNormHeat

/-!
# The heat equation in the maximum norm: the classical finite difference scheme

The heat equation `uₜ = Δu` on the cube `Q = b + (0, s)ⁿ` with homogeneous Dirichlet data,
discretized in space by the classical `(2n + 1)`-point finite difference Laplacian on the uniform
grid of mesh size `h = s / (N + 1)` (`fdLaplacian s N = FiniteDifference.laplacian`, on the
interior nodes `{1, …, N}ⁿ`, `U = 0` at the boundary nodes),
`(Δₕ U)(p) = Σᵢ (U(p + eᵢ) - 2 U(p) + U(p - eᵢ)) / h²`.

The finite difference Laplacian **is** the lumped-mass `P₁` Laplacian of the Freudenthal mesh
(`fdLaplacian_eq`, from the stencil theorem `MaxNormHeat.lumpedLaplacian_apply`), so the finite
difference family `FiniteDifferenceHeat.family` has the same discrete semigroups, resolvents and
rational schemes as `MaxNormHeat.family` (`family_res`, `family_step`): the two methods produce the
same iterates, and the maximum-norm estimates of `MaxNormHeat.maxNormHeat` are those of the finite
difference scheme. The discrete maximum principle is also proved directly on the grid
(`FiniteDifference.isSubMarkovGenerator_laplacian`).

## Main results

**`FiniteDifferenceHeat.finiteDifferenceHeat`** (statement `FiniteDifferenceHeat.Verdict`):
`Δₕ` is the lumped-mass `P₁` Laplacian; `Δₕ` is a sub-Markov generator; consistency
`‖Iₕ Δu - Δₕ Iₕ u‖_∞ ≤ n B h² / 12`; and, against every classical solution, the semidiscrete
(method of lines) error `O(h²)`, backward Euler `O(τ + h²)`, Brenner–Thomée's stability bound
`1 + C'_r √k` and the error of every A-stable rational scheme, all in the maximum norm at the
nodes. `finiteDifferenceHeat_nonvacuous`: the first eigenmode
satisfies the hypotheses.

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15
  (the lumped mass method and the finite difference scheme)
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set Finset NormedSpace Feec.FiniteElement Feec.TimeStepping
open Feec.Models.Cube.Geometry (openCube closedCube)
open Feec.Models.Cube.MaxNormHeat (Nodes Space meshSize interp HeatSolution lumpedLaplacian
  lumpedLaplacian_apply maxNormHeat)

@[expose] public noncomputable section

namespace Feec.Models.Cube.FiniteDifferenceHeat

variable {n : ℕ} {b : Fin n → ℝ} {s : ℝ}

/-- **The finite difference Laplacian** `Δₕ` on the interior nodes `{1, …, N}ⁿ` of the uniform
grid of mesh size `h = s / (N + 1)`, homogeneous Dirichlet data:
`(Δₕ U)(p) = Σᵢ (U(p + eᵢ) - 2 U(p) + U(p - eᵢ)) / h²`. -/
abbrev fdLaplacian (s : ℝ) (N : ℕ) : Space n N →L[ℝ] Space n N :=
  FiniteDifference.laplacian (interiorNodes n (N + 1)) (meshSize s N)

/-- **The finite difference Laplacian is the lumped-mass `P₁` Laplacian** of the Freudenthal
mesh. [Thomee2006], Ch. 15 -/
theorem fdLaplacian_eq (b : Fin n → ℝ) (hs : 0 < s) (N : ℕ) :
    fdLaplacian s N = lumpedLaplacian b hs N := by
  ext U p
  rw [lumpedLaplacian_apply]
  rfl

/-- **The finite difference family**: the Laplacians `Δₕ` on `ℝ^{interior nodes}` with the maximum
norm, a uniformly stable family with `M = 1`. -/
abbrev family (n : ℕ) (s : ℝ) : StableFamily ℝ ℕ :=
  StableFamily.ofSubMarkov (fun N => Nodes n N) (fdLaplacian s) fun _ =>
    FiniteDifference.isSubMarkovGenerator_laplacian _ _

/-- Backward Euler for the finite difference family is backward Euler for the lumped-mass family. -/
theorem family_res (b : Fin n → ℝ) (hs : 0 < s) (τ : ℝ) (N : ℕ) :
    (family n s).res τ N = (MaxNormHeat.family b hs).res τ N := by
  simp only [StableFamily.res, StableFamily.discrete, fdLaplacian_eq b hs]

/-- Every rational scheme for the finite difference family is that of the lumped-mass family. -/
theorem family_step (b : Fin n → ℝ) (hs : 0 < s) (r : RationalScheme) (τ : ℝ) (N : ℕ) :
    (family n s).step r τ N = (MaxNormHeat.family b hs).step r τ N := by
  simp only [StableFamily.step, family_res b hs]

/-! ### The verdict -/

/-- The conclusions of `finiteDifferenceHeat` for the cube `b + (0, s)ⁿ`: the finite difference
Laplacian is the lumped-mass `P₁` Laplacian (so every rational scheme has the same iterates for
both, `family_step`); the discrete maximum principle, consistency, and the semidiscrete, backward
Euler and rational-scheme errors in the maximum norm against every classical solution;
Brenner–Thomée's stability bound, and the verdict of the Banach layer for the family. -/
structure Verdict (b : Fin n → ℝ) (hs : 0 < s) : Prop where
  /-- the finite difference Laplacian is the lumped-mass `P₁` Laplacian of the Freudenthal mesh -/
  eq_lumpedLaplacian (N : ℕ) : fdLaplacian s N = lumpedLaplacian b hs N
  /-- the discrete maximum principle: `e^{tΔₕ}` is positive and contractive in the maximum norm -/
  maximumPrinciple (N : ℕ) : IsSubMarkovGenerator (fdLaplacian (n := n) s N)
  /-- consistency in the maximum norm, `‖Iₕ Δu - Δₕ Iₕ u‖_∞ ≤ n B h² / 12` -/
  consistency (N : ℕ) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 4 u) {B : ℝ}
    (hB : ∀ x ∈ closedCube b s, ∀ i, |(partialDeriv i)^[4] u x| ≤ B)
    (hbd : ∀ x ∈ closedCube b s, x ∉ openCube b s → u x = 0) :
    ‖interp b s N (laplacian u) - fdLaplacian s N (interp b s N u)‖ ≤
      n * B * meshSize s N ^ 2 / 12
  /-- the semidiscrete (method of lines) error against every classical solution -/
  semidiscrete {T : ℝ} (S : HeatSolution b s T) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (v : Space n N) : ‖interp b s N (S.u t) - exp (t • fdLaplacian s N) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + t * S.defect N
  /-- backward Euler, `O(τ + h²)` in the maximum norm -/
  backwardEuler {T : ℝ} (S : HeatSolution b s T) {u₂ : ℝ → (Fin n → ℝ) → ℝ} {B₂ : ℝ}
    (hu₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, HasDerivAt (fun t => S.u₁ t x) (u₂ t x) t)
    (hB₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, |u₂ t x| ≤ B₂) (N : ℕ) {τ : ℝ} (hτ : 0 < τ)
    {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) :
    ‖interp b s N (S.u (k * τ)) - ((family n s).res τ N ^ k) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * (3 / 2 * τ * B₂ + S.defect N)
  /-- Brenner–Thomée's stability bound for every A-stable rational scheme -/
  stable_rational {r : RationalScheme} (hr : r.IsAStable) (N : ℕ) {τ : ℝ} (hτ : 0 < τ) (k : ℕ) :
    ‖(family n s).step r τ N ^ k‖ ≤ 1 + r.sqrtConst * √k
  /-- every A-stable rational scheme of order `p` against every classical solution -/
  rational {T : ℝ} (S : HeatSolution b s T) {r : RationalScheme} (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) (N : ℕ) {τ : ℝ} (hτ : 0 < τ) {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) :
    ‖interp b s N (S.u (k * τ)) - ((family n s).step r τ N ^ k) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * S.defect N +
        r.sharpConst p * (k * τ) * τ ^ p * ‖(fdLaplacian s N ^ (p + 1)) v‖
  /-- the verdict of the Banach layer for the finite difference family (`M = 1`) -/
  banach : (family n s).Verdict

/-- **The heat equation in the maximum norm, finite differences** (the `(2n + 1)`-point scheme on
the uniform grid of the cube `b + (0, s)ⁿ`, Dirichlet data): see `Verdict`. The estimates are
those of the lumped-mass `P₁` method (`MaxNormHeat.maxNormHeat`) through `fdLaplacian_eq`.
[Thomee2006], Ch. 15; [BrennerThomee1979] -/
theorem finiteDifferenceHeat (b : Fin n → ℝ) (hs : 0 < s) : Verdict b hs where
  eq_lumpedLaplacian := fdLaplacian_eq b hs
  maximumPrinciple N := FiniteDifference.isSubMarkovGenerator_laplacian _ _
  consistency N _ hu _ hB hbd := by
    rw [fdLaplacian_eq b hs]; exact (maxNormHeat b hs).consistency N hu hB hbd
  semidiscrete S N _ ht v := by
    rw [fdLaplacian_eq b hs]; exact (maxNormHeat b hs).semidiscrete S N ht v
  backwardEuler S _ _ hu₂ hB₂ N _ hτ _ hk v := by
    rw [family_res b hs]; exact (maxNormHeat b hs).backwardEuler S hu₂ hB₂ N hτ hk v
  stable_rational hr N _ hτ k := by
    rw [family_step b hs]; exact (maxNormHeat b hs).stable_rational hr N hτ k
  rational S _ hr _ hp N _ hτ _ hk v := by
    rw [family_step b hs, fdLaplacian_eq b hs]
    exact (maxNormHeat b hs).rational S hr hp N hτ hk v
  banach := stableFamily _

/-- **The verdict is not vacuous**: the first eigenmode `MaxNormHeat.sineSolution` is a nonzero
classical solution with `|uₜₜ| ≤ λ²`, so all the error clauses apply to it. -/
theorem finiteDifferenceHeat_nonvacuous (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) :
    Verdict b hs ∧ ∃ S : HeatSolution b s T, S.u 0 ≠ 0 ∧
      ∃ (u₂ : ℝ → (Fin n → ℝ) → ℝ) (B₂ : ℝ),
        (∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, HasDerivAt (fun t => S.u₁ t x) (u₂ t x) t) ∧
        ∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, |u₂ t x| ≤ B₂ :=
  have ⟨_, S, hS, h₂, _⟩ := MaxNormHeat.maxNormHeat_nonvacuous b hs T
  ⟨finiteDifferenceHeat b hs, S, hS, h₂⟩

end Feec.Models.Cube.FiniteDifferenceHeat
