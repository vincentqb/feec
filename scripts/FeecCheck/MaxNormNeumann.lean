module

public import Feec.Models.Cube.MaxNormNeumann
public import Feec.Instances.CrownNonVacuity

/-!
# Regression test: the Neumann maximum-norm verdict before time stepping

`Feec.Models.Cube.MaxNormNeumann.Verdict` gained the fields `backwardEuler`, `stable_rational`,
`rational`, `semidiscrete_fe`, `backwardEuler_fe` and `rational_fe` (at the end), and
`Feec.Models.Cube.MaxNormNeumann.maxNormNeumann_nonvacuous` bounds of the second time derivative
and of the second space derivatives of the witness; the field `neumann` of
`Instances.CrownNonVacuity` states the new non-vacuity. Below, the earlier verdict, the earlier
non-vacuity statement and the earlier field `neumann` are stated verbatim and derived from the
new API. The counting functions `upCount`, `downCount` and `vertexCount` moved to
`Feec.FiniteElement` (`Feec.FiniteElement.LumpedMass`) with the level of the mesh as argument
(`vertexCount (N + 1)` for the earlier `vertexCount N`); the earlier `vertexCount` is stated
verbatim as `vertexCount_old`, and the earlier verdict with it.

This file is part of the `FeecCheck` library, not of `Feec`.
-/

@[expose] public noncomputable section

namespace FeecCheck.MaxNormNeumann

open Set Finset NormedSpace Feec.Mesh Feec.FiniteElement Feec.TimeStepping
open Feec.Models.Cube.MaxNormHeat (meshSize)
open Feec.Models.Cube.Geometry (closedCube)
open Feec.Models.Cube.MaxNormNeumann

variable {n : ℕ} {s : ℝ}

/-- The earlier `MaxNormNeumann.vertexCount`, verbatim. -/
def vertexCount_old (N : ℕ) (p : Fin n → ℤ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∑ j, ∑ m : Fin n → Fin (N + 1),
    if finLattice m + kuhnLattice σ j = p then 1 else 0

/-- The earlier `vertexCount N` is `Feec.FiniteElement.vertexCount (N + 1)`. -/
theorem vertexCount_old_eq (N : ℕ) (p : Fin n → ℤ) : vertexCount_old N p = vertexCount (N + 1) p :=
  rfl

/-- The earlier `MaxNormNeumann.Verdict`, verbatim. -/
structure Verdict_old (b : Fin n → ℝ) (hs : 0 < s) : Prop where
  /-- the discrete maximum principle: `e^{tLₕ}` is positive and contractive in the maximum norm -/
  maximumPrinciple (N : ℕ) : IsSubMarkovGenerator (neumannLaplacian b hs N)
  /-- conservation: `Lₕ 𝟙 = 0` -/
  conservation (N : ℕ) : neumannLaplacian b hs N (fun _ => 1) = 0
  /-- the stencil at every node, `(Lₕ Iₕ u)(p) = (n + 1) S_u(p) / C(p)` -/
  stencil (N : ℕ) (u : (Fin n → ℝ) → ℝ) (p : Nodes n N) :
    neumannLaplacian b hs N (interp b s N u) p =
      (n + 1) * stencilSum b s N u p / vertexCount_old N (p : Fin n → ℤ)
  /-- consistency `O(h²)` at the interior nodes -/
  consistency_interior (N : ℕ) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 4 u) {B : ℝ}
    (hB : ∀ x ∈ closedCube b s, ∀ i, |(partialDeriv i)^[4] u x| ≤ B) {p : Nodes n N}
    (hp : (p : Fin n → ℤ) ∈ interiorNodes n (N + 1)) :
    |Feec.Models.Cube.MaxNormHeat.laplacian u (node b (meshSize s N) p) -
        neumannLaplacian b hs N (interp b s N u) p| ≤ n * B * meshSize s N ^ 2 / 12
  /-- consistency `O(1)` at the boundary nodes, for `∂_ν u = 0` -/
  consistency_boundary (N : ℕ) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) {B : ℝ}
    (hB : ∀ x ∈ closedCube b s, ∀ i, |partialDeriv i (partialDeriv i u) x| ≤ B)
    (hneu : ∀ x ∈ closedCube b s, ∀ i, x i = b i ∨ x i = b i + s → partialDeriv i u x = 0)
    (p : Nodes n N) {l : Fin n} (hl : (p : Fin n → ℤ) l = 0 ∨ (p : Fin n → ℤ) l = N + 1) :
    |Feec.Models.Cube.MaxNormHeat.laplacian u (node b (meshSize s N) p) -
        neumannLaplacian b hs N (interp b s N u) p| ≤ n * B * (1 + (n + 1).factorial)
  /-- the barrier: `Lₕ χ ≤ -s / (2 h n!)` at the boundary nodes, `s / h ≥ K_n` -/
  barrier (N : ℕ) (p : Nodes n N) {l : Fin n}
    (hl : (p : Fin n → ℤ) l = 0 ∨ (p : Fin n → ℤ) l = N + 1)
    (hK : layerConst n ≤ s / meshSize s N) :
    neumannLaplacian b hs N (interp b s N (chi b s)) p ≤
      -(s / meshSize s N) / (2 * n.factorial)
  /-- the semidiscrete error `O(h)` in the maximum norm at the nodes -/
  semidiscrete {T : ℝ} (S : NeumannSolution b s T) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (v : Space n N) :
    ‖interp b s N (S.u t) - exp (t • neumannLaplacian b hs N) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + t * S.defect N +
        layerConst n * S.boundaryDefect * meshSize s N * (t / s + s)
  /-- the verdict of the Banach layer for the Neumann family (`M = 1`) -/
  banach : (family b hs).Verdict


/-- The earlier verdict, from the new one. -/
theorem verdict_old (b : Fin n → ℝ) (hs : 0 < s) : Verdict_old b hs :=
  let V := maxNormNeumann b hs
  ⟨V.maximumPrinciple, V.conservation, V.stencil, V.consistency_interior,
    V.consistency_boundary, V.barrier, V.semidiscrete, V.banach⟩

/-- The earlier `MaxNormNeumann.maxNormNeumann_nonvacuous`, verbatim (with `Verdict_old`). -/
theorem maxNormNeumann_nonvacuous_old (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) :
    Verdict_old b hs ∧ ∃ S : NeumannSolution b s T, S.u 0 ≠ 0 := by
  obtain ⟨-, S, h0, -⟩ := maxNormNeumann_nonvacuous b hs T
  exact ⟨verdict_old b hs, S, h0⟩

universe u in
/-- The earlier field `neumann` of `Instances.CrownNonVacuity`, from the new one. -/
theorem crownNonVacuity_neumann_old (h : Feec.Instances.CrownNonVacuity.{u})
    (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) :
    Verdict_old b hs ∧ ∃ S : NeumannSolution b s T, S.u 0 ≠ 0 := by
  obtain ⟨-, S, h0, -⟩ := h.neumann b hs T
  exact ⟨verdict_old b hs, S, h0⟩

end FeecCheck.MaxNormNeumann
