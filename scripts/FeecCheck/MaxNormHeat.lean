module

public import Feec.Models.Cube.MaxNormHeat
public import Feec.Instances.CrownNonVacuity

/-!
# Regression test: the maximum-norm heat verdict before the finite element fields

`Feec.Models.Cube.MaxNormHeat.Verdict` gained the fields `lumpedMass_eq_inner`, `galerkin`,
`semidiscrete_fe`, `backwardEuler_fe` and `rational_fe` (at the end), and
`Feec.Models.Cube.MaxNormHeat.maxNormHeat_nonvacuous` a bound of the second derivatives of the
witness. `MaxNormHeat.lumpedLaplacian` is now the general lumped-mass Laplacian
`Feec.FiniteElement.lumpedLaplacianOn` on the interior nodes, and `MaxNormHeat.lumpedLaplacianFun`
(with `lumpedLaplacianFun_apply`) is gone; `Instances.CrownNonVacuity` gained a last field
`neumann`, and its field `maxNorm` states the new non-vacuity. Below, the earlier verdict, the
earlier non-vacuity statement, the earlier `lumpedLaplacianFun` with its stencil, and the earlier
field `maxNorm` are stated verbatim and derived from the new API, and so are
`Feec.FiniteElement.p1Stiffness_indicator_nonpos` (now with the hypothesis `IsNonobtuse M`) and
the removed `Feec.FiniteElement.fderiv_apply_eq_sum_partialDeriv` (now at the root, general).
The field `nonobtuse` now states `Feec.FiniteElement.IsNonobtuse` of the meshes; the earlier
field (nonpositive off-diagonal stiffness) and the removed wrapper
`Feec.FiniteElement.p1Stiffness_freudenthalMesh_indicator_nonpos` are derived from it with
`Feec.FiniteElement.p1Stiffness_indicator_nonpos`. The extension by zero `MaxNormHeat.ext` is
gone (now `FiniteDifference.zeroExt`, of any finite lattice grid); it is restated below. The
error estimates are now those of the family of non-obtuse meshes `MaxNormHeat.meshes`
(`Feec.FiniteElement.NonobtuseMeshes.maxNormHeat`), and `MaxNormHeat.HeatSolution.hasDerivAt_interp`
is gone; it is restated below.

This file is part of the `FeecCheck` library, not of `Feec`.
-/

@[expose] public noncomputable section

namespace FeecCheck.MaxNormHeat

open Set Finset NormedSpace Feec.Mesh Feec.FiniteElement Feec.TimeStepping
open Feec.Models.Cube.Geometry (openCube closedCube)
open Feec.Models.Cube.MaxNormHeat

variable {n : ℕ} {s : ℝ}

/-- The removed `MaxNormHeat.ext`, verbatim (now `FiniteDifference.zeroExt`). -/
def ext {N : ℕ} (U : Space n N) (q : Fin n → ℤ) : ℝ :=
  if h : q ∈ interiorNodes n (N + 1) then U ⟨q, h⟩ else 0

/-- The earlier `MaxNormHeat.Verdict`, verbatim. -/
structure Verdict_old (b : Fin n → ℝ) (hs : 0 < s) : Prop where
  /-- the Freudenthal meshes are non-obtuse: nonpositive off-diagonal stiffness -/
  nonobtuse (N : ℕ) [NeZero N] {x y : Fin n → ℝ} (hxy : x ≠ y) :
    p1Stiffness (freudenthalMesh b s hs N) (nodalIndicator x) (nodalIndicator y) ≤ 0
  /-- the lumped-mass `P₁` Laplacian is the `(2n + 1)`-point difference Laplacian -/
  stencil (N : ℕ) (U : Space n N) (p : Nodes n N) :
    lumpedLaplacian b hs N U p = ∑ l, (ext U ((p : Fin n → ℤ) + Pi.single l 1) - 2 * U p +
      ext U ((p : Fin n → ℤ) - Pi.single l 1)) / meshSize s N ^ 2
  /-- the discrete maximum principle: `e^{tLₕ}` is positive and contractive in the maximum norm -/
  maximumPrinciple (N : ℕ) : IsSubMarkovGenerator (lumpedLaplacian b hs N)
  /-- consistency in the maximum norm, `‖Iₕ Δu - Lₕ Iₕ u‖_∞ ≤ n B h² / 12` -/
  consistency (N : ℕ) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 4 u) {B : ℝ}
    (hB : ∀ x ∈ closedCube b s, ∀ i, |(partialDeriv i)^[4] u x| ≤ B)
    (hbd : ∀ x ∈ closedCube b s, x ∉ openCube b s → u x = 0) :
    ‖interp b s N (laplacian u) - lumpedLaplacian b hs N (interp b s N u)‖ ≤
      n * B * meshSize s N ^ 2 / 12
  /-- the semidiscrete error against every classical solution -/
  semidiscrete {T : ℝ} (S : HeatSolution b s T) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (v : Space n N) : ‖interp b s N (S.u t) - exp (t • lumpedLaplacian b hs N) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + t * S.defect N
  /-- backward Euler, `O(τ + h²)` in the maximum norm -/
  backwardEuler {T : ℝ} (S : HeatSolution b s T) {u₂ : ℝ → (Fin n → ℝ) → ℝ} {B₂ : ℝ}
    (hu₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, HasDerivAt (fun t => S.u₁ t x) (u₂ t x) t)
    (hB₂ : ∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, |u₂ t x| ≤ B₂) (N : ℕ) {τ : ℝ} (hτ : 0 < τ)
    {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) :
    ‖interp b s N (S.u (k * τ)) - ((family b hs).res τ N ^ k) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * (3 / 2 * τ * B₂ + S.defect N)
  /-- Brenner–Thomée's stability bound for every A-stable rational scheme -/
  stable_rational {r : RationalScheme} (hr : r.IsAStable) (N : ℕ) {τ : ℝ} (hτ : 0 < τ) (k : ℕ) :
    ‖(family b hs).step r τ N ^ k‖ ≤ 1 + r.sqrtConst * √k
  /-- every A-stable rational scheme of order `p` against every classical solution -/
  rational {T : ℝ} (S : HeatSolution b s T) {r : RationalScheme} (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) (N : ℕ) {τ : ℝ} (hτ : 0 < τ) {k : ℕ} (hk : k * τ ≤ T) (v : Space n N) :
    ‖interp b s N (S.u (k * τ)) - ((family b hs).step r τ N ^ k) v‖ ≤
      ‖interp b s N (S.u 0) - v‖ + k * τ * S.defect N +
        r.sharpConst p * (k * τ) * τ ^ p * ‖(lumpedLaplacian b hs N ^ (p + 1)) v‖
  /-- the verdict of the Banach layer for the maximum-norm family (`M = 1`) -/
  banach : (family b hs).Verdict


/-- The earlier verdict, from the new one. -/
theorem verdict_old (b : Fin n → ℝ) (hs : 0 < s) : Verdict_old b hs :=
  let V := maxNormHeat b hs
  ⟨fun N _ _ _ hxy => p1Stiffness_indicator_nonpos _ (V.nonobtuse N) hxy, V.stencil,
    V.maximumPrinciple, V.consistency, V.semidiscrete, V.backwardEuler, V.stable_rational,
    V.rational, V.banach⟩

/-- The earlier `MaxNormHeat.maxNormHeat_nonvacuous`, verbatim (with `Verdict_old`). -/
theorem maxNormHeat_nonvacuous_old (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) :
    Verdict_old b hs ∧ ∃ S : HeatSolution b s T, S.u 0 ≠ 0 ∧
      ∃ (u₂ : ℝ → (Fin n → ℝ) → ℝ) (B₂ : ℝ),
        (∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, HasDerivAt (fun t => S.u₁ t x) (u₂ t x) t) ∧
        ∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, |u₂ t x| ≤ B₂ := by
  obtain ⟨-, S, h0, h2, -⟩ := maxNormHeat_nonvacuous b hs T
  exact ⟨verdict_old b hs, S, h0, h2⟩

variable {N : ℕ}

/-- The earlier `MaxNormHeat.lumpedLaplacianFun`, verbatim. -/
def lumpedLaplacianFun_old (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) : Space n N := fun p =>
  -p1Stiffness (freudenthalMesh b s hs (N + 1)) (nodalIndicator (node b (meshSize s N) p))
    (nodal b s U) / lumpedMass (freudenthalMesh b s hs (N + 1)) (node b (meshSize s N) p)

/-- `MaxNormHeat.lumpedLaplacian` is the earlier `lumpedLaplacianFun`. -/
theorem lumpedLaplacian_eq_old (b : Fin n → ℝ) (hs : 0 < s) (U : Space n N) :
    lumpedLaplacian b hs N U = lumpedLaplacianFun_old b hs U :=
  funext fun p => lumpedLaplacian_apply_eq b hs U p

/-- The earlier `MaxNormHeat.lumpedLaplacianFun_apply`, verbatim (with `lumpedLaplacianFun_old`). -/
theorem lumpedLaplacianFun_apply_old {b : Fin n → ℝ} (hs : 0 < s) (U : Space n N)
    (p : Nodes n N) :
    lumpedLaplacianFun_old b hs U p = ∑ l, (ext U ((p : Fin n → ℤ) + Pi.single l 1) - 2 * U p +
      ext U ((p : Fin n → ℤ) - Pi.single l 1)) / meshSize s N ^ 2 := by
  rw [← lumpedLaplacian_eq_old]
  exact lumpedLaplacian_apply b hs U p

universe u in
/-- The earlier field `maxNorm` of `Instances.CrownNonVacuity`, from the new one. -/
theorem crownNonVacuity_maxNorm_old (h : Feec.Instances.CrownNonVacuity.{u})
    (b : Fin n → ℝ) (hs : 0 < s) (T : ℝ) :
    Verdict_old b hs ∧ ∃ S : HeatSolution b s T, S.u 0 ≠ 0 ∧
      ∃ (u₂ : ℝ → (Fin n → ℝ) → ℝ) (B₂ : ℝ),
        (∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, HasDerivAt (fun t => S.u₁ t x) (u₂ t x) t) ∧
        ∀ t ∈ Icc 0 T, ∀ x ∈ openCube b s, |u₂ t x| ≤ B₂ := by
  obtain ⟨-, S, h0, h2, -⟩ := h.maxNorm b hs T
  exact ⟨verdict_old b hs, S, h0, h2⟩

/-- The earlier `FiniteElement.p1Stiffness_indicator_nonpos`, verbatim. -/
theorem p1Stiffness_indicator_nonpos_old (M : SimplicialMesh n)
    (hM : ∀ T ∈ M.simplices, ∀ j k, j ≠ k →
      baryGrad T.points j ⬝ᵥ baryGrad T.points k ≤ 0)
    {x y : Fin n → ℝ} (hxy : x ≠ y) :
    p1Stiffness M (nodalIndicator x) (nodalIndicator y) ≤ 0 :=
  p1Stiffness_indicator_nonpos M hM hxy

/-- The earlier `FiniteElement.fderiv_apply_eq_sum_partialDeriv`, verbatim. -/
theorem fderiv_apply_eq_sum_partialDeriv_old (f : (Fin n → ℝ) → ℝ) (x v : Fin n → ℝ) :
    fderiv ℝ f x v = ∑ j, v j * partialDeriv j f x :=
  _root_.fderiv_apply_eq_sum_partialDeriv f x v

/-- The earlier `FiniteElement.p1Stiffness_freudenthalMesh_indicator_nonpos`, verbatim. -/
theorem p1Stiffness_freudenthalMesh_indicator_nonpos_old (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s)
    (N : ℕ) [NeZero N] {x y : Fin n → ℝ} (hxy : x ≠ y) :
    p1Stiffness (freudenthalMesh b s hs N) (nodalIndicator x) (nodalIndicator y) ≤ 0 :=
  p1Stiffness_indicator_nonpos _ ((maxNormHeat b hs).nonobtuse N) hxy

/-- The earlier `MaxNormHeat.HeatSolution.hasDerivAt_interp`, verbatim. -/
theorem hasDerivAt_interp_old {b : Fin n → ℝ} {T : ℝ} (S : HeatSolution b s T) (hs : 0 < s)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivAt (fun t => interp b s N (S.u t)) (interp b s N (S.u₁ t)) t :=
  hasDerivAt_pi.2 fun p => S.hasDerivAt t ht _ (node_mem_openCube hs p)

end FeecCheck.MaxNormHeat
