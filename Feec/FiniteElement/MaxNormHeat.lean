module

public import Feec.FiniteElement.LumpedLaplacian
public import Feec.FiniteElement.P1Global
public import Feec.TimeStepping.StableFamily

/-!
# The lumped-mass heat equation in the maximum norm on non-obtuse meshes

A **family of non-obtuse meshes with nodes** (`Feec.FiniteElement.NonobtuseMeshes n κ`) is a
family of simplicial meshes `Mₕ` of domains in `ℝⁿ` (`h : κ`), each non-obtuse
(`Feec.FiniteElement.IsNonobtuse`), with injective nodes `xₕ : ιₕ → ℝⁿ`, `ιₕ` finite. Its
lumped-mass `P₁` Laplacians `Lₕ = lumpedLaplacianOn Mₕ xₕ` (`NonobtuseMeshes.L`) discretize the
heat equation `uₜ = Δu` with homogeneous Dirichlet data at the vertices that are not nodes; when
every vertex is a node (the Neumann case) the boundary condition is the natural one. No shape
regularity, quasi-uniformity or geometry of the domain enters: by the discrete maximum principle
(`Feec.FiniteElement.isSubMarkovGenerator_lumpedLaplacianOn`, Ciarlet–Raviart) every `Lₕ` is a
sub-Markov generator, so the `Lₕ` form a uniformly stable family in the maximum norm at the nodes
(`NonobtuseMeshes.family`, `M = 1`) and the Banach layer (`Feec.TimeStepping.stableFamily`)
applies.

The exact solution `u` enters only through its **nodal consistency error**
`εₕ(t) = ‖Iₕ uₜ(t) - Lₕ Iₕ u(t)‖_∞`, `Iₕ` the nodal interpolant (`NonobtuseMeshes.interp`). This
error depends on the mesh: `O(h²)` for the uniform stencil of the Freudenthal meshes of a cube
(`Feec.Models.Cube.MaxNormHeat.norm_interp_laplacian_sub_le`), only `O(1)` in general (and at the
boundary nodes of the Neumann problem on the cube), so the estimates below are stated with a bound
`ε` of `εₕ` on the time interval and no rate in `h`.

## Main results

**`NonobtuseMeshes.maxNormHeat`** (statement `NonobtuseMeshes.Verdict`): for every family,

1. (**the discrete maximum principle**) `Lₕ` is a sub-Markov generator, and `Lₕ 𝟙 = 0` when every
   vertex of `Mₕ` is a node;
2. (**semidiscrete error**, `norm_interp_sub_exp_le`) if `εₕ ≤ ε` on `[0, t]`,
   `‖Iₕ u(t) - e^{tLₕ} v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + t ε`;
3. (**backward Euler**, `norm_interp_sub_res_pow_le`) if moreover `‖Iₕ uₜₜ‖_∞ ≤ B` on `[0, kτ]`,
   `‖Iₕ u(kτ) - (1 - τLₕ)⁻ᵏ v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + kτ (3/2 τ B + ε)`;
4. (**every A-stable rational scheme** `r`) Brenner–Thomée's stability bound
   `‖r(τLₕ)ᵏ‖_∞ ≤ 1 + C'_r √k` (`norm_step_pow_le`) and, for `r` of order `p`,
   `‖Iₕ u(kτ) - r(τLₕ)ᵏ v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + kτ ε + C_r kτ τᵖ ‖Lₕ^{p+1} v‖_∞`
   (`norm_interp_sub_step_pow_le`);
5. the verdict of the Banach layer for the family (`Feec.TimeStepping.StableFamily.Verdict`);
6. (**the finite element function**, `abs_sub_p1Interp_nodalFun_le`) on a simplex `K` of `Mₕ` of
   diameter `≤ δ` (maximum norm), for `u ∈ C²` with `|∂ᵢ∂ₖ u| ≤ D` on `K` vanishing at the
   vertices of `K` that are not nodes, `|u(y) - U_h(y)| ≤ ‖Iₕ u - U‖_∞ + n² D δ² / 2` at every
   `y ∈ K` (`U_h` the `P₁` function with nodal values `U`,
   `Feec.FiniteElement.abs_sub_p1Interp_le_of_vertices`), so 2–4 bound the error of the finite
   element function in `L^∞` of the meshed domain.

## References

* [P. G. Ciarlet, P.-A. Raviart, *Maximum principle and uniform convergence for the finite element method*][CiarletRaviart1973]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15
  (the lumped mass method and the maximum principle)
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set NormedSpace Feec.Mesh Feec.TimeStepping

@[expose] public noncomputable section

namespace Feec.FiniteElement

/-- A **family of non-obtuse meshes with nodes**: non-obtuse simplicial meshes `Mₕ` (`h : κ`)
with injective nodes `xₕ : ιₕ → ℝⁿ`, `ιₕ` finite. The vertices that are not nodes carry the value
`0` (Dirichlet data); if every vertex is a node the boundary condition is the natural one. -/
structure NonobtuseMeshes (n : ℕ) (κ : Type*) where
  /-- the meshes -/
  mesh : κ → SimplicialMesh n
  /-- the node index sets -/
  Node : κ → Type
  [fintype : ∀ h, Fintype (Node h)]
  /-- the nodes -/
  x : ∀ h, Node h → Fin n → ℝ
  injective : ∀ h, Function.Injective (x h)
  isNonobtuse : ∀ h, IsNonobtuse (mesh h)

attribute [instance] NonobtuseMeshes.fintype

namespace NonobtuseMeshes

variable {n : ℕ} {κ : Type*} (F : NonobtuseMeshes n κ)

/-- The lumped-mass `P₁` Laplacian `Lₕ` of `Mₕ` on the nodes `xₕ`. -/
abbrev L (h : κ) : (F.Node h → ℝ) →L[ℝ] (F.Node h → ℝ) := lumpedLaplacianOn (F.mesh h) (F.x h)

/-- **The discrete maximum principle** (Ciarlet–Raviart): every `Lₕ` is a sub-Markov generator.
[CiarletRaviart1973] -/
theorem isSubMarkovGenerator (h : κ) : IsSubMarkovGenerator (F.L h) :=
  isSubMarkovGenerator_lumpedLaplacianOn (F.isNonobtuse h) (F.injective h)

/-- **The maximum-norm family**: the `Lₕ` on `ℝ^{ιₕ}` with the maximum norm, a uniformly stable
family with `M = 1`. -/
abbrev family : StableFamily ℝ κ :=
  StableFamily.ofSubMarkov F.Node F.L F.isSubMarkovGenerator

/-- The nodal interpolant `(Iₕ u)(p) = u(xₕ p)`. -/
def interp (h : κ) (u : (Fin n → ℝ) → ℝ) : F.Node h → ℝ := fun p => u (F.x h p)

/-- **The semidiscrete error in the maximum norm**: if `u` has time derivative `u₁` at the nodes
on `[0, t]` and nodal consistency error `‖Iₕ u₁ - Lₕ Iₕ u‖_∞ ≤ ε` there,
`‖Iₕ u(t) - e^{tLₕ} v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + t ε`. [Thomee2006], Ch. 15 -/
theorem norm_interp_sub_exp_le (h : κ) {u u₁ : ℝ → (Fin n → ℝ) → ℝ} {t ε : ℝ} (ht : 0 ≤ t)
    (hu : ∀ s ∈ Icc 0 t, ∀ q, HasDerivAt (fun s => u s (F.x h q)) (u₁ s (F.x h q)) s)
    (hε : ∀ s ∈ Icc 0 t, ‖F.interp h (u₁ s) - F.L h (F.interp h (u s))‖ ≤ ε)
    (v : F.Node h → ℝ) :
    ‖F.interp h (u t) - exp (t • F.L h) v‖ ≤ ‖F.interp h (u 0) - v‖ + t * ε := by
  simpa using F.family.norm_sub_exp_le_of_defect h ht (U := fun s => F.interp h (u s))
    (fun s hs => hasDerivAt_pi.2 (hu s hs)) hε v

/-- **Backward Euler in the maximum norm**: if moreover `u₁` has time derivative `u₂` at the nodes
with `‖Iₕ u₂‖_∞ ≤ B` on `[0, kτ]`,
`‖Iₕ u(kτ) - (1 - τLₕ)⁻ᵏ v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + kτ (3/2 τ B + ε)`, unconditionally. -/
theorem norm_interp_sub_res_pow_le {τ : ℝ} (hτ : 0 < τ) (h : κ) {u u₁ u₂ : ℝ → (Fin n → ℝ) → ℝ}
    {k : ℕ} {B ε : ℝ}
    (hu : ∀ s ∈ Icc 0 (k * τ), ∀ q, HasDerivAt (fun s => u s (F.x h q)) (u₁ s (F.x h q)) s)
    (hu₁ : ∀ s ∈ Icc 0 (k * τ), ∀ q, HasDerivAt (fun s => u₁ s (F.x h q)) (u₂ s (F.x h q)) s)
    (hB : ∀ s ∈ Icc 0 (k * τ), ‖F.interp h (u₂ s)‖ ≤ B)
    (hε : ∀ s ∈ Icc 0 (k * τ), ‖F.interp h (u₁ s) - F.L h (F.interp h (u s))‖ ≤ ε)
    (v : F.Node h → ℝ) :
    ‖F.interp h (u (k * τ)) - (F.family.res τ h ^ k) v‖ ≤
      ‖F.interp h (u 0) - v‖ + k * τ * (3 / 2 * τ * B + ε) := by
  simpa using F.family.norm_sub_res_pow_le_of_traj hτ h (U := fun s => F.interp h (u s))
    (U₁ := fun s => F.interp h (u₁ s)) (U₂ := fun s => F.interp h (u₂ s))
    (fun s hs => hasDerivAt_pi.2 (hu s hs)) (fun s hs => hasDerivAt_pi.2 (hu₁ s hs)) hB hε v

/-- **Brenner–Thomée's stability bound in the maximum norm**: `‖r(τLₕ)ᵏ‖_∞ ≤ 1 + C'_r √k` for
every A-stable `r`, uniformly in `h`. [BrennerThomee1979] -/
theorem norm_step_pow_le {r : RationalScheme} (hr : r.IsAStable) {τ : ℝ} (hτ : 0 < τ) (h : κ)
    (k : ℕ) : ‖F.family.step r τ h ^ k‖ ≤ 1 + r.sqrtConst * √k := by
  simpa using F.family.norm_step_pow_le hr hτ h k

/-- **Every A-stable rational scheme in the maximum norm**: for `r` of order `p`,
`‖Iₕ u(kτ) - r(τLₕ)ᵏ v‖_∞ ≤ ‖Iₕ u(0) - v‖_∞ + kτ ε + C_r kτ τᵖ ‖Lₕ^{p+1} v‖_∞`. -/
theorem norm_interp_sub_step_pow_le {r : RationalScheme} (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) (h : κ) {u u₁ : ℝ → (Fin n → ℝ) → ℝ} {k : ℕ}
    {ε : ℝ}
    (hu : ∀ s ∈ Icc 0 (k * τ), ∀ q, HasDerivAt (fun s => u s (F.x h q)) (u₁ s (F.x h q)) s)
    (hε : ∀ s ∈ Icc 0 (k * τ), ‖F.interp h (u₁ s) - F.L h (F.interp h (u s))‖ ≤ ε)
    (v : F.Node h → ℝ) :
    ‖F.interp h (u (k * τ)) - (F.family.step r τ h ^ k) v‖ ≤
      ‖F.interp h (u 0) - v‖ + k * τ * ε +
        r.sharpConst p * (k * τ) * τ ^ p * ‖(F.L h ^ (p + 1)) v‖ := by
  simpa using F.family.norm_sub_step_pow_le_of_traj hr hp hτ h (U := fun s => F.interp h (u s))
    (fun s hs => hasDerivAt_pi.2 (hu s hs)) hε v

/-- **The finite element function in the maximum norm**: on a simplex `K` of `Mₕ` with
`|y - z|_∞ ≤ δ` on `K`, for `u ∈ C²` with `|∂ᵢ∂ₖ u| ≤ D` on `K` vanishing at the vertices of `K`
that are not nodes, `|u(y) - U_h(y)| ≤ ‖Iₕ u - U‖_∞ + n² D δ² / 2` on `K`, `U_h = Π_K U` the
`P₁` function with nodal values `U` (a `P₁` function attains its extrema at the vertices, plus the
`P₁` interpolation error). -/
theorem abs_sub_p1Interp_nodalFun_le (h : κ) {K : Affine.Simplex ℝ (Fin n → ℝ) n}
    {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) {D δ : ℝ}
    (hD : ∀ y ∈ K.closedInterior, ∀ i k, |partialDeriv k (partialDeriv i u) y| ≤ D)
    (hδ : ∀ y ∈ K.closedInterior, ∀ z ∈ K.closedInterior, dist y z ≤ δ)
    (hbd : ∀ j, K.points j ∉ range (F.x h) → u (K.points j) = 0) (U : F.Node h → ℝ)
    {y : Fin n → ℝ} (hy : y ∈ K.closedInterior) :
    |u y - p1Interp K.points (nodalFun (F.x h) U) y| ≤
      ‖F.interp h u - U‖ + n ^ 2 * D * δ ^ 2 / 2 := by
  refine abs_sub_p1Interp_le_of_vertices K hu hD hδ (fun j => ?_) hy
  by_cases hj : K.points j ∈ range (F.x h)
  · obtain ⟨q, hq⟩ := hj
    rw [← hq, nodalFun_apply (F.injective h)]
    simpa [interp, Real.norm_eq_abs] using norm_le_pi_norm (F.interp h u - U) q
  · have : nodalFun (F.x h) U (K.points j) = 0 :=
      Finset.sum_eq_zero fun q _ => ite_eq_right_iff.2 fun e => absurd ⟨q, e⟩ hj
    rw [hbd j hj, this, sub_zero, abs_zero]
    exact norm_nonneg _

/-- The conclusions of `maxNormHeat` for a family of non-obtuse meshes: the discrete maximum
principle, the semidiscrete, backward Euler and rational-scheme errors in terms of the nodal
consistency error, Brenner–Thomée's stability bound, the verdict of the Banach layer, and the
maximum-norm error of the finite element function on the simplices. -/
structure Verdict : Prop where
  /-- the discrete maximum principle: `e^{tLₕ}` is positive and contractive in the maximum norm -/
  maximumPrinciple (h : κ) : IsSubMarkovGenerator (F.L h)
  /-- conservation, `Lₕ 𝟙 = 0`, when every vertex of `Mₕ` is a node -/
  conservation (h : κ) (hV : ∀ T ∈ (F.mesh h).simplices, ∀ j, T.points j ∈ range (F.x h)) :
    F.L h (fun _ => 1) = 0
  /-- the semidiscrete error in terms of the nodal consistency error -/
  semidiscrete (h : κ) {u u₁ : ℝ → (Fin n → ℝ) → ℝ} {t ε : ℝ} (ht : 0 ≤ t)
    (hu : ∀ s ∈ Icc 0 t, ∀ q, HasDerivAt (fun s => u s (F.x h q)) (u₁ s (F.x h q)) s)
    (hε : ∀ s ∈ Icc 0 t, ‖F.interp h (u₁ s) - F.L h (F.interp h (u s))‖ ≤ ε)
    (v : F.Node h → ℝ) :
    ‖F.interp h (u t) - exp (t • F.L h) v‖ ≤ ‖F.interp h (u 0) - v‖ + t * ε
  /-- backward Euler, unconditionally -/
  backwardEuler {τ : ℝ} (hτ : 0 < τ) (h : κ) {u u₁ u₂ : ℝ → (Fin n → ℝ) → ℝ} {k : ℕ} {B ε : ℝ}
    (hu : ∀ s ∈ Icc 0 (k * τ), ∀ q, HasDerivAt (fun s => u s (F.x h q)) (u₁ s (F.x h q)) s)
    (hu₁ : ∀ s ∈ Icc 0 (k * τ), ∀ q, HasDerivAt (fun s => u₁ s (F.x h q)) (u₂ s (F.x h q)) s)
    (hB : ∀ s ∈ Icc 0 (k * τ), ‖F.interp h (u₂ s)‖ ≤ B)
    (hε : ∀ s ∈ Icc 0 (k * τ), ‖F.interp h (u₁ s) - F.L h (F.interp h (u s))‖ ≤ ε)
    (v : F.Node h → ℝ) :
    ‖F.interp h (u (k * τ)) - (F.family.res τ h ^ k) v‖ ≤
      ‖F.interp h (u 0) - v‖ + k * τ * (3 / 2 * τ * B + ε)
  /-- Brenner–Thomée's stability bound for every A-stable rational scheme -/
  stable_rational {r : RationalScheme} (hr : r.IsAStable) {τ : ℝ} (hτ : 0 < τ) (h : κ) (k : ℕ) :
    ‖F.family.step r τ h ^ k‖ ≤ 1 + r.sqrtConst * √k
  /-- every A-stable rational scheme of order `p` -/
  rational {r : RationalScheme} (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ}
    (hτ : 0 < τ) (h : κ) {u u₁ : ℝ → (Fin n → ℝ) → ℝ} {k : ℕ} {ε : ℝ}
    (hu : ∀ s ∈ Icc 0 (k * τ), ∀ q, HasDerivAt (fun s => u s (F.x h q)) (u₁ s (F.x h q)) s)
    (hε : ∀ s ∈ Icc 0 (k * τ), ‖F.interp h (u₁ s) - F.L h (F.interp h (u s))‖ ≤ ε)
    (v : F.Node h → ℝ) :
    ‖F.interp h (u (k * τ)) - (F.family.step r τ h ^ k) v‖ ≤
      ‖F.interp h (u 0) - v‖ + k * τ * ε +
        r.sharpConst p * (k * τ) * τ ^ p * ‖(F.L h ^ (p + 1)) v‖
  /-- the verdict of the Banach layer for the maximum-norm family (`M = 1`) -/
  banach : F.family.Verdict
  /-- the error of the finite element function on a simplex from the nodal error -/
  fe (h : κ) {K : Affine.Simplex ℝ (Fin n → ℝ) n} {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u)
    {D δ : ℝ} (hD : ∀ y ∈ K.closedInterior, ∀ i k, |partialDeriv k (partialDeriv i u) y| ≤ D)
    (hδ : ∀ y ∈ K.closedInterior, ∀ z ∈ K.closedInterior, dist y z ≤ δ)
    (hbd : ∀ j, K.points j ∉ range (F.x h) → u (K.points j) = 0) (U : F.Node h → ℝ)
    {y : Fin n → ℝ} (hy : y ∈ K.closedInterior) :
    |u y - p1Interp K.points (nodalFun (F.x h) U) y| ≤
      ‖F.interp h u - U‖ + n ^ 2 * D * δ ^ 2 / 2

/-- **The lumped-mass heat equation in the maximum norm on non-obtuse meshes**: see `Verdict`.
[CiarletRaviart1973]; [Thomee2006], Ch. 15; [BrennerThomee1979] -/
theorem maxNormHeat : F.Verdict where
  maximumPrinciple := F.isSubMarkovGenerator
  conservation h hV := lumpedLaplacianOn_apply_one (F.injective h) hV
  semidiscrete h _ _ _ _ ht hu hε v := F.norm_interp_sub_exp_le h ht hu hε v
  backwardEuler hτ h _ _ _ _ _ _ hu hu₁ hB hε v := F.norm_interp_sub_res_pow_le hτ h hu hu₁ hB hε v
  stable_rational hr _ hτ h k := F.norm_step_pow_le hr hτ h k
  rational hr _ hp _ hτ h _ _ _ _ hu hε v := F.norm_interp_sub_step_pow_le hr hp hτ h hu hε v
  banach := stableFamily _
  fe h _ _ hu _ _ hD hδ hbd U _ hy := F.abs_sub_p1Interp_nodalFun_le h hu hD hδ hbd U hy

end NonobtuseMeshes

end Feec.FiniteElement
