module

public import Feec.HilbertComplex.BGG.DiscreteWave

/-!
# BGG stability and convergence modulo finite-dimensional harmonic forms

The continuous hypotheses `Feec.BGG.Stability` of [QuennevilleBelair2015], Prop 5.3, require
exactness of both rows of the BGG data (5.1) at `V⁰`, `Ṽ⁰`, `V¹` and `Ṽ¹`. With boundary
conditions on part of the boundary (the mirror conditions of `Feec.Models.Cube.MirrorBGG`), the
rows carry harmonic forms: constants in the top row at `V⁰` (no boundary condition), and the
constant forms `dxₐ` in the components of the bottom row at `Ṽ¹`. This file isolates what the
Ch. 6 convergence theory of `Feec.HilbertComplex.BGG.EllipticProjection` and
`Feec.HilbertComplex.BGG.DiscreteWave` really uses, and generalizes it to finite-dimensional (in
fact arbitrary) harmonic spaces:

* the **top row plays no role** in the Strang bound of the elliptic projection (6.4) and in the
  wave rate (the mass term of the shifted form controls `σ`), so `poinc0` and `exact1` (which fail
  on the top row of the mirror complex) are not needed;
* on the bottom row only the Poincaré inequality on `Ṽ⁰` and a **Hodge decomposition modulo a
  space `𝔥 ⊆ Ṽ¹`** of harmonic forms are used, `v = dψ + w + k`, `‖w‖ ≤ C_p ‖dv‖`, `k ∈ 𝔥`, with
  `𝔥 ⊥ dṼ⁰` and `S₁ 𝔥 = 0` (for the mirror complex `𝔥 = span{dxₐ in the component a}`, whose
  `S₁ = 2 vskw` vanishes because diagonal matrices are symmetric);
* on the discrete side, `𝔥 ⊆ Ṽₕ¹` (the harmonic forms are discrete), so the discrete exactness at
  `Ṽₕ¹` holds modulo `𝔥` (`HarmonicStability.exact_bot_h`) and the harmonic part drops out of the
  consistency error of `S₁,ₕ` (`HarmonicStability.weakConsistency_of_regularPotential_of_bound`).

The results are the Strang bound, the rate of the elliptic projection and the end-to-end `O(h)`
convergence of (6.3) (`HarmonicStability.exists_discreteSolution_norm_sub_le_rate`) under
`HarmonicStability`, which `Stability` implies with `𝔥 = ⊥` (`Stability.toHarmonicStability`).
Each is proved once, under `HarmonicStability`, next to its `Stability` form, which is a
corollary; this module imports them all.

## Main definitions

* `Feec.BGG.HarmonicStability D 𝔥 C_p C_S` (in `Feec.HilbertComplex.BGG.Discrete`): the
  continuous hypotheses modulo `𝔥`.

## Main results

* `Feec.BGG.Stability.toHarmonicStability`, `HarmonicStability.dt0_injective`
  (`Feec.HilbertComplex.BGG.Discrete`).
* `Feec.BGG.HarmonicStability.exact_bot_h` and
  `Feec.BGG.HarmonicStability.weakConsistency_of_regularPotential_of_bound`: the weak consistency
  of `S₁,ₕ` from regular potentials, modulo `𝔥` (`Feec.HilbertComplex.BGG.WeakConsistency`).
* `Feec.BGG.HarmonicStability.strang_shiftedForm_h`, `HarmonicStability.strang_energy`,
  `HarmonicStability.toSegmentH_dt0_injective`, `HarmonicStability.strang_of_isEllipticProjection`:
  the Strang bound of (6.4) (`Feec.HilbertComplex.BGG.EllipticProjection`).
* `Feec.BGG.HarmonicStability.norm_sub_embedH_ellipticProjection_le` and
  **`Feec.BGG.HarmonicStability.exists_discreteSolution_norm_sub_le_rate`**: `O(h)` convergence of
  (6.3) from the elliptic projection of the exact initial state
  (`Feec.HilbertComplex.BGG.DiscreteWave`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 5.3, §6.2 ((6.3), (6.4), Prop 6.2), Thm 4.14
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3 (Hodge decomposition with harmonic forms, discrete harmonic forms)
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002] (Strang lemma)

Bibliography: [references.bib](../../../docs/references.bib)
-/

