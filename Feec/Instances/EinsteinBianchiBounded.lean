module

public import Feec.HilbertComplex.Approximation.Crown
public import Feec.Models.Cube.Static
public import Feec.Models.Cube.EigenDense
public import Feec.Models.Box.EigenDense
public import Feec.Models.StarShaped.EigenDense

/-!
# The Einstein–Bianchi system with the thesis' boundary conditions: which data keep TSD

For the thesis' complex `H̊¹(Ω; ℝ³) → H̊(curl, Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)`
(`Feec.Models.BoundedDomain.gradCurl`) on a bounded open `Ω ⊆ ℝ³`, the TSD constraint
`K = {0} × L²(TSD) × L²(TSD)` of the EB system (4.14) is not reducing on cubes
(`Feec.Counterexamples.CubeStationary`), so constraint propagation fails for some data. The FEEC
theorem says for which: for **every** constrained FEEC discretization `G` of the complex with the
constraint `K` (every conforming family of it), every datum `x` and every family of discrete data
`ιₕ vₕ → x`, the residuals `dist(ξₕ(t), K)` tend to `0` at every `t ≥ 0` iff `e^{tL} x ∈ K` for
every `t ≥ 0` (`ConstrainedFEEC.tendsto_infDist_zero_iff`, from the field `tendsto_infDist` of the
verdict). The analysis of the invariant core identifies these data:

* on every bounded open `Ω` with a complete set of eigenvectors (`EigenDense`), they form the
  invariant core `K*` (`residual_tendsto_zero_iff_mem_coreSub`, from
  `Feec.Models.BoundedDomain.gradCurl_coreSub_spectral`); `EigenDense` holds on every domain
  star-shaped with respect to a ball (`starDomain_residual_tendsto_zero_iff`, from Weber
  compactness, `Feec.Models.StarShaped.StarDomain.eigenDense_gradCurl`), in particular on every
  bounded convex set and every ball; there `K*` consists of stationary data iff no TSD eigenfield
  `u` has `curl u ∉ H̊(curl)` (`Feec.Models.BoundedDomain.not_coreSub_le_stationary_iff`, with
  `Feec.Models.StarShaped.coreSub_le_stationary_ball_iff` on balls);
* on every open cube and every box (unequal sides), they are exactly the **stationary** data of
  `K` (`cube_residual_tendsto_zero_iff`, `box_residual_tendsto_zero_iff`, from
  `Feec.Models.Cube.Ident.forward_iff`, `Feec.Models.Box.forward_iff`: the wave group has pure point
  spectrum and only trigonometric polynomials of the wrong parity are TSD), for every
  `{0} × S₁ × S₂` with `S₁, S₂ ⊆ L²(TSD)`;
* on `Q = (0, ½)³` these stationary data form an infinite-dimensional space: the magnetic fields
  `(0, 0, ∇²(e^{-τ x₁} cos(τ x₂)))` (`cube_residual_tendsto_zero_hess`,
  `Feec.Models.Cube.Parity.inj₂_hessQ_mem_invariantCore`;
  `Feec.Models.BoundedDomain.linearIndependent_hessL2_expCos`).

No finite element discretization of the thesis' complex (finite-dimensional subcomplexes with
uniformly bounded commuting projections) is constructed here; the statements hold for every one.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17, corrected), §4.6 (Thm 4.14)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi.Bounded

open Feec.HilbertComplex Feec.ShortHilbertComplex Feec.Models.BoundedDomain
open Feec.Domain (L2F)

variable {κ : Type*}

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- The state space `L²(Ω; ℝ³) × L²(Ω; ℝ³ˣ³) × L²(Ω; ℝ³ˣ³)` of the thesis' complex. -/
abbrev Space (Ω : Set R3) := PiLp 2 (W3 (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))

/-- **The data whose residuals vanish are those of `K*`** on every bounded open `Ω` with a complete
set of eigenvectors: for every discretization `G` of the thesis' complex with the TSD constraint,
every datum `x` and every family `ιₕ vₕ → x`, the residuals tend to `0` at every `t ≥ 0` iff
`x ∈ K*`. [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected), Thm 4.14 -/
theorem residual_tendsto_zero_iff_mem_coreSub {Ω : Set R3} {hΩ : IsOpen Ω}
    (hb : Bornology.IsBounded Ω) (hD : (gradCurl ℝ hΩ).EigenDense)
    (G : ConstrainedFEEC (gradCurl ℝ hΩ).toHilbertComplex κ) [G.l.NeBot]
    (hK : G.K = totalSub (family3 ⊥ (tsd Ω) (tsd Ω))) {x : Space Ω}
    {v : ∀ h, G.toApprox.X h} (hv : G.toApprox.Converges v x) :
    (∀ t, 0 ≤ t → Tendsto (fun h => infDist (G.toApprox.sol h (v h) t) (G.K : Set (Space Ω)))
      G.l (𝓝 0)) ↔ x ∈ (gradCurl ℝ hΩ).coreSub (tsd Ω) (tsd Ω) := by
  rw [G.tendsto_infDist_zero_iff hv, hK]
  exact (gradCurl_coreSub_spectral hΩ hb hD).1 x

/-- **On every domain star-shaped with respect to a ball** (every bounded convex set, every ball),
the data whose residuals vanish are those of `K*`, unconditionally (Weber compactness gives the
complete set of eigenvectors, `Feec.Models.StarShaped.StarDomain.eigenDense_gradCurl`).
[QuennevilleBelair2015], §4.10 (Prop 4.17, corrected) -/
theorem starDomain_residual_tendsto_zero_iff (D : Models.StarShaped.StarDomain 3)
    (G : ConstrainedFEEC (gradCurl ℝ D.isOpen).toHilbertComplex κ) [G.l.NeBot]
    (hK : G.K = totalSub (family3 ⊥ (tsd D.Ω) (tsd D.Ω))) {x : Space D.Ω}
    {v : ∀ h, G.toApprox.X h} (hv : G.toApprox.Converges v x) :
    (∀ t, 0 ≤ t → Tendsto (fun h => infDist (G.toApprox.sol h (v h) t)
      (G.K : Set (Space D.Ω))) G.l (𝓝 0)) ↔
      x ∈ (gradCurl ℝ D.isOpen).coreSub (tsd D.Ω) (tsd D.Ω) :=
  residual_tendsto_zero_iff_mem_coreSub D.isBounded D.eigenDense_gradCurl G hK hv

open Feec.Models.Cube in
/-- **On every open cube the data whose residuals vanish are the stationary data of `K`**: for every
discretization `G` of the thesis' complex on `∏ (bᵢ, bᵢ + s)` with a constraint
`K = {0} × S₁ × S₂`, `S₁, S₂ ⊆ L²(TSD)`, every datum `x` and every family `ιₕ vₕ → x`, the residuals
tend to `0` at every `t ≥ 0` iff `x ∈ K` and `x` is stationary (`L x = 0`).
[QuennevilleBelair2015], §4.10 (Prop 4.17, corrected) -/
theorem cube_residual_tendsto_zero_iff {b : R3} {s : ℝ} (hs : 0 < s)
    {S1 S2 : Submodule ℝ (L2F ℝ (Geometry.openCube b s) Ix)} (h1 : S1 ≤ tsd (Geometry.openCube b s))
    (h2 : S2 ≤ tsd (Geometry.openCube b s)) (G : ConstrainedFEEC (Ident.complexCube b s) κ)
    [G.l.NeBot] (hK : G.K = totalSub (family3 ⊥ S1 S2)) {x : PiLp 2 (Ident.WC b s)}
    {v : ∀ h, G.toApprox.X h} (hv : G.toApprox.Converges v x) :
    (∀ t, 0 ≤ t → Tendsto (fun h => infDist (G.toApprox.sol h (v h) t)
      (G.K : Set (PiLp 2 (Ident.WC b s)))) G.l (𝓝 0)) ↔
      x ∈ G.K ∧ x ∈ (Ident.complexCube b s).waveGroup.stationary := by
  rw [G.tendsto_infDist_zero_iff hv, hK]
  exact Ident.forward_iff hs h1 h2 x

open Feec.Models.Cube in
/-- **The stationary magnetic data of `Q` have vanishing residuals** for every discretization with
the TSD constraint: the Hessians `(0, 0, ∇²(e^{-τ x₁} cos(τ x₂)))` of harmonic functions, linearly
independent for distinct `τ` (`Feec.Models.BoundedDomain.linearIndependent_hessL2_expCos`), lie in
`K*`. [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected) -/
theorem cube_residual_tendsto_zero_hess (G : ConstrainedFEEC RowWise.cubeComplex κ) [G.l.NeBot]
    (hK : G.K = totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (Geometry.Q (Fin 3)) (Fin 3)))
      (tsd (Geometry.Q (Fin 3))) (tsd (Geometry.Q (Fin 3))))) (τ : ℝ)
    {v : ∀ h, G.toApprox.X h}
    (hv : G.toApprox.Converges v (inj₂ (𝕜 := ℝ) (L2F ℝ (Geometry.Q (Fin 3)) (Fin 3))
      (L2F ℝ (Geometry.Q (Fin 3)) Ix) (L2F ℝ (Geometry.Q (Fin 3)) Ix) (Parity.hessQ τ))) (t : ℝ)
    (ht : 0 ≤ t) :
    Tendsto (fun h => infDist (G.toApprox.sol h (v h) t)
      (G.K : Set (PiLp 2 RowWise.WQ))) G.l (𝓝 0) := by
  refine (G.tendsto_infDist_zero_iff hv).2 (fun t _ => ?_) t ht
  rw [hK]
  exact C0Group.mem_invariantCore.1 (Parity.inj₂_hessQ_mem_invariantCore τ) t

open Feec.Models.Box in
/-- **On every box `∏ (aᵢ, aᵢ + ℓᵢ)` the data whose residuals vanish are the stationary data of
`K`**, for every discretization of the thesis' complex with a constraint `{0} × S₁ × S₂`,
`S₁, S₂ ⊆ L²(TSD)`. [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected) -/
theorem box_residual_tendsto_zero_iff {a ℓ : R3} (hℓ : ∀ i, 0 < ℓ i)
    {S1 S2 : Submodule ℝ (L2F ℝ (openBox a ℓ) Ix)} (h1 : S1 ≤ tsd (openBox a ℓ))
    (h2 : S2 ≤ tsd (openBox a ℓ)) (G : ConstrainedFEEC (complexBox a ℓ) κ) [G.l.NeBot]
    (hK : G.K = totalSub (family3 ⊥ S1 S2)) {x : PiLp 2 (WB a ℓ)} {v : ∀ h, G.toApprox.X h}
    (hv : G.toApprox.Converges v x) :
    (∀ t, 0 ≤ t → Tendsto (fun h => infDist (G.toApprox.sol h (v h) t)
      (G.K : Set (PiLp 2 (WB a ℓ)))) G.l (𝓝 0)) ↔
      x ∈ G.K ∧ x ∈ (complexBox a ℓ).waveGroup.stationary := by
  rw [G.tendsto_infDist_zero_iff hv, hK]
  exact forward_iff hℓ h1 h2 x

end Feec.Instances.EinsteinBianchi.Bounded
