module

public import Feec.Counterexamples.BoundedDomainTSD
public import Feec.Models.Cube.Ident

/-!
# Cubes with the thesis' boundary conditions: only stationary data propagate

On an open cube `∏ (bᵢ, bᵢ + s)` with the thesis' boundary conditions (the minimal grad–curl
complex `H̊¹ → H̊(curl) → L²`), thesis Prop 4.17 fails in two ways:

* **forward invariance forces stationarity**: the forward orbit of a datum under the wave group
  stays in `{0} × S₁ × S₂` (`S₁, S₂ ⊆ L²(TSD)`) iff the datum lies there and is stationary
  (`forward_iff_stationary`); the largest invariant subspace of the thesis' constraint consists
  of the data `(0, 0, B₀)` with `B₀ ∈ L²(TSD)`, `curl B₀ = 0` (`mem_invariantCore_tsd_iff`).
  These are the cube results of `Feec.Models.Cube.Ident` (the complex on `Q = (0, ½)³` is a
  compression of the torus complex, whose wave group has pure point spectrum);
* **TSD data do not propagate**: the cube is a nonempty bounded open set, so the datum
  `(0, 0, β)` of `Feec.Counterexamples.BoundedDomainTSD` leaves the constraint at once
  (`tsd_not_propagates`).

With tensorial mirror boundary conditions instead, TSD data do propagate on every cube
(`Feec.Models.Cube.Mirror.propagatesCube`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17)
-/

open scoped InnerProductSpace LinearPMap
open Set

@[expose] public noncomputable section

namespace Feec.Counterexamples.CubeStationary

open Models.BoundedDomain (R3 Ix gradCurl tsd)
open Models.Cube.Geometry (openCube isOpen_openCube isBounded_openCube)
open Models.Cube.Ident (WC complexCube)
open Domain (L2F)
open HilbertComplex (totalSub)
open ShortHilbertComplex (W3 family3 inj₂)

variable {b : R3} {s : ℝ}

theorem nonempty_openCube (hs : 0 < s) : (openCube b s).Nonempty :=
  ⟨fun i => b i + s / 2, fun i _ => ⟨by linarith, by linarith⟩⟩

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- **On every open cube with the thesis' boundary conditions, TSD data do not propagate**: the
TSD datum `(0, 0, β)` lies in `D(L) ∩ K`, `K = {0} × L²(TSD) × L²(TSD)`, and for every `T > 0`
every strong solution of `U' = L U` from it leaves `K`. [QuennevilleBelair2015], Prop 4.17 (refuted) -/
theorem tsd_not_propagates (hs : 0 < s) :
    ∃ U₀ ∈ (gradCurl ℝ (isOpen_openCube b s)).wave.domain,
      U₀ ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3)))
        (tsd (openCube b s)) (tsd (openCube b s))) ∧
      ∀ T > 0, ∀ U : ℝ → PiLp 2 (W3 (L2F ℝ (openCube b s) (Fin 3))
          (L2F ℝ (openCube b s) Ix) (L2F ℝ (openCube b s) Ix)), U 0 = U₀ →
        Evolution.IsStrongSolution (gradCurl ℝ (isOpen_openCube b s)).wave (Icc 0 T) 0 U →
          ∃ t ∈ Icc 0 T, U t ∉ totalSub (family3
            (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3)))
            (tsd (openCube b s)) (tsd (openCube b s))) :=
  BoundedDomainTSD.tsd_not_propagates (isOpen_openCube b s) (isBounded_openCube b s)
    (nonempty_openCube hs) _ le_rfl

/-- **On every open cube with the thesis' boundary conditions, forward invariance forces
stationarity**, for every `S₁, S₂ ⊆ L²(TSD)`. [QuennevilleBelair2015], Prop 4.17 (refuted) -/
theorem forward_iff_stationary (hs : 0 < s) {S1 S2 : Submodule ℝ (L2F ℝ (openCube b s) Ix)}
    (h1 : S1 ≤ tsd (openCube b s)) (h2 : S2 ≤ tsd (openCube b s)) (y : PiLp 2 (WC b s)) :
    (∀ t, 0 ≤ t → (complexCube b s).waveGroup.S t y ∈
        totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3))) S1 S2)) ↔
      y ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3))) S1 S2) ∧
        y ∈ (complexCube b s).waveGroup.stationary :=
  Models.Cube.Ident.forward_iff hs h1 h2 y

/-- **The largest invariant subspace of the thesis' constraint on a cube** consists of the
stationary data `(0, 0, B₀)`, `B₀ ∈ L²(TSD)`, `curl B₀ = 0`. [QuennevilleBelair2015], Prop 4.17 (refuted) -/
theorem mem_invariantCore_tsd_iff (hs : 0 < s) (y : PiLp 2 (WC b s)) :
    y ∈ (complexCube b s).waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3)))
          (tsd (openCube b s)) (tsd (openCube b s)))) ↔
      ∃ B ∈ tsd (openCube b s), ∃ h : B ∈ ((gradCurl ℝ (isOpen_openCube b s)).d₁†).domain,
        (gradCurl ℝ (isOpen_openCube b s)).d₁† ⟨B, h⟩ = 0 ∧
          y = inj₂ (𝕜 := ℝ) (L2F ℝ (openCube b s) (Fin 3)) (L2F ℝ (openCube b s) Ix)
            (L2F ℝ (openCube b s) Ix) B :=
  Models.Cube.Ident.mem_invariantCore_tsd_iff hs y

end Feec.Counterexamples.CubeStationary
