module

public import Feec.Counterexamples.BoundedDomainTSD
public import Feec.Models.Box.EigenDense

/-!
# Boxes with the thesis' boundary conditions: only stationary data propagate

On an open box `B = ∏ (aᵢ, aᵢ + ℓᵢ)` with arbitrary (possibly unequal) sides `ℓᵢ > 0` and the
thesis' boundary conditions (the minimal grad–curl complex `H̊¹ → H̊(curl) → L²`), thesis
Prop 4.17 fails in the same two ways as on cubes (`Feec.Counterexamples.CubeStationary`):

* **forward invariance forces stationarity** (`forward_iff_stationary_box`): the forward orbit of
  a datum under the wave group stays in `{0} × S₁ × S₂` (`S₁, S₂ ⊆ L²(TSD)`) iff the datum lies
  there and is stationary; the largest invariant subspace of the thesis' constraint
  `K = {0} × L²(TSD) × L²(TSD)` consists of the data `(0, 0, B₀)` with `B₀ ∈ L²(TSD)`,
  `curl B₀ = 0` (`mem_invariantCore_tsd_iff_box`), and there is no TSD eigenfield
  (`not_exists_tsd_eigenfield_box`). These are the results of `Feec.Models.Box.EigenDense`: the box
  complex is the compression of the anisotropic torus complex (frequencies `d * 2πn`,
  `dᵢ = 1/(2ℓᵢ)`), whose wave group has pure point spectrum;
* **TSD data do not propagate** (`tsd_not_propagates_box`): the box is a nonempty bounded open
  set, so the datum `(0, 0, β)` of `Feec.Counterexamples.BoundedDomainTSD` leaves the constraint at
  once.

**What remains open.** On a general bounded `Ω` (a ball, a Lipschitz domain) it is not known
whether `K*` contains a moving datum. The strongest general statement is
`Feec.Models.BoundedDomain.not_coreSub_le_stationary_iff` (`Feec.Models.BoundedDomain.MovingTSD`):
under a complete set of eigenvectors (`EigenDense`), `K*` moves iff some nonzero TSD eigenfield
`u` has `curl u ∉ H̊(curl)`; and `EigenDense` is proved on cubes and boxes only
(`Feec.Models.Cube.EigenDense`, `Feec.Models.Box.EigenDense`). The tensorial mirror complexes of
`Feec.Models.Cube.Mirror` are not transported to boxes here.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17)
-/

open scoped InnerProductSpace LinearPMap
open Set

@[expose] public noncomputable section

namespace Feec.Counterexamples.BoxStationary

open Models.BoundedDomain (R3 Ix gradCurl tsd)
open Models.Box (openBox isOpen_openBox isBounded_openBox nonempty_openBox WB complexBox)
open Domain (L2F)
open HilbertComplex (totalSub)
open ShortHilbertComplex (W3 family3 inj₂)

variable {a ℓ : R3}

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- **On every open box with the thesis' boundary conditions, TSD data do not propagate**: the
TSD datum `(0, 0, β)` lies in `D(L) ∩ K`, `K = {0} × L²(TSD) × L²(TSD)`, and for every `T > 0`
every strong solution of `U' = L U` from it leaves `K`.
[QuennevilleBelair2015], Prop 4.17 (refuted) -/
theorem tsd_not_propagates_box (hℓ : ∀ i, 0 < ℓ i) :
    ∃ U₀ ∈ (gradCurl ℝ (isOpen_openBox a ℓ)).wave.domain,
      U₀ ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openBox a ℓ) (Fin 3)))
        (tsd (openBox a ℓ)) (tsd (openBox a ℓ))) ∧
      ∀ T > 0, ∀ U : ℝ → PiLp 2 (W3 (L2F ℝ (openBox a ℓ) (Fin 3))
          (L2F ℝ (openBox a ℓ) Ix) (L2F ℝ (openBox a ℓ) Ix)), U 0 = U₀ →
        Evolution.IsStrongSolution (gradCurl ℝ (isOpen_openBox a ℓ)).wave (Icc 0 T) 0 U →
          ∃ t ∈ Icc 0 T, U t ∉ totalSub (family3
            (⊥ : Submodule ℝ (L2F ℝ (openBox a ℓ) (Fin 3)))
            (tsd (openBox a ℓ)) (tsd (openBox a ℓ))) :=
  BoundedDomainTSD.tsd_not_propagates (isOpen_openBox a ℓ) (isBounded_openBox a ℓ)
    (nonempty_openBox a hℓ) _ le_rfl

/-- **On every open box with the thesis' boundary conditions, forward invariance forces
stationarity**, for every `S₁, S₂ ⊆ L²(TSD)`. [QuennevilleBelair2015], Prop 4.17 (refuted) -/
theorem forward_iff_stationary_box (hℓ : ∀ i, 0 < ℓ i)
    {S1 S2 : Submodule ℝ (L2F ℝ (openBox a ℓ) Ix)}
    (h1 : S1 ≤ tsd (openBox a ℓ)) (h2 : S2 ≤ tsd (openBox a ℓ)) (y : PiLp 2 (WB a ℓ)) :
    (∀ t, 0 ≤ t → (complexBox a ℓ).waveGroup.S t y ∈
        totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openBox a ℓ) (Fin 3))) S1 S2)) ↔
      y ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openBox a ℓ) (Fin 3))) S1 S2) ∧
        y ∈ (complexBox a ℓ).waveGroup.stationary :=
  Models.Box.forward_iff hℓ h1 h2 y

/-- **The largest invariant subspace of the thesis' constraint on a box** consists of the
stationary data `(0, 0, B₀)`, `B₀ ∈ L²(TSD)`, `curl B₀ = 0`.
[QuennevilleBelair2015], Prop 4.17 (refuted) -/
theorem mem_invariantCore_tsd_iff_box (hℓ : ∀ i, 0 < ℓ i) (y : PiLp 2 (WB a ℓ)) :
    y ∈ (complexBox a ℓ).waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openBox a ℓ) (Fin 3)))
          (tsd (openBox a ℓ)) (tsd (openBox a ℓ)))) ↔
      ∃ B ∈ tsd (openBox a ℓ), ∃ h : B ∈ ((gradCurl ℝ (isOpen_openBox a ℓ)).d₁†).domain,
        (gradCurl ℝ (isOpen_openBox a ℓ)).d₁† ⟨B, h⟩ = 0 ∧
          y = inj₂ (𝕜 := ℝ) (L2F ℝ (openBox a ℓ) (Fin 3)) (L2F ℝ (openBox a ℓ) Ix)
            (L2F ℝ (openBox a ℓ) Ix) B :=
  Models.Box.mem_invariantCore_tsd_iff hℓ y

/-- **No TSD eigenfield on a box**: the curl–curl eigenproblem `curl† curl u = ω² u`, `ω > 0`,
has no nonzero solution `u ∈ L²(TSD) ∩ H̊(curl)`. [QuennevilleBelair2015], Prop 4.17 (refuted) -/
theorem not_exists_tsd_eigenfield_box (hℓ : ∀ i, 0 < ℓ i) :
    ¬ ∃ ω : ℝ, 0 < ω ∧ ∃ v : L2F ℝ (openBox a ℓ) Ix, v ≠ 0 ∧ v ∈ tsd (openBox a ℓ) ∧
      (gradCurl ℝ (isOpen_openBox a ℓ)).IsEigenfield ω v :=
  Models.Box.not_exists_tsd_eigenfield_box hℓ

/-- The results apply to boxes with unequal sides, e.g. `(0, 1) × (0, 2) × (0, 3)`. -/
theorem forward_iff_stationary_box_123 {S1 S2 : Submodule ℝ (L2F ℝ (openBox 0 ![1, 2, 3]) Ix)}
    (h1 : S1 ≤ tsd (openBox 0 ![1, 2, 3])) (h2 : S2 ≤ tsd (openBox 0 ![1, 2, 3]))
    (y : PiLp 2 (WB 0 ![1, 2, 3])) :
    (∀ t, 0 ≤ t → (complexBox 0 ![1, 2, 3]).waveGroup.S t y ∈
        totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openBox 0 ![1, 2, 3]) (Fin 3))) S1 S2)) ↔
      y ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openBox 0 ![1, 2, 3]) (Fin 3))) S1 S2) ∧
        y ∈ (complexBox 0 ![1, 2, 3]).waveGroup.stationary :=
  forward_iff_stationary_box (fun i => by fin_cases i <;> norm_num) h1 h2 y

end Feec.Counterexamples.BoxStationary
