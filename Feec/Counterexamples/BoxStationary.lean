module

public import Feec.Counterexamples.BoundedDomainTSD
public import Feec.Models.Box.EigenDense

/-!
# The minimal grad–curl complex on boxes: only stationary data propagate

On an open box with the minimal grad–curl complex `H̊¹ → H̊(curl) → L²` (cf.
[QuennevilleBelair2015], Prop 4.17), only stationary data stay in `{0} × S₁ × S₂`,
`S₁, S₂ ⊆ L²(TSD)`, there is no TSD eigenfield, and the TSD datum `(0, 0, β)` leaves
`{0} × L²(TSD) × L²(TSD)`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10

Bibliography: [references.bib](../../docs/references.bib)
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

/-- On every open box, some datum of `D(L) ∩ K`, `K = {0} × L²(TSD) × L²(TSD)`, has no strong
solution of `U' = L U` staying in `K`. -/
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

/-- On every open box, for `S₁, S₂ ⊆ L²(TSD)`, the forward orbit of `y` stays in
`{0} × S₁ × S₂` iff `y` lies there and is stationary. -/
theorem forward_iff_stationary_box (hℓ : ∀ i, 0 < ℓ i)
    {S1 S2 : Submodule ℝ (L2F ℝ (openBox a ℓ) Ix)}
    (h1 : S1 ≤ tsd (openBox a ℓ)) (h2 : S2 ≤ tsd (openBox a ℓ)) (y : PiLp 2 (WB a ℓ)) :
    (∀ t, 0 ≤ t → (complexBox a ℓ).waveGroup.S t y ∈
        totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openBox a ℓ) (Fin 3))) S1 S2)) ↔
      y ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openBox a ℓ) (Fin 3))) S1 S2) ∧
        y ∈ (complexBox a ℓ).waveGroup.stationary :=
  Models.Box.forward_iff hℓ h1 h2 y

/-- On every open box, the largest invariant subspace of `{0} × L²(TSD) × L²(TSD)` consists of
the data `(0, 0, B₀)` with `B₀ ∈ L²(TSD)` and `curl B₀ = 0`. -/
theorem mem_invariantCore_tsd_iff_box (hℓ : ∀ i, 0 < ℓ i) (y : PiLp 2 (WB a ℓ)) :
    y ∈ (complexBox a ℓ).waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openBox a ℓ) (Fin 3)))
          (tsd (openBox a ℓ)) (tsd (openBox a ℓ)))) ↔
      ∃ B ∈ tsd (openBox a ℓ), ∃ h : B ∈ ((gradCurl ℝ (isOpen_openBox a ℓ)).d₁†).domain,
        (gradCurl ℝ (isOpen_openBox a ℓ)).d₁† ⟨B, h⟩ = 0 ∧
          y = inj₂ (𝕜 := ℝ) (L2F ℝ (openBox a ℓ) (Fin 3)) (L2F ℝ (openBox a ℓ) Ix)
            (L2F ℝ (openBox a ℓ) Ix) B :=
  Models.Box.mem_invariantCore_tsd_iff hℓ y

/-- On every open box, `curl† curl` has no nonzero TSD eigenfield `u ∈ L²(TSD) ∩ H̊(curl)`. -/
theorem not_exists_tsd_eigenfield_box (hℓ : ∀ i, 0 < ℓ i) :
    ¬ ∃ ω : ℝ, 0 < ω ∧ ∃ v : L2F ℝ (openBox a ℓ) Ix, v ≠ 0 ∧ v ∈ tsd (openBox a ℓ) ∧
      (gradCurl ℝ (isOpen_openBox a ℓ)).IsEigenfield ω v :=
  Models.Box.not_exists_tsd_eigenfield_box hℓ

end Feec.Counterexamples.BoxStationary
