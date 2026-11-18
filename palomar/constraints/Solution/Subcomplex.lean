module

public import Solution.Box

/-!
# Reducing subcomplexes propagate

The third part of `FEEC.constraint_propagation` ([QuennevilleBelair2015], Prop 4.16): a short
complex of the challenge, closed densely defined operators `d⁰`, `d¹` with `d¹ d⁰ = 0`, is a
`Feec.ShortHilbertComplex`; closed `Zⁱ` with `P_{Zⁱ} D(dⁱ) ⊆ D(dⁱ)` and `dⁱ P_{Zⁱ} = P_{Zⁱ⁺¹} dⁱ`
form a reducing subcomplex (`Feec.HilbertComplex.ReducingSubcomplex.of_rel`), whose product is
kept by the strong solutions of the Hodge wave equation
(`Feec.HilbertComplex.ReducingSubcomplex.propagates`), carried by the identity state maps of
`Solution.Box` (the sign of `σ` is the sign convention of the challenge).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.9 (Prop 4.16)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open Set

@[expose] public noncomputable section

universe u

namespace FEEC

open Feec
open Feec.HilbertComplex (totalSub)
open Feec.ShortHilbertComplex (W3 family3 mk3 mem_totalSub_family3)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- **Reducing subcomplexes propagate.** -/
theorem subcomplex_of {W0 W1 W2 : Type u} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
    [CompleteSpace W0] [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    (d0 : W0 →ₗ.[ℝ] W1) (d1 : W1 →ₗ.[ℝ] W2) (hd0 : Dense (d0.domain : Set W0))
    (hd1 : Dense (d1.domain : Set W1)) (hc0 : d0.IsClosed) (hc1 : d1.IsClosed)
    (hcomp : ∀ x : d0.domain, ∃ h : d0 x ∈ d1.domain, d1 ⟨_, h⟩ = 0)
    (Z0 : Submodule ℝ W0) (Z1 : Submodule ℝ W1) (Z2 : Submodule ℝ W2)
    [Z0.HasOrthogonalProjection] [Z1.HasOrthogonalProjection] [Z2.HasOrthogonalProjection]
    (hZ : IsReducingSubcomplex d0 d1 Z0 Z1 Z2) (T : ℝ) (U : ℝ → W0 × W1 × W2) (hU : IsStrongSolution {p | IsHodgeWave d0 d1 p.1 p.2} (Icc 0 T) U)
    (h0 : (U 0).1 ∈ Z0) (h1 : (U 0).2.1 ∈ Z1) (h2 : (U 0).2.2 ∈ Z2) :
    ∀ t ∈ Icc 0 T, (U t).1 ∈ Z0 ∧ (U t).2.1 ∈ Z1 ∧ (U t).2.2 ∈ Z2 := by
  let S : ShortHilbertComplex ℝ W0 W1 W2 :=
    ⟨d0, d1, hd0, hd1, hc0, hc1, fun x => (hcomp x).1, fun x => (hcomp x).2⟩
  have hred : S.toHilbertComplex.ReducingSubcomplex (family3 Z0 Z1 Z2) :=
    HilbertComplex.ReducingSubcomplex.of_rel fun i j hij => by
      fin_cases i <;> fin_cases j <;> simp at hij
      · exact ⟨fun x => (hZ.1 x).1, fun x => (hZ.1 x).2⟩
      · exact ⟨fun x => (hZ.2 x).1, fun x => (hZ.2 x).2⟩
  have hU' := isStrongSolution_toFeec (LinearIsometryEquiv.refl ℝ W0)
    (LinearIsometryEquiv.refl ℝ W1) (LinearIsometryEquiv.refl ℝ W2) S (fun _ _ => Iff.rfl)
    (fun _ _ => Iff.rfl) hU
  have hp := hred.propagates hU' (by
      rw [mem_totalSub_family3]
      exact ⟨Z0.neg_mem h0, h1, h2⟩) fun _ _ => Submodule.zero_mem _
  intro t ht
  obtain ⟨k0, k1, k2⟩ := mem_totalSub_family3.1 (hp t ht)
  have k0' : -(U t).1 ∈ Z0 := k0
  exact ⟨by simpa using Z0.neg_mem k0', k1, k2⟩

end FEEC
