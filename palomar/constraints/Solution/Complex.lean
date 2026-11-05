module

public import Solution.General
public import Feec.HilbertComplex.Dirac
public import Feec.HilbertComplex.Reducing

/-!
# Hilbert complexes (solution)

A Hilbert complex of the challenge is a `Feec.HilbertComplex` on `ComplexShape.up ℤ` with the
same fields (`HilbertComplex.toFeec`, as in `palomar/feec`), and the wave operator of a window is
that of the `Feec` window `toFeec.window a m` (`wave_eq`). Its skew-adjointness is
`Feec.HilbertComplex.isSkewAdjoint_wave`; a reducing subcomplex of the challenge restricts to a
`Feec.HilbertComplex.ReducingSubcomplex` of the window, whose total space reduces the wave
operator (`Feec.HilbertComplex.ReducingSubcomplex.isReducing_wave`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.6, Prop 4.16

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace FEEC.ConstraintPropagation

namespace HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 W) (a : ℤ) (m : ℕ)

/-- The complex as a `Feec` Hilbert complex on `ComplexShape.up ℤ`. -/
def toFeec : Feec.HilbertComplex 𝕜 (ComplexShape.up ℤ) W where
  d := H.d
  shape := H.shape
  dense := H.dense
  closed := H.closed
  mapsTo := H.mapsTo
  d_comp_d := H.d_comp_d

theorem totalD_eq : H.totalD a m = (H.toFeec.window a m).totalD := by
  refine LinearPMap.ext rfl fun x hx hy => ?_
  ext j
  rw [Feec.HilbertComplex.totalD_apply]
  rfl

theorem wave_eq : H.wave a m = (H.toFeec.window a m).wave := by
  rw [wave, totalD_eq, Feec.HilbertComplex.wave_eq]

theorem isSkewAdjoint_wave : IsSkewAdjoint (H.wave a m) := by
  rw [wave_eq]
  exact (H.toFeec.window a m).isSkewAdjoint_wave

theorem isReducing_wave {S : ∀ i, Submodule 𝕜 (W i)} [∀ i, (S i).HasOrthogonalProjection]
    (hS : H.IsReducingSubcomplex S) :
    ∃ (K : Submodule 𝕜 (Total W a m)) (_ : K.HasOrthogonalProjection),
      (∀ x, x ∈ K ↔ ∀ i : Fin m, x i ∈ S (a + (i : ℕ))) ∧ IsReducing (H.wave a m) K := by
  have hR : (H.toFeec.window a m).ReducingSubcomplex fun i : Fin m => S (a + (i : ℕ)) :=
    ⟨fun i j => ⟨fun x => (hS _ _ x).1, fun x => (hS _ _ x).2⟩⟩
  refine ⟨Feec.HilbertComplex.totalSub fun i : Fin m => S (a + (i : ℕ)), inferInstance,
    fun x => Iff.rfl, ?_⟩
  rw [isReducing_iff, wave_eq]
  exact hR.isReducing_wave

end HilbertComplex

end FEEC.ConstraintPropagation
