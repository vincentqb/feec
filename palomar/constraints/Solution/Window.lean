module

public import Solution.Engine
public import Feec.HilbertComplex.Window
public import Feec.HilbertComplex.Dirac
public import Feec.HilbertComplex.HodgeHeat
public import Feec.HilbertComplex.Reducing

/-!
# Windows of Hilbert complexes

The field `window` of `FEEC.PropagationCriterion`. A Hilbert complex of the challenge is a
`Feec.HilbertComplex` on `ComplexShape.up ℤ` (`HilbertComplex.toFeec`, the same fields), and its
window `[a, a + m)` (`Feec.HilbertComplex.window`) has the challenge's total differential, wave
operator and heat operator (`totalD_eq`, `wave_eq`, `heat_eq`, as in `palomar/feec`). So the wave
operator is densely defined and skew-adjoint (`Feec.HilbertComplex.dense_wave_domain`,
`Feec.HilbertComplex.isSkewAdjoint_wave`), its square `-Δ` is m-dissipative
(`Feec.HilbertComplex.isMDissipative_neg_hodgeLaplacian`), and the product of a reducing
subcomplex reduces the wave operator (`Feec.HilbertComplex.ReducingSubcomplex.isReducing_wave`),
hence is kept by Stone's group, which every evolution is (`group_of` of `Solution.Engine`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4 (Thm 4.6), §4.9 (Prop 4.16)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex

variable (H : HilbertComplex 𝕜 W) (a : ℤ) (m : ℕ)

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

omit [∀ i, CompleteSpace (W i)] in
theorem sq_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) :
    sq A = A.sq := by
  have hd : (sq A).domain = A.sq.domain := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hx⟩
      exact ⟨hx, hy⟩
    · rintro ⟨hx, hAx⟩
      exact ⟨Submodule.mem_map.2 ⟨⟨x, hx⟩, hAx, rfl⟩, hx⟩
  exact LinearPMap.ext hd fun x hx hy => rfl

theorem heat_eq : sq (H.wave a m) = -(H.toFeec.window a m).hodgeLaplacian := by
  rw [sq_eq, wave_eq, Feec.HilbertComplex.hodgeLaplacian, neg_neg]

/-- **The window of a Hilbert complex**: the wave operator is densely defined and skew-adjoint,
the heat operator is m-dissipative, and every evolution of the wave operator keeps the product of
a reducing subcomplex. -/
theorem window_of [∀ i, NormedSpace ℝ (W i)] :
    Dense ((H.wave a m).domain : Set (Total W a m)) ∧ (H.wave a m)† = -H.wave a m ∧
      (∀ x : (sq (H.wave a m)).domain,
        RCLike.re ⟪sq (H.wave a m) x, (x : Total W a m)⟫_𝕜 ≤ 0) ∧
      (∀ y, ∃ x : (sq (H.wave a m)).domain, (x : Total W a m) - sq (H.wave a m) x = y) ∧
      ∀ (Z : ∀ i, Submodule 𝕜 (W i)) [∀ i, (Z i).HasOrthogonalProjection],
        (∀ i j (x : (H.d i j).domain), ∃ hx : (Z i).starProjection (x : W i) ∈ (H.d i j).domain,
          H.d i j ⟨_, hx⟩ = (Z j).starProjection (H.d i j x)) →
        ∀ S, IsEvolution 𝕜 (H.wave a m).graph univ S → ∀ t (x : Total W a m),
          (∀ i : Fin m, x i ∈ Z (a + (i : ℕ))) → ∀ i : Fin m, S t x i ∈ Z (a + (i : ℕ)) := by
  have hD : Dense ((H.wave a m).domain : Set (Total W a m)) := by
    rw [wave_eq]; exact (H.toFeec.window a m).dense_wave_domain
  have hskew : (H.wave a m)† = -H.wave a m := by
    rw [wave_eq]; exact (H.toFeec.window a m).isSkewAdjoint_wave
  have hM : (sq (H.wave a m)).IsMDissipative := by
    rw [heat_eq]; exact (H.toFeec.window a m).isMDissipative_neg_hodgeLaplacian
  refine ⟨hD, hskew, hM.dissipative, fun y => by simpa using hM.surjective one_pos y,
    fun Z _ hZ S hS t x hx i => ?_⟩
  have hR : (H.toFeec.window a m).ReducingSubcomplex fun i : Fin m => Z (a + (i : ℕ)) :=
    ⟨fun i j => ⟨fun x => (hZ _ _ x).1, fun x => (hZ _ _ x).2⟩⟩
  have hred : IsReducing (H.wave a m)
      (Feec.HilbertComplex.totalSub fun i : Fin m => Z (a + (i : ℕ))) := by
    rw [isReducing_iff, wave_eq]
    exact hR.isReducing_wave
  obtain ⟨S₀, -, huniq, -, -, hK⟩ := group_of (H.wave a m) hD hskew
  rw [huniq S hS]
  exact ((hK _).1.1 hred) t x hx i

end HilbertComplex

end FEEC
