module

public import Solution.WhitneyScheme

/-!
# `TimeStepping.crankNicolson_cube`

A smooth row solution of the challenge is `Feec`'s `RowSolution` (`RowSolution.toFeec`: the
challenge's `codiff` is `Feec`'s formal adjoint `formalAdjD`). The Whitney interpolant of a row
is `RowSolution.interp` (`ofD_interp`), the representatives of `U(t)` are `RowSolution.field`
(`toRow_field`), and `TimeStepping.crankNicolson_cube` is
`Feec.Models.Cube.Inhomogeneous.RowSolution.whitney_cn_error_le_row` on the Freudenthal meshes,
with the well-posedness `whitney_existsUnique_cnStep`, the unisolvence of the face integrals
(`isWhitneyInterp_cube_iff`) and `V̊ₕ¹ ≠ 0` (`whitneyMin_one_ne_bot`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set MeasureTheory

@[expose] public noncomputable section

namespace TimeStepping

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.Inhomogeneous
  Feec.HilbertComplex

/-- A smooth row solution of the challenge as a `Feec` row solution. -/
def RowSolution.toFeec {T L : ℝ} (X : TimeStepping.RowSolution T L) :
    Feec.Models.Cube.Inhomogeneous.RowSolution T L where
  u := X.u
  u₁ := X.u₁
  u₂ := X.u₂
  u₃ := X.u₃
  isDeg t i y s hs := X.isDeg t i y s hs
  contDiff := X.contDiff
  continuous₁ := X.continuous₁
  continuous₂ := X.continuous₂
  continuous₃ := X.continuous₃
  hasDerivAt₁ := X.hasDerivAt₁
  hasDerivAt₂ := X.hasDerivAt₂
  hasDerivAt₃ := X.hasDerivAt₃
  pde₀ := X.pde₀
  pde₁ := X.pde₁
  pde₂ := X.pde₂
  bound := X.bound
  lipschitz := X.lipschitz
  bound₃ := X.bound₃

variable {T L : ℝ} (X : TimeStepping.RowSolution T L)

/-- The Whitney interpolant of the challenge's row is `Feec`'s row interpolant. -/
theorem ofD_interp {N : ℕ} {t : ℝ} {w : Row} (h : IsRowInterp (cubeMesh N) (X.u t) w) :
    w = ofD N (X.toFeec.interp N t) := by
  obtain ⟨h0, h1, h2⟩ := h
  have e0 := (isWhitneyInterp_cube_iff N 0 ⟨X.u t 0, X.toFeec.continuous t 0⟩ _).1 h0
  have e1 := (isWhitneyInterp_cube_iff N 1 ⟨X.u t 1, X.toFeec.continuous t 1⟩ _).1 h1
  have e2 := (isWhitneyInterp_cube_iff N 2 ⟨X.u t 2, X.toFeec.continuous t 2⟩ _).1 h2
  exact Prod.ext e0 (Prod.ext e1 e2)

/-- The representatives of `U(t)` are `Feec`'s `RowSolution.field`. -/
theorem toRow_field {t : ℝ} {U : Row} (h0 : IsRepr (cube 3) 0 (X.u t 0) U.1)
    (h1 : IsRepr (cube 3) 1 (X.u t 1) U.2.1) (h2 : IsRepr (cube 3) 2 (X.u t 2) U.2.2) :
    U = toRow (X.toFeec.field t) := by
  have key : ∀ (i : Fin 3) (x : L2F ℝ (cubeDomain 3) (formIdx 3 ((0 : ℤ) + ((i : ℕ) : ℤ)))),
      IsRepr (cube 3) _ (X.u t i) x → x = X.toFeec.field t i := fun i x hx =>
    PiLp.ext fun s => Lp.ext ((hx s).trans (coeFn_formL2 (isOpen_cubeDomain 3).measurableSet
      (isBounded_cubeDomain 3) _ ⟨X.u t i, X.toFeec.continuous t i⟩ s).symm)
  exact Prod.ext (key 0 _ h0) (Prod.ext (key 1 _ h1) (key 2 _ h2))

include X in
theorem zero_le_L {Δt : ℝ} {M : ℕ} (hΔt : 0 < Δt) (hM : (M : ℝ) * Δt ≤ T) : 0 ≤ L := by
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg M) hΔt.le).trans hM
  have hy : (fun _ : Fin 3 => (1 / 4 : ℝ)) ∈ closure (cube 3) :=
    subset_closure fun i _ => by norm_num
  exact (norm_nonneg _).trans (X.bound 0 ⟨le_rfl, hT⟩ 0 _ hy).1

end TimeStepping
