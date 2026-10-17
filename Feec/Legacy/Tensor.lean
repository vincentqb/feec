module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs

/-!
# Feec foundation §G: component tensors

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

(0,4)-tensors in components, their symmetries, the Minkowski metric, Levi-Civita symbols,
and the row-wise `curl`, `div`, `vskw` of Lemma 3.5.

## References

* [QuennevilleBelair2015], §2.2–2.3 (Minkowski metric, Riemann-tensor symmetries, Prop 2.1),
  §3.1 (Levi-Civita symbol), §3.4 (Lemma 3.5: `curl`, `div`, `vskw`)
* [Wald1984], §3.2 (symmetries of the Riemann tensor)
-/

@[expose] public noncomputable section

namespace Feec.Legacy

/-! ## §G. Component tensors (Ch 2–3) -/

section Tensor

variable {ι : Type*}

/-- Levi-Civita symbol on `Fin 3` (determinant of basis rows).
See [QuennevilleBelair2015, §3.1]. -/
def eps3 (i j k : Fin 3) : ℝ :=
  Matrix.det (Matrix.of ![Pi.single i (1 : ℝ), Pi.single j 1, Pi.single k 1])

/-- first jet of a 3×3 matrix field: `dA c = ∂_c A`. -/
abbrev Jet1 := Fin 3 → Matrix (Fin 3) (Fin 3) ℝ

/-- row-wise curl, thesis convention `(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}`.
See [QuennevilleBelair2015, Lemma 3.5]. -/
def curl (dA : Jet1) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b => ∑ c, ∑ d, eps3 b c d * dA c a d

/-- row-wise divergence `(div A)_a = ∂_b A_{ab}`. See [QuennevilleBelair2015, Lemma 3.5]. -/
def div (dA : Jet1) : Fin 3 → ℝ := fun a => ∑ b, dA b a b

/-- `(vskw A)_a = ½ ε_{abc} A_{bc}`. NB: the BGG map is `S₁ = 2·vskw` (thesis says `vskw`).
See [QuennevilleBelair2015, Lemma 3.5] (definition) and §5.3 (use as the BGG map). -/
def vskw (A : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  fun a => (1 / 2 : ℝ) * ∑ b, ∑ c, eps3 a b c * A b c

end Tensor

end Feec.Legacy

/-! Sanity check that the API elaborates. -/
section Checks
open Feec.Legacy
example : eps3 0 1 2 = 1 := by simp [eps3, Matrix.det_fin_three]
end Checks
