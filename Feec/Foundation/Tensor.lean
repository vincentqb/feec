module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs

/-!
# Feec foundation §G: component tensors

(0,4)-tensors in components, their symmetries, the Minkowski metric, Levi-Civita symbols,
and the row-wise `curl`, `div`, `vskw` of Lemma 3.5.

## References

* [QuennevilleBelair2015], §2.2–2.3 (Minkowski metric, Riemann-tensor symmetries, Prop 2.1),
  §3.1 (Levi-Civita symbol), §3.4 (Lemma 3.5: `curl`, `div`, `vskw`)
* [Wald1984], §3.2 (symmetries of the Riemann tensor)
-/

@[expose] public noncomputable section

namespace Feec

/-! ## §G. Component tensors (Ch 2–3) -/

section Tensor

/-- (0,4)-tensor in components over an index type `ι`.
See [QuennevilleBelair2015, §2.3, §3.2]. -/
abbrev T4 (ι : Type*) := ι → ι → ι → ι → ℝ

variable {ι : Type*}

/-- skew-symmetry in each of the two index pairs.
See [QuennevilleBelair2015, Prop 2.1]; cf. [Wald1984, §3.2]. -/
def PairSkew (C : T4 ι) : Prop :=
  ∀ a b c d, C a b c d = -C b a c d ∧ C a b c d = -C a b d c
/-- first (algebraic) Bianchi identity `C_{a[bcd]} = 0`.
See [QuennevilleBelair2015, Prop 2.1]; cf. [Wald1984, §3.2]. -/
def Bianchi1 (C : T4 ι) : Prop := ∀ a b c d, C a b c d + C a c d b + C a d b c = 0
/-- interchange (pair) symmetry `C_{abcd} = C_{cdab}`.
See [QuennevilleBelair2015, §2.3]; cf. [Wald1984, §3.2]. -/
def Interchange (C : T4 ι) : Prop := ∀ a b c d, C a b c d = C c d a b

/-- Minkowski metric, signature (−+++), diagonal entries.
See [QuennevilleBelair2015, §2.2, §2.7]; cf. [Wald1984]. -/
def η : Fin 4 → ℝ := ![-1, 1, 1, 1]

/-- Levi-Civita symbol on `Fin 3` (determinant of basis rows).
See [QuennevilleBelair2015, §3.1]. -/
def eps3 (i j k : Fin 3) : ℝ :=
  Matrix.det (Matrix.of ![Pi.single i (1 : ℝ), Pi.single j 1, Pi.single k 1])

/-- Levi-Civita symbol on `Fin 4`. See [QuennevilleBelair2015, §3.1]. -/
def eps4 (a b c d : Fin 4) : ℝ :=
  Matrix.det (Matrix.of ![Pi.single a (1 : ℝ), Pi.single b 1, Pi.single c 1, Pi.single d 1])

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

/-- partial derivative of a scalar field on `ℝⁿ` (coordinates). -/
def pd {n : ℕ} (i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

end Tensor

end Feec

/-! Sanity check that the API elaborates. -/
section Checks
open Feec
example : eps3 0 1 2 = 1 := by simp [eps3, Matrix.det_fin_three]
end Checks
