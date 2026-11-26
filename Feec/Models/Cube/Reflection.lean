module

public import Feec.Models.Cube.Basic
public import Feec.Models.Torus.GradCurl
public import Feec.HilbertComplex.RestrictScalars

/-!
# Reflections of the torus `𝕋³ = ℝ³/ℤ³` and the real torus grad–curl complex

The reflection group `(ℤ/2)³` of the cube `Q = (0, ½)³`, the signs of the reflections of the
Fourier frequencies, and the torus grad–curl complex as a real Hilbert complex, reduced by its TSD
constraint (`RealTorus.reducingSubcomplex`).

## Main definitions

* `Feec.Models.Cube.ReflGroup`: the reflection group `(ℤ/2)³`.
* `MirrorTorus.sgn`: the signs `s_k(a)` of the frequency reflections.
* `RealTorus.gradCurl`, `RealTorus.constraint`: the torus complex and its TSD constraint over `ℝ`.
-/

@[expose] public noncomputable section

namespace Feec.Models.Cube

/-- The reflection group `(ℤ/2)³` of the cube. -/
abbrev ReflGroup : Type := Multiplicative (Fin 3 → ZMod 2)

end Feec.Models.Cube

/-! ### Reflections of the frequencies -/

namespace Feec.Models.Cube.MirrorTorus

open scoped InnerProductSpace
open Feec.Fourier Feec.Fourier.GradCurl

/-- The sign `s_k(a)`: `-1` if `a = k`, `1` otherwise. -/
def sgn (k a : Fin 3) : ℂ := if a = k then -1 else 1

theorem sgn_mul_self (k a : Fin 3) : sgn k a * sgn k a = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem conj_sgn (k a : Fin 3) : (starRingEnd ℂ) (sgn k a) = sgn k a := by
  unfold sgn; split_ifs <;> simp

theorem leviCivita3_sgn (k b c d : Fin 3) :
    leviCivita3 ℂ b c d * (sgn k c * sgn k d) = -(sgn k b * leviCivita3 ℂ b c d) := by
  fin_cases k <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [sgn, leviCivita3_apply]

theorem freq_flipAt (k : Fin 3) (n : Fin 3 → ℤ) (a : Fin 3) :
    ((Fourier.Torus.freq (Fourier.Torus.flipAt k n) a : ℝ) : ℂ) =
      sgn k a * (Fourier.Torus.freq n a : ℂ) := by
  simp only [Fourier.Torus.freq_apply, Fourier.Torus.flipAt_apply, sgn]
  split_ifs <;> push_cast <;> ring

end Feec.Models.Cube.MirrorTorus

/-! ### The torus grad–curl complex over `ℝ` -/

namespace Feec.Models.Cube.RealTorus

open scoped InnerProductSpace
open MeasureTheory Feec.Fourier Feec.Fourier.GradCurl Feec.ShortHilbertComplex
open Feec.Models.Torus.GradCurl (Space)

theorem isScalarTower (i : Fin 3) : @IsScalarTower ℝ ℂ (Space i) _ _
    (L2.innerProductSpace : InnerProductSpace ℝ (Space i)).toNormedSpace.toModule.toDistribMulAction.toMulAction.toSMul := by
  fin_cases i
  · exact inferInstanceAs (IsScalarTower ℝ ℂ (Lp Vec 2 (Measure.count : Measure (Fin 3 → ℤ))))
  · exact inferInstanceAs (IsScalarTower ℝ ℂ (Lp Mat 2 (Measure.count : Measure (Fin 3 → ℤ))))
  · exact inferInstanceAs (IsScalarTower ℝ ℂ (Lp Mat 2 (Measure.count : Measure (Fin 3 → ℤ))))

attribute [local instance] isScalarTower

theorem real_inner_eq_re (i : Fin 3) (x y : Space i) : ⟪x, y⟫_ℝ = RCLike.re ⟪x, y⟫_ℂ := by
  fin_cases i
  · exact L2.real_inner_eq_re_inner (E := Vec) EuclideanSpace.real_inner_eq_re_inner x y
  · exact L2.real_inner_eq_re_inner (E := Mat) EuclideanSpace.real_inner_eq_re_inner x y
  · exact L2.real_inner_eq_re_inner (E := Mat) EuclideanSpace.real_inner_eq_re_inner x y

/-- The torus grad–curl complex as a real Hilbert complex. -/
abbrev gradCurl : HilbertComplex ℝ ComplexShape.fin3 Space :=
  Models.Torus.GradCurl.complex.restrictScalars

theorem wave_gradCurl : gradCurl.wave = Models.Torus.GradCurl.complex.wave.restrictScalars :=
  HilbertComplex.wave_restrictScalars real_inner_eq_re

/-- The TSD constraint `{0} × L²(TSD) × L²(TSD)` as a real subspace. -/
abbrev constraint (i : Fin 3) :
    @Submodule ℝ (Space i) _ _ (L2.innerProductSpace : InnerProductSpace ℝ (Space i)).toModule :=
  @Submodule.restrictScalars ℝ ℂ (Space i) _ _ _
    (L2.innerProductSpace : InnerProductSpace ℝ (Space i)).toModule _ _ (isScalarTower i)
    (Models.Torus.GradCurl.constraint i)

/-- **The TSD constraint reduces the real torus complex.** -/
theorem reducingSubcomplex : gradCurl.ReducingSubcomplex constraint :=
  Models.Torus.GradCurl.reducingSubcomplex.restrictScalars real_inner_eq_re

end Feec.Models.Cube.RealTorus
