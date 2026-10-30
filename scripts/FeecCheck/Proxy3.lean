module

public import Feec.Algebra.Proxy3

/-!
# Regression tests: the vector proxies of `Feec.Algebra.Proxy3`

The proxies `vec1`, `vec2`, `vol` of polynomial forms are now defined for families of
coefficients in any additive group (with the identities `d = grad, curl, div` proved for any
partial derivatives, `Feec.Koszul.Proxy3.vec1_coordD`, `vec2_coordD`, `vol_coordD`). The theorems
`proxy3_old_*` state the old polynomial definitions verbatim and derive them from the new API.

This file is part of the `FeecCheck` library, not of `Feec`.
-/

public section

namespace FeecCheck.Proxy3

open Feec.Koszul Feec.Koszul.Proxy3

variable {R : Type*} [CommRing R]

/-- The old `vec1 (ω : PolyForm R (Fin 3)) : PolyVec R := fun i => ω {i}`. -/
theorem proxy3_old_vec1 (ω : PolyForm R (Fin 3)) : (vec1 ω : PolyVec R) = fun i => ω {i} := rfl

/-- The old `vec2 (ω : PolyForm R (Fin 3)) : PolyVec R := ![ω {1, 2}, -ω {0, 2}, ω {0, 1}]`. -/
theorem proxy3_old_vec2 (ω : PolyForm R (Fin 3)) :
    (vec2 ω : PolyVec R) = ![ω {1, 2}, -ω {0, 2}, ω {0, 1}] := rfl

/-- The old `vol (ω : PolyForm R (Fin 3)) : MvPolynomial (Fin 3) R := ω {0, 1, 2}`. -/
theorem proxy3_old_vol (ω : PolyForm R (Fin 3)) :
    (vol ω : MvPolynomial (Fin 3) R) = ω {0, 1, 2} := rfl

end FeecCheck.Proxy3
