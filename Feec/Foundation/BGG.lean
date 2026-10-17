module

public import Feec.HilbertComplex.BGG.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Feec foundation §F: BGG data (compatibility layer)

The BGG data of thesis §5.1 now live in `Feec.HilbertComplex.BGG.Basic`, over any ring and, for
`Feec.BGG.Data`, for complexes of any length. `Feec.BGGData` is the real one-segment case
`Feec.BGG.Segment ℝ`; the old statements below are thin shims over the new results.

## References

* [QuennevilleBelair2015], §5.1 (BGG data, complex (5.1))
* [ArnoldHu2021] (complexes from complexes: the BGG-type construction behind `BGGData`)
-/

@[expose] public noncomputable section

namespace Feec

/-- Top complex `V0 → V1 → W2`, bottom complex `Ṽ0 → Ṽ1 → W̃2`, connecting maps
`S0 : Ṽ0 → V1`, `S1 : Ṽ1 → W2`, anticommuting: the real case of `Feec.BGG.Segment`.
See [QuennevilleBelair2015, §5.1]; cf. [ArnoldHu2021]. -/
abbrev BGGData (V0 V1 W2 Vt0 Vt1 Wt2 : Type*)
    [AddCommGroup V0] [Module ℝ V0] [AddCommGroup V1] [Module ℝ V1]
    [AddCommGroup W2] [Module ℝ W2] [AddCommGroup Vt0] [Module ℝ Vt0]
    [AddCommGroup Vt1] [Module ℝ Vt1] [AddCommGroup Wt2] [Module ℝ Wt2] :=
  BGG.Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2

namespace BGGData

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [AddCommGroup V0] [Module ℝ V0] [AddCommGroup V1] [Module ℝ V1]
  [AddCommGroup W2] [Module ℝ W2] [AddCommGroup Vt0] [Module ℝ Vt0]
  [AddCommGroup Vt1] [Module ℝ Vt1] [AddCommGroup Wt2] [Module ℝ Wt2]
  (D : BGGData V0 V1 W2 Vt0 Vt1 Wt2)

theorem mem_Γ {x : V0 × Vt0} : x ∈ D.Γ ↔ D.d0 x.1 = D.S0 x.2 := BGG.Segment.mem_Γ D

/-- (5.1) is a complex. See [QuennevilleBelair2015, §5.1]; cf. [ArnoldHu2021]. -/
theorem D1_D0 (x : D.Γ) : D.D1 (D.D0 x) = 0 := BGG.Segment.D1_D0 D x

end BGGData

end Feec
