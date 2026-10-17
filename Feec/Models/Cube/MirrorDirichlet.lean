module

public import Feec.Models.Cube.Mirror
public import Feec.Legacy.MirrorCube.CubeDense

/-!
# The mirror complex on the cube between the minimal and the maximal realizations

The mirror complex on `Q = (0, ½)³` (`Feec.Models.Cube.Mirror.complexQ`) lies between the
**minimal** realizations `H̊¹(Q) → H̊(curl, Q)` (the bounded-domain complex with Dirichlet
conditions, `Feec.Legacy.BoundedDomain.thesisComplex`) and the **maximal** ones:

* `Ident.minimal_le_mirror`: `d^{min} ≤ d^{mirror}` for both differentials, i.e. `H̊¹(Q) ⊆ D(d₀)`
  and `H̊(curl, Q) ⊆ D(d₁)` with the same (weak) derivatives;
* `Ident.mirror_domain_le_maximal`: `H̊(curl, Q) ⊆ D(d₁) ⊆ H(curl, Q)`.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17)
* [Brezis2011], §9.2 (extension by reflection)
-/

open Feec.Legacy

open scoped RealInnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

namespace Feec.Models.Cube

open Feec.Legacy.HilbertComplex2 Feec.ShortHilbertComplex Feec.Legacy.Constraints Feec.Legacy.Torus
  Feec.Legacy.Box
open Feec.Legacy.BoxIdent (cxQ Qr)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

namespace Ident

/-- The minimal realization `H̊¹(Q) → H̊(curl, Q)` is a restriction of the mirror complex on `Q`:
`d^{min} ≤ d^{mirror}` for both differentials. -/
theorem minimal_le_mirror :
    cxQ.d0 ≤ Feec.Legacy.MirrorCube.mirrorCxQ.d0 ∧ cxQ.d1 ≤ Feec.Legacy.MirrorCube.mirrorCxQ.d1 := by
  refine ⟨⟨fun u hu => (Feec.Legacy.MirrorCube.gradClosure_le_mirror ⟨u, hu⟩).1, fun x y hxy => ?_⟩,
    ⟨fun u hu => (Feec.Legacy.MirrorCube.curlClosure_le_mirror ⟨u, hu⟩).1, fun x y hxy => ?_⟩⟩
  · obtain ⟨h, e⟩ := Feec.Legacy.MirrorCube.gradClosure_le_mirror x
    rw [← e]; exact apply_congr' _ _ _ hxy
  · obtain ⟨h, e⟩ := Feec.Legacy.MirrorCube.curlClosure_le_mirror x
    rw [← e]; exact apply_congr' _ _ _ hxy

/-- The mirror curl on `Q` lies between the minimal and the maximal curl:
`H̊(curl, Q) ⊆ D(d₁) ⊆ H(curl, Q)`. -/
theorem mirror_domain_le_maximal :
    Feec.Legacy.BoundedDomain.HcurlZero Qr ⊆
        (Feec.Legacy.MirrorCube.mirrorCxQ.d1.domain : Set Feec.Legacy.MirrorCube.MQ) ∧
      (Feec.Legacy.MirrorCube.mirrorCxQ.d1.domain : Set Feec.Legacy.MirrorCube.MQ) ⊆
        Feec.Legacy.BoundedDomain.HcurlM Qr :=
  Feec.Legacy.MirrorCube.HcurlZero_le_d1_le_HcurlM

end Ident

end Feec.Models.Cube
