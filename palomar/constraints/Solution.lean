module

public import Solution.Verdicts
public import Solution.MirrorProp
public import Solution.Absorbing
public import Solution.Subcomplex
public import Solution.Window

/-!
# Which boundary conditions keep the TSD constraints (solution)

`FEEC.constraint_propagation`: the fields `group` and `semigroup` from `group_of` and
`semigroup_of` (`Solution.Engine`, Stone's group and the Lumer–Phillips semigroup of `Feec` with
their reducing-subspace criteria and the uniqueness of evolutions), `window` from
`HilbertComplex.window_of` (`Solution.Window`, the windows of `Feec`'s Hilbert complexes), and
`shortComplex` from `subcomplex_of` (`Solution.Subcomplex`).
`FEEC.tsd_boundary_conditions`: the natural boundary conditions on bounded domains, on domains
star-shaped with respect to a ball, on the unit ball and on boxes (`natural_of`, `starShaped_of`,
`ball_of`, `box_of` of `Solution.Verdicts`, through the grad–curl bridge `Solution.GradCurl`, and
`tsd_not_propagates_of` of `Solution.Bounded` for the system with weak symmetry), the absorbing
boundary conditions (`absorbing_of_eq`, `Solution.Absorbing`) and the mirror boundary conditions
(`mirror_tsd_propagates_of`, `Solution.MirrorProp`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10, §6.1, §6.3
* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §III.5.6

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set MeasureTheory LinearPMap

@[expose] public noncomputable section

namespace FEEC

theorem constraint_propagation : PropagationCriterion :=
  ⟨fun L hL hskew => group_of L hL hskew, fun A hdiss hsurj => semigroup_of A hdiss hsurj,
    fun H a m => H.window_of a m,
    fun d0 d1 hd0 hd1 hc0 hc1 hcomp Z0 Z1 Z2 _ _ _ hZ T U hU h0 h1 h2 =>
      subcomplex_of d0 d1 hd0 hd1 hc0 hc1 hcomp Z0 Z1 Z2 hZ T U hU h0 h1 h2⟩

theorem tsd_boundary_conditions : TSDVerdict :=
  have hA := absorbing_of_eq (Feec.Models.Cube.FEM.cubeDomain_eq_Q 3)
    (Feec.Models.Cube.FEM.cubeDomain_eq_Q 2)
  have hM := mirror_tsd_propagates_of
  ⟨fun _ hΩ hb hne => natural_of hΩ hb hne, fun _ hΩ hb hne hstar => starShaped_of hΩ hb hne hstar,
    fun _ hξ v hv hE hC => ball_of _ hξ v hv hE hC, fun _ _ hℓ => box_of hℓ,
    ⟨hA.1, hA.2.1, hA.2.2⟩, ⟨hM.1, hM.2.1, hM.2.2.1, hM.2.2.2⟩⟩

end FEEC
