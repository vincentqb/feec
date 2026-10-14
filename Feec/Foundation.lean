module

public import Feec.Foundation.Operators
public import Feec.Foundation.Evolution
public import Feec.Foundation.Complex
public import Feec.Foundation.BGG
public import Feec.Foundation.Tensor

/-!
# Feec foundation: shared definitions

Sections:
* §A `Feec.Foundation.Operators`
* §B `Feec.Foundation.Evolution`
* §C, §D, §E `Feec.Foundation.Complex`
* §F `Feec.Foundation.BGG`
* §G `Feec.Foundation.Tensor`

Conventions: real scalars only; `open scoped RealInnerProductSpace` (so `⟪x, y⟫ = ⟪x, y⟫_ℝ`);
complexes indexed by explicit segments `k, k+1, k+2` (no `k-1`).
No `axiom`, no `sorry`: missing theory (Hille–Yosida/Stone, Sobolev spaces, traces)
enters only as explicit hypotheses / structure fields.

## References

* [QuennevilleBelair2015], §2.2–2.3 (Minkowski metric, Riemann-tensor symmetries, Prop 2.1),
  §3.1 (Levi-Civita symbol), §3.4 (Lemma 3.5: `curl`, `div`, `vskw`), §4.1 (unbounded operators,
  adjoints, (4.1a)), §4.2 (Hilbert complexes, domain complex, cycles/boundaries/harmonic forms),
  §4.3 (Thm 4.3, Thm 4.4), §4.4 (Hodge wave operator (4.5), Thm 4.6, weak form (4.7)),
  §4.6 (subcomplexes, bounded cochain projections, the form `A`), §5.1 (BGG data, complex (5.1))
* [Arnold2018] (FEEC framework: Hilbert complexes, domain complexes, subcomplexes and bounded
  cochain projections)
* [AFW2010] (closed Hilbert complexes, Hodge decomposition, approximation by subcomplexes with
  bounded cochain projections; the thesis' main FEEC source, cited there as [5])
* [AFW2006] (FEEC, cited by the thesis together with [AFW2010])
* [BruningLesch1992] (unbounded Hilbert complexes; cited by the thesis for §4.2)
* [CazenaveHaraux1998], Prop 4.1.6 and Cor 2.4.9 (the Hille–Yosida corollary the thesis cites for
  Thm 4.3; here only the hypothesis `WellPosedExistence`)
* [Pazy1983], §1.10 (Stone's theorem) and Ch. 4 (inhomogeneous problems): classical background
  for the existence hypothesis
* [ArnoldHu2021] (complexes from complexes: the BGG-type construction behind `BGGData`)
* [Wald1984], §3.2 (symmetries of the Riemann tensor)
-/
