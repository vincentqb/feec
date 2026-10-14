module

public import Feec.Foundation
public import Feec.Ch2.Curvature
public import Feec.Ch2.Linearized
public import Feec.Ch3.Bivector
public import Feec.Ch3.EB
public import Feec.Ch4.Adjoint
public import Feec.Ch4.Constraints
public import Feec.Ch4.ErrorEstimate
public import Feec.Ch4.Existence
public import Feec.Ch4.Galerkin
public import Feec.Ch4.Hodge
public import Feec.Ch4.HodgeW
public import Feec.Ch4.HodgeWave
public import Feec.Ch4.Restriction
public import Feec.Ch4.Torus
public import Feec.Ch5.BGG
public import Feec.Ch5.Discrete
public import Feec.Ch6.TimeDependent
public import Feec.Ch7.CrankNicolson

/-!
# Feec

Formalization of the abstract framework of
V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*,
PhD thesis, University of Minnesota, 2015.

This root module publicly imports every module of the library. `Feec.Foundation` re-exports
its parts `Feec.Foundation.{Operators, Evolution, Complex, BGG, Tensor}`.

## References

* [QuennevilleBelair2015]
-/
