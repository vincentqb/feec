module

public import Feec.Foundation
public import Feec.Domain.Complexes
public import Feec.Domain.ConstCoeffOp
public import Feec.Domain.Constrained
public import Feec.Domain.L2Field
public import Feec.Domain.Mollify
public import Feec.Domain.Obstruction
public import Feec.Domain.Operators
public import Feec.Fourier.SpectralGalerkin
public import Feec.Fourier.Weak
public import Feec.Models.BoundedDomain.GradCurl
public import Feec.Models.BoundedDomain.SymCurl
public import Feec.Evolution.Constrained
public import Feec.Evolution.Duhamel
public import Feec.Evolution.Energy
public import Feec.Evolution.Forcing
public import Feec.Evolution.Solution
public import Feec.Evolution.Tangent
public import Feec.Evolution.WellPosed
public import Feec.FiniteElement.Dof
public import Feec.ForMathlib.Analysis.Gronwall
public import Feec.ForMathlib.Analysis.Inequalities
public import Feec.ForMathlib.Calculus.Partial
public import Feec.ForMathlib.Calculus.TimeSlice
public import Feec.ForMathlib.Lp.CountEquiv
public import Feec.ForMathlib.Lp.ProdEquiv
public import Feec.Fourier.BGGSymbol
public import Feec.Fourier.ClosedRange
public import Feec.Fourier.Euclidean
public import Feec.Fourier.ExteriorSymbol
public import Feec.Fourier.FibreReducing
public import Feec.Fourier.GradCurlSymbol
public import Feec.Fourier.Reality
public import Feec.Fourier.SymCurlSymbol
public import Feec.Fourier.SymbolComplex
public import Feec.Fourier.Torus
public import Feec.HilbertComplex.Approximation.CochainProjection
public import Feec.HilbertComplex.Approximation.DiscreteHodge
public import Feec.HilbertComplex.Approximation.MixedError
public import Feec.HilbertComplex.Approximation.SemidiscreteWave
public import Feec.HilbertComplex.Approximation.Subcomplex
public import Feec.HilbertComplex.Basic
public import Feec.HilbertComplex.BGG.Basic
public import Feec.HilbertComplex.BGG.Discrete
public import Feec.HilbertComplex.BGG.TimeDependent
public import Feec.HilbertComplex.BGG.ToComplex
public import Feec.HilbertComplex.BGG.Twisted
public import Feec.HilbertComplex.BGG.WeakSymmetry
public import Feec.HilbertComplex.Compactness
public import Feec.HilbertComplex.Dirac
public import Feec.HilbertComplex.DomainComplex
public import Feec.HilbertComplex.Dual
public import Feec.HilbertComplex.Equivariant
public import Feec.HilbertComplex.Hodge
public import Feec.HilbertComplex.HodgeLaplacian
public import Feec.HilbertComplex.HodgeWave
public import Feec.HilbertComplex.Mixed
public import Feec.HilbertComplex.Reality
public import Feec.HilbertComplex.Reducing
public import Feec.HilbertComplex.Short
public import Feec.HilbertComplex.Transport
public import Feec.HilbertComplex.Window
public import Feec.Models.Euclidean.BGG
public import Feec.Models.Euclidean.DeRham
public import Feec.Models.Euclidean.GradCurl
public import Feec.Models.Euclidean.SymCurl
public import Feec.Models.Torus.BGG
public import Feec.Models.Torus.DeRham
public import Feec.Models.Torus.GradCurl
public import Feec.Models.Torus.SymCurl
public import Feec.Operator.Multiplication
public import Feec.Operator.Resolvent
public import Feec.Semigroup.Basic
public import Feec.Semigroup.Invariance
public import Feec.Semigroup.Perturbation
public import Feec.Semigroup.Spectral
public import Feec.Semigroup.Stone
public import Feec.TimeStepping.BlockMatrix
public import Feec.TimeStepping.Cayley
public import Feec.Variational.BabuskaNecas
public import Feec.Variational.Fortin
public import Feec.Variational.Galerkin
public import Feec.Variational.GalerkinEvolution
public import Feec.Variational.InfSup
public import Feec.Variational.SaddlePoint
public import Feec.Ch2.Curvature
public import Feec.Ch2.Linearized
public import Feec.Ch3.Bivector
public import Feec.Ch3.EB
public import Feec.Ch4.Adjoint
public import Feec.Ch4.BoundedDensity
public import Feec.Ch4.BoundedDomain
public import Feec.Ch4.BoundedDomainExt
public import Feec.Ch4.BoundedInterior
public import Feec.Ch4.BoundedKstar
public import Feec.Ch4.BoundedSalvage
public import Feec.Ch4.BoundedSalvageDim
public import Feec.Ch4.BoundedSalvageMax
public import Feec.Ch4.BoundedSym
public import Feec.Ch4.BoundedSymDual
public import Feec.Ch4.BoundedSymExt
public import Feec.Ch4.Box
public import Feec.Ch4.BoxForward
public import Feec.Ch4.BoxIdent
public import Feec.Ch4.BoxMirror
public import Feec.Ch4.BoxReduce
public import Feec.Ch4.BoxRestrict
public import Feec.Ch4.BoxStatic
public import Feec.Ch4.BoxThesis
public import Feec.Ch4.Constraints
public import Feec.Ch4.Duhamel
public import Feec.Ch4.ErrorEstimate
public import Feec.Ch4.ErrorEstimateDL
public import Feec.Ch4.Existence
public import Feec.Ch4.Galerkin
public import Feec.Ch4.Hodge
public import Feec.Ch4.HodgeW
public import Feec.Ch4.HodgeWave
public import Feec.Ch4.Restriction
public import Feec.Ch4.Stone
public import Feec.Ch4.StoneApplications
public import Feec.Ch4.StoneDuhamel
public import Feec.Ch4.StoneForcing
public import Feec.Ch4.Torus
public import Feec.Ch4.TorusGroup
public import Feec.Ch4.TorusSym
public import Feec.Ch4.TorusWeak
public import Feec.Ch4.Unconditional
public import Feec.Ch4.Whole
public import Feec.Ch4.WholeIdent
public import Feec.Ch4.WholeMul
public import Feec.Ch4.WholeRange
public import Feec.Ch4.WholeReal
public import Feec.Ch4.WholeSym
public import Feec.Ch4.WholeWeak
public import Feec.Ch5.BGG
public import Feec.Ch5.Discrete
public import Feec.Ch6.Bounded
public import Feec.Ch6.TimeDependent
public import Feec.Ch6.Whole
public import Feec.Ch7.CrankNicolson
public import Feec.Repair.C2
public import Feec.Repair.C410
public import Feec.Repair.C417
public import Feec.Repair.C417BggCube
public import Feec.Repair.C417BggTorus
public import Feec.Repair.C417Compress
public import Feec.Repair.C417Cube
public import Feec.Repair.C417CubeDense
public import Feec.Repair.C417Ext
public import Feec.Repair.C417Pi
public import Feec.Repair.C419Cube
public import Feec.Repair.C419Pi
public import Feec.Repair.C67
public import Feec.Repair.C67Minres
public import Feec.Repair.C67Prop62

/-!
# Feec

Formalization of the abstract framework of
V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*,
PhD thesis, University of Minnesota, 2015.

This root module publicly imports every module of the library. `Feec.Foundation` re-exports
its parts `Feec.Foundation.{Operators, Evolution, Complex, BGG, Tensor}`. The modules
`Feec.Repair.*` prove corrected versions of the thesis results listed in `docs/OVERVIEW.md`.

## References

* [QuennevilleBelair2015]
-/
