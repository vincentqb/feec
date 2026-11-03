module

public import Feec.Models.Cube.AbsorbingFiniteSpeed
public import Feec.Models.Cube.AbsorbingGalerkin

/-!
# The linearized Einstein–Bianchi system on the cube with absorbing boundary conditions

The row-wise system `Ė = -curl B`, `Ḃ = curl E` on `Q = (0, ½)³` with the absorbing
(Silver–Müller) condition `n × Eᵢ + (Bᵢ)_τ = 0` (`Feec.Models.Cube.Absorbing`), as an instance of
the dissipative FEEC theorem `Feec.HilbertComplex.dissipFEEC`. **`absorbingVerdict`** bundles:

1. **well-posedness and radiation**: the generator is m-dissipative, smooth states with the
   boundary condition are in its domain, the energy decreases by twice the outgoing flux
   `∫₀ᵗ ‖E_τ‖²_{L²(∂Q)}`, strictly from some state;
2. **the constraint**: the Gauss laws propagate from TSD data and TSD holds on the domain of dependence of TSD
   data, but **TSD is not invariant** (`Feec.Models.Cube.Absorbing.not_invariant_tsdPair`): the
   naive absorbing condition is not constraint preserving;
3. **finite speed**: the absorbing solution equals every weak solution of the system in `Q` with
   the same data on the domain of dependence;
4. **the semi-discrete scheme** with the boundary term (dense-sequence Galerkin spaces): the
   `dissipFEEC` verdict with a dense core, convergence for every datum, the discrete energy
   identity, and TSD residuals with a positive limit.

Open: a constraint-preserving absorbing condition (in the sense of
[FriedrichNagy1999], [KreissWinicour2006], [CPRST2003]); the ball; finite element spaces on the
Freudenthal meshes (conformity in the energy space, approximation including the boundary term,
rate classes); the identification of the energy space with the Green-triple space; that smooth
states with the boundary condition form a core, the converse of
`Feec.Models.Cube.Absorbing.mem_domain_of_smooth`, and density of tangential traces of smooth
fields in `L²(∂Q)`; weak solutions other than the absorbing orbits for the finite-speed clause.

## References

* [H. Friedrich, G. Nagy, *The Initial Boundary Value Problem for Einstein's Vacuum Field Equation*][FriedrichNagy1999]
* [H.-O. Kreiss, J. Winicour, *Problems which are well posed in a generalized sense with applications to the Einstein equations*][KreissWinicour2006]
* [G. Calabrese, J. Pullin, O. Reula, O. Sarbach, M. Tiglio, *Well Posed Constraint-Preserving Boundary Conditions for the Linearized Einstein Equations*][CPRST2003]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §3.4 (the system), §4.10 (bounded domains)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set MeasureTheory Filter Topology Metric Feec.HilbertComplex Feec.Domain
open Feec.Models.BoundedDomain

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi

open Feec.Models.Cube.Absorbing Feec.Models.Cube.Geometry

/-- **The absorbing verdict**: the verdict of the dissipative FEEC theorem for the semi-discrete
scheme `absorbingGalerkin` with its dense core (`K = tsdPair`), and the instance-only fields:
well-posedness and radiation, the constraint (Gauss laws, TSD on the domain of dependence, TSD
not invariant), finite speed, and the discrete energy identity and TSD residuals of positive
limit of the scheme. -/
structure AbsorbingVerdict : Prop extends absorbingGalerkin.Verdict absorbingGalerkinCore where
  /-- the generator is m-dissipative -/
  isMDissipative : absorbing.IsMDissipative
  /-- smooth states with the boundary condition `n × E + B_τ = 0` are in the domain, where the
  generator is `(-curl B, curl E)` and the trace is `E_τ` -/
  smooth_mem_domain (E B : C1Field) (hEB : E.tan + B.flux = 0) :
    ∃ h : (WithLp.toLp 2 (E.l2, B.l2) : State) ∈ absorbing.domain,
      absorbing ⟨_, h⟩ = WithLp.toLp 2 (-B.curlL2, E.curlL2) ∧
        impedanceTriple.trace ⟨_, h⟩ = E.tan
  /-- the energy decreases by twice the outgoing flux `∫₀ᵗ ‖E_τ‖²_{L²(∂Q)}` -/
  energy_flux (u₀ : absorbing.domain) (t : ℝ) (ht : 0 ≤ t) :
    ‖absorbingSemigroup.S t u₀‖ ^ 2 = ‖(u₀ : State)‖ ^ 2 -
      2 * ∫ s in (0 : ℝ)..t, ‖impedanceTriple.traceExt (absorbingSemigroup.S s u₀)‖ ^ 2
  /-- strictly from some state -/
  exists_inner_neg : ∃ u : absorbing.domain, ⟪absorbing u, (u : State)⟫_ℝ < 0
  /-- the Gauss laws propagate from TSD data -/
  gauss (u₀ : State) (hu₀ : u₀ ∈ tsdPair) (t : ℝ) (ht : 0 ≤ t) (φ : Fin 3 → R3 → ℝ)
    (hφ : IsTestField (Q (Fin 3)) φ) :
    (∑ ij : Ix, ∫ x in Q (Fin 3), (absorbingSemigroup.S t u₀).fst ij x *
      partialDeriv ij.2 (φ ij.1) x = 0) ∧
    ∑ ij : Ix, ∫ x in Q (Fin 3), (absorbingSemigroup.S t u₀).snd ij x * partialDeriv ij.2 (φ ij.1) x = 0
  /-- TSD holds on the domain of dependence of TSD data -/
  symTF_depDomain (u₀ : State) (hu₀ : u₀ ∈ tsdPair) (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ y ∂volume.restrict (depDomain (Q (Fin 3)) t),
      SymTF (absorbingSemigroup.S t u₀).fst y ∧ SymTF (absorbingSemigroup.S t u₀).snd y
  /-- but TSD is not invariant -/
  not_invariant : ¬ ∀ t, 0 ≤ t → ∀ x ∈ tsdPair, absorbingSemigroup.S t x ∈ tsdPair
  /-- (**finite speed**) the absorbing solution equals every weak solution of the system in `Q`
  with the same data on the domain of dependence -/
  eq_depDomain (T : ℝ) (u₀ : State) (W : ℝ → State) (hW : IsWeakRowEB T W) (hW0 : W 0 = u₀)
    (t : ℝ) (ht : t ∈ Icc 0 T) (j : FIdx) :
    ∀ᵐ y ∂volume.restrict (depDomain (Q (Fin 3)) t),
      toField (absorbingSemigroup.S t u₀) j y = toField (W t) j y
  /-- the core of the scheme is dense -/
  dense_core : absorbingGalerkinCore.Data.topologicalClosure = ⊤
  /-- the discrete energy decreases by twice the discrete outgoing flux -/
  discrete_energy_flux (n : ℕ) (x : absorbingGalerkin.X n) (t : ℝ) (ht : 0 ≤ t) :
    ‖absorbingGalerkin.sol n x t‖ ^ 2 = ‖absorbingGalerkin.incl n x‖ ^ 2 -
      2 * ∫ s in (0 : ℝ)..t,
        ‖galerkinData.Γh n ((C0Group.ofBounded (galerkinData.Lh n)).S s x).fst‖ ^ 2
  /-- before every `T > 0` some TSD datum leaves TSD, and the TSD residuals of every convergent
  family of discrete solutions tend to its positive residual -/
  residual_not_invariant (T : ℝ) (hT : 0 < T) :
    ∃ x ∈ tsdPair, ∃ t ∈ Icc 0 T, absorbingSemigroup.S t x ∉ tsdPair ∧
      0 < infDist (absorbingSemigroup.S t x) (tsdPair : Set State) ∧
      Tendsto (fun n => absorbingGalerkin.incl n (absorbingGalerkin.proj n x)) atTop (𝓝 x) ∧
      ∀ v : ∀ n, absorbingGalerkin.X n,
        Tendsto (fun n => absorbingGalerkin.incl n (v n)) atTop (𝓝 x) →
        Tendsto (fun n => infDist (absorbingGalerkin.sol n (v n) t) (tsdPair : Set State))
          atTop (𝓝 (infDist (absorbingSemigroup.S t x) (tsdPair : Set State)))

/-- **The linearized Einstein–Bianchi system on the cube with absorbing boundary conditions**:
well posed and radiating, the Gauss laws propagate, TSD holds on the domain of dependence but is
not invariant, finite speed of propagation, and the semi-discrete scheme converges (the
`dissipFEEC` verdict) with TSD residuals of positive limit. -/
theorem absorbingVerdict : AbsorbingVerdict :=
  { absorbingGalerkin_verdict.2 with
    isMDissipative := isMDissipative_absorbing
    smooth_mem_domain := mem_domain_of_smooth
    energy_flux := fun u₀ _ ht => norm_sq_absorbingSemigroup u₀ ht
    exists_inner_neg := exists_inner_absorbing_neg
    gauss := fun _ hu₀ _ ht φ hφ => absorbingSemigroup_divFree hu₀ ht φ hφ
    symTF_depDomain := fun _ hu₀ _ ht => absorbingSemigroup_symTF_depDomain hu₀ ht
    not_invariant := not_invariant_tsdPair
    eq_depDomain := fun _ _ _ hW hW0 _ ht j => absorbingSemigroup_eq_depDomain hW hW0 ht j
    dense_core := absorbingGalerkin_verdict.1
    discrete_energy_flux := fun n x _ ht => absorbingGalerkin_energy n x ht
    residual_not_invariant := fun _ hT => absorbingGalerkin_residual_not_invariant hT }

end Feec.Instances.EinsteinBianchi
