module

public import Feec.HilbertComplex.Approximation.Reweight
public import Feec.Instances.Maxwell
public import Feec.Physics.Maxwell.Coefficients

/-!
# Maxwell's equations in linear media as instances of the FEEC theorem

A linear medium (`Feec.Maxwell.Medium`: permittivity `ε = e† e` on the electric fields, degree
`a + 1`, and permeability `μ = m† m` on the magnetic fields, degree `a + 2`, bounded isomorphisms
`e`, `m`; e.g. `e = ε^{1/2}`, `m = μ^{1/2}` for uniformly bounded, uniformly positive coefficient
fields `λ ≤ ε(x), μ(x) ≤ Λ`) reweights a Hilbert complex `H` on `ℕ` or `ℤ`: the weights
`mediumWeights a M` are `e` in degree `a + 1`, `(m†)⁻¹` in degree `a + 2` and the identity
elsewhere, so that the reweighted complex `H.conj (mediumWeights a M)` has `d' = e d` out of
degree `a`, `d' = (m†)⁻¹ d e⁻¹` out of degree `a + 1` and `d' = d m†` out of degree `a + 2`, in
the conjugated variables `(σ, e E, m H)` ([AFW2010], §6.1; [Monk2003]).

**Maxwell's equations in the medium are an instance of the FEEC theorem**: every conforming
family `F` of `H` gives the conforming family `mediumFamily F a M` of the reweighted complex
(`ConformingFamily.conj`, the same finite element spaces with the weighted inner products, in the
conjugated variables), and every Jackson estimate of `F` gives one of it
(`ConformingFamily.Jackson.conj`). Hence the Maxwell verdict (`maxwellFEEC`: well-posedness,
convergence, the Gauss laws reduce `L` and propagate, the Gauss residual tends to `0`) and the
rated FEEC theorem hold in every medium (`medium_maxwellFEEC`). The projections of the reweighted
family are bounded by `max (Medium.cond M) 1` times those of `F` (`norm_mediumFamily_π_le`), where
the condition number `Medium.cond M` is at most `√(Λ / λ)` for isotropic media
(`Maxwell.Medium.isotropic_cond_le`). The Gauss laws of the reweighted window are the **weighted
Gauss laws** `σ = 0`, `d† (ε E) = 0`, `d (μ H) = 0` of the medium (`mem_windowGauss_medium_iff`).

## Instances

* every medium, every admissible sequence `S` of the periodic table, both boundary conditions:
  on the cube (`cube_medium_maxwellFEEC`), on parallelepipeds (`para_medium_maxwellFEEC`) and on
  domains star-shaped with respect to a ball (`star_medium_maxwellFEEC`), with the rates of the
  Jackson estimates `polyJackson`, `polyJacksonMin` for data whose unweighted fields are regular;
* **isotropic inhomogeneous media** on the cube (`cube_isotropic_maxwellFEEC`), multiplication
  by measurable scalar fields `λ ≤ ε(x), μ(x) ≤ Λ` (`Maxwell.Medium.isotropic`, over `ℝ`), both
  boundary conditions, with projections bounded by `max √(Λ / λ) 1` times those of `F`.

The theorems hold for every `Medium ℝ` on the finite element spaces, so for an anisotropic medium
once real factors `e`, `m` with `e† e = ε`, `m† m = μ` are given; their existence for real
symmetric uniformly positive matrix fields is not formalized (over `ℂ` it is
`Maxwell.Medium.exists_anisotropic`, but the finite element families are real).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3, §5, §6.1 (variable coefficients)
* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003] (variable coefficients
  `ε`, `μ`)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.9 (Prop. 4.16)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open MeasureTheory LinearPMap

@[expose] public noncomputable section

namespace Feec.Instances.Maxwell

open Feec.HilbertComplex Feec.Maxwell
open Feec.FiniteElement (PolySeq)

/-! ### The weights of a medium -/

section Weights

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α]
  [CharZero α] [DecidableEq α] {V : α → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, CompleteSpace (V i)] (a : α)
  (M : Medium 𝕜 (V (a + ((1 : Fin 3) : α))) (V (a + ((2 : Fin 3) : α))))

omit [DecidableEq α] in
theorem electric_ne_magnetic : a + ((1 : Fin 3) : α) ≠ a + ((2 : Fin 3) : α) := fun h => by
  have := add_left_cancel h
  norm_num at this

/-- **The weights of a medium** on the Maxwell window in degree `a`: `e` on the electric fields
(degree `a + 1`), `(m†)⁻¹` on the magnetic fluxes (degree `a + 2`), the identity elsewhere. -/
def mediumWeights : ∀ i, V i ≃L[𝕜] V i :=
  Function.update (Function.update (fun i => ContinuousLinearEquiv.refl 𝕜 (V i))
    (a + ((1 : Fin 3) : α)) M.e) (a + ((2 : Fin 3) : α)) M.m.adjoint.symm

theorem mediumWeights_electric : mediumWeights a M (a + ((1 : Fin 3) : α)) = M.e := by
  rw [mediumWeights, Function.update_of_ne (electric_ne_magnetic a), Function.update_self]

omit [IsCancelAdd α] [CharZero α] in
theorem mediumWeights_magnetic : mediumWeights a M (a + ((2 : Fin 3) : α)) = M.m.adjoint.symm :=
  Function.update_self ..

/-- **The condition numbers of the weights** of a medium are at most `max (Medium.cond M) 1`. -/
theorem mediumWeights_cond_le (i : α) :
    ‖(mediumWeights a M i : V i →L[𝕜] V i)‖ * ‖((mediumWeights a M i).symm : V i →L[𝕜] V i)‖ ≤
      max M.cond 1 := by
  by_cases h2 : i = a + ((2 : Fin 3) : α)
  · subst h2
    rw [mediumWeights_magnetic, ContinuousLinearEquiv.symm_symm,
      ContinuousLinearEquiv.norm_adjoint_symm, ContinuousLinearEquiv.norm_adjoint, mul_comm]
    exact (le_max_right _ _).trans (le_max_left _ _)
  by_cases h1 : i = a + ((1 : Fin 3) : α)
  · subst h1
    rw [mediumWeights_electric]
    exact (le_max_left _ _).trans (le_max_left _ _)
  refine le_trans ?_ (le_max_right _ _)
  simp only [mediumWeights, Function.update_of_ne h2, Function.update_of_ne h1]
  exact (mul_le_mul ContinuousLinearMap.norm_id_le ContinuousLinearMap.norm_id_le (norm_nonneg _)
    zero_le_one).trans_eq (one_mul 1)

end Weights

/-! ### Maxwell's equations in a medium -/

section Medium

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α]
  [CharZero α] [DecidableEq α] {V : α → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, CompleteSpace (V i)]
  {H : HilbertComplex 𝕜 (ComplexShape.up α) V} {κ : Type*} (F : ConformingFamily H κ) (a : α)
  (M : Medium 𝕜 (V (a + ((1 : Fin 3) : α))) (V (a + ((2 : Fin 3) : α))))

/-- **The conforming family of Maxwell's equations in the medium `M`**: the spaces of `F` with
the weighted inner products, in the conjugated variables `(σ, e E, m H)`, a conforming family of
the reweighted complex `H.conj (mediumWeights a M)` (`ConformingFamily.conj`). -/
abbrev mediumFamily : ConformingFamily (H.conj (mediumWeights a M)) κ :=
  F.conj _ ⟨_, mediumWeights_cond_le a M⟩

/-- **The projections of Maxwell's family in the medium** are bounded by the condition number of
the medium times the bound of the projections of `F`. -/
theorem norm_mediumFamily_π_le (h : κ) (i : α) (x : V i) :
    ‖((mediumFamily F a M).π h).π i x‖ ≤ max M.cond 1 * F.projBound * ‖x‖ := by
  refine (F.norm_conj_π_le h i x).trans ?_
  gcongr
  exacts [zero_le_one.trans F.one_le_projBound, mediumWeights_cond_le a M i]

/-- **The Gauss laws of the reweighted window are the weighted Gauss laws** of the medium: in the
conjugated variables `x = (σ, e E, m H)`, `σ = 0`, `d† (ε E) = 0` and `d (μ H) = 0`. -/
theorem mem_windowGauss_medium_iff {x : PiLp 2 fun i : Fin 3 => V (a + i)} :
    x ∈ windowGauss (H.conj (mediumWeights a M)) a ↔
      x 0 = 0 ∧
        M.ε (M.e.symm (x 1)) ∈ ((H.d (a + ((0 : Fin 3) : α)) (a + ((1 : Fin 3) : α)))†).ker ∧
        M.μ (M.m.symm (x 2)) ∈ magnetic H a := by
  rw [mem_gauss]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · change x 1 ∈ ((H.d _ _).conj (mediumWeights a M _) (mediumWeights a M _))†.ker ↔ _
    rw [LinearPMap.adjoint_conj _ _ (H.dense _ _), LinearPMap.mem_ker_conj_iff,
      ContinuousLinearEquiv.symm_symm, mediumWeights_electric, Medium.ε_e_symm_apply]
  · change x 2 ∈ ((H.d _ _).conj (mediumWeights a M _) (mediumWeights a M _)).ker ↔ _
    rw [LinearPMap.mem_ker_conj_iff, mediumWeights_magnetic, ContinuousLinearEquiv.symm_symm,
      Medium.μ_m_symm_apply]

variable [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)] {ρ : Type*}

/-- **The FEEC theorem for Maxwell's equations in a linear medium**: for every conforming family
`F` of a Hilbert complex on `ℕ` or `ℤ`, every degree `a` and every medium `M`, the Maxwell verdict
(`maxwellFEEC`) of the reweighted family, whose Gauss laws are the weighted ones
(`mem_windowGauss_medium_iff`), and, for every Jackson estimate `J` of `F`, the rated FEEC
theorem (`ConformingFamily.feec_rated`) for the reweighted Jackson estimate: the errors are
`O(hᵒʳᵈ⁽ˢ⁾)` for data whose unweighted fields are `s`-regular. [AFW2010], §6.1; [Monk2003];
[QuennevilleBelair2015], Thms 4.6, 4.7, 4.14, Prop. 4.16 -/
theorem medium_maxwellFEEC (J : F.Jackson ρ) :
    Verdict (mediumFamily F a M) a ∧ ConformingFamily.Verdict.Rated (mediumFamily F a M) J.conj :=
  ⟨maxwellFEEC _ a, ConformingFamily.feec_rated _ _⟩

end Medium

/-! ### The cube, parallelepipeds and star-shaped domains -/

section Models

open Models.Cube Models.StarShaped Feec.Domain

variable {n : ℕ} [NeZero n] (S : PolySeq) (a : ℤ)

/-- **Maxwell's equations in every linear medium on the cube** `Q = (0, ½)ⁿ`, at every polynomial
order (every admissible sequence `S`), with a perfect magnetic conductor (`FEM.polyFamily`) and a
perfect electric conductor (`FEM.polyFamilyMin`): the Maxwell verdict and the rates
`O(h^{s+1})` of the Jackson estimates `FEM.polyJackson`, `FEM.polyJacksonMin`. -/
theorem cube_medium_maxwellFEEC
    (M : Medium ℝ (L2F ℝ (FEM.cubeDomain n) (formIdx n (a + ((1 : Fin 3) : ℤ))))
      (L2F ℝ (FEM.cubeDomain n) (formIdx n (a + ((2 : Fin 3) : ℤ))))) :
    (Verdict (mediumFamily (FEM.polyFamily n S) a M) a ∧
      ConformingFamily.Verdict.Rated (mediumFamily (FEM.polyFamily n S) a M)
        (FEM.polyJackson n S).conj) ∧
    (Verdict (mediumFamily (FEM.polyFamilyMin n S) a M) a ∧
      ConformingFamily.Verdict.Rated (mediumFamily (FEM.polyFamilyMin n S) a M)
        (FEM.polyJacksonMin n S).conj) :=
  ⟨medium_maxwellFEEC (FEM.polyFamily n S) a M (FEM.polyJackson n S),
    medium_maxwellFEEC (FEM.polyFamilyMin n S) a M (FEM.polyJacksonMin n S)⟩

/-- **Maxwell's equations in every linear medium on a parallelepiped** `Ω = A · Q + b`, at every
polynomial order, both boundary conditions (`Parallelepiped.polyFamily`,
`Parallelepiped.polyFamilyMin`, with their Jackson estimates). -/
theorem para_medium_maxwellFEEC (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (b : Fin n → ℝ)
    (M : Medium ℝ (L2F ℝ (Models.Parallelepiped.domain A b) (formIdx n (a + ((1 : Fin 3) : ℤ))))
      (L2F ℝ (Models.Parallelepiped.domain A b) (formIdx n (a + ((2 : Fin 3) : ℤ))))) :
    (Verdict (mediumFamily (Models.Parallelepiped.polyFamily A hA b S) a M) a ∧
      ConformingFamily.Verdict.Rated (mediumFamily (Models.Parallelepiped.polyFamily A hA b S) a M)
        (Models.Parallelepiped.polyJackson A hA b S).conj) ∧
    (Verdict (mediumFamily (Models.Parallelepiped.polyFamilyMin A hA b S) a M) a ∧
      ConformingFamily.Verdict.Rated
        (mediumFamily (Models.Parallelepiped.polyFamilyMin A hA b S) a M)
        (Models.Parallelepiped.polyJacksonMin A hA b S).conj) :=
  ⟨medium_maxwellFEEC (Models.Parallelepiped.polyFamily A hA b S) a M
      (Models.Parallelepiped.polyJackson A hA b S),
    medium_maxwellFEEC (Models.Parallelepiped.polyFamilyMin A hA b S) a M
      (Models.Parallelepiped.polyJacksonMin A hA b S)⟩

/-- **Maxwell's equations in every linear medium on a domain star-shaped with respect to a
ball**, with any uniformly shape-regular, quasi-uniform mesh family, at every polynomial order,
both boundary conditions (`MeshFamily.polyFamily`, `MeshFamily.polyFamilyMin`, with their Jackson
estimates). -/
theorem star_medium_maxwellFEEC {D : StarDomain n} (F : MeshFamily D)
    (M : Medium ℝ (L2F ℝ D.Ω (formIdx n (a + ((1 : Fin 3) : ℤ))))
      (L2F ℝ D.Ω (formIdx n (a + ((2 : Fin 3) : ℤ))))) :
    (Verdict (mediumFamily (F.polyFamily S) a M) a ∧
      ConformingFamily.Verdict.Rated (mediumFamily (F.polyFamily S) a M)
        (F.polyJackson S).conj) ∧
    (Verdict (mediumFamily (F.polyFamilyMin S) a M) a ∧
      ConformingFamily.Verdict.Rated (mediumFamily (F.polyFamilyMin S) a M)
        (F.polyJacksonMin S).conj) :=
  ⟨medium_maxwellFEEC (F.polyFamily S) a M (F.polyJackson S),
    medium_maxwellFEEC (F.polyFamilyMin S) a M (F.polyJacksonMin S)⟩

variable {ε μ : (Fin n → ℝ) → ℝ}
  (hε : AEStronglyMeasurable ε (volume.restrict (FEM.cubeDomain n)))
  (hμ : AEStronglyMeasurable μ (volume.restrict (FEM.cubeDomain n))) {c C : ℝ} (hc : 0 < c)
  (hεb : ∀ᵐ x ∂volume.restrict (FEM.cubeDomain n), c ≤ ε x ∧ ε x ≤ C)
  (hμb : ∀ᵐ x ∂volume.restrict (FEM.cubeDomain n), c ≤ μ x ∧ μ x ≤ C)

/-- **Maxwell's equations in an isotropic inhomogeneous medium on the cube**, a concrete instance
of `cube_medium_maxwellFEEC`: permittivity and permeability the multiplication by measurable
scalar fields `c ≤ ε(x), μ(x) ≤ C`, `c > 0` (`Maxwell.Medium.isotropic`, factors `√ε`, `√μ`),
at every polynomial order, with a perfect magnetic and a perfect electric conductor: the Maxwell
verdict, whose Gauss laws are `σ = 0`, `d† (ε E) = 0`, `d (μ H) = 0` with
`(ε E)_j = ε(x) E_j(x)` (`Maxwell.Medium.isotropic_ε_apply`), the rates of `FEM.polyJackson`,
`FEM.polyJacksonMin`, and projections bounded by `max √(C / c) 1` times those of the unweighted
family (`norm_mediumFamily_π_le`, `Maxwell.Medium.isotropic_cond_le`). -/
theorem cube_isotropic_maxwellFEEC :
    ((Verdict (mediumFamily (FEM.polyFamily n S) a
      (Medium.isotropic ℝ _ _ hε hμ hc hεb hμb)) a ∧
      ConformingFamily.Verdict.Rated (mediumFamily (FEM.polyFamily n S) a
        (Medium.isotropic ℝ _ _ hε hμ hc hεb hμb)) (FEM.polyJackson n S).conj) ∧
    (Verdict (mediumFamily (FEM.polyFamilyMin n S) a
      (Medium.isotropic ℝ _ _ hε hμ hc hεb hμb)) a ∧
      ConformingFamily.Verdict.Rated (mediumFamily (FEM.polyFamilyMin n S) a
        (Medium.isotropic ℝ _ _ hε hμ hc hεb hμb)) (FEM.polyJacksonMin n S).conj)) ∧
    ∀ h i x,
      ‖((mediumFamily (FEM.polyFamily n S) a
        (Medium.isotropic ℝ _ _ hε hμ hc hεb hμb)).π h).π i x‖ ≤
        max √(C / c) 1 * (FEM.polyFamily n S).projBound * ‖x‖ ∧
      ‖((mediumFamily (FEM.polyFamilyMin n S) a
        (Medium.isotropic ℝ _ _ hε hμ hc hεb hμb)).π h).π i x‖ ≤
        max √(C / c) 1 * (FEM.polyFamilyMin n S).projBound * ‖x‖ := by
  have hM := max_le_max_right 1 (Medium.isotropic_cond_le (𝕜 := ℝ)
    (ι := formIdx n (a + ((1 : Fin 3) : ℤ))) (κ := formIdx n (a + ((2 : Fin 3) : ℤ)))
    hε hμ hc hεb hμb)
  refine ⟨cube_medium_maxwellFEEC S a _, fun h i x => ⟨?_, ?_⟩⟩
  · refine (norm_mediumFamily_π_le (FEM.polyFamily n S) a
      (Medium.isotropic ℝ _ _ hε hμ hc hεb hμb) h i x).trans ?_
    gcongr
    exact zero_le_one.trans (ConformingFamily.one_le_projBound _)
  · refine (norm_mediumFamily_π_le (FEM.polyFamilyMin n S) a
      (Medium.isotropic ℝ _ _ hε hμ hc hεb hμb) h i x).trans ?_
    gcongr
    exact zero_le_one.trans (ConformingFamily.one_le_projBound _)

end Models

end Feec.Instances.Maxwell
