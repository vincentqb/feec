module

public import Feec.HilbertComplex.Approximation.Reweight
public import Feec.Instances.Maxwell
public import Feec.Physics.Maxwell.Coefficients

/-!
# Maxwell's equations in linear media as instances of the FEEC theorem

A linear medium reweights a Hilbert complex by `e` on the electric fields and `(m†)⁻¹` on the
magnetic fluxes, `ε = e† e`, `μ = m† m`; every conforming family and Jackson estimate give those of
the reweighted complex, so the Maxwell verdict and the rated FEEC theorem hold in every medium.

## Main results

* `medium_maxwellFEEC`: the Maxwell verdict and the rated FEEC theorem in every medium.
* `mem_windowGauss_medium_iff`: the Gauss laws `σ = 0`, `d† (ε E) = 0`, `d (μ H) = 0` of a medium.
* `cube_isotropic_maxwellFEEC`: isotropic inhomogeneous media on the cube.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

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

/-- The weights of a medium: `e` in degree `a + 1`, `(m†)⁻¹` in degree `a + 2`, `1` elsewhere. -/
def mediumWeights : ∀ i, V i ≃L[𝕜] V i :=
  Function.update (Function.update (fun i => ContinuousLinearEquiv.refl 𝕜 (V i))
    (a + ((1 : Fin 3) : α)) M.e) (a + ((2 : Fin 3) : α)) M.m.adjoint.symm

theorem mediumWeights_electric : mediumWeights a M (a + ((1 : Fin 3) : α)) = M.e := by
  rw [mediumWeights, Function.update_of_ne (electric_ne_magnetic a), Function.update_self]

omit [IsCancelAdd α] [CharZero α] in
theorem mediumWeights_magnetic : mediumWeights a M (a + ((2 : Fin 3) : α)) = M.m.adjoint.symm :=
  Function.update_self ..

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

/-- The conforming family of Maxwell's equations in the medium `M`, in variables `(σ, e E, m H)`. -/
abbrev mediumFamily : ConformingFamily (H.conj (mediumWeights a M)) κ :=
  F.conj _ ⟨_, mediumWeights_cond_le a M⟩

theorem norm_mediumFamily_π_le (h : κ) (i : α) (x : V i) :
    ‖((mediumFamily F a M).π h).π i x‖ ≤ max M.cond 1 * F.projBound * ‖x‖ := by
  refine (F.norm_conj_π_le h i x).trans ?_
  gcongr
  exacts [zero_le_one.trans F.one_le_projBound, mediumWeights_cond_le a M i]

/-- **The Gauss laws of the reweighted window are the weighted Gauss laws** `σ = 0`,
`d† (ε E) = 0`, `d (μ H) = 0`. -/
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

/-- **The FEEC theorem for Maxwell's equations in a linear medium**, with the rates of every Jackson
estimate. [AFW2010], §6.1; [Monk2003]; [QuennevilleBelair2015], Thms 4.6, 4.7, 4.14, Prop. 4.16 -/
theorem medium_maxwellFEEC (J : F.Jackson ρ) :
    Verdict (mediumFamily F a M) a ∧ ConformingFamily.Verdict.Rated (mediumFamily F a M) J.conj :=
  ⟨maxwellFEEC _ a, ConformingFamily.feec_rated _ _⟩

end Medium

/-! ### The cube, parallelepipeds and star-shaped domains -/

section Models

open Models.Cube Models.StarShaped Feec.Domain

variable {n : ℕ} [NeZero n] (S : PolySeq) (a : ℤ)

/-- **Maxwell's equations in every linear medium on the cube**, at every polynomial order, with both
boundary conditions. -/
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

/-- **Maxwell's equations in every linear medium on a parallelepiped.** -/
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

/-- **Maxwell's equations in every linear medium on a star-shaped domain.** -/
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

/-- **Maxwell's equations in an isotropic inhomogeneous medium on the cube**, with projections
bounded by `max √(C / c) 1` times those of the unweighted family. -/
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
