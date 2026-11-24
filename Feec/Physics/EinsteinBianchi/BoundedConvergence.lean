module

public import Feec.Physics.EinsteinBianchi.BoundedFailure
public import Feec.Models.Cube.WeakSymmetryConvergence
public import Feec.Semigroup.DomainSq
public import Feec.ForMathlib.Analysis.DiagonalChoice

/-!
# The scheme (6.5) converges for every datum in `D(L)`, and to a solution that leaves TSD

[QuennevilleBelair2015], §6.3: the semi-discrete scheme (6.5) on `Q = (0, ½)³` with the elements
of Table 6.1 and the thesis' boundary conditions (`Feec.Models.Cube.WeakSymmetry.cubeWave`).
This file removes the hypothesis `IsRateApproximable` of
`Feec.EinsteinBianchi.BoundedFailure.tendsto_of_isRateApproximable` and
`Feec.EinsteinBianchi.BoundedFailure.waveFEM_converges_to_non_tsd_of_isRateApproximable`.

**Strong solutions with `U(0) ∈ D(L²)` are classical solutions of (6.2).** If `V` and `L V` are
strong solutions of the forms-model Hodge wave equation (and `L² V` is continuous), then `V` is a
`Feec.BGG.ExactWave` of the cube data (`exactOfStrong`): the multiplier functional is
`ℓ(t)(dτ − S₀ψ) = ⟪σ'(t), τ⟫ − ⟪u(t), dψ⟫`, well defined because this vanishes on `Γ`
(`inner_sub_inner_eq_zero`), and extended to `H̊Λ¹(Q)` by a linear right inverse of
`(τ, ψ) ↦ dτ − S₀ψ` (onto by the regular decomposition, `tsA_surjective`); it is represented by the
`L²` data `(σ', u)` (`IsMultRep`), not `L²`-bounded in general. The observables `dφ = d₀σ`,
`S¹u`, `du` are bounded functions of `L V` (`projK_comp1_waveOf`: `d₀x₀` is the projection of
`(L x)₁` on `R(d₁*)ᗮ`).

**Convergence for every datum in `D(L)`.** For `U(0) ∈ D(L²)` the Models theorem
`Feec.Models.Cube.WeakSymmetry.cubeWave_converges` gives convergence of (6.5) from the elliptic
projection; `D(L²)` is dense (`LinearPMap.IsSkewAdjoint.exists_mem_domain_sq_lt`: the resolvent
means `J_n` of Stone's theorem map into `D(L²)`), and the energy estimate of (6.1) carries the
approximation to every strong solution (`eventually_exists_dvec_le`). The solutions of (6.5) keep
their distance in energy, so by Lax's principle (`tendstoUniformlyOn_iff_tendsto_of_stable`)
every family of them whose initial states converge converges (`tendsto_of_isStrongSolution`): the
datum of a family of solutions of (6.5) only has to converge at `t = 0`.

## Main results

* `exactOfStrong`, `exactOfStrong_isMultRep`, `exactOfStrong_isMultRep'`, `exactOfStrong_vec`.
* `isStrongSolution_of_generator`, `exists_orbit_sq`: the orbits of Stone's group.
* `eventually_exists_dvec_le`: every strong solution is the uniform limit of solutions of (6.5).
* **`tendsto_of_isStrongSolution`**, **`tendsto_of_mem_wave_domain`**: convergence of (6.5) without
  rate for every datum in `D(L)` (no regularity hypothesis).
* **`waveFEM_converges_to_non_tsd`**: for the TSD datum `(0, 0, (0, β))` of
  `Feec.Counterexamples.BoundedBGG.bggComplex_verdict`, the continuous solution leaves TSD, every
  family of solutions of (6.5) whose initial states converge converges to it uniformly on
  `[0,T]`, and for all large `N` the discrete fields leave TSD: the method converges to the wrong
  physics. No hypothesis.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.1 ((6.1), (6.2)), §6.2 ((6.3), (6.4), Prop 6.2), §6.3 ((6.5), Table 6.1)
* [T. Cazenave, A. Haraux, *An Introduction to Semilinear Evolution Equations*][CazenaveHaraux1998],
  Cor. 2.4.9 (Stone's theorem)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open Set Filter Topology MeasureTheory

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi.BoundedConvergence

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry Feec.Models.BoundedDomain Feec.EinsteinBianchi.WaveFEM
  Feec.EinsteinBianchi.MatrixModel Feec.EinsteinBianchi.BoundedFailure

/-! ### Calculus through isometric embeddings -/

theorem continuousOn_of_isometry {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E →ₗ[ℝ] F) (hg : ∀ x, ‖g x‖ = ‖x‖)
    {f : ℝ → E} {s : Set ℝ} (h : ContinuousOn (fun r => g (f r)) s) : ContinuousOn f s :=
  ((AddMonoidHomClass.isometry_of_norm g hg).isUniformInducing.isInducing.continuousOn_iff).2 h

theorem hasDerivWithinAt_of_isometry {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E →ₗ[ℝ] F) (hg : ∀ x, ‖g x‖ = ‖x‖)
    {f : ℝ → E} {f' : E} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt (fun r => g (f r)) (g f') s t) : HasDerivWithinAt f f' s t := by
  rw [hasDerivWithinAt_iff_isLittleO] at h ⊢
  rw [← Asymptotics.isLittleO_norm_left] at h ⊢
  have e : (fun r => ‖f r - f t - (r - t) • f'‖) =
      fun r => ‖g (f r) - g (f t) - (r - t) • g f'‖ :=
    funext fun r => by rw [← map_smul, ← map_sub, ← map_sub, hg]
  rw [e]; exact h

/-! ### The multiplier functional -/

/-- The map `(τ, ψ) ↦ dτ − S₀ψ` of the cube data. -/
def tsA : (U0 × Wv U0) →ₗ[ℝ] U1 :=
  bggSegment.d0 ∘ₗ LinearMap.fst ℝ U0 (Wv U0) - bggSegment.S0 ∘ₗ LinearMap.snd ℝ U0 (Wv U0)

theorem tsA_apply (x : U0 × Wv U0) : tsA x = bggSegment.d0 x.1 - bggSegment.S0 x.2 := rfl

/-- **`(τ, ψ) ↦ dτ − S₀ψ` is onto `H̊Λ¹(Q)`** (the regular decomposition,
`Feec.BGG.Stability.exists_decomp` with `curlPotential`). -/
theorem tsA_surjective : Function.Surjective tsA := fun μ => by
  obtain ⟨τ, ψ, h, -⟩ := bggStability_curlPotentialConst.exists_decomp μ
  exact ⟨(τ, ψ), h⟩

/-- A linear right inverse of `tsA`. -/
def tsR : U1 →ₗ[ℝ] U0 × Wv U0 :=
  (LinearMap.exists_rightInverse_of_surjective tsA
    (LinearMap.range_eq_top.2 tsA_surjective)).choose

theorem tsA_tsR (μ : U1) : tsA (tsR μ) = μ :=
  LinearMap.congr_fun (LinearMap.exists_rightInverse_of_surjective tsA
    (LinearMap.range_eq_top.2 tsA_surjective)).choose_spec μ

/-- The multiplier functional of the data `(a, b)`: `μ ↦ ⟪a, τ⟫ − ⟪b, dψ⟫` for the preimage
`(τ, ψ) = tsR μ` of `μ`. -/
def multOf (a : W0) (b : Wv W1) : U1 →ₗ[ℝ] ℝ :=
  ((innerSL ℝ a).toLinearMap ∘ₗ D0.domain.subtype ∘ₗ LinearMap.fst ℝ U0 (Wv U0) -
    (innerSL ℝ b).toLinearMap ∘ₗ incl1 ∘ₗ bggSegment.dt0 ∘ₗ LinearMap.snd ℝ U0 (Wv U0)) ∘ₗ tsR

theorem multOf_apply (a : W0) (b : Wv W1) (μ : U1) :
    multOf a b μ = ⟪a, ((tsR μ).1 : W0)⟫ - ⟪b, incl1 (bggSegment.dt0 (tsR μ).2)⟫ := rfl

/-- **The multiplier of data vanishing on `Γ` is represented by them**: if
`⟪a, τ⟫ = ⟪b, dψ⟫` whenever `dτ = S₀ψ`, then `multOf a b (dτ − S₀ψ) = ⟪a, τ⟫ − ⟪b, dψ⟫`. -/
theorem isMultRep_multOf {a : W0} {b : Wv W1}
    (hvan : ∀ τ ψ, bggSegment.d0 τ = bggSegment.S0 ψ →
      ⟪a, (τ : W0)⟫ - ⟪b, incl1 (bggSegment.dt0 ψ)⟫ = 0) : IsMultRep (multOf a b) a b := by
  intro τ ψ
  set p := tsR (bggSegment.d0 τ - bggSegment.S0 ψ)
  have hp : tsA p = tsA (τ, ψ) := tsA_tsR _
  have hk : bggSegment.d0 (p.1 - τ) = bggSegment.S0 (p.2 - ψ) := by
    rw [tsA_apply, tsA_apply] at hp
    rw [map_sub, map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.1 hp
  have h := hvan _ _ hk
  rw [multOf_apply]
  simp only [Submodule.coe_sub, map_sub, inner_sub_right] at h
  linarith

/-! ### The orthogonal projection onto `R(d₁*)ᗮ` -/

section Proj

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- The range of `d₁*` in `(L²Λ¹)³`. -/
def rangeAdj : Submodule ℝ (Wv W1) := LinearMap.range (bggHilb.D1L†).toFun

/-- `R(d₁*)ᗮ`. -/
def rangeAdjPerp : Submodule ℝ (Wv W1) := Submodule.orthogonal rangeAdj

instance : rangeAdjPerp.HasOrthogonalProjection := by
  have : CompleteSpace rangeAdjPerp := (Submodule.isClosed_orthogonal rangeAdj).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- The orthogonal projection onto `R(d₁*)ᗮ ⊇ R(d₀)`. -/
def projK : Wv W1 →L[ℝ] Wv W1 := rangeAdjPerp.starProjection

set_option maxHeartbeats 1000000 in
/-- **`d₀x₀` is a bounded function of `L x`**: `P_{R(d₁*)ᗮ} (L x)₁ = d₀ x₀` on `D(L)` (the two
terms of `(L x)₁ = d₀x₀ − d₁*x₂` are orthogonal). -/
theorem projK_comp1_waveOf {x : WS} (hx : x ∈ formsShort.wave.domain) :
    projK (comp1 (waveOf x)) = bggHilb.D0Γ ⟨comp0 x, dom0 hx⟩ := by
  rw [comp1_waveOf hx, map_sub]
  have hm : bggHilb.D0Γ ⟨comp0 x, dom0 hx⟩ ∈ bggHilb.D1L.domain :=
    formsShort.mapsTo ⟨comp0 x, dom0 hx⟩
  have hc : bggHilb.D1L ⟨_, hm⟩ = 0 := formsShort.comp ⟨comp0 x, dom0 hx⟩
  have h1 : bggHilb.D0Γ ⟨comp0 x, dom0 hx⟩ ∈ rangeAdjPerp := by
    rw [rangeAdjPerp, Submodule.mem_orthogonal]
    rintro _ ⟨y, rfl⟩
    have hadj : ⟪bggHilb.D1L† y, bggHilb.D0Γ ⟨comp0 x, dom0 hx⟩⟫ =
        ⟪(y : WithLp 2 (W2 × Wv W2)), bggHilb.D1L ⟨_, hm⟩⟫ :=
      LinearPMap.adjoint_isFormalAdjoint formsShort.dense₁ y ⟨_, hm⟩
    change ⟪bggHilb.D1L† y, bggHilb.D0Γ ⟨comp0 x, dom0 hx⟩⟫ = 0
    rw [hadj, hc, inner_zero_right]
  have h2 : bggHilb.D1L† ⟨comp2 x, dom2 hx⟩ ∈ Submodule.orthogonal rangeAdjPerp :=
    Submodule.le_orthogonal_orthogonal _ ⟨⟨comp2 x, dom2 hx⟩, rfl⟩
  rw [projK, Submodule.starProjection_eq_self_iff.2 h1,
    (Submodule.starProjection_apply_eq_zero_iff _).2 h2, sub_zero]

end Proj

/-! ### Points of `D(L)` in the domain model -/

section PointDomain

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- The multiplier datum `a = σ'` of a point: `−(L x)₀`. -/
def aOf (x : WS) : W0 := -((comp0 (waveOf x) : bggHilb.Γbar) : W0)

/-- The multiplier datum `b = u` of a point: `x₁`. -/
def bOf (x : WS) : Wv W1 := comp1 x

theorem d0_graphDom_σOf_eq (x : WS) :
    bggSegment.d0 (D0.graphDom (σOf x)) = bggSegment.S0 (rp (φOf x)) := by
  refine Subtype.ext ?_
  have h := mem_gammaOf x
  change D0 (D0.graphDom (σOf x)) = wsL2 (Ω := cubeDomain 3) 0 (incl0 (rp (φOf x)))
  rw [LinearPMap.apply_graphDom, incl0_rp, ← cubeWaveData_S0, ← cubeWaveData_d0]
  exact h

variable {x : WS} (hx : x ∈ formsShort.wave.domain)
include hx

theorem coe_graphDom_σOf : ((D0.graphDom (σOf x) : U0) : W0) = -((comp0 x : bggHilb.Γbar) : W0) :=
  graphFst_σOf (dom0 hx)

theorem incl1_dt0_φOf :
    incl1 (bggSegment.dt0 (rp (φOf x))) = -projK (comp1 (waveOf x)) := by
  rw [projK_comp1_waveOf hx, ← ιt1_bggDt0]
  exact cubeWaveData_dt0_φOf (dom0 hx)

theorem segS1_uOf : bggSegment.S1 (uOf x) = compML (waveOf x) :=
  ((compML_apply _).trans (ec_point hx)).symm

theorem dt1_uOf : bggSegment.dt1 (uOf x) = compρL (waveOf x) :=
  ((compρL_apply _).trans (ed_point hx)).symm

set_option maxHeartbeats 1000000 in
/-- **(6.2a) tested on `Γ` vanishes** at a point of `D(L)`: `⟪σ', τ⟫ = ⟪u, dψ⟫` when
`dτ = S₀ψ`. -/
theorem inner_sub_inner_eq_zero (τ : U0) (ψ : Wv U0)
    (h : bggSegment.d0 τ = bggSegment.S0 ψ) :
    ⟪aOf x, (τ : W0)⟫ - ⟪bOf x, incl1 (bggSegment.dt0 ψ)⟫ = 0 := by
  have h' : cubeWaveData.d0 (D0.toGraphSpace τ) = cubeWaveData.S0 (toGraphVec0 ψ) := by
    rw [cubeWaveData_d0, cubeWaveData_S0, ιt0_toGraphVec0, LinearPMap.graphSnd_toGraphSpace]
    exact congrArg Subtype.val h
  have e := ea_point hx (D0.toGraphSpace τ) (toGraphVec0 ψ) h'
  have e1 : cubeWaveData.i0 (D0.toGraphSpace τ) = (τ : W0) := rfl
  have e2 : cubeWaveData.it1 (uOf x) = comp1 x := incl1_uOf (dom1 hx)
  have e3 : cubeWaveData.dt0 (toGraphVec0 ψ) = incl1 (bggSegment.dt0 ψ) :=
    ιt1_bggDt0_toGraphVec0 ψ
  rw [e1, e2, e3] at e
  exact e

end PointDomain

/-! ### Strong solutions with `U(0) ∈ D(L²)` are classical solutions of (6.2) -/

section Exact

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- `−(x₀ : W0)` as a bounded map. -/
def negComp0L : WS →L[ℝ] W0 := -(bggHilb.Γbar.subtypeL.comp comp0L)

theorem hasDerivWithinAt_Ici_of_strong {T : ℝ} {V : ℝ → WS}
    (hV : Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 V) {t : ℝ} (ht : t ∈ Ico 0 T)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : WS →L[ℝ] E) :
    HasDerivWithinAt (fun s => g (V s)) (g (waveOf (V t))) (Ici t) t :=
  hasDerivWithinAt_Ici_of_Icc ht (g.hasFDerivAt.comp_hasDerivWithinAt t
    (hasDerivWithinAt_waveOf hV (Ico_subset_Icc_self ht))) fun _ _ => rfl

variable {T : ℝ} {V : ℝ → WS} (hV : Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 V)
  (hW : Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 fun t => waveOf (V t))
  (hX : ContinuousOn (fun t => waveOf (waveOf (V t))) (Icc 0 T))
include hV hW

include hX in
set_option maxHeartbeats 8000000 in
/-- **A strong solution with `L V` strong and `L² V` continuous is a classical solution of (6.2)**
of the cube data (`Feec.BGG.ExactWave bggSegment`, source `0`): the states are the components of
`V` (with `(σ, φ) ↦ (−σ, −φ)` as in `solutionOfStrong`), the time derivatives those of `L V`, and
the multiplier `multOf σ' u` (`IsMultRep` by `inner_sub_inner_eq_zero`). -/
def exactOfStrong : Feec.BGG.ExactWave bggSegment T (srcFun 0) where
  σ t := D0.graphDom (σOf (V t))
  φ t := rp (φOf (V t))
  u t := uOf (V t)
  M t := compML (V t)
  ρ t := compρL (V t)
  ℓ t := multOf (aOf (V t)) (bOf (V t))
  σ' t := D0.graphDom (σOf (waveOf (V t)))
  φ' t := rp (φOf (waveOf (V t)))
  u' t := uOf (waveOf (V t))
  M' t := compML (waveOf (V t))
  ρ' t := compρL (waveOf (V t))
  ℓ' t := multOf (aOf (waveOf (V t))) (bOf (waveOf (V t)))
  cσ := continuousOn_of_isometry D0.domain.subtype (fun _ => rfl) (traj_cσ hV)
  cu := continuousOn_of_isometry incl1 norm_incl1 (traj_cu hV)
  cM := compML.continuous.comp_continuousOn hV.continuousOn
  cρ := compρL.continuous.comp_continuousOn hV.continuousOn
  cdφ := continuousOn_of_isometry incl1 norm_incl1
    ((((projK.comp comp1L).continuous.comp_continuousOn hW.continuousOn).neg).congr
      fun s hs => incl1_dt0_φOf (hV.mem_domain hs))
  cSu := (compML.continuous.comp_continuousOn hW.continuousOn).congr
    fun s hs => segS1_uOf (hV.mem_domain hs)
  cdu := (compρL.continuous.comp_continuousOn hW.continuousOn).congr
    fun s hs => dt1_uOf (hV.mem_domain hs)
  cℓ μ := by
    simp only [multOf_apply, aOf, bOf]
    exact ((negComp0L.continuous.comp_continuousOn hW.continuousOn).inner
      continuousOn_const).sub
      ((comp1L.continuous.comp_continuousOn hV.continuousOn).inner continuousOn_const)
  cσ' := continuousOn_of_isometry D0.domain.subtype (fun _ => rfl) (traj_cσ hW)
  cu' := continuousOn_of_isometry incl1 norm_incl1 (traj_cu hW)
  cM' := compML.continuous.comp_continuousOn hW.continuousOn
  cρ' := compρL.continuous.comp_continuousOn hW.continuousOn
  cdφ' := continuousOn_of_isometry incl1 norm_incl1
    ((((projK.comp comp1L).continuous.comp_continuousOn hX).neg).congr
      fun s hs => incl1_dt0_φOf (hW.mem_domain hs))
  cSu' := (compML.continuous.comp_continuousOn hX).congr
    fun s hs => segS1_uOf (hW.mem_domain hs)
  cdu' := (compρL.continuous.comp_continuousOn hX).congr
    fun s hs => dt1_uOf (hW.mem_domain hs)
  cℓ' μ := by
    simp only [multOf_apply, aOf, bOf]
    exact ((negComp0L.continuous.comp_continuousOn hX).inner continuousOn_const).sub
      ((comp1L.continuous.comp_continuousOn hW.continuousOn).inner continuousOn_const)
  dσ t ht := by
    refine hasDerivWithinAt_of_isometry D0.domain.subtype (fun _ => rfl) ?_
    have h := traj_dσ hV ht
    rwa [← graphFst_σOf (dom0 (hW.mem_domain (Ico_subset_Icc_self ht)))] at h
  du t ht := by
    refine hasDerivWithinAt_of_isometry incl1 norm_incl1 ?_
    have h := traj_du hV ht
    rwa [← incl1_uOf (dom1 (hW.mem_domain (Ico_subset_Icc_self ht)))] at h
  dM t ht := traj_dM hV ht
  dρ t ht := traj_dρ hV ht
  ddφ t ht := by
    refine hasDerivWithinAt_of_isometry incl1 norm_incl1 ?_
    have h := (hasDerivWithinAt_Ici_of_strong hW ht (projK.comp comp1L)).neg
    have e1 : ∀ s ∈ Icc 0 T, incl1 (bggSegment.dt0 (rp (φOf (V s)))) =
        -(projK.comp comp1L) (waveOf (V s)) := fun s hs => incl1_dt0_φOf (hV.mem_domain hs)
    have e2 : incl1 (bggSegment.dt0 (rp (φOf (waveOf (V t))))) =
        -(projK.comp comp1L) (waveOf (waveOf (V t))) :=
      incl1_dt0_φOf (hW.mem_domain (Ico_subset_Icc_self ht))
    rw [e2]
    refine h.congr_of_eventuallyEq ?_ (e1 t (Ico_subset_Icc_self ht))
    filter_upwards [Icc_mem_nhdsGE_of_mem ht] with s hs using e1 s hs
  dSu t ht := by
    have h := hasDerivWithinAt_Ici_of_strong hW ht compML
    rw [← segS1_uOf (hW.mem_domain (Ico_subset_Icc_self ht))] at h
    refine h.congr_of_eventuallyEq ?_ (segS1_uOf (hV.mem_domain (Ico_subset_Icc_self ht)))
    filter_upwards [Icc_mem_nhdsGE_of_mem ht] with s hs using segS1_uOf (hV.mem_domain hs)
  ddu t ht := by
    have h := hasDerivWithinAt_Ici_of_strong hW ht compρL
    rw [← dt1_uOf (hW.mem_domain (Ico_subset_Icc_self ht))] at h
    refine h.congr_of_eventuallyEq ?_ (dt1_uOf (hV.mem_domain (Ico_subset_Icc_self ht)))
    filter_upwards [Icc_mem_nhdsGE_of_mem ht] with s hs using dt1_uOf (hV.mem_domain hs)
  dℓ t ht μ := by
    simp only [multOf_apply, aOf, bOf]
    exact (Feec.BGG.hasDerivWithinAt_inner_const (hasDerivWithinAt_Ici_of_strong hW ht negComp0L)
      _).sub (Feec.BGG.hasDerivWithinAt_inner_const (hasDerivWithinAt_Ici_of_strong hV ht comp1L) _)
  ea t ht τ ψ := by
    have hrep := isMultRep_multOf (inner_sub_inner_eq_zero
      (hV.mem_domain (Ico_subset_Icc_self ht))) τ ψ
    rw [hrep]
    have e1 : ((D0.graphDom (σOf (waveOf (V t))) : U0) : W0) = aOf (V t) :=
      coe_graphDom_σOf (hW.mem_domain (Ico_subset_Icc_self ht))
    have e2 : ⟪uOf (V t), bggSegment.dt0 ψ⟫ = ⟪bOf (V t), incl1 (bggSegment.dt0 ψ)⟫ := by
      rw [inner_wv_U1, incl1_uOf (dom1 (hV.mem_domain (Ico_subset_Icc_self ht)))]; rfl
    change ⟪((D0.graphDom (σOf (waveOf (V t))) : U0) : W0), (τ : W0)⟫ -
      ⟪uOf (V t), bggSegment.dt0 ψ⟫ - _ = 0
    rw [e1, e2]; ring
  eb t ht v := by
    have hxt := hV.mem_domain (Ico_subset_Icc_self ht)
    have hwt := hW.mem_domain (Ico_subset_Icc_self ht)
    have h := eb_point hxt v
    have e1 : ⟪uOf (waveOf (V t)), v⟫ = ⟪comp1 (waveOf (V t)), cubeWaveData.it1 v⟫ := by
      rw [inner_wv_U1, incl1_uOf (dom1 hwt)]; rfl
    have e2 : ⟪bggSegment.dt0 (rp (φOf (V t))), v⟫ =
        ⟪cubeWaveData.dt0 (φOf (V t)), cubeWaveData.it1 v⟫ := by
      rw [inner_wv_U1, ← ιt1_bggDt0]; rfl
    rw [srcFun_apply, Pi.zero_apply, inner_zero_left]
    change ⟪uOf (waveOf (V t)), v⟫ + ⟪bggSegment.dt0 (rp (φOf (V t))), v⟫ +
      ⟪compML (V t), cubeWaveData.S1 v⟫ + ⟪compρL (V t), cubeWaveData.dt1 v⟫ = 0
    rw [e1, e2]; exact h
  ec t ht N := by
    rw [segS1_uOf (hV.mem_domain (Ico_subset_Icc_self ht))]; exact sub_self _
  ed t ht μ := by
    rw [dt1_uOf (hV.mem_domain (Ico_subset_Icc_self ht))]; exact sub_self _
  ee t _ := d0_graphDom_σOf_eq (V t)
  ee' t _ := d0_graphDom_σOf_eq (waveOf (V t))

include hX in
set_option maxHeartbeats 4000000 in
theorem exactOfStrong_isMultRep :
    ∀ t ∈ Icc 0 T, IsMultRep ((exactOfStrong hV hW hX).ℓ t) (aOf (V t)) (bOf (V t)) :=
  fun _ ht => isMultRep_multOf (inner_sub_inner_eq_zero (hV.mem_domain ht))

include hX in
set_option maxHeartbeats 4000000 in
theorem exactOfStrong_isMultRep' : ∀ t ∈ Icc 0 T,
    IsMultRep ((exactOfStrong hV hW hX).ℓ' t) (aOf (waveOf (V t))) (bOf (waveOf (V t))) :=
  fun _ ht => isMultRep_multOf (inner_sub_inner_eq_zero (hW.mem_domain ht))

include hX in
set_option maxHeartbeats 4000000 in
/-- The energy vector of `exactOfStrong` is that of `solutionOfStrong`. -/
theorem exactOfStrong_vec {t : ℝ} (ht : t ∈ Icc 0 T) :
    (exactWave_toSolution (exactOfStrong hV hW hX)).vec t = (solutionOfStrong hV).vec t := by
  rw [exactWave_toSolution_vec, solutionOfStrong_vec hV ht]
  have hxt := hV.mem_domain ht
  have e1 : (((exactOfStrong hV hW hX).σ t : U0) : W0) = -((comp0 (V t) : bggHilb.Γbar) : W0) :=
    coe_graphDom_σOf hxt
  have e2 : incl1 ((exactOfStrong hV hW hX).u t) = comp1 (V t) := incl1_uOf (dom1 hxt)
  exact congrArg (Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2))
    (Prod.ext e1 (Prod.ext e2 (Prod.ext rfl rfl)))

end Exact

/-! ### Orbits of Stone's group and the density of `D(L²)` -/

section Group

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {A : E →ₗ.[ℝ] E}

/-- Orbits of domain points are strong solutions of `U' = A U`. -/
theorem isStrongSolution_of_generator {G : Feec.C0Group ℝ E} (hgen : G.generator = A)
    {x : E} (hx : x ∈ A.domain) (I : Set ℝ) :
    Evolution.IsStrongSolution A I 0 fun t => G.S t x := by
  subst hgen
  refine Evolution.IsStrongSolution.of_deriv fun t _ =>
    ⟨G.generator ⟨G.S t x, G.mapsTo_domain ⟨x, hx⟩ t⟩,
      G.generator.mem_graph ⟨G.S t x, G.mapsTo_domain ⟨x, hx⟩ t⟩, ?_⟩
  simpa using (G.hasDerivAt_apply' ⟨x, hx⟩ t).hasDerivWithinAt

theorem mem_domain_of_generator {G : Feec.C0Group ℝ E} (hgen : G.generator = A)
    {x : E} (hx : x ∈ A.domain) (t : ℝ) : G.S t x ∈ A.domain := by
  subst hgen; exact G.mapsTo_domain ⟨x, hx⟩ t

theorem generator_apply_S_of_eq {G : Feec.C0Group ℝ E} (hgen : G.generator = A)
    {x : E} (hx : x ∈ A.domain) (t : ℝ) (h : G.S t x ∈ A.domain) :
    A ⟨G.S t x, h⟩ = G.S t (A ⟨x, hx⟩) := by
  subst hgen; exact G.generator_apply_S ⟨x, hx⟩ t

/-- **Orbits of `D(A²)`**: for `y ∈ D(A²)` there is a strong solution `V` of `U' = A U` with
`V(0) = y` such that `A V` is a strong solution and `A² V` is continuous (the orbit of Stone's
group). -/
theorem exists_orbit_sq (hA : A.IsSkewAdjoint) {y : E} (hy : y ∈ A.domain)
    (hAy : A ⟨y, hy⟩ ∈ A.domain) (I : Set ℝ) :
    ∃ (V : ℝ → E) (h : ∀ t, V t ∈ A.domain) (h' : ∀ t, A ⟨V t, h t⟩ ∈ A.domain),
      V 0 = y ∧ Evolution.IsStrongSolution A I 0 V ∧
      Evolution.IsStrongSolution A I 0 (fun t => A ⟨V t, h t⟩) ∧
      Continuous fun t => A ⟨A ⟨V t, h t⟩, h' t⟩ := by
  have hgen := hA.generator_group
  set G := hA.group
  have h : ∀ t, G.S t y ∈ A.domain := mem_domain_of_generator hgen hy
  have hW : ∀ t, A ⟨G.S t y, h t⟩ = G.S t (A ⟨y, hy⟩) := fun t =>
    generator_apply_S_of_eq hgen hy t (h t)
  have h' : ∀ t, A ⟨G.S t y, h t⟩ ∈ A.domain := fun t => by
    rw [hW]; exact mem_domain_of_generator hgen hAy t
  have hX : ∀ t, A ⟨A ⟨G.S t y, h t⟩, h' t⟩ = G.S t (A ⟨A ⟨y, hy⟩, hAy⟩) := fun t => by
    have e : (⟨A ⟨G.S t y, h t⟩, h' t⟩ : A.domain) =
        ⟨G.S t (A ⟨y, hy⟩), mem_domain_of_generator hgen hAy t⟩ := Subtype.ext (hW t)
    rw [e]; exact generator_apply_S_of_eq hgen hAy t _
  refine ⟨fun t => G.S t y, h, h', by simp [G.map_zero], isStrongSolution_of_generator hgen hy I,
    ?_, ?_⟩
  · exact (isStrongSolution_of_generator hgen hAy I).congr (fun t _ => (hW t).symm)
      fun _ _ => rfl
  · exact (G.strongCont _).congr fun t => (hX t).symm

end Group

/-! ### Convergence of (6.5) for every datum in `D(L)` -/

section Converge

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- The energy vector `(−x₀, x₁, M, ρ)` of a point of the total space, a bounded map. -/
def vecL : WS →L[ℝ] Feec.BGG.EnergySpace W0 (Wv W1) W2 (Wv W2) :=
  (Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2)).comp
    (negComp0L.prod (comp1L.prod (compML.prod compρL)))

theorem solutionOfStrong_vec_eq {T : ℝ} {V : ℝ → WS}
    (hV : Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 V) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (solutionOfStrong hV).vec t = vecL (V t) :=
  solutionOfStrong_vec hV ht

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

set_option maxHeartbeats 8000000 in
/-- **Every strong solution is the uniform limit of solutions of (6.5)** of the forms-model Hodge
wave equation on the cube ([QuennevilleBelair2015], §6.3, (6.5), Table 6.1, thesis' boundary
conditions; no hypothesis): for every `ε > 0` and all large `N`, some solution of (6.5) (source
`0`) is within `ε` of the solution `solutionOfStrong hV` of (6.1) on `[0,T]` in the energy norm.
Approximate `V(0)` by `y ∈ D(L²)` (`LinearPMap.IsSkewAdjoint.exists_mem_domain_sq_lt`); the orbit
of `y` is a classical solution of (6.2) (`exactOfStrong`) to which (6.5) converges from its
elliptic projection (`Feec.Models.Cube.WeakSymmetry.cubeWave_converges`), and it stays within
`‖V(0) - y‖` of `V` by the energy estimate of (6.1) (`Feec.BGG.WaveData.Solution.norm_vec_sub_le`).
-/
theorem eventually_exists_dvec_le {T : ℝ} (hT0 : 0 < T) {V : ℝ → WS}
    (hV : Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 V) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
      ∀ t ∈ Icc 0 T, ‖(solutionOfStrong hV).vec t - dvec (cubeFEM hT hB N) sh t‖ ≤ ε := by
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / 2 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hA := formsShort.isSkewAdjoint_wave
  have hδ : 0 < η / (‖vecL‖ + 1) := by positivity
  obtain ⟨y, hy, hAy, hyd⟩ := hA.exists_mem_domain_sq_lt (V 0) hδ
  obtain ⟨Vy, hd, hd', hVy0, hVy, hWy', hXy'⟩ := exists_orbit_sq hA hy hAy (Icc 0 T)
  have hWy : Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 fun t => waveOf (Vy t) :=
    hWy'.congr (fun t _ => (waveOf_eq (hd t)).symm) fun _ _ => rfl
  have hXy : ContinuousOn (fun t => waveOf (waveOf (Vy t))) (Icc 0 T) := by
    refine hXy'.continuousOn.congr fun t _ => ?_
    change waveOf (waveOf (Vy t)) = formsShort.wave ⟨formsShort.wave ⟨Vy t, hd t⟩, hd' t⟩
    rw [waveOf_eq (hd t), waveOf_eq (hd' t)]
  obtain ⟨sy, hsy⟩ : ∃ s, s = exactOfStrong hVy hWy hXy := ⟨_, rfl⟩
  have hrep : ∀ t ∈ Icc 0 T, IsMultRep (sy.ℓ t) (aOf (Vy t)) (bOf (Vy t)) := by
    rw [hsy]; exact exactOfStrong_isMultRep hVy hWy hXy
  have hrep' : ∀ t ∈ Icc 0 T,
      IsMultRep (sy.ℓ' t) (aOf (waveOf (Vy t))) (bOf (waveOf (Vy t))) := by
    rw [hsy]; exact exactOfStrong_isMultRep' hVy hWy hXy
  have conv := cubeWave_converges hT hB hT0 (f := 0) continuousOn_const sy
    (a := fun t => aOf (Vy t)) (b := fun t => bOf (Vy t))
    (a' := fun t => aOf (waveOf (Vy t))) (b' := fun t => bOf (waveOf (Vy t)))
    (negComp0L.continuous.comp_continuousOn hWy.continuousOn)
    (comp1L.continuous.comp_continuousOn hVy.continuousOn)
    (negComp0L.continuous.comp_continuousOn hXy)
    (comp1L.continuous.comp_continuousOn hWy.continuousOn)
    hrep hrep' hη
  filter_upwards [conv] with N hN
  obtain ⟨shy, -, hshy⟩ := hN
  refine ⟨shy, fun t ht => ?_⟩
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.le⟩
  obtain ⟨w, hw⟩ : ∃ w, w = solutionOfStrong hV := ⟨_, rfl⟩
  obtain ⟨wy, hwy⟩ : ∃ w, w = exactWave_toSolution sy := ⟨_, rfl⟩
  rw [← hw]
  have hc0 : ContinuousOn ((0 : ℝ → Wv W1) - 0) (Icc 0 T) := by
    rw [sub_self]; exact continuousOn_const
  have k1 : ‖w.vec t - wy.vec t‖ ≤ ‖w.vec 0 - wy.vec 0‖ := by
    simpa using w.norm_vec_sub_le wy hc0 t ht
  have k0 : ‖w.vec 0 - wy.vec 0‖ < η := by
    rw [hwy, hsy, exactOfStrong_vec hVy hWy hXy h0T, hw, solutionOfStrong_vec_eq hV h0T,
      solutionOfStrong_vec_eq hVy h0T, hVy0, ← map_sub]
    have h1 := vecL.le_opNorm (V 0 - y)
    have h2 : ‖vecL‖ * ‖V 0 - y‖ ≤ ‖vecL‖ * (η / (‖vecL‖ + 1)) :=
      mul_le_mul_of_nonneg_left hyd.le (norm_nonneg _)
    have h3 : ‖vecL‖ * (η / (‖vecL‖ + 1)) < η := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg vecL]
    linarith
  have k2 : ‖wy.vec t - dvec (cubeFEM hT hB N) shy t‖ ≤ η := by
    rw [hwy, norm_vec_sub_dvec (cubeFEM hT hB N) sy shy t]; exact hshy t ht
  calc ‖w.vec t - dvec (cubeFEM hT hB N) shy t‖
      ≤ ‖w.vec t - wy.vec t‖ + ‖wy.vec t - dvec (cubeFEM hT hB N) shy t‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ η + η := add_le_add (k1.trans k0.le) k2
    _ = ε := by rw [hηdef]; ring

set_option maxHeartbeats 8000000 in
/-- **Convergence of (6.5) without rate for every strong solution** of the forms-model Hodge
wave equation on the cube ([QuennevilleBelair2015], §6.3, (6.5), Table 6.1, thesis' boundary
conditions; no hypothesis): every family of solutions of (6.5) (source `0`) whose initial
states converge to `V(0)` in the energy norm converges to the solution `solutionOfStrong hV` of
(6.1) uniformly on `[0,T]`. Lax's principle (`tendstoUniformlyOn_iff_tendsto_of_stable`): the
solutions of (6.5) keep their distance in energy (`norm_dvec_sub_le`) and approximate the solution
uniformly (`eventually_exists_dvec_le`). -/
theorem tendsto_of_isStrongSolution {T : ℝ} (hT0 : 0 < T) {V : ℝ → WS}
    (hV : Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 V)
    (sh : ∀ N, Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0))
    (h0 : Tendsto (fun N => ‖(solutionOfStrong hV).vec 0 - dvec (cubeFEM hT hB N) (sh N) 0‖)
      atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T,
      ‖(solutionOfStrong hV).vec t - dvec (cubeFEM hT hB N) (sh N) t‖ < ε := by
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.le⟩
  set A : ℕ → Set (ℝ → Feec.BGG.EnergySpace W0 (Wv W1) W2 (Wv W2)) := fun N =>
    Set.range fun s : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0) =>
      dvec (cubeFEM hT hB N) s
  have hA : ∀ N, ∀ v ∈ A N, ∀ w ∈ A N, ∀ t ∈ Icc 0 T, dist (v t) (w t) ≤ 1 * dist (v 0) (w 0) := by
    rintro N _ ⟨s₁, rfl⟩ _ ⟨s₂, rfl⟩ t ht
    have hg : ContinuousOn (cubeSource hT hB N 0 - cubeSource hT hB N 0) (Icc 0 T) := by
      rw [sub_self]; exact continuousOn_const
    simpa [dist_eq_norm] using norm_dvec_sub_le (cubeFEM hT hB N) s₁ s₂ hg ht
  have hu : ∀ ε > 0, ∀ᶠ N in atTop, ∃ w ∈ A N, ∀ t ∈ Icc 0 T,
      dist ((solutionOfStrong hV).vec t) (w t) ≤ ε := fun ε hε =>
    (eventually_exists_dvec_le hT hB hT0 hV hε).mono fun N ⟨s, hs⟩ =>
      ⟨_, ⟨s, rfl⟩, fun t ht => (dist_eq_norm _ _).trans_le (hs t ht)⟩
  have hconv := (tendstoUniformlyOn_iff_tendsto_of_stable h0T hA hu
    (v := fun N => dvec (cubeFEM hT hB N) (sh N)) fun N => ⟨sh N, rfl⟩).2
    (tendsto_iff_norm_sub_tendsto_zero.2 (h0.congr fun N => norm_sub_rev _ _))
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hconv ε hε] with N hN t ht
  exact (dist_eq_norm _ _).symm.trans_lt (hN t ht)

end Converge

/-! ### Every datum in `D(L)`, and the TSD datum -/

section Beta

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

open Feec.Counterexamples.BoundedBGG Feec.Counterexamples.BoundedDomainTSD

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

set_option maxHeartbeats 4000000 in
/-- **Convergence of (6.5) for every datum in `D(L)`** ([QuennevilleBelair2015], §6.3, (6.5),
Table 6.1, thesis' boundary conditions; no hypothesis): for every `U₀` in the domain of the
forms-model Hodge wave operator, the Hodge wave equation has a classical solution `V` on `[0,T]`
(Stone, `Feec.EinsteinBianchi.WaveFEM.bgg_wave_existsUnique` with `curlPotential`), which solves
(6.1) (`solutionOfStrong`) with initial energy vector `(−σ₀, u₀, M₀, ρ₀)`, and every family of
solutions of (6.5) (source `0`) whose initial states converge to it converges to it uniformly on
`[0,T]` (`tendsto_of_isStrongSolution`). -/
theorem tendsto_of_mem_wave_domain {T : ℝ} (hT0 : 0 < T) {U₀ : WS}
    (hU₀ : U₀ ∈ formsShort.wave.domain) :
    ∃ (V : ℝ → WS) (hV : Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 V), V 0 = U₀ ∧
      (solutionOfStrong hV).vec 0 = Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2)
        (-((comp0 U₀ : bggHilb.Γbar) : W0), comp1 U₀, compML U₀, compρL U₀) ∧
      ∀ sh : ∀ N, Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
        Tendsto (fun N => ‖(solutionOfStrong hV).vec 0 - dvec (cubeFEM hT hB N) (sh N) 0‖) atTop
          (𝓝 0) →
        ∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T,
          ‖(solutionOfStrong hV).vec t - dvec (cubeFEM hT hB N) (sh N) t‖ < ε := by
  obtain ⟨V, hV0, hV, -⟩ := bgg_wave_existsUnique curlPotential hU₀ (a := 0) (b := T)
    (Evolution.ForcingClass.admissible_zero _ 0 T)
  have hVs : Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 V := hV.toIsStrongSolution
  refine ⟨V, hVs, hV0, ?_, fun sh hsh0 => tendsto_of_isStrongSolution hT hB hT0 hVs sh hsh0⟩
  rw [solutionOfStrong_vec hVs ⟨le_rfl, hT0.le⟩, hV0]

set_option maxHeartbeats 4000000 in
/-- **The method converges to the wrong physics** ([QuennevilleBelair2015], §6.3, (6.5) with
Table 6.1 and the thesis' boundary conditions; no hypothesis: the regularity hypothesis is
discharged by `curlPotential` and convergence is `tendsto_of_isStrongSolution`). For the TSD
datum `(σ, u, (M, B))(0) = (0, 0, (0, β))`, `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)`, of
`Feec.Counterexamples.BoundedBGG.bggComplex_verdict` on `Q`:
1. the matrix-model Hodge wave equation has a unique strong solution `U = betaU` on `[0,T]`, with
   `σ ≡ 0`, and `U` **leaves TSD**: `E(t) ∉ L²(TSD)` for some `t` and `B(t)` is not symmetric for
   some `t`;
2. read in the forms model (`Feec.EinsteinBianchi.MatrixModel`), `U` is a solution `w = betaW` of
   (6.1) with initial energy vector `(0, 0, 0, ρ(0))`, `ρ(0) = ⋆β` row by row;
3. the scheme (6.5) has solutions from the projected data `(0, 0, 0, P ρ(0))`, and their initial
   states converge to `w(0)`;
4. every family of solutions of (6.5) whose initial states converge to `w(0)` converges to `w`
   uniformly on `[0,T]` (in energy, hence `E_h(t) → E(t)` and `B_h(t) → B(t)` uniformly for the
   matrix proxies `E_h = rowsEquiv uₕ`, `B_h = rows2Equiv ρₕ`), and the discrete fields
   themselves leave TSD: at the times of item 1, for all large `N`, `E_h(t) ∉ L²(TSD)` and
   `B_h(t)` is not symmetric. -/
theorem waveFEM_converges_to_non_tsd {T : ℝ} (hT0 : 0 < T) :
    (betaU hT0 0 = betaDatum ∧
      Evolution.IsStrongSolution matrixComplex.wave (Icc 0 T) 0 (betaU hT0) ∧
      (∀ V, V 0 = betaDatum → Evolution.IsStrongSolution matrixComplex.wave (Icc 0 T) 0 V →
        EqOn V (betaU hT0) (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, (betaU hT0 t 0 : L2 ℝ (cubeDomain 3)) = 0) ∧
      (∃ t ∈ Icc 0 T, betaE hT0 t ∉ tsd (cubeDomain 3)) ∧
      ∃ t ∈ Icc 0 T, betaB hT0 t ∉ symSub ℝ (cubeDomain 3)) ∧
    (betaW hT0).vec 0 = Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2) (0, 0, 0, rhoBeta) ∧
    (∃ sh : ∀ N, Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
      (∀ N, (sh N).σ 0 = 0 ∧ (sh N).u 0 = 0 ∧ (sh N).M 0 = 0 ∧ (sh N).ρ 0 = rhoBetaH hT hB N) ∧
      Tendsto (fun N => ‖(betaW hT0).vec 0 - dvec (cubeFEM hT hB N) (sh N) 0‖) atTop (𝓝 0)) ∧
    ∀ sh : ∀ N, Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
      Tendsto (fun N => ‖(betaW hT0).vec 0 - dvec (cubeFEM hT hB N) (sh N) 0‖) atTop (𝓝 0) →
      (∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T,
        ‖(betaW hT0).vec t - dvec (cubeFEM hT hB N) (sh N) t‖ < ε) ∧
      (∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T,
        ‖betaE hT0 t - rowsEquiv (incl1 (((sh N).u t : (cubeFEM hT hB N).Vt1h) : Wv U1))‖ < ε ∧
        ‖betaB hT0 t - rows2Equiv (((sh N).ρ t : (cubeFEM hT hB N).Wt2h) : Wv W2)‖ < ε) ∧
      (∃ t ∈ Icc 0 T, ∀ᶠ N in atTop,
        rowsEquiv (incl1 (((sh N).u t : (cubeFEM hT hB N).Vt1h) : Wv U1)) ∉
          tsd (cubeDomain 3)) ∧
      ∃ t ∈ Icc 0 T, ∀ᶠ N in atTop,
        rows2Equiv (((sh N).ρ t : (cubeFEM hT hB N).Wt2h) : Wv W2) ∉
          symSub ℝ (cubeDomain 3) := by
  obtain ⟨h1, h2, h3, -⟩ := waveFEM_converges_to_non_tsd_of_isRateApproximable hT hB hT0
  have h1c := h1
  obtain ⟨-, -, -, -, ⟨t₁, ht₁, hE⟩, ⟨t₂, ht₂, hBt⟩⟩ := h1c
  refine ⟨h1, h2, h3, fun sh hsh0 => ?_⟩
  have hconv := tendsto_of_isStrongSolution hT hB hT0
    (isStrongSolution_forms (betaU_spec hT0).2.1) sh hsh0
  have hEB : ∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T,
      ‖betaE hT0 t - rowsEquiv (incl1 (((sh N).u t : (cubeFEM hT hB N).Vt1h) : Wv U1))‖ < ε ∧
      ‖betaB hT0 t - rows2Equiv (((sh N).ρ t : (cubeFEM hT hB N).Wt2h) : Wv W2)‖ < ε :=
    fun ε hε => (hconv ε hε).mono fun N hN t ht =>
      ⟨(norm_rowsEquiv_sub_le hT hB hT0 ht (sh N)).trans_lt (hN t ht),
        (norm_rows2Equiv_sub_le hT hB hT0 ht (sh N)).trans_lt (hN t ht)⟩
  refine ⟨hconv, hEB, ⟨t₁, ht₁, ?_⟩, ⟨t₂, ht₂, ?_⟩⟩
  · exact eventually_not_mem_of_tendsto isClosed_tsd hE fun ε hε =>
      (hEB ε hε).mono fun N hN => (hN t₁ ht₁).1
  · exact eventually_not_mem_of_tendsto isClosed_symSub hBt fun ε hε =>
      (hEB ε hε).mono fun N hN => (hN t₂ ht₂).2

end Beta

end Feec.EinsteinBianchi.BoundedConvergence
