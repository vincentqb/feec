module

public import Feec.Physics.EinsteinBianchi.BoundedFailure
public import Feec.Models.Cube.WeakSymmetryConvergence

/-!
# The scheme (6.5) converges for every datum in `D(L)`, and to a solution that leaves TSD

[QuennevilleBelair2015], §6.3: the semi-discrete scheme (6.5) on `Q = (0, ½)³` with the elements
of Table 6.1 and the thesis' boundary conditions (`Feec.Models.Cube.WeakSymmetry.cubeWave`).
This file removes the hypothesis `IsRateApproximable` of
`Feec.EinsteinBianchi.BoundedFailure.tendsto_of_isRateApproximable`.

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
projection; `D(L²)` is dense (`exists_mem_domain_sq_lt`: the resolvent means `J_n` of Stone's
theorem map into `D(L²)`), and the energy estimates of (6.1) and (6.5) carry convergence to every
datum (`tendsto_of_isStrongSolution`, Lax). The datum of a family of solutions of (6.5) only has to
converge at `t = 0`.

## Main results

* `exactOfStrong`, `exactOfStrong_isMultRep`, `exactOfStrong_isMultRep'`, `exactOfStrong_vec`.
* `isStrongSolution_group`, `exists_mem_domain_sq_lt`.
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
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open Set Filter Topology MeasureTheory

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi.BoundedFailure

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry Feec.Models.BoundedDomain Feec.EinsteinBianchi.WaveFEM
  Feec.EinsteinBianchi.MatrixModel

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
    bggSegment.d0 (graphDom D0 (σOf x)) = bggSegment.S0 (rp (φOf x)) := by
  refine Subtype.ext ?_
  have h := mem_gammaOf x
  change D0 (graphDom D0 (σOf x)) = wsL2 (Ω := cubeDomain 3) 0 (incl0 (rp (φOf x)))
  rw [apply_graphDom, incl0_rp, ← cubeWaveData_S0, ← cubeWaveData_d0]
  exact h

variable {x : WS} (hx : x ∈ formsShort.wave.domain)
include hx

theorem coe_graphDom_σOf : ((graphDom D0 (σOf x) : U0) : W0) = -((comp0 x : bggHilb.Γbar) : W0) :=
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

theorem negComp0L_apply (x : WS) : negComp0L x = -((comp0 x : bggHilb.Γbar) : W0) := rfl

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
  σ t := graphDom D0 (σOf (V t))
  φ t := rp (φOf (V t))
  u t := uOf (V t)
  M t := compML (V t)
  ρ t := compρL (V t)
  ℓ t := multOf (aOf (V t)) (bOf (V t))
  σ' t := graphDom D0 (σOf (waveOf (V t)))
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
    have e1 : ((graphDom D0 (σOf (waveOf (V t))) : U0) : W0) = aOf (V t) :=
      coe_graphDom_σOf (hW.mem_domain (Ico_subset_Icc_self ht))
    have e2 : ⟪uOf (V t), bggSegment.dt0 ψ⟫ = ⟪bOf (V t), incl1 (bggSegment.dt0 ψ)⟫ := by
      rw [inner_wv_U1, incl1_uOf (dom1 (hV.mem_domain (Ico_subset_Icc_self ht)))]; rfl
    change ⟪((graphDom D0 (σOf (waveOf (V t))) : U0) : W0), (τ : W0)⟫ -
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

end Feec.EinsteinBianchi.BoundedFailure
