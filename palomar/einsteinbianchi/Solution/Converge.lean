module

public import Solution.CubeUnique
public import Solution.Bounded
public import Feec.Physics.EinsteinBianchi.BoundedInitialData
public import Feec.Instances.EinsteinBianchiFEMCube
public import Feec.ForMathlib.LinearPMap.SkewMaximal

/-!
# With the electric boundary conditions the method converges from every datum of `D(L)`

The convergence clauses of `FEEC.weakSymmetry_electric`.

**The challenge's system is `Feec`'s forms model.** The state map `toWS`,
`(σ, u, M, ρ) ↦ (−σ, u, (M, ρ))` (`Feec.Instances.EinsteinBianchi.FEM.vecInv`; `Γ̄ = L²Λ⁰(Q)`), is
an isometric isomorphism onto the total space of `Feec.EinsteinBianchi.MatrixModel.formsShort`,
the short Hilbert complex `Γ̄ → (L²Λ¹)³ → L²Λ² × (L²Λ²)³` of (6.1). A pair of its graph is a pair
of the challenge's relation `IsWave` (`isWave_of_mem_graph`: the identities of (6.1) at a point of
`D(L)`, `Feec.EinsteinBianchi.BoundedFailure.eb_point` and its siblings); conversely, the relation
is skew (`IsWave.sub`, `IsWave.inner_eq_zero`) and the wave operator is skew-adjoint, hence
maximal skew (`LinearPMap.IsSkewAdjoint.mem_graph_of_inner`), so every pair of the relation lies in
the graph (`mem_graph_of_isWave`). Strong solutions correspond (`isStrongSolution_toWS`,
`isStrongSolution_ofWS`).

**The semi-discrete solutions are `Feec`'s.** A solution of (6.5) of the challenge on `[0, T]`
for `cubeQ` has compatible data (`exists_toDS` on `[0, T/2]`,
`Feec.Models.Cube.WeakSymmetry.cubeWave_exists_iff_compatible_u`), so `Feec`'s solution on `[0, T]`
from the same data exists (`cubeWave_exists_unique`), and by uniqueness (`cube_wave_unique`) its
energy vectors are those of the challenge's solution (`exists_DS_eq`).

**Convergence** is then `Feec.EinsteinBianchi.BoundedConvergence.tendsto_of_isStrongSolution`,
and every state is the limit of initial states of trajectories by
`Feec.EinsteinBianchi.BoundedConvergence.exists_tendsto_dvec` (`exists_trajectories_tendsto`,
`cube_converges`). From the TSD datum `(0, 0, 0, ⋆β)` of `datumBeta_spec` the limit leaves TSD,
and the discrete fields leave the closed sets of TSD and of symmetric fields with it
(`cube_beta`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.1 ((6.1), (6.2)), §6.2 (Prop 6.2), §6.3 ((6.5))

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open Set Filter Topology MeasureTheory

@[expose] public noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 8000000

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.HilbertComplex Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry Feec.EinsteinBianchi.WaveFEM
open Feec.Models.BoundedDomain (Ix tsd)
open Feec.EinsteinBianchi.MatrixModel (formsShort)
open Feec.EinsteinBianchi.BoundedFailure (WS comp0 comp1 comp2 compML compρL comp0L comp1L
  compML_apply compρL_apply waveOf waveOf_eq σOf φOf uOf gammaOf graphFst_σOf incl1_uOf dom0 dom1
  mem_gammaOf ea_point eb_point ec_point ed_point solutionOfStrong dvec embQ
  eventually_not_mem_of_tendsto)
open Feec.EinsteinBianchi.BoundedConvergence (vecL solutionOfStrong_vec_eq
  tendsto_of_isStrongSolution exists_tendsto_dvec)
open Feec.Instances.EinsteinBianchi.FEM (vecInv vecL_vecInv norm_vecL norm_vecInv gammaTop)

attribute [-instance] Feec.ShortHilbertComplex.instNormedSpaceRealW3
  Feec.ShortHilbertComplex.instIsScalarTowerRealW3

/-! ### The state map -/

/-- The states `(σ, u, M, ρ)` of (6.1) on the cube, in `Feec`'s types. -/
abbrev St : Type := W0 × Wv W1 × W2 × Wv W2

/-- A shortcut for the inner product of the total space (synthesis through `W3` fails). -/
instance instIPSWS : InnerProductSpace ℝ WS := inferInstance

/-- **The state map** `(σ, u, M, ρ) ↦ (−σ, u, (M, ρ))` into the total space of the forms model. -/
def toWS : St →L[ℝ] WS := vecInv ∘L Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2)

/-- Its inverse: the energy coordinates `(−x₀, x₁, M, ρ)` of a point. -/
def ofWS : WS →L[ℝ] St :=
  (Feec.Instances.EinsteinBianchi.FEM.EState.mkL (P0 := W0) (Pt1 := Wv W1) (P2 := W2)
    (Pt2 := Wv W2)).symm.toContinuousLinearMap ∘L vecL

theorem vecL_toWS (x : St) : vecL (toWS x) = Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2) x :=
  vecL_vecInv _

theorem ofWS_toWS (x : St) : ofWS (toWS x) = x := by
  change (Feec.Instances.EinsteinBianchi.FEM.EState.mkL (P0 := W0) (Pt1 := Wv W1) (P2 := W2)
    (Pt2 := Wv W2)).symm (vecL (toWS x)) = x
  rw [vecL_toWS]
  exact (Feec.Instances.EinsteinBianchi.FEM.EState.mkL (P0 := W0) (Pt1 := Wv W1) (P2 := W2)
    (Pt2 := Wv W2)).symm_apply_apply x

theorem vecL_injective : Function.Injective vecL := fun a b h => by
  have : ‖a - b‖ = 0 := by rw [← norm_vecL, map_sub, h, sub_self, norm_zero]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

theorem toWS_ofWS (y : WS) : toWS (ofWS y) = y := by
  refine vecL_injective ?_
  rw [vecL_toWS]
  exact (Feec.Instances.EinsteinBianchi.FEM.EState.mkL (P0 := W0) (Pt1 := Wv W1) (P2 := W2)
    (Pt2 := Wv W2)).apply_symm_apply (vecL y)

/-- `vecInv` as a linear isometry. -/
def vecInvLI : Feec.Instances.EinsteinBianchi.FEM.CEnergy →ₗᵢ[ℝ] WS :=
  ⟨vecInv.toLinearMap, norm_vecInv⟩

/-- **The state map preserves the energy inner product.** -/
theorem inner_toWS (a b : St) : ⟪toWS a, toWS b⟫ =
    ⟪a.1, b.1⟫ + ⟪a.2.1, b.2.1⟫ + ⟪a.2.2.1, b.2.2.1⟫ + ⟪a.2.2.2, b.2.2.2⟫ := by
  have h := vecInvLI.inner_map_map (Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2) a)
    (Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2) b)
  exact h.trans (Feec.BGG.isEnergyEmbedding_energyEmb a b)

theorem coe_comp0_toWS (x : St) : ((comp0 (toWS x) : bggHilb.Γbar) : W0) = -x.1 := by
  change ((-gammaTop.symm x.1 : bggHilb.Γbar) : W0) = -x.1
  rw [Submodule.coe_neg]
  exact congrArg Neg.neg (gammaTop.apply_symm_apply x.1)

theorem comp1_toWS (x : St) : comp1 (toWS x) = x.2.1 := rfl

theorem compML_toWS (x : St) : compML (toWS x) = x.2.2.1 := rfl

theorem compρL_toWS (x : St) : compρL (toWS x) = x.2.2.2 := rfl

/-! ### The relation `IsWave` is the graph of the wave operator -/

/-- **A pair of the graph is a pair of the relation**: the identities of (6.1) at a point of
`D(L)`. -/
theorem isWave_of_mem_graph {U V : St} (h : (toWS U, toWS V) ∈ formsShort.wave.graph) :
    𝒟.IsWave U V := by
  obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff _).1 h
  have hz1' : (z : WS) = toWS U := hz1
  have hz2' : formsShort.wave z = toWS V := hz2
  have hx : toWS U ∈ formsShort.wave.domain := hz1' ▸ z.2
  have hw : waveOf (toWS U) = toWS V := by
    rw [waveOf_eq hx, ← hz2']
    exact congrArg _ (Subtype.ext hz1'.symm)
  have hσ : ((graphDom D0 (σOf (toWS U)) : D0.domain) : W0) = U.1 := by
    change D0.graphFst (σOf (toWS U)) = U.1
    rw [graphFst_σOf (dom0 hx), coe_comp0_toWS, neg_neg]
  have hu : ((ofWv1 (uOf (toWS U)) : 𝒟.dt1.domain) : Wv W1) = U.2.1 := by
    rw [coe_ofWv1, incl1_uOf (dom1 hx)]; rfl
  have hcV : ((comp0 (waveOf (toWS U)) : bggHilb.Γbar) : W0) = -V.1 := by
    rw [hw, coe_comp0_toWS]
  refine ⟨graphDom D0 (σOf (toWS U)), e0.symm (rp (φOf (toWS U))), ofWv1 (uOf (toWS U)), hσ, hu,
    ?_, fun τ ψ hτψ => ?_, fun v => ?_, ?_, ?_⟩
  · have hg := mem_gammaOf (toWS U)
    rw [cubeWaveData_d0, cubeWaveData_S0] at hg
    change D0 (graphDom D0 (σOf (toWS U))) = wsL2 (Ω := cubeDomain 3) 0 (incl0 (rp (φOf (toWS U))))
    rw [apply_graphDom]
    exact hg
  · have hτ : cubeWaveData.d0 (D0.toGraphSpace τ) =
        cubeWaveData.S0 (toGraphVec0 (e0 ψ)) := by
      rw [cubeWaveData_d0, cubeWaveData_S0, ιt0_toGraphVec0, LinearPMap.graphSnd_toGraphSpace,
        incl0_e0]
      exact hτψ
    have he := ea_point hx (D0.toGraphSpace τ) (toGraphVec0 (e0 ψ)) hτ
    rw [hcV, neg_neg] at he
    change ⟪V.1, D0.graphFst (D0.toGraphSpace τ)⟫ -
      ⟪incl1 (uOf (toWS U)), ιt1 (bggDt0 (toGraphVec0 (e0 ψ)))⟫ = 0 at he
    rw [LinearPMap.graphFst_toGraphSpace, ιt1_bggDt0_toGraphVec0, dt0_e0, incl1_uOf (dom1 hx)]
      at he
    rw [hu]
    exact sub_eq_zero.1 he
  · have he := eb_point hx (e1 v)
    rw [hw] at he
    change ⟪comp1 (toWS V), incl1 (e1 v)⟫ + ⟪ιt1 (bggDt0 (φOf (toWS U))), incl1 (e1 v)⟫ +
      ⟪compML (toWS U), bggSegment.S1 (e1 v)⟫ + ⟪compρL (toWS U), bggSegment.dt1 (e1 v)⟫ = 0
      at he
    rw [comp1_toWS, compML_toWS, compρL_toWS, incl1_e1, ιt1_bggDt0, S1_e1, dt1_e1] at he
    change ⟪V.2.1, (v : Wv W1)⟫ = -⟪𝒟.dt0 (e0.symm (rp (φOf (toWS U)))), (v : Wv W1)⟫ -
      ⟪U.2.2.1, 𝒟.S1 v⟫ - ⟪U.2.2.2, 𝒟.dt1 v⟫
    rw [dt0_e0_symm]
    linarith
  · have he := ec_point hx
    rw [hw] at he
    change V.2.2.1 = 𝒟.S1 (ofWv1 (uOf (toWS U)))
    rw [S1_ofWv1]
    exact he
  · have he := ed_point hx
    rw [hw] at he
    change V.2.2.2 = 𝒟.dt1 (ofWv1 (uOf (toWS U)))
    rw [dt1_ofWv1]
    exact he

/-- The component sum `⟪a, b⟫` of two states. -/
def stInner (a b : St) : ℝ := ⟪a.1, b.1⟫ + ⟪a.2.1, b.2.1⟫ + ⟪a.2.2.1, b.2.2.1⟫ + ⟪a.2.2.2, b.2.2.2⟫

/-- **The relation is skew**: `⟪V, Z⟫ + ⟪W, U⟫ = 0` for pairs `(U, V)`, `(Z, W)`. -/
theorem isWave_skew {U V Z W : St} (h : 𝒟.IsWave U V) (h' : 𝒟.IsWave Z W) :
    stInner V Z + stInner W U = 0 := by
  have e1 := h.inner_eq_zero
  have e2 := h'.inner_eq_zero
  have e3 := (h.sub h').inner_eq_zero
  simp only [Prod.fst_sub, Prod.snd_sub, inner_sub_left, inner_sub_right] at e3
  unfold stInner
  linarith

/-- **A pair of the relation lies in the graph**: the wave operator is skew-adjoint, hence
maximal skew. -/
theorem mem_graph_of_isWave {U V : St} (h : 𝒟.IsWave U V) :
    (toWS U, toWS V) ∈ formsShort.wave.graph := by
  refine formsShort.isSkewAdjoint_wave.mem_graph_of_inner fun z => ?_
  have hz : 𝒟.IsWave (ofWS z) (ofWS (formsShort.wave z)) := isWave_of_mem_graph (by
    rw [toWS_ofWS, toWS_ofWS]; exact formsShort.wave.mem_graph z)
  have hs := isWave_skew h hz
  have e1 : ⟪toWS V, (z : WS)⟫ = stInner V (ofWS z) := by
    rw [show stInner V (ofWS z) = ⟪toWS V, toWS (ofWS z)⟫ from (inner_toWS _ _).symm,
      toWS_ofWS]
  have e2 : ⟪toWS U, formsShort.wave z⟫ = stInner (ofWS (formsShort.wave z)) U := by
    rw [show stInner (ofWS (formsShort.wave z)) U =
      ⟪toWS (ofWS (formsShort.wave z)), toWS U⟫ from (inner_toWS _ _).symm, toWS_ofWS,
      real_inner_comm]
  rw [e1, e2]
  linarith

/-- **The challenge's strong solutions are `Feec`'s.** -/
theorem isStrongSolution_toWS {I : Set ℝ} {U : ℝ → St}
    (hU : IsStrongSolution {p | 𝒟.IsWave p.1 p.2} I U) :
    Feec.Evolution.IsStrongSolution formsShort.wave I 0 fun t => toWS (U t) where
  continuousOn := toWS.continuous.comp_continuousOn hU.1
  deriv t ht := by
    obtain ⟨V, hV, hd⟩ := hU.2 t ht
    exact ⟨toWS V, mem_graph_of_isWave hV,
      (toWS.hasFDerivAt.comp_hasDerivWithinAt t hd).congr_deriv (add_zero _).symm⟩

/-- **`Feec`'s strong solutions are the challenge's.** -/
theorem isStrongSolution_ofWS {I : Set ℝ} {X : ℝ → WS}
    (hX : Feec.Evolution.IsStrongSolution formsShort.wave I 0 X) :
    IsStrongSolution {p | 𝒟.IsWave p.1 p.2} I fun t => ofWS (X t) := by
  refine ⟨ofWS.continuous.comp_continuousOn hX.continuousOn, fun t ht => ?_⟩
  obtain ⟨v, hv, hd⟩ := hX.deriv t ht
  have hd' : HasDerivWithinAt X v I t := hd.congr_deriv (add_zero v)
  refine ⟨ofWS v, isWave_of_mem_graph ?_, ofWS.hasFDerivAt.comp_hasDerivWithinAt t hd'⟩
  rw [toWS_ofWS, toWS_ofWS]; exact hv

/-! ### The semi-discrete solutions -/

section Disc

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

/-- **`Feec`'s semi-discrete solutions are solutions of (6.5) of the challenge.** -/
theorem isDiscreteWave_ofDS {N : ℕ} {T : ℝ} {f : ℝ → Wv W1}
    (sh : @Feec.BGG.DiscreteSolution (cubeFEM hT hB N).V0h (cubeFEM hT hB N).V1h
      (cubeFEM hT hB N).W2h (cubeFEM hT hB N).Vt0h (cubeFEM hT hB N).Vt1h (cubeFEM hT hB N).Wt2h
      _ _ _ _ _ _ _ _ _ _ _ _ (cubeWave hT hB N) T (cubeSource hT hB N f)) :
    (cubeQ hT hB N).IsDiscreteWave T f (fun t => ((sh.σ t : U0) : 𝒟.d0.domain))
      (fun t => e0.symm (sh.φ t : Wv U0)) (fun t => ofWv1 (sh.u t : Wv U1))
      (fun t => (sh.M t : W2)) (fun t => (sh.ρ t : Wv W2)) (fun t => ((sh.lam t : U1) : W1)) := by
  refine ⟨?_, ?_, ?_, ?_, fun t ht => ?_,
    fun t => ((sh.σ' t : U0) : W0), fun t => ((ofWv1 (sh.u' t : Wv U1) : 𝒟.dt1.domain) : Wv W1),
    fun t => (sh.M' t : W2), fun t => (sh.ρ' t : Wv W2), fun t ht => ?_⟩
  · exact continuous_subtype_val.comp_continuousOn (continuous_subtype_val.comp_continuousOn sh.cσ)
  · exact incl1CLM.continuous.comp_continuousOn (continuous_subtype_val.comp_continuousOn sh.cu)
  · exact continuous_subtype_val.comp_continuousOn sh.cM
  · exact continuous_subtype_val.comp_continuousOn sh.cρ
  · have hc := sh.constraint ht
    exact ⟨(sh.σ t).2, fun a => (sh.φ t).2 a, fun a => (sh.u t).2 a, (sh.M t).2,
      fun a => (sh.ρ t).2 a, (sh.lam t).2,
      (congrArg (fun x : (cubeFEM hT hB N).V1h => ((x : U1) : W1)) hc :)⟩
  · have ht' : t ∈ Icc 0 T := Ico_subset_Icc_self ht
    have hu1 := hasDerivWithinAt_coe _ (sh.du t ht)
    have hu2 := hasDerivWithinAt_piCoe D1.domain hu1
    refine ⟨hasDerivWithinAt_coe _ (hasDerivWithinAt_coe _ (sh.dσ t ht)), hu2,
      hasDerivWithinAt_coe _ (sh.dM t ht), hasDerivWithinAt_coe _ (sh.dρ t ht),
      fun τ ψ hτ hψ => ?_, fun v hv => ?_, fun z hz => ?_, fun z hz => ?_⟩
    · exact sh.ea t ht' ⟨τ, hτ⟩ ⟨e0 ψ, e0_mem hT hB N hψ⟩
    · have := sh.eb t ht ⟨e1 v, e1_mem hT hB N hv⟩
      have hs := inner_cubeSource hT hB N f t ⟨e1 v, e1_mem hT hB N hv⟩
      exact this.trans hs
    · have := sh.ec t ht ⟨z, hz⟩
      exact sub_eq_zero.1 this
    · have := sh.ed t ht ⟨z, fun a => hz a⟩
      exact sub_eq_zero.1 this

/-- **A solution of (6.5) of the challenge on `[0, T]` is `Feec`'s**: there is a `Feec` solution
on `[0, T]` with the same energy vectors. -/
theorem exists_DS_eq {N : ℕ} {T : ℝ} (hT0 : 0 < T) {σ : ℝ → 𝒟.d0.domain}
    {φ : ℝ → 𝒟.dt0.domain} {u : ℝ → 𝒟.dt1.domain} {M : ℝ → W2} {ρ : ℝ → Wv W2}
    {lam : ℝ → W1} (hw : (cubeQ hT hB N).IsDiscreteWave T 0 σ φ u M ρ lam) :
    ∃ s : @Feec.BGG.DiscreteSolution (cubeFEM hT hB N).V0h (cubeFEM hT hB N).V1h
      (cubeFEM hT hB N).W2h (cubeFEM hT hB N).Vt0h (cubeFEM hT hB N).Vt1h (cubeFEM hT hB N).Wt2h
      _ _ _ _ _ _ _ _ _ _ _ _ (cubeWave hT hB N) T (cubeSource hT hB N 0),
      ∀ t ∈ Icc 0 T, dvec (cubeFEM hT hB N) s t =
        Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2) ((σ t : W0), (u t : Wv W1), M t, ρ t) := by
  have hT2 : 0 < T / 2 := half_pos hT0
  obtain ⟨s₁, hs₁⟩ := exists_toDS hT hB N (half_lt_self hT0) hw
  have hf0 : ContinuousOn (cubeSource hT hB N (0 : ℝ → Wv W1)) (Icc 0 T) :=
    continuousOn_cubeSource hT hB N continuousOn_const
  have hC2 := (cubeWave_exists_iff_compatible_u hT hB N hT2
    (continuousOn_cubeSource hT hB N continuousOn_const) (fe0 hT hB N (σ 0))
    (fet1 hT hB N (u 0)) (fe2 hT hB N (M 0)) (fet2 hT hB N (ρ 0))).1
    ⟨s₁, (hs₁ 0).1, (hs₁ 0).2.1, (hs₁ 0).2.2.1, (hs₁ 0).2.2.2.1⟩
  obtain ⟨s, ⟨e0', e1', e2', e3'⟩, -, -⟩ := cubeWave_exists_unique hT hB N hT0 hf0
    (fe0 hT hB N (σ 0)) (fet1 hT hB N (u 0)) (fe2 hT hB N (M 0)) (fet2 hT hB N (ρ 0)) hC2
  have hw' := isDiscreteWave_ofDS hT hB s
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.le⟩
  have m := hw.2.2.2.2.1 0 h0
  have hσ0 : σ 0 = ((s.σ 0 : U0) : 𝒟.d0.domain) := by
    rw [e0']; exact Subtype.ext ((cubeQ hT hB N).π0_id _ m.1).symm
  have hu0 : u 0 = ofWv1 (s.u 0 : Wv U1) := by
    rw [e1']; exact Subtype.ext ((cubeQ hT hB N).πt1_id _ m.2.2.1).symm
  have hM0 : M 0 = (s.M 0 : W2) := by
    rw [e2']; exact ((cubeQ hT hB N).π2_id _ m.2.2.2.1).symm
  have hρ0 : ρ 0 = (s.ρ 0 : Wv W2) := by
    rw [e3']; exact ((cubeQ hT hB N).πt2_id _ m.2.2.2.2.1).symm
  obtain ⟨hu, -⟩ := cube_wave_unique hT hB N hT0 hw hw' hσ0 hu0 hM0 hρ0
  refine ⟨s, fun t ht => ?_⟩
  obtain ⟨a, b, c, d⟩ := hu t ht
  change Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2) (((s.σ t : U0) : W0), incl1 (s.u t : Wv U1),
    (s.M t : W2), (s.ρ t : Wv W2)) = _
  rw [a, b, c, d]
  rfl

/-- `‖ι a - ι b‖` is the state norm of `a - b` for the energy embedding `ι`. -/
theorem norm_energyEmb_sub (a b : St) :
    ‖Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2) a - Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2) b‖ =
      stateNorm (a - b) :=
  Feec.BGG.Discrete.norm_sub_of_isEnergyEmbedding Feec.BGG.isEnergyEmbedding_energyEmb a b

theorem norm_u_le_stateNorm (x : St) : ‖x.2.1‖ ≤ stateNorm x :=
  (le_abs_self _).trans (Real.abs_le_sqrt (by
    nlinarith [sq_nonneg ‖x.1‖, sq_nonneg ‖x.2.2.1‖, sq_nonneg ‖x.2.2.2‖]))

theorem norm_ρ_le_stateNorm (x : St) : ‖x.2.2.2‖ ≤ stateNorm x :=
  (le_abs_self _).trans (Real.abs_le_sqrt (by
    nlinarith [sq_nonneg ‖x.1‖, sq_nonneg ‖x.2.1‖, sq_nonneg ‖x.2.2.1‖]))

/-- The trajectory of a solution of (6.5) of the challenge. -/
theorem trajectory_spec {N : ℕ} {T : ℝ} {Uh : ℝ → St}
    (h : Uh ∈ (cubeQ hT hB N).trajectories T 0) :
    ∃ σ φ u M ρ lam, (cubeQ hT hB N).IsDiscreteWave T 0 σ φ u M ρ lam ∧
      ∀ t, Uh t = ((σ t : W0), (u t : Wv W1), M t, ρ t) := h

/-! ### Convergence -/

/-- **Every state is the limit of initial states of trajectories of (6.5)** (no source), although
their initial values are constrained: `Feec`'s solutions of `exists_tendsto_dvec`. -/
theorem exists_trajectories_tendsto (U₀ : St) {T : ℝ} (hT0 : 0 < T) :
    ∃ Uh : ℕ → ℝ → St, (∀ N, Uh N ∈ (cubeQ hT hB N).trajectories T 0) ∧
      Tendsto (fun N => stateNorm (U₀ - Uh N 0)) atTop (𝓝 0) := by
  obtain ⟨sh, hsh⟩ := exists_tendsto_dvec hT hB hT0 (toWS U₀)
  refine ⟨fun N t => ((((sh N).σ t : U0) : W0), incl1 ((sh N).u t : Wv U1), ((sh N).M t : W2),
    ((sh N).ρ t : Wv W2)), fun N => ⟨_, _, _, _, _, _, isDiscreteWave_ofDS hT hB (sh N),
      fun _ => rfl⟩, hsh.congr fun N => ?_⟩
  have e : dvec (cubeFEM hT hB N) (sh N) 0 = Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2)
      ((((sh N).σ 0 : U0) : W0), incl1 ((sh N).u 0 : Wv U1), ((sh N).M 0 : W2),
        ((sh N).ρ 0 : Wv W2)) := rfl
  rw [vecL_toWS, e, norm_energyEmb_sub]

/-- **Convergence of (6.5) from every datum of `D(L)`** (the electric boundary conditions): a
strong solution exists, the datum is the limit of initial states of trajectories of (6.5), and
every family of trajectories of (6.5) whose initial states converge to the datum converges to
every strong solution uniformly on `[0, T]`. -/
theorem cube_converges {U₀ V : St} {T : ℝ} (hW : 𝒟.IsWave U₀ V) (hT0 : 0 < T) :
    (∃ U, U 0 = U₀ ∧ IsStrongSolution {p | 𝒟.IsWave p.1 p.2} (Icc 0 T) U) ∧
    (∃ Uh : ℕ → ℝ → St, (∀ N, Uh N ∈ (cubeQ hT hB N).trajectories T 0) ∧
      Tendsto (fun N => stateNorm (U₀ - Uh N 0)) atTop (𝓝 0)) ∧
    ∀ U (Uh : ℕ → ℝ → St), U 0 = U₀ → IsStrongSolution {p | 𝒟.IsWave p.1 p.2} (Icc 0 T) U →
      (∀ N, Uh N ∈ (cubeQ hT hB N).trajectories T 0) →
      Tendsto (fun N => stateNorm (U₀ - Uh N 0)) atTop (𝓝 0) →
      ∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T, stateNorm (U t - Uh N t) < ε := by
  refine ⟨?_, exists_trajectories_tendsto hT hB U₀ hT0, fun U Uh hU0 hU hUh h0 => ?_⟩
  · have hdom : toWS U₀ ∈ formsShort.wave.domain :=
      LinearPMap.mem_domain_of_mem_graph (mem_graph_of_isWave hW)
    refine ⟨fun t => ofWS (formsShort.toHilbertComplex.waveGroup.S t (toWS U₀)), ?_,
      isStrongSolution_ofWS (formsShort.toHilbertComplex.isStrongSolution_waveGroup hdom T)⟩
    simp [ofWS_toWS]
  have hV := isStrongSolution_toWS hU
  have hDS : ∀ N, ∃ s : @Feec.BGG.DiscreteSolution (cubeFEM hT hB N).V0h (cubeFEM hT hB N).V1h
      (cubeFEM hT hB N).W2h (cubeFEM hT hB N).Vt0h (cubeFEM hT hB N).Vt1h (cubeFEM hT hB N).Wt2h
      _ _ _ _ _ _ _ _ _ _ _ _ (cubeWave hT hB N) T (cubeSource hT hB N 0),
      ∀ t ∈ Icc 0 T, dvec (cubeFEM hT hB N) s t =
        Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2) (Uh N t) := fun N => by
    obtain ⟨σ, φ, u, M, ρ, lam, hw, he⟩ := trajectory_spec hT hB (hUh N)
    obtain ⟨s, hs⟩ := exists_DS_eq hT hB hT0 hw
    exact ⟨s, fun t ht => (hs t ht).trans (by rw [he t])⟩
  choose s hs using hDS
  have key : ∀ N, ∀ t ∈ Icc 0 T, ‖(solutionOfStrong hV).vec t - dvec (cubeFEM hT hB N) (s N) t‖ =
      stateNorm (U t - Uh N t) := fun N t ht => by
    rw [solutionOfStrong_vec_eq hV ht, vecL_toWS, hs N t ht, norm_energyEmb_sub]
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.le⟩
  have h0' : Tendsto (fun N => ‖(solutionOfStrong hV).vec 0 - dvec (cubeFEM hT hB N) (s N) 0‖)
      atTop (𝓝 0) := by
    refine h0.congr fun N => ?_
    rw [key N 0 h0T, hU0]
  intro ε hε
  filter_upwards [tendsto_of_isStrongSolution hT hB hT0 hV s h0' ε hε] with N hN t ht
  rw [← key N t ht]
  exact hN t ht

/-! ### The TSD datum `(0, 0, 0, ⋆β)` -/

theorem isOpen_cube3 : IsOpen (cube 3) := isOpen_cubeDomain 3
theorem isBounded_cube3 : Bornology.IsBounded (cube 3) := isBounded_cubeDomain 3

/-- The TSD fields of the cube form a closed set. -/
theorem isClosed_setOf_isTSD : IsClosed {w : L2Vec (cube 3) 1 | IsTSD (mat1 w)} := by
  have e : {w : L2Vec (cube 3) 1 | IsTSD (mat1 w)} =
      fieldE ⁻¹' (tsd (cube 3) : Set (L2F ℝ (cube 3) Ix)) := by
    ext w
    rw [mem_ofPred_eq, isTSD_iff, toIx_mat1]
    rfl
  rw [e]
  exact (Feec.Models.BoundedDomain.isClosed_tsd).preimage fieldE.continuous

/-- The symmetric magnetic fields form a closed set. -/
theorem isClosed_setOf_symm :
    IsClosed {w : L2Vec (cube 3) 2 | ∀ a i, mat2 w a i = mat2 w i a} := by
  have hc : ∀ a i, Continuous fun w : L2Vec (cube 3) 2 => mat2 w a i := fun a i =>
    ((PiLp.continuous_apply 2 _ (a, i)).comp fieldB.continuous :)
  simp only [ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_eq (hc a i) (hc i a)

/-- **From the TSD datum `(0, 0, 0, ⋆β)` the method converges to a solution that leaves TSD.** -/
theorem cube_beta : ∃ (U₀ V : St), 𝒟.IsWave U₀ V ∧ IsTSDState (Ω := cube 3) U₀ ∧ ∀ T > 0,
    ∀ U, U 0 = U₀ → IsStrongSolution {p | 𝒟.IsWave p.1 p.2} (Icc 0 T) U →
      (∃ t ∈ Icc 0 T, ¬IsTSD (mat1 (Ω := cube 3) (U t).2.1) ∧ ∀ Uh : ℕ → ℝ → St,
        (∀ N, Uh N ∈ (cubeQ hT hB N).trajectories T 0) →
        Tendsto (fun N => stateNorm (U₀ - Uh N 0)) atTop (𝓝 0) →
        ∀ᶠ N in atTop, ¬IsTSD (mat1 (Ω := cube 3) (Uh N t).2.1)) ∧
      ∃ t ∈ Icc 0 T, (∃ a i, mat2 (Ω := cube 3) (U t).2.2.2 a i ≠ mat2 (U t).2.2.2 i a) ∧
        ∀ Uh : ℕ → ℝ → St, (∀ N, Uh N ∈ (cubeQ hT hB N).trajectories T 0) →
        Tendsto (fun N => stateNorm (U₀ - Uh N 0)) atTop (𝓝 0) →
        ∀ᶠ N in atTop, ∃ a i, mat2 (Ω := cube 3) (Uh N t).2.2.2 a i ≠ mat2 (Uh N t).2.2.2 i a := by
  obtain ⟨⟨V, hV⟩, hTSD, hspec⟩ := datumBeta_spec isOpen_cube3 isBounded_cube3
    Feec.EinsteinBianchi.BoundedFailure.nonempty_cubeDomain
  rw [bggData_cube_eq] at hV hspec
  refine ⟨datumBeta isOpen_cube3 isBounded_cube3, V, hV, hTSD, fun T hT0 U hU0 hU => ?_⟩
  obtain ⟨⟨t₁, ht₁, hE⟩, ⟨t₂, ht₂, a, i, hB'⟩⟩ := (hspec T hT0).2 U hU0 hU
  obtain ⟨-, -, hconv⟩ := cube_converges hT hB hV hT0
  refine ⟨⟨t₁, ht₁, hE, fun Uh hUh h0 => ?_⟩, ⟨t₂, ht₂, ⟨a, i, hB'⟩, fun Uh hUh h0 => ?_⟩⟩
  · have hc := hconv U Uh hU0 hU hUh h0
    have := eventually_not_mem_of_tendsto isClosed_setOf_isTSD (x := (U t₁).2.1) hE
      (y := fun N => (Uh N t₁).2.1) fun ε hε => (hc ε hε).mono fun N hN =>
        lt_of_le_of_lt (norm_u_le_stateNorm (U t₁ - Uh N t₁)) (hN t₁ ht₁)
    exact this
  · have hc := hconv U Uh hU0 hU hUh h0
    have hnot : (U t₂).2.2.2 ∉ {w : L2Vec (cube 3) 2 | ∀ a i, mat2 w a i = mat2 w i a} :=
      fun h => hB' (h a i)
    have := eventually_not_mem_of_tendsto isClosed_setOf_symm hnot
      (y := fun N => (Uh N t₂).2.2.2) fun ε hε => (hc ε hε).mono fun N hN =>
        lt_of_le_of_lt (norm_ρ_le_stateNorm (U t₂ - Uh N t₂)) (hN t₂ ht₂)
    refine this.mono fun N hN => ?_
    by_contra h
    push Not at h
    exact hN h

end Disc

end FEEC
