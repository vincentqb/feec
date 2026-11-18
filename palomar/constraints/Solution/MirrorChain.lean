module

public import Solution.MirrorForward
public import Feec.Models.Cube.MirrorConstraint

/-!
# TSD states of the challenge are constrained states of `D(L)` of the mirror complex

For a TSD state `X` with `L X = Y` (the challenge's operator), the complexification `cplx X`
lies in the domain of the wave operator of `Feec.Models.Cube.MirrorBGG.complexQ` and in its
constraint, with `L (cplx X) = cplx Y`, and `Y` is again TSD (`forward`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.1

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open Set MeasureTheory

@[expose] public noncomputable section

namespace FEEC

open Feec Feec.Domain Feec.Models.BoundedDomain
open Feec.Models.Cube.FEM (cubeDomain cubeDomain_eq_Q)
open Feec.Models.Cube.Geometry (Q)
open Feec.Models.Cube.RowWise (ofRealL ofRealF ofRealF_apply)
open Feec.Models.Cube.MirrorWeakSymmetry
open Feec.Models.Cube.MirrorBGG (SpaceQ complexQ tsdQ W2Q)
open Feec.HilbertComplex (totalSub)

theorem castL2_apply_eq {Ω Ω' : Set (Fin 3 → ℝ)} (h : Ω = Ω') {ι ι' : Type*} [Fintype ι]
    [Fintype ι'] {f : L2F ℝ Ω ι} {g : L2F ℝ Ω ι'} {i : ι} {j : ι'} (c : ℝ)
    (e : f i = c • g j) : castL2 h ι f i = c • castL2 h ι' g j := by
  subst h; exact e

theorem sgn3_eq_sg2 (i : Fin 3) : sgn3 i = sg2 i := by
  fin_cases i <;> norm_num [sgn3, sg2]

theorem cplxE_eq (X : MState) : cplxE X = ofRealF (cQ Ix (fieldE X.2.1)) := by
  refine PiLp.ext fun p => ?_
  rw [ofRealF_apply]
  change ofRealL _ _ = ofRealL _ _
  congr 1
  have e := castL2_apply_eq (cubeDomain_eq_Q 3) (f := fieldE X.2.1) (g := X.2.1 p.1) (i := p)
    (j := eq1 p.2) 1 (one_smul ℝ _).symm
  rw [one_smul] at e
  exact e.symm

theorem cplxB_eq (X : MState) : cplxB X = ofRealF (cQ Ix (fieldB X.2.2.2)) := by
  refine PiLp.ext fun p => ?_
  rw [ofRealF_apply, castL2_apply_eq (cubeDomain_eq_Q 3) (sgn3 p.2) (g := X.2.2.2 p.1)
    (j := ix2 p.2) rfl, (ofRealL _).map_smul, sgn3_eq_sg2]
  change ((sg2 p.2 : ℝ) : ℂ) • ofRealL _ _ = _
  rw [← real_smul_Lp]
  rfl

theorem mem_tsd_cQ {u : L2F ℝ (cubeDomain 3) Ix} (hu : u ∈ tsd (cubeDomain 3)) :
    cQ Ix u ∈ tsd (Q (Fin 3)) :=
  (mem_tsd_castL2_symm (cubeDomain_eq_Q 3) (cQ Ix u)).1 (by
    rw [LinearIsometryEquiv.symm_apply_apply]; exact hu)

/-- **TSD states of `D(L)` are constrained states of `D(L)` of the mirror complex**, with
`L (cplx X) = cplx (L X)`, and `L X` is TSD. -/
theorem forward {X Y : MState} (h : mirrorData.IsWave X Y) (hX : IsTSDState X) :
    ∃ hd : cplx X ∈ complexQ.wave.domain, cplx X ∈ totalSub tsdQ ∧
      complexQ.wave ⟨_, hd⟩ = cplx Y ∧ IsTSDState Y := by
  obtain ⟨h0, hM, hE, hB⟩ := hX
  obtain ⟨σ, φ, u, -, hu, -, -, -, hS, hd1⟩ := id h
  have hum : X.2.1 ∈ mirrorData.dt1.domain := hu ▸ u.2
  obtain ⟨hEd, eE⟩ := cplxE_mem X hum
  obtain ⟨hBd, eB⟩ := mem_adjoint_cplx h h0 hM
  rw [isTSD_iff, toIx_mat1] at hE
  rw [isTSD_iff, toIx_mat2] at hB
  have hE' : fieldE (Ω := cubeDomain 3) X.2.1 ∈ tsd (cubeDomain 3) := hE
  have hB' : fieldB (Ω := cubeDomain 3) X.2.2.2 ∈ tsd (cubeDomain 3) := hB
  have hEc := ofRealF_tsd (mem_tsd_cQ hE')
  have hBc := ofRealF_tsd (mem_tsd_cQ hB')
  rw [← cplxE_eq] at hEc
  rw [← cplxB_eq] at hBc
  obtain ⟨hEs, hEt, hEv⟩ := hEc
  obtain ⟨hBs, hBt, hBv⟩ := hBc
  have hE1 := Feec.Models.Cube.MirrorBGG.mem_tsdQ_one_of_tsd hEd hEs hEt hEv
  have hB2 := Feec.Models.Cube.MirrorBGG.mem_tsdQ_two_of_tsd hBd hBs hBt hBv
  obtain ⟨hEa, eEa⟩ := Feec.Models.Cube.MirrorBGG.mem_adjoint_d₀_of_mem_tsdQ hE1
  have hc : cplx X ∈ totalSub tsdQ :=
    Feec.Models.Cube.MirrorBGG.mem_tsdQ_iff.2 ⟨rfl, hE1, rfl, hB2⟩
  have hd : cplx X ∈ complexQ.wave.domain :=
    complexQ.mem_wave_domain_fin3 (Submodule.zero_mem _) hEd hEa hBd
  set x : complexQ.wave.domain := ⟨_, hd⟩
  have hred : complexQ.wave x ∈ totalSub tsdQ :=
    Feec.Models.Cube.MirrorBGG.reducingSubcomplexQ.isReducing_wave.mapsTo x hc
  have hax := (Feec.Models.Cube.MirrorBGG.mem_tsdQ_iff.1 hred).2.2.1
  have hreal : realL (cplx X) = X := realL_cplx h0 hM
  have hY1 : Y.1 = 0 := fst_eq_zero_of_isWave h fun τ ψ _ => by
      have e := inner_rowsW1L_dt0 (x := x) hc ψ
      rwa [show rowsW1L (stEL (x : PiLp 2 SpaceQ)) = X.2.1 from
        congrArg (fun Z : MState => Z.2.1) hreal] at e
  have hY2 : Y.2.2.1 = 0 := by
    rw [hS]
    change wedge (cube 3) 1 (u : L2Vec (cube 3) 1) = 0
    rw [wedge_eq, hu, ← show rowsW1L (cplxE X) = X.2.1 from
      congrArg (fun Z : MState => Z.2.1) hreal]
    exact wsL2_rowsW1L_of_symm hEs
  have hw : complexQ.wave x = cplx Y := by
    refine PiLp.ext fun i => ?_
    fin_cases i
    · refine (complexQ.wave_apply_fin3_zero x).trans ?_
      change _ = (0 : SpaceQ 0)
      rw [neg_eq_zero]
      exact (LinearPMap.apply_congr' _ _ _ rfl).trans eEa
    · refine (complexQ.wave_apply_fin3_one x).trans ?_
      have e0 : complexQ.d 0 1 ⟨(x : PiLp 2 SpaceQ) 0, x.2.1 0 1⟩ = 0 :=
        LinearPMap.map_zero _
      rw [e0, zero_sub, show (complexQ.d 1 2)† ⟨(x : PiLp 2 SpaceQ) 2, x.2.2 2 1⟩ =
        -cplxE Y from (LinearPMap.apply_congr' _ _ _ rfl).trans eB]
      exact neg_neg (cplxE Y)
    · have e : complexQ.wave x 2 = WithLp.toLp 2 (Feec.Models.Cube.MirrorBGG.axialQ (cplxE X),
          ofRealRows2 fun a => cQ _ (mirrorData.dt1 ⟨X.2.1, hum⟩ a)) :=
        (complexQ.wave_apply_fin3_two x).trans ((LinearPMap.apply_congr' _ _ _ rfl).trans eE)
      have hax' : Feec.Models.Cube.MirrorBGG.axialQ (cplxE X) = 0 :=
        (congrArg (fun z : W2Q => (WithLp.ofLp z).1) e).symm.trans hax
      refine e.trans ?_
      change _ = WithLp.toLp 2 (0, cplxB Y)
      rw [hax', cplxB, hd1, show mirrorData.dt1 ⟨X.2.1, hum⟩ = mirrorData.dt1 u from
        congrArg _ (Subtype.ext hu.symm)]
  refine ⟨hd, hc, hw, ?_⟩
  rw [← realL_cplx hY1 hY2, ← hw]
  exact isTSDState_realL hred

end FEEC
