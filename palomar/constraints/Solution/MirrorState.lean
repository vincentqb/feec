module

public import Solution.MirrorTSD

/-!
# Constrained states of `Feec`'s mirror complex as states of the challenge

`Feec.Models.Cube.MirrorBGG.complexQ` has complex scalars and matrix fields; its real part
`realL x = (0, rows of Re E, 0, rows of ⋆ Re B)` is a state of the challenge's mirror data. On the
constraint, `realL` intertwines the wave operators (`isWave_realL`: the equations of
`Feec.Models.Cube.MirrorWeakSymmetry.TSDDatum.exactWave`, pointwise in time, for states of
`D(L)`), and constrained states have TSD real parts (`isTSDState_realL`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.1 ((6.1), (6.2))

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set MeasureTheory

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.Models.BoundedDomain
open Feec.Models.Cube.FEM (cubeDomain cubeDomain_eq_Q)
open Feec.Models.Cube.Geometry (Q)
open Feec.Models.Cube.RowWise (reF)
open Feec.Models.Cube.MirrorWeakSymmetry
open Feec.Models.Cube.MirrorBGG (SpaceQ complexQ tsdQ W2Q)
open Feec.HilbertComplex (totalSub)

/-- A state of the challenge on the cube. -/
abbrev MState : Type := L2Form (cube 3) 0 × L2Vec (cube 3) 1 × L2Form (cube 3) 2 × L2Vec (cube 3) 2

/-- **The real state of a mirror state**: `(0, rows of Re E, 0, rows of ⋆ Re B)`. -/
def realL : PiLp 2 SpaceQ →L[ℝ] MState :=
  (0 : PiLp 2 SpaceQ →L[ℝ] L2Form (cube 3) 0).prod ((rowsW1L.comp stEL).prod
    ((0 : PiLp 2 SpaceQ →L[ℝ] L2Form (cube 3) 2).prod (rowsW2L.comp stBL)))

theorem realL_apply (x : PiLp 2 SpaceQ) :
    realL x = (0, rowsW1L (stEL x), 0, rowsW2L (stBL x)) := rfl

theorem eq1_eq (b : Fin 3) : eq1 b = ix1 b := rfl
theorem eq2_eq (i : Fin 3) : eq2 i = ix2 i := rfl

/-! ### TSD real parts -/

theorem fieldE_castL2 {Ω Ω' : Set (Fin 3 → ℝ)} (h : Ω = Ω')
    (v : Fin 3 → L2F ℝ Ω' (formIdx 3 1)) :
    fieldE (WithLp.toLp 2 fun a => (castL2 h _).symm (v a) : L2Vec Ω 1) =
      (castL2 h Ix).symm (WithLp.toLp 2 fun p => v p.1 (ix1 p.2)) := by
  subst h; rfl

theorem fieldB_castL2 {Ω Ω' : Set (Fin 3 → ℝ)} (h : Ω = Ω')
    (v : Fin 3 → L2F ℝ Ω' (formIdx 3 2)) :
    fieldB (WithLp.toLp 2 fun a => (castL2 h _).symm (v a) : L2Vec Ω 2) =
      (castL2 h Ix).symm (WithLp.toLp 2 fun p => sgn3 p.2 • v p.1 (ix2 p.2)) := by
  subst h; rfl

theorem mem_tsd_castL2_symm {Ω Ω' : Set (Fin 3 → ℝ)} (h : Ω = Ω') (u : L2F ℝ Ω' Ix) :
    (castL2 h Ix).symm u ∈ tsd Ω ↔ u ∈ tsd Ω' := by
  subst h; rfl

theorem sgn3_mul_sg2 (i : Fin 3) : sgn3 i * sg2 i = 1 := by
  fin_cases i <;> norm_num [sgn3, sg2]

/-- The electric field of `realL x` is the real part of `E`. -/
theorem fieldE_rowsW1L (E : Feec.Models.Cube.Mirror.MQ) :
    fieldE (rowsW1L E) = (cQ Ix).symm (reF E) := by
  have h := fieldE_castL2 (cubeDomain_eq_Q 3) (fun a => rowRe E a)
  refine (congrArg fieldE (PiLp.ext fun a => rfl)).trans (h.trans ?_)
  congr 1
  refine PiLp.ext fun p => ?_
  change rowRe E p.1 (eq1 p.2) = _
  rw [rowRe_eq1]
  rfl

/-- The magnetic field of `realL x` is the real part of `B`. -/
theorem fieldB_rowsW2L (B : Feec.Models.Cube.Mirror.MQ) :
    fieldB (rowsW2L B) = (cQ Ix).symm (reF B) := by
  have h := fieldB_castL2 (cubeDomain_eq_Q 3) (fun a => rowRe2 B a)
  refine (congrArg fieldB (PiLp.ext fun a => rfl)).trans (h.trans ?_)
  congr 1
  refine PiLp.ext fun p => ?_
  change sgn3 p.2 • rowRe2 B p.1 (eq2 p.2) = _
  rw [rowRe2_eq2, smul_smul, sgn3_mul_sg2, one_smul]
  rfl

/-- **Constrained mirror states have TSD real parts.** -/
theorem isTSDState_realL {x : PiLp 2 SpaceQ} (hx : x ∈ totalSub tsdQ) :
    IsTSDState (realL x) := by
  obtain ⟨-, -, hE, hB⟩ := Feec.Models.Cube.MirrorBGG.tsd_of_mem_tsdQ hx
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [isTSD_iff, toIx_mat1]
    change fieldE (rowsW1L (stEL x)) ∈ tsd (cube 3)
    rw [fieldE_rowsW1L]
    exact (mem_tsd_castL2_symm (cubeDomain_eq_Q 3) _).2 (reF_mem_tsd hE.1 hE.2.1 hE.2.2)
  · rw [isTSD_iff, toIx_mat2]
    change fieldB (rowsW2L (stBL x)) ∈ tsd (cube 3)
    rw [fieldB_rowsW2L]
    exact (mem_tsd_castL2_symm (cubeDomain_eq_Q 3) _).2 (reF_mem_tsd hB.1 hB.2.1 hB.2.2)

/-! ### The wave operators -/

theorem dPart_apply_eq {n : ℕ} {J : Finset (Fin n)} {k : ℤ} (x : (dPart J k).domain) :
    dPart J k x = Feec.Models.Cube.DeRhamIdent.dPart (cubeDomain n) J k
      ⟨(x : L2Form (cube n) k), dPart_eq J k ▸ x.2⟩ :=
  LinearPMap.apply_of_eq' (dPart_eq J k) x

/-- A vector of the domain of `vecOp (dPart {a} k)` as `Feec`'s vector of domain elements. -/
def toBU1 (v : mirrorData.dt1.domain) : BU1 :=
  WithLp.toLp 2 fun a => ⟨(v : L2Vec (cube 3) 1) a, by
    have h := v.2 a; rw [show (fun a => dPart {a} 1) a = dPart {a} 1 from rfl, dPart_eq] at h
    exact h⟩

/-- The same in degree `0`. -/
def toBU0 (ψ : mirrorData.dt0.domain) : BU0 :=
  WithLp.toLp 2 fun a => ⟨(ψ : L2Vec (cube 3) 0) a, by
    have h := ψ.2 a; rw [show (fun a => dPart {a} 0) a = dPart {a} 0 from rfl, dPart_eq] at h
    exact h⟩

theorem bIncl1_toBU1 (v : mirrorData.dt1.domain) :
    bIncl1 (toBU1 v) = (v : L2Vec (cube 3) 1) := rfl

theorem bD1_toBU1 (v : mirrorData.dt1.domain) : bD1 (toBU1 v) = mirrorData.dt1 v :=
  PiLp.ext fun a => (dPart_apply_eq ⟨(v : L2Vec (cube 3) 1) a, v.2 a⟩).symm

theorem bIncl1_bD0_toBU0 (ψ : mirrorData.dt0.domain) : bIncl1 (bD0 (toBU0 ψ)) = mirrorData.dt0 ψ :=
  PiLp.ext fun a => (dPart_apply_eq ⟨(ψ : L2Vec (cube 3) 0) a, ψ.2 a⟩).symm

section State

variable {x : complexQ.wave.domain}

/-- The electric field of a state of `D(L)` lies in the domain of `d̃¹`. -/
theorem rowsW1L_mem : rowsW1L (stEL x) ∈ mirrorData.dt1.domain := fun a => by
  change _ ∈ (dPart {a} 1).domain
  rw [dPart_eq]
  exact (rowsBU_mem (eDom x) a).1

variable (hx : (x : PiLp 2 SpaceQ) ∈ totalSub tsdQ)
include hx

/-- `⟪E, d̃ψ⟫ = 0` for the bottom `0`-forms. -/
theorem inner_rowsW1L_dt0 (ψ : mirrorData.dt0.domain) :
    ⟪rowsW1L (stEL x), mirrorData.dt0 ψ⟫ = 0 := by
  have h := inner_rowsBU_bD0 hx (toBU0 ψ)
  rw [inner_BU1, bIncl1_rowsBU_state, bIncl1_bD0_toBU0] at h
  exact h

/-- `⟪E', v⟫ + ⟪⋆B, d̃v⟫ = 0`. -/
theorem inner_rowsW1L_wave (v : mirrorData.dt1.domain) :
    ⟪rowsW1L (stEL (complexQ.wave x)), (v : L2Vec (cube 3) 1)⟫ +
      ⟪rowsW2L (stBL x), mirrorData.dt1 v⟫ = 0 := by
  rw [← bIncl1_toBU1 v, ← bD1_toBU1 v, inner_rowsW1L, inner_rowsW2L]
  obtain ⟨hX, eX⟩ := ofRealRows_BU1_mem (toBU1 v)
  have hM : (WithLp.ofLp (stW2 x)).1 = 0 := (Feec.Models.Cube.MirrorBGG.mem_tsdQ_iff.1 hx).2.2.1
  rw [stEL_apply, inner_waveQ_one x hx _ hX, eX, WithLp.prod_inner_apply, WithLp.ofLp_toLp, hM,
    inner_zero_left, zero_add, map_neg, stBL_apply]
  exact neg_add_cancel _

/-- **`realL` intertwines the wave operators on the constraint.** -/
theorem isWave_realL : mirrorData.IsWave (realL x) (realL (complexQ.wave x)) := by
  have hsym := (Feec.Models.Cube.MirrorBGG.tsd_of_mem_tsdQ hx).2.2.1.1
  refine ⟨0, 0, ⟨_, rowsW1L_mem⟩, rfl, rfl, ?_, fun τ ψ _ => ?_, fun v => ?_, ?_, ?_⟩
  · rw [LinearPMap.map_zero, Submodule.coe_zero, map_zero]
  · change ⟪(0 : L2Form (cube 3) 0), (τ : L2Form (cube 3) 0)⟫ = _
    rw [inner_zero_left]
    exact (inner_rowsW1L_dt0 hx ψ).symm
  · have h := inner_rowsW1L_wave hx v
    change ⟪rowsW1L (stEL (complexQ.wave x)), (v : L2Vec (cube 3) 1)⟫ =
      -⟪mirrorData.dt0 0, (v : L2Vec (cube 3) 1)⟫ - ⟪(0 : L2Form (cube 3) 2), mirrorData.S1 v⟫ -
        ⟪rowsW2L (stBL x), mirrorData.dt1 v⟫
    rw [LinearPMap.map_zero, inner_zero_left, inner_zero_left]
    linarith
  · change (0 : L2Form (cube 3) 2) = wedge (cube 3) 1 (rowsW1L (stEL x))
    rw [wedge_eq]
    exact (wsL2_rowsW1L_of_symm hsym).symm
  · change rowsW2L (stBL (complexQ.wave x)) = mirrorData.dt1 ⟨_, rowsW1L_mem⟩
    rw [← bD1_rowsBU_state, ← bD1_toBU1]
    congr 1
    refine PiLp.ext fun a => Subtype.ext ?_
    exact congrArg Subtype.val (rowsBU_apply_of_mem _ a (rowsBU_mem (eDom x) a).1)

end State

end FEEC
