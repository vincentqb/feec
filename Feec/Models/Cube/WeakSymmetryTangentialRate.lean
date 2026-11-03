module

public import Feec.Models.Cube.TangentialRate
public import Feec.Models.Cube.WeakSymmetryWave

/-!
# Non-vacuity of the rates on the cube beyond flat data

The rates of Thm 5.5 (`cubeFEM_rate_tr`, `Feec.Models.Cube.WeakSymmetryFEM`) and of the
semi-discrete scheme (6.5) (`cubeWave_rate_tr`, `Feec.Models.Cube.WeakSymmetryWave`) are stated
on the class `FEM.IsCsFormTr 0` (`Feec.Models.Cube.TangentialRate`): `C²` fields up to `∂Q` whose
tangential components vanish on `∂Q`, with no condition on the normal components. This module
shows that the class reaches beyond flat data (`FEM.IsCsFormMin`).

* The field `u = ((sin 2πy₁ sin 2πy₂) dx₀, 0, 0)` (with `σ = φ = λ = 0`, divergence free with
  `S¹u = 0`) has a normal component that does not vanish on `∂Q` (`normalWitness_ne_zero`, the
  first row being `normalWitness`) and is not flat (`not_isCsFormMin_tangentialU0`).
* `waveTangential T` is a classical solution of (6.2) built on it (`u(t) = ū`,
  `ρ(t) = t curl ū`, `M = 0`), meeting the hypotheses of `cubeWave_rate_tr`
  (`waveTangential_hyps`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3, Table 5.1, Thm 5.5; §6.2 (6.4), §6.3 (6.5), Table 6.1
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], §6.2 (vanishing tangential
  traces), Ch. 7 (approximation estimates)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace ContDiff
open MeasureTheory Set Filter

@[expose] public noncomputable section

namespace Feec.Models.Cube.WeakSymmetry

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex Feec.Models.Cube.FEM

/-! ### A smooth solution of (5.3) with nonzero normal component on `∂Q` -/

section TangentialManufactured

/-- A derivative along `eᵢ` of a function independent of `yᵢ` vanishes. -/
theorem fderiv_coordDir_eq_zero_of_indep {g : (Fin 3 → ℝ) → ℝ} (hg : Differentiable ℝ g)
    {i : Fin 3} (hind : ∀ (y : Fin 3 → ℝ) (t : ℝ), g (y + t • coordDir i) = g y)
    (y : Fin 3 → ℝ) : fderiv ℝ g y (coordDir i) = 0 := by
  have h1 : HasDerivAt (fun t : ℝ => g (y + t • coordDir i)) (fderiv ℝ g y (coordDir i)) 0 := by
    have hl : HasDerivAt (fun t : ℝ => y + t • (coordDir i : Fin 3 → ℝ)) (coordDir i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordDir i : Fin 3 → ℝ)).const_add y
    have h2 : HasFDerivAt g (fderiv ℝ g y) (y + (0 : ℝ) • (coordDir i : Fin 3 → ℝ)) := by
      simpa using (hg y).hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) hl
  have h2 : HasDerivAt (fun t : ℝ => g (y + t • coordDir i)) 0 0 := by
    simp_rw [hind]; exact hasDerivAt_const _ _
  exact h1.unique h2

/-- The components of the witness `w = (sin 2πy₁ sin 2πy₂) dx₀`. -/
abbrev tangentialψ : formIdx 3 1 → (Fin 3 → ℝ) → ℝ := formComp (normalWitness (n := 3))

theorem contDiff_tangentialψ (r : formIdx 3 1) : ContDiff ℝ ∞ (tangentialψ r) :=
  contDiff_pi.1 contDiff_normalWitness r.1

/-- **`w` is divergence free**: `dᵗw = -∂₀ w₀ = 0` (`w₀` does not depend on `y₀`). -/
theorem formalAdj_tangentialψ : (extDerivOp ℝ 3 0).formalAdj.apply tangentialψ = 0 := by
  funext r y
  rw [formalAdj_extDerivOp_apply, extDAdj, Pi.zero_apply, Pi.zero_apply, neg_eq_zero]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : j ∉ r.1 := Finset.mem_compl.1 hj
  rw [formExt_of_card tangentialψ (card_insert_of_formIdx r hj')]
  have hr : r.1 = ∅ := Finset.card_eq_zero.1 (by exact_mod_cast r.2)
  have hins : insert j r.1 = {j} := by rw [hr]; rfl
  by_cases hj0 : j = 0
  · subst hj0
    have hd : Differentiable ℝ (tangentialψ ⟨insert 0 r.1, card_insert_of_formIdx r hj'⟩) :=
      (contDiff_tangentialψ _).differentiable (by simp)
    rw [fderiv_coordDir_eq_zero_of_indep hd (fun z t => ?_) y, mul_zero]
    simp only [tangentialψ, formComp, normalWitness, hins, ↓reduceIte]
    refine Finset.prod_congr rfl fun l hl => ?_
    have hl0 : l ≠ 0 := Finset.ne_of_mem_erase hl
    simp [coordDir, hl0]
  · have h0 : tangentialψ ⟨insert j r.1, card_insert_of_formIdx r hj'⟩ = fun _ => 0 := by
      funext z
      simp only [tangentialψ, formComp, normalWitness, hins]
      rw [ite_eq_right_iff]; intro h; exact absurd (Finset.singleton_inj.1 h) hj0
    rw [h0]; simp

/-- The class of `w` in `L²Λ¹(Q)`. -/
def tangentialX : W1 :=
  formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) 1
    ⟨normalWitness, contDiff_normalWitness.continuous⟩

theorem exists_isCsFormTr_tangentialX : ∃ L, 0 ≤ L ∧ IsCsFormTr 0 1 L tangentialX :=
  isCsFormTr_normalWitness 0

/-- **`w ∈ H̊Λ¹(Q)`** with `d_min w = (dw)|_Q`. -/
theorem tangentialX_mem : ∃ h : tangentialX ∈ D1.domain, D1 ⟨_, h⟩ =
    formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) 2
      ⟨FiniteElement.extDeriv normalWitness,
        continuous_extDeriv ((contDiff_normalWitness (n := 3)).of_le (by simp))⟩ := by
  obtain ⟨L, -, hL⟩ := exists_bound_iteratedFDeriv_le (n := 3) (m := 1)
    ((contDiff_normalWitness (n := 3)).of_le (by simp))
  obtain ⟨L', -, hL'⟩ := exists_bound_iteratedFDeriv_le (n := 3) (m := 0)
    (contDiff_extDeriv (m := 0) ((contDiff_normalWitness (n := 3)).of_le (by simp)))
  exact mem_minimal_of_isTangentialZero (L := max L L')
    ((contDiff_normalWitness (n := 3)).of_le (by simp)) isDeg_normalWitness
    isTangentialZero_normalWitness
    (fun y hy => by simpa using (hL 0 (Nat.zero_le _) y hy).trans (le_max_left _ _))
    (fun y hy => by
      simpa [norm_iteratedFDeriv_one] using (hL 1 le_rfl y hy).trans (le_max_left _ _))
    (fun y hy => by simpa using (hL' 0 le_rfl y hy).trans (le_max_right _ _))

/-- The witness as a point of `H̊Λ¹(Q)`. -/
def tangentialU0 : U1 := ⟨tangentialX, tangentialX_mem.1⟩

/-- **The manufactured `u`** with nonzero normal component on `∂Q`: first row
`(sin 2πy₁ sin 2πy₂) dx₀`, other rows zero. -/
def tangentialU : Wv U1 := WithLp.toLp 2 (Pi.single 0 tangentialU0)

theorem tangentialU_apply_of_ne {a : Fin 3} (ha : a ≠ 0) : tangentialU a = 0 := by
  change (Pi.single (0 : Fin 3) tangentialU0 : Fin 3 → U1) a = 0
  exact Pi.single_eq_of_ne ha _

theorem tangentialU_apply_zero : tangentialU 0 = tangentialU0 := by
  change (Pi.single (0 : Fin 3) tangentialU0 : Fin 3 → U1) 0 = _
  exact Pi.single_eq_same _ _

/-- `⟪w, d ψ⟫ = 0` for `ψ ∈ H̊Λ⁰(Q)` (`dᵗw = 0`, Green's formula on `D(d_min)`). -/
theorem inner_tangentialX_D0 (x : U0) : ⟪tangentialX, D0 x⟫ = 0 := by
  have hψs : ∀ r, ContDiff ℝ 1 (tangentialψ r) := fun r =>
    (contDiff_tangentialψ r).of_le (by simp)
  have hψ : ∀ r, MemLp (tangentialψ r) 2 (volume.restrict (cubeDomain 3)) := fun r =>
    memLp_of_continuous (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3)
      (hψs r).continuous
  have hAψ : ∀ r, MemLp ((extDerivOp ℝ 3 0).formalAdj.apply tangentialψ r) 2
      (volume.restrict (cubeDomain 3)) := fun r => by
    rw [formalAdj_tangentialψ]; exact MemLp.zero
  have key := (extDerivOp ℝ 3 0).minimal_green (isOpen_cubeDomain 3) (extDerivOp_isOrderLE 0) x
    hψs hψ hAψ
  have h0 : toL2F hAψ = 0 := by
    refine PiLp.ext fun r => ?_
    rw [PiLp.zero_apply]
    refine Lp.ext ?_
    filter_upwards [(hAψ r).coeFn_toLp, Lp.coeFn_zero ℝ 2 (volume.restrict (cubeDomain 3))]
      with y h1 h2
    change ((hAψ r).toLp _ : L2 ℝ (cubeDomain 3)) y = _
    rw [h1, h2, formalAdj_tangentialψ]
    rfl
  change ⟪toL2F hψ, D0 x⟫ = 0
  rw [real_inner_comm, key, h0, inner_zero_right]

theorem inner_tangentialU_dt0 (ψ : Wv U0) : ⟪tangentialU, bggSegment.dt0 ψ⟫ = 0 := by
  rw [inner_Vt, Fin.sum_univ_three, tangentialU_apply_of_ne (by decide : (1 : Fin 3) ≠ 0),
    tangentialU_apply_of_ne (by decide : (2 : Fin 3) ≠ 0), inner_zero_left, inner_zero_left,
    add_zero, add_zero, tangentialU_apply_zero]
  exact inner_tangentialX_D0 (ψ 0)

/-- **`S¹u = 0`** (`S¹u = Σₐ dxₐ ∧ uₐ = dx₀ ∧ w₀ dx₀ = 0`). -/
theorem segS1_tangentialU : bggSegment.S1 tangentialU = 0 := by
  change wsL2 (Ω := cubeDomain 3) 1 (incl1 tangentialU) = 0
  refine PiLp.ext fun t => ?_
  rw [wsL2_apply, PiLp.zero_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [wsCoeff_eq]
  split_ifs with h
  · by_cases ha : p.1 = 0
    · have hp : (incl1 tangentialU) p.1 p.2 = 0 := by
        change (((tangentialU p.1 : U1) : W1) p.2) = 0
        rw [ha, tangentialU_apply_zero]
        refine formL2_apply_eq_zero fun y => ?_
        change normalWitness y p.2.1 = 0
        simp only [normalWitness]
        rw [ite_eq_right_iff]
        intro h'
        exfalso
        have : (0 : Fin 3) ∈ t.1.erase p.1 := by rw [h.2, h']; exact Finset.mem_singleton_self _
        rw [ha] at this
        simp at this
      rw [hp, smul_zero]
    · have hp : (incl1 tangentialU) p.1 = 0 := by
        change ((tangentialU p.1 : U1) : W1) = 0
        rw [tangentialU_apply_of_ne ha]; rfl
      rw [hp, PiLp.zero_apply, smul_zero]
  · rw [zero_smul]

/-- **The manufactured `u` is not flat**: its first row has a nonzero normal component at the
boundary point `(0, ⅛, ⅛)` (`normalWitness_ne_zero`) and is in no class `IsCsFormMin`. -/
theorem not_isCsFormMin_tangentialU0 (s : ℕ) (L : ℝ) :
    ¬ IsCsFormMin s 1 L ((tangentialU 0 : U1) : W1) := by
  rw [tangentialU_apply_zero]
  exact not_isCsFormMin_normalWitness s L

theorem tangentialU_ne_zero : tangentialU ≠ 0 := by
  intro h
  have h0 : tangentialX = 0 := by
    have := congrArg (fun z : Wv U1 => ((z 0 : U1) : W1)) h
    simpa [tangentialU_apply_zero, tangentialU0] using this
  exact not_isCsFormMin_normalWitness (n := 3) 0 0
    (by change IsCsFormMin 0 1 0 tangentialX; rw [h0]; exact IsCsFormMin.zero 0 1 le_rfl)

end TangentialManufactured

/-! ### A classical solution of (6.2) with nonzero normal component on `∂Q` -/

section WaveTangential

/-- The components of `dw` (`w` the witness). -/
abbrev tangentialDψ : formIdx 3 2 → (Fin 3 → ℝ) → ℝ :=
  formComp (FiniteElement.extDeriv (normalWitness (n := 3)))

theorem contDiff_tangentialDψ (r : formIdx 3 2) : ContDiff ℝ 1 (tangentialDψ r) :=
  contDiff_pi.1 (contDiff_extDeriv (m := 1) ((contDiff_normalWitness (n := 3)).of_le (by simp)))
    r.1

theorem memLp_tangentialDψ (r : formIdx 3 2) :
    MemLp (tangentialDψ r) 2 (volume.restrict (cubeDomain 3)) :=
  memLp_of_continuous (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3)
    (contDiff_tangentialDψ r).continuous

theorem memLp_formalAdj_tangentialDψ (r : formIdx 3 1) :
    MemLp ((extDerivOp ℝ 3 1).formalAdj.apply tangentialDψ r) 2
      (volume.restrict (cubeDomain 3)) :=
  memLp_of_continuous (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3)
    (ConstCoeffOp.continuous_apply _ (formalAdj_extDerivOp_isOrderLE 1) contDiff_tangentialDψ r)

/-- The source `f̄ = (curl* curl w, 0, 0) ∈ (L²Λ¹)³` (`dᵗ dw`, an `L²` field: `w` is smooth up to
the boundary). -/
def waveTangentialSrc : Wv W1 :=
  WithLp.toLp 2 (Pi.single 0 (toL2F memLp_formalAdj_tangentialDψ))

theorem waveTangentialSrc_apply_of_ne {a : Fin 3} (ha : a ≠ 0) : waveTangentialSrc a = 0 := by
  simp [waveTangentialSrc, ha]

theorem waveTangentialSrc_apply_zero :
    waveTangentialSrc 0 = toL2F memLp_formalAdj_tangentialDψ := by
  simp [waveTangentialSrc]

theorem D1_tangentialU0 : D1 tangentialU0 = toL2F memLp_tangentialDψ :=
  tangentialX_mem.2

/-- `⟪curl u, curl v⟫ = ⟪f̄, v⟫` (Green's formula on `D(d_min)`; no condition on `dw` at `∂Q`). -/
theorem inner_dt1_tangentialU (v : Wv U1) :
    ⟪bggSegment.dt1 tangentialU, bggSegment.dt1 v⟫ = ⟪waveTangentialSrc, incl1 v⟫ := by
  rw [inner_Vt, inner_Vt, Fin.sum_univ_three, Fin.sum_univ_three]
  have h1 : ∀ a : Fin 3, a ≠ 0 → (bggSegment.dt1 tangentialU) a = 0 := fun a ha => by
    change D1 (tangentialU a) = 0
    rw [tangentialU_apply_of_ne ha, LinearPMap.map_zero]
  have h2 : ∀ a : Fin 3, a ≠ 0 → waveTangentialSrc a = 0 := fun a ha =>
    waveTangentialSrc_apply_of_ne ha
  have n1 : (1 : Fin 3) ≠ 0 := by simp
  have n2 : (2 : Fin 3) ≠ 0 := by simp
  have z1 : ⟪(bggSegment.dt1 tangentialU) 1, (bggSegment.dt1 v) 1⟫ = 0 := by
    rw [h1 1 n1]; exact inner_zero_left _
  have z2 : ⟪(bggSegment.dt1 tangentialU) 2, (bggSegment.dt1 v) 2⟫ = 0 := by
    rw [h1 2 n2]; exact inner_zero_left _
  have z3 : ⟪waveTangentialSrc 1, (incl1 v) 1⟫ = 0 := by
    rw [h2 1 n1]; exact inner_zero_left _
  have z4 : ⟪waveTangentialSrc 2, (incl1 v) 2⟫ = 0 := by
    rw [h2 2 n2]; exact inner_zero_left _
  simp only [z1, z2, z3, z4, add_zero]
  have e0 : (bggSegment.dt1 tangentialU) 0 = toL2F memLp_tangentialDψ := by
    change D1 (tangentialU 0) = _
    rw [tangentialU_apply_zero, D1_tangentialU0]
  have e1 : waveTangentialSrc 0 = toL2F memLp_formalAdj_tangentialDψ :=
    waveTangentialSrc_apply_zero
  simp only [e0, e1]
  have key := (extDerivOp ℝ 3 1).minimal_green (isOpen_cubeDomain 3) (extDerivOp_isOrderLE 1)
    (v 0) contDiff_tangentialDψ memLp_tangentialDψ memLp_formalAdj_tangentialDψ
  have e2 : (bggSegment.dt1 v) 0 = D1 (v 0) := rfl
  have e3 : (incl1 v) 0 = ((v 0 : U1) : W1) := rfl
  simp only [e2, e3]
  rw [real_inner_comm, key, real_inner_comm]

/-- **A classical solution of (6.2) on the cube whose fields are not flat at `∂Q`**: `σ = φ = 0`,
`u(t) = ū = tangentialU` (normal component nonzero on `{y₀ = 0}`), `M ≡ 0` (`S¹ū = 0`),
`ρ(t) = t curl ū`, `ℓ = 0`, source `f(t) = t f̄`, `f̄ = (curl* curl w, 0, 0)`. -/
def waveTangential (T : ℝ) :
    Feec.BGG.ExactWave bggSegment T (srcFun fun t => t • waveTangentialSrc) where
  σ _ := 0
  φ _ := 0
  u _ := tangentialU
  M _ := 0
  ρ t := t • bggSegment.dt1 tangentialU
  ℓ _ := 0
  σ' _ := 0
  φ' _ := 0
  u' _ := 0
  M' _ := 0
  ρ' _ := bggSegment.dt1 tangentialU
  ℓ' _ := 0
  cσ := continuousOn_const
  cu := continuousOn_const
  cM := continuousOn_const
  cρ := (continuous_id.smul continuous_const).continuousOn
  cdφ := continuousOn_const
  cSu := continuousOn_const
  cdu := continuousOn_const
  cℓ _ := continuousOn_const
  cσ' := continuousOn_const
  cu' := continuousOn_const
  cM' := continuousOn_const
  cρ' := continuousOn_const
  cdφ' := continuousOn_const
  cSu' := continuousOn_const
  cdu' := continuousOn_const
  cℓ' _ := continuousOn_const
  dσ t _ := hasDerivWithinAt_const _ _ _
  du t _ := hasDerivWithinAt_const _ _ _
  dM t _ := hasDerivWithinAt_const _ _ _
  dρ t _ := by
    simpa using ((hasDerivAt_id t).smul_const (bggSegment.dt1 tangentialU)).hasDerivWithinAt
  ddφ t _ := by simpa using hasDerivWithinAt_const t (Ici t) (bggSegment.dt0 (0 : Wv U0))
  dSu t _ := by simpa using hasDerivWithinAt_const t (Ici t) (bggSegment.S1 tangentialU)
  ddu t _ := by simpa using hasDerivWithinAt_const t (Ici t) (bggSegment.dt1 tangentialU)
  dℓ t _ μ := by simpa using hasDerivWithinAt_const t (Ici t) (0 : ℝ)
  ea _ _ τ ψ := by
    simp only [inner_zero_left, LinearMap.zero_apply, zero_sub, sub_zero, neg_eq_zero]
    exact inner_tangentialU_dt0 ψ
  eb t _ v := by
    rw [srcFun_apply]
    simp only [map_zero, inner_zero_left, zero_add, inner_smul_left, RCLike.conj_to_real,
      inner_dt1_tangentialU]
  ec _ _ N := by simp [segS1_tangentialU]
  ed _ _ μ := by simp
  ee _ _ := by rw [map_zero, map_zero]
  ee' _ _ := by rw [map_zero, map_zero]

/-- **Non-vacuity of `cubeWave_rate_tr` beyond the flat class**: `waveTangential T` meets the
hypotheses of `cubeWave_rate_tr` with one bound `L` on `[0,T]`, has `u(t) ≠ 0`, and its `u(t)` is
not flat (`not_isCsFormMin_tangentialU0`). -/
theorem waveTangential_hyps {T : ℝ} (hT : 0 < T) : ∃ L, 0 ≤ L ∧
    (∀ t ∈ Icc 0 T, IsSmoothStateTr L ((waveTangential T).σ t) ((waveTangential T).φ t)
        ((waveTangential T).u t) ((waveTangential T).M t) ((waveTangential T).ρ t) ∧
      IsSmoothStateTr L ((waveTangential T).σ' t) ((waveTangential T).φ' t)
        ((waveTangential T).u' t) ((waveTangential T).M' t) ((waveTangential T).ρ' t)) ∧
    (∀ t ∈ Icc 0 T, ∀ μ : U1, |(waveTangential T).ℓ t μ| ≤ L * ‖μ‖ ∧
      |(waveTangential T).ℓ' t μ| ≤ L * ‖μ‖) ∧
    (∀ t, (waveTangential T).u t ≠ 0) := by
  obtain ⟨Lu, hLu0, hLu⟩ := exists_isCsFormTr_tangentialX
  obtain ⟨Ld, hLd0, hLd⟩ := exists_isCsFormTr (n := 3) 0 (k := 2)
    (contDiff_extDeriv (m := 2) ((contDiff_normalWitness (n := 3)).of_le (by simp)))
    (IsDeg.extDeriv isDeg_normalWitness)
    (isTangentialZero_normalWitness.extDeriv
      ((contDiff_normalWitness (n := 3)).differentiable (by simp)))
  have hd0 : IsCsFormTr 0 2 Ld ((bggSegment.dt1 tangentialU) 0) := by
    have e : (bggSegment.dt1 tangentialU) 0 = toL2F memLp_tangentialDψ := by
      change D1 (tangentialU 0) = _
      rw [tangentialU_apply_zero, D1_tangentialU0]
    rw [e]; exact hLd
  have hdne : ∀ a : Fin 3, a ≠ 0 → (bggSegment.dt1 tangentialU) a = 0 := fun a ha => by
    change D1 (tangentialU a) = 0
    rw [tangentialU_apply_of_ne ha, LinearPMap.map_zero]
  set L1 := Lu + Ld
  have hL10 : 0 ≤ L1 := add_nonneg hLu0 hLd0
  refine ⟨(1 + T) * L1, by positivity, fun t ht => ?_, fun t _ μ => ?_,
    fun _ => tangentialU_ne_zero⟩
  · have hta : |t| ≤ 1 + T := by rw [abs_of_nonneg ht.1]; linarith [ht.2]
    have hLL : ∀ {L' : ℝ}, L' ≤ L1 → L' ≤ (1 + T) * L1 := fun h =>
      h.trans (le_mul_of_one_le_left hL10 (by linarith))
    have hz : ∀ k : ℕ, IsCsFormTr 0 (k : ℤ) ((1 + T) * L1)
        (0 : L2F ℝ (cubeDomain 3) (formIdx 3 k)) := fun k => isCsFormTr_zero 0 k (by positivity)
    have hρ : ∀ a, IsCsFormTr 0 2 ((1 + T) * L1) ((bggSegment.dt1 tangentialU) a) := fun a => by
      by_cases ha : a = 0
      · subst ha; exact hd0.mono (hLL (le_add_of_nonneg_left hLu0))
      · rw [hdne a ha]; exact hz 2
    have hρt : ∀ a, IsCsFormTr 0 2 ((1 + T) * L1)
        ((t • bggSegment.dt1 tangentialU : Wv W2) a) := fun a => by
      rw [PiLp.smul_apply]
      by_cases ha : a = 0
      · subst ha
        exact (hd0.smul t).mono (mul_le_mul hta (le_add_of_nonneg_left hLu0) hLd0 (by linarith))
      · rw [hdne a ha, smul_zero]; exact hz 2
    have hu : ∀ a, IsCsFormTr 0 1 ((1 + T) * L1) ((tangentialU a : U1) : W1) := fun a => by
      by_cases ha : a = 0
      · subst ha; rw [tangentialU_apply_zero]; exact hLu.mono (hLL (le_add_of_nonneg_right hLd0))
      · rw [tangentialU_apply_of_ne ha]; exact hz 1
    exact ⟨⟨hz 0, fun a => hz 0, hu, hz 2, hρt⟩, ⟨hz 0, fun a => hz 0, fun a => hz 1, hz 2, hρ⟩⟩
  · simp only [waveTangential, LinearMap.zero_apply, abs_zero]
    exact ⟨by positivity, by positivity⟩

end WaveTangential

end Feec.Models.Cube.WeakSymmetry
