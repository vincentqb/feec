module

public import Solution.Defs
public import Feec.HilbertComplex.BGG.WeakConsistency

/-!
# BGG data with weak symmetry of the challenge in `Feec`

BGG data of the challenge (`WeakSymmetryData`, unbounded `d` and bounded `S`) satisfying
`IsBGG` are a `Feec.BGG.Segment` on the domains with their `L²` inner products
(`WeakSymmetryData.toSegment`), and a discretization is a `Feec.BGG.Discrete` of it
(`Discretization.toDiscrete`: the spaces pulled back to the domains, the projections restricted to
them). The hypotheses of the challenge give those of `Feec` with constants `C` and
`C_app = 1 + C` (`toStability`, `toBounded`, `toCompatible`, `happ0`, `hpot`), and the theorem
`FEEC.WeakSymmetryData.weakSymmetry_of` is `Feec.BGG.Discrete.existsUnique_mixed_h` (Prop 5.4) and
`Feec.BGG.Discrete.error_estimate_of_weakConsistency` with
`Feec.BGG.Discrete.weakConsistency_of_potential_of_bound` (Thm 5.5).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.2, Prop 5.4, Thm 5.5

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set

@[expose] public noncomputable section

universe u

namespace FEEC.WeakSymmetryData

variable {W0 W1 W2 Wt0 Wt1 Wt2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2]
  [InnerProductSpace ℝ Wt2]

/-! ### The hypotheses of the abstract theorem (not compared: the cube theorem states the
conclusions) -/

/-- The rows are complexes, `R(d⁰) ⊆ D(d¹)`, `d¹d⁰ = 0` and `R(d̃⁰) ⊆ D(d̃¹)`, `d̃¹d̃⁰ = 0`, and
`S` anticommutes with them: `S⁰D(d̃⁰) ⊆ D(d¹)` and `d¹S⁰ = -S¹d̃⁰` (a morphism `Ṽ → V[1]`). -/
def IsBGG (D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2) : Prop :=
  (∀ x : D.d0.domain, ∃ h : D.d0 x ∈ D.d1.domain, D.d1 ⟨_, h⟩ = 0) ∧
    (∀ x : D.dt0.domain, ∃ h : D.dt0 x ∈ D.dt1.domain, D.dt1 ⟨_, h⟩ = 0) ∧
    ∀ ψ : D.dt0.domain, ∃ h : D.S0 ψ ∈ D.d1.domain, D.d1 ⟨_, h⟩ = -D.S1 (D.dt0 ψ)

/-- **The continuous hypotheses with constant `C`** ([QuennevilleBelair2015], §5.1, Prop 5.3):
Poincaré inequalities on `V⁰` and `Ṽ⁰`, exactness of the top row at `V¹`, the Hodge decomposition
`v = d̃ψ + w`, `‖w‖ ≤ C ‖d̃v‖`, on `Ṽ¹`, the regular decomposition `d¹V¹ = d¹S⁰Ṽ⁰` with the bound
`‖d̃φ‖ ≤ C ‖d¹x‖`, and `‖S⁰‖, ‖S¹‖ ≤ C`. -/
structure IsStable (D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2) (C : ℝ) : Prop where
  poincare : ∀ σ : D.d0.domain, ‖(σ : W0)‖ ≤ C * ‖D.d0 σ‖
  poincare_t : ∀ φ : D.dt0.domain, ‖(φ : Wt0)‖ ≤ C * ‖D.dt0 φ‖
  exact : ∀ μ : D.d1.domain, D.d1 μ = 0 → ∃ ρ : D.d0.domain, D.d0 ρ = μ
  hodge_t : ∀ v : D.dt1.domain, ∃ (ψ : D.dt0.domain) (w : D.dt1.domain),
    (v : Wt1) = D.dt0 ψ + w ∧ ‖(w : Wt1)‖ ≤ C * ‖D.dt1 v‖
  regular : ∀ x : D.d1.domain, ∃ (φ : D.dt0.domain) (h : D.S0 φ ∈ D.d1.domain),
    D.d1 ⟨_, h⟩ = D.d1 x ∧ ‖D.dt0 φ‖ ≤ C * ‖D.d1 x‖
  norm_S0 : ‖D.S0‖ ≤ C
  norm_S1 : ‖D.S1‖ ≤ C

/-- The squared **projection error** of `(σ, φ, u)` in the norms of `errorSq` (with `d π = π d`). -/
def Discretization.projErrorSq {D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2}
    (Q : D.Discretization) (σ : D.d0.domain) (φ : D.dt0.domain) (u : D.dt1.domain) : ℝ :=
  ‖Q.π0 σ - σ‖ ^ 2 + ‖Q.π1 (D.d0 σ) - D.d0 σ‖ ^ 2 + ‖Q.πt0 φ - φ‖ ^ 2 +
    ‖Q.πt1 (D.dt0 φ) - D.dt0 φ‖ ^ 2 + ‖Q.πt1 u - u‖ ^ 2 + ‖Q.π2 (D.S1 (Q.πt1 u - u))‖ ^ 2 +
    ‖Q.πt2 (D.dt1 u) - D.dt1 u‖ ^ 2

variable {D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2}

/-- A linear map into the domain of `T` from values in it. -/
def codDomain {E F G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G] (T : F →ₗ.[ℝ] G) (A : E →ₗ[ℝ] F) (h : ∀ x, A x ∈ T.domain) :
    E →ₗ[ℝ] T.domain :=
  LinearMap.codRestrict _ A h

/-- **BGG data as a `Feec` segment on the domains.** -/
def toSegment (hD : D.IsBGG) :
    Feec.BGG.Segment ℝ D.d0.domain D.d1.domain W2 D.dt0.domain D.dt1.domain Wt2 where
  d0 := codDomain D.d1 D.d0.toFun fun x => (hD.1 x).1
  d1 := D.d1.toFun
  dt0 := codDomain D.dt1 D.dt0.toFun fun x => (hD.2.1 x).1
  dt1 := D.dt1.toFun
  S0 := codDomain D.d1 (D.S0.toLinearMap ∘ₗ D.dt0.domain.subtype) fun ψ => (hD.2.2 ψ).1
  S1 := D.S1.toLinearMap ∘ₗ D.dt1.domain.subtype
  d1_d0 x := (hD.1 x).2
  dt1_dt0 x := (hD.2.1 x).2
  anticomm ψ := (hD.2.2 ψ).2

variable (hD : D.IsBGG)

@[simp] theorem coe_toSegment_d0 (x : D.d0.domain) :
    ((D.toSegment hD).d0 x : W1) = D.d0 x := rfl
@[simp] theorem toSegment_d1 (x : D.d1.domain) : (D.toSegment hD).d1 x = D.d1 x := rfl
@[simp] theorem coe_toSegment_dt0 (x : D.dt0.domain) :
    ((D.toSegment hD).dt0 x : Wt1) = D.dt0 x := rfl
@[simp] theorem toSegment_dt1 (x : D.dt1.domain) : (D.toSegment hD).dt1 x = D.dt1 x := rfl
@[simp] theorem coe_toSegment_S0 (ψ : D.dt0.domain) :
    ((D.toSegment hD).S0 ψ : W1) = D.S0 ψ := rfl
@[simp] theorem toSegment_S1 (v : D.dt1.domain) : (D.toSegment hD).S1 v = D.S1 v := rfl

theorem graphSq_d0 (x : D.d0.domain) :
    Feec.BGG.graphSq (D.toSegment hD).d0 x = ‖(x : W0)‖ ^ 2 + ‖D.d0 x‖ ^ 2 := rfl
theorem graphSq_d1 (x : D.d1.domain) :
    Feec.BGG.graphSq (D.toSegment hD).d1 x = ‖(x : W1)‖ ^ 2 + ‖D.d1 x‖ ^ 2 := rfl
theorem graphSq_dt0 (x : D.dt0.domain) :
    Feec.BGG.graphSq (D.toSegment hD).dt0 x = ‖(x : Wt0)‖ ^ 2 + ‖D.dt0 x‖ ^ 2 := rfl
theorem graphSq_dt1 (x : D.dt1.domain) :
    Feec.BGG.graphSq (D.toSegment hD).dt1 x = ‖(x : Wt1)‖ ^ 2 + ‖D.dt1 x‖ ^ 2 := rfl

/-- **The continuous hypotheses with constant `C` are `Feec`'s `Stability` with `C`, `C`, `C`.** -/
theorem IsStable.toStability {C : ℝ} (hS : D.IsStable C) :
    Feec.BGG.Stability (D.toSegment hD) C C C where
  Cp_nonneg := (norm_nonneg _).trans hS.norm_S0
  CR_nonneg := (norm_nonneg _).trans hS.norm_S0
  CS_nonneg := (norm_nonneg _).trans hS.norm_S0
  poinc0 σ := hS.poincare σ
  poinct0 φ := hS.poincare_t φ
  exact1 μ hμ := by
    obtain ⟨ρ, hρ⟩ := hS.exact μ hμ
    exact ⟨ρ, Subtype.ext hρ⟩
  hodget1 v := by
    obtain ⟨ψ, w, hv, hw⟩ := hS.hodge_t v
    exact ⟨ψ, w, Subtype.ext hv, hw⟩
  reg x := by
    obtain ⟨φ, h, e, hφ⟩ := hS.regular x
    exact ⟨φ, e, hφ⟩
  boundS0 ψ := by
    have hC : 0 ≤ C := (norm_nonneg _).trans hS.norm_S0
    rw [graphSq_d1, graphSq_dt0]
    change ‖D.S0 ψ‖ ^ 2 + ‖(D.toSegment hD).d1 ((D.toSegment hD).S0 ψ)‖ ^ 2 ≤ _
    rw [(D.toSegment hD).anticomm, norm_neg, toSegment_S1]
    have h1 : ‖D.S0 ψ‖ ≤ C * ‖(ψ : Wt0)‖ :=
      (D.S0.le_opNorm _).trans (mul_le_mul_of_nonneg_right hS.norm_S0 (norm_nonneg _))
    have h2 : ‖D.S1 ((D.toSegment hD).dt0 ψ)‖ ≤ C * ‖D.dt0 ψ‖ :=
      (D.S1.le_opNorm _).trans (mul_le_mul_of_nonneg_right hS.norm_S1 (norm_nonneg _))
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have := pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith
  boundS1 v := by
    rw [graphSq_dt1, toSegment_S1]
    have h1 : ‖D.S1 v‖ ≤ C * ‖(v : Wt1)‖ :=
      (D.S1.le_opNorm _).trans (mul_le_mul_of_nonneg_right hS.norm_S1 (norm_nonneg _))
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg C, sq_nonneg ‖D.dt1 v‖]

namespace Discretization

variable {hD} (Q : D.Discretization)

/-- A projection `π : W → W` with values in `V ⊆ D(T)` as a linear map of `D(T)`. -/
def restrictP {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [AddCommGroup G] [Module ℝ G]
    (T : F →ₗ.[ℝ] G) (P : F →L[ℝ] F) (h : ∀ x, P x ∈ T.domain) : T.domain →ₗ[ℝ] T.domain :=
  codDomain T (P.toLinearMap ∘ₗ T.domain.subtype) fun x => h x

variable (hD) in
/-- **A discretization as a `Feec` discretization** of `toSegment`. -/
def toDiscrete : Feec.BGG.Discrete (D.toSegment hD) where
  V0h := Q.V0.comap D.d0.domain.subtype
  V1h := Q.V1.comap D.d1.domain.subtype
  W2h := Q.V2
  Vt0h := Q.Vt0.comap D.dt0.domain.subtype
  Vt1h := Q.Vt1.comap D.dt1.domain.subtype
  Wt2h := Q.Vt2
  d0_mem x hx := Q.d0_mem x hx
  d1_mem x hx := Q.d1_mem x hx
  dt0_mem x hx := Q.dt0_mem x hx
  dt1_mem x hx := Q.dt1_mem x hx
  P0 := restrictP D.d0 Q.π0 fun x => Q.le0 (Q.π0_mem x)
  P1 := restrictP D.d1 Q.π1 fun x => Q.le1 (Q.π1_mem x)
  P2 := Q.π2.toLinearMap
  Pt0 := restrictP D.dt0 Q.πt0 fun x => Q.let0 (Q.πt0_mem x)
  Pt1 := restrictP D.dt1 Q.πt1 fun x => Q.let1 (Q.πt1_mem x)
  Pt2 := Q.πt2.toLinearMap
  P0_mem x := Q.π0_mem x
  P1_mem x := Q.π1_mem x
  P2_mem x := Q.π2_mem x
  Pt0_mem x := Q.πt0_mem x
  Pt1_mem x := Q.πt1_mem x
  Pt2_mem x := Q.πt2_mem x
  P0_id _ hx := Subtype.ext (Q.π0_id _ hx)
  P1_id _ hx := Subtype.ext (Q.π1_id _ hx)
  P2_id x hx := Q.π2_id x hx
  Pt0_id _ hx := Subtype.ext (Q.πt0_id _ hx)
  Pt1_id _ hx := Subtype.ext (Q.πt1_id _ hx)
  Pt2_id x hx := Q.πt2_id x hx
  comm0 x := Subtype.ext (Q.comm0 x)
  comm1 x := Q.comm1 x
  commt0 x := Subtype.ext (Q.commt0 x)
  commt1 x := Q.commt1 x

@[simp] theorem coe_P0 (x : D.d0.domain) : ((Q.toDiscrete hD).P0 x : W0) = Q.π0 x := rfl
@[simp] theorem coe_P1 (x : D.d1.domain) : ((Q.toDiscrete hD).P1 x : W1) = Q.π1 x := rfl
@[simp] theorem P2_apply (x : W2) : (Q.toDiscrete hD).P2 x = Q.π2 x := rfl
@[simp] theorem coe_Pt0 (x : D.dt0.domain) : ((Q.toDiscrete hD).Pt0 x : Wt0) = Q.πt0 x := rfl
@[simp] theorem coe_Pt1 (x : D.dt1.domain) : ((Q.toDiscrete hD).Pt1 x : Wt1) = Q.πt1 x := rfl
@[simp] theorem Pt2_apply (x : Wt2) : (Q.toDiscrete hD).Pt2 x = Q.πt2 x := rfl
@[simp] theorem coe_S0h (ψ : D.dt0.domain) :
    ((Q.toDiscrete hD).S0h ψ : W1) = Q.π1 (D.S0 ψ) := rfl
@[simp] theorem S1h_apply (v : D.dt1.domain) : (Q.toDiscrete hD).S1h v = Q.π2 (D.S1 v) := rfl

/-- The pulled-back spaces are finite-dimensional. -/
theorem finiteDimensional_comap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V p : Submodule ℝ E) [FiniteDimensional ℝ V] : FiniteDimensional ℝ (V.comap p.subtype) :=
  Module.Finite.of_injective
    (LinearMap.codRestrict V (p.subtype ∘ₗ (V.comap p.subtype).subtype) fun x => x.2)
    fun x y h => by
      have e := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext e)


theorem norm_comp_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : E →L[ℝ] F) {C : ℝ} (hA : ‖A‖ ≤ C) (x : E) : ‖A x‖ ≤ C * ‖x‖ :=
  (A.le_opNorm x).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))

/-- **Projections bounded by `C` are `Feec`'s `Bounded C`** (graph-norm bounds from `d π = π d`). -/
theorem IsBounded.toBounded {C : ℝ} (hB : Q.IsBounded C) : (Q.toDiscrete hD).Bounded C where
  CP_nonneg := (norm_nonneg _).trans hB.1
  P1 x := by
    rw [graphSq_d1, graphSq_d1, coe_P1]
    change ‖Q.π1 x‖ ^ 2 + ‖D.d1 ⟨Q.π1 x, Q.le1 (Q.π1_mem x)⟩‖ ^ 2 ≤ _
    rw [Q.comm1]
    have := pow_le_pow_left₀ (norm_nonneg _) (norm_comp_le Q.π1 hB.2.1 (x : W1)) 2
    have := pow_le_pow_left₀ (norm_nonneg _) (norm_comp_le Q.π2 hB.2.2.1 (D.d1 x)) 2
    nlinarith
  P2 z := norm_comp_le Q.π2 hB.2.2.1 z
  Pt1 v := by
    rw [graphSq_dt1, graphSq_dt1, coe_Pt1]
    change ‖Q.πt1 v‖ ^ 2 + ‖D.dt1 ⟨Q.πt1 v, Q.let1 (Q.πt1_mem v)⟩‖ ^ 2 ≤ _
    rw [Q.commt1]
    have := pow_le_pow_left₀ (norm_nonneg _) (norm_comp_le Q.πt1 hB.2.2.2.2.1 (v : Wt1)) 2
    have := pow_le_pow_left₀ (norm_nonneg _) (norm_comp_le Q.πt2 hB.2.2.2.2.2 (D.dt1 v)) 2
    nlinarith

theorem Compatible.toCompatible (h : Q.Compatible) : (Q.toDiscrete hD).Compatible := fun ψ =>
  Subtype.ext (h ψ)

/-- The consistency of `S⁰ₕ` in `Feec`'s form, `C_app = 1 + C`. -/
theorem happ0 {C h : ℝ} (hh : 0 ≤ h) (hc : Q.IsConsistent C h) :
    ∀ ψ ∈ (Q.toDiscrete hD).Vt0h, ‖(D.toSegment hD).S0 ψ - (Q.toDiscrete hD).S0h ψ‖ ^ 2 ≤
      ((1 + C) * h) ^ 2 * Feec.BGG.graphSq (D.toSegment hD).dt0 ψ := fun ψ hψ => by
  rw [graphSq_dt0]
  have e : ‖(D.toSegment hD).S0 ψ - (Q.toDiscrete hD).S0h ψ‖ = ‖D.S0 ψ - Q.π1 (D.S0 ψ)‖ := rfl
  rw [e]
  have h1 := hc.1 ψ hψ
  have h2 : C * h * ‖D.dt0 ψ‖ ≤ (1 + C) * h * ‖D.dt0 ψ‖ := by
    gcongr; linarith
  have := pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
  nlinarith [sq_nonneg ((1 + C) * h), sq_nonneg ‖(ψ : Wt0)‖]

/-- The regular potentials in `Feec`'s form, `C_inc = 1`, `C_reg = C`, `C_app = 1 + C`. -/
theorem hpot {C h : ℝ} (hC : 0 ≤ C) (hh : 0 ≤ h) (hc : Q.IsConsistent C h) :
    ∀ v ∈ (Q.toDiscrete hD).Vt1h, ∃ w, (D.toSegment hD).dt1 w = (D.toSegment hD).dt1 v ∧
      ‖w‖ ≤ 1 * C * ‖(D.toSegment hD).dt1 v‖ ∧
      ‖w - (Q.toDiscrete hD).Pt1 w‖ ≤ (1 + C) * h * (C * ‖(D.toSegment hD).dt1 v‖) ∧
      ‖((D.toSegment hD).S1 - (Q.toDiscrete hD).S1h) w‖ ≤
        (1 + C) * h * (C * ‖(D.toSegment hD).dt1 v‖) := fun v hv => by
  obtain ⟨w, e, h1, h2, h3⟩ := hc.2 v hv
  have hle : C * h * ‖D.dt1 v‖ ≤ (1 + C) * h * (C * ‖D.dt1 v‖) := by
    have := mul_nonneg (mul_nonneg hC hh) (norm_nonneg (D.dt1 v))
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC hC) hh) (norm_nonneg (D.dt1 v))]
  exact ⟨w, e, by rw [one_mul]; exact h1, h2.trans hle, h3.trans hle⟩

end Discretization

/-! ### `FEEC.WeakSymmetryData.weakSymmetry_of` -/

theorem errorConst_nonneg (C : ℝ) : 0 ≤ Feec.BGG.Discrete.errorConst C C C C (1 + C) := by
  unfold Feec.BGG.Discrete.errorConst
  have := Feec.BGG.Discrete.KL_pos C C C C
  positivity

/-- **The abstract theorem** (not compared in this entry): Prop 5.4
(`Feec.BGG.Discrete.existsUnique_mixed_h`) and Thm 5.5
(`Feec.BGG.Discrete.error_estimate_of_weakConsistency` with the weak consistency of
`Feec.BGG.Discrete.weakConsistency_of_potential_of_bound`) through `toSegment`, `toDiscrete`. -/
theorem weakSymmetry_of (C : ℝ) : ∃ K : ℝ, ∀ {W0 W1 W2 Wt0 Wt1 Wt2 : Type u}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [NormedAddCommGroup W1]
    [InnerProductSpace ℝ W1] [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
    [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0] [NormedAddCommGroup Wt1]
    [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
    (D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2) (Q : D.Discretization), D.IsBGG →
    D.IsStable C → Q.IsBounded C → Q.Compatible →
    (∀ F, ∃! x : D.d0.domain × D.dt0.domain × D.dt1.domain × W1,
      Q.IsDiscreteSolution F x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
    ∀ (h Λ : ℝ), 0 ≤ h → Q.IsConsistent C h → ∀ F σ φ u lam σh φh uh lamh,
      D.IsSolution F σ φ u lam → ‖lam‖ ≤ Λ →
      (∀ w : D.d1.domain, |⟪D.S1 u, D.d1 w⟫_ℝ| ≤ Λ * ‖(w : W1)‖) →
      Q.IsDiscreteSolution F σh φh uh lamh →
      Q.errorSq σ σh φ φh u uh ≤ K * (Q.projErrorSq σ φ u + h ^ 2 * (Λ ^ 2 + ‖D.S1 u‖ ^ 2) +
        ‖D.S1 u - Q.π2 (D.S1 u)‖ ^ 2) := by
  set a := √(1 + C ^ 2) * (1 + C * (1 + 1 * C))
  set b := (1 + (1 + C) * C) * C
  set E := Feec.BGG.Discrete.errorConst C C C C (1 + C)
  have hE := errorConst_nonneg C
  refine ⟨E * (1 + 2 * a ^ 2 + 2 * b ^ 2), ?_⟩
  intro W0 W1 W2 Wt0 Wt1 Wt2 _ _ _ _ _ _ _ _ _ _ _ _ D Q hD hS hB hc
  have H := hS.toStability hD
  have B := Discretization.IsBounded.toBounded (hD := hD) Q hB
  have h54 := Discretization.Compatible.toCompatible (hD := hD) Q hc
  have hC : 0 ≤ C := (norm_nonneg _).trans hS.norm_S0
  have := Q.fd0; have := Q.fd1; have := Q.fdt0; have := Q.fdt1
  have : FiniteDimensional ℝ (Q.toDiscrete hD).V0h := Discretization.finiteDimensional_comap _ _
  have : FiniteDimensional ℝ (Q.toDiscrete hD).V1h := Discretization.finiteDimensional_comap _ _
  have : FiniteDimensional ℝ (Q.toDiscrete hD).Vt0h := Discretization.finiteDimensional_comap _ _
  have : FiniteDimensional ℝ (Q.toDiscrete hD).Vt1h := Discretization.finiteDimensional_comap _ _
  refine ⟨fun F => ?_, fun h Λ hh hcons F σ φ u lam σh φh uh lamh hsol hlam hz hdisc => ?_⟩
  · obtain ⟨x, hx, huniq⟩ := Feec.BGG.Discrete.existsUnique_mixed_h H h54 F
    refine ⟨((x.1 : D.d0.domain), (x.2.1 : D.dt0.domain), (x.2.2.1 : D.dt1.domain),
      ((x.2.2.2 : D.d1.domain) : W1)), ⟨x.1.2, x.2.1.2, x.2.2.1.2, x.2.2.2.2,
        fun τ ψ hτ hψ => hx.1 τ hτ ψ hψ, fun v hv => hx.2.1 v hv,
        congrArg Subtype.val (Feec.BGG.Discrete.constraint_of_inner x.1.2 hx.2.2)⟩, ?_⟩
    rintro ⟨σ', φ', u', l'⟩ ⟨h1, h2, h3, h4, e1, e2, e3⟩
    have := huniq (⟨σ', h1⟩, ⟨φ', h2⟩, ⟨u', h3⟩, ⟨⟨l', Q.le1 h4⟩, h4⟩)
      ⟨fun τ hτ ψ hψ => e1 τ ψ hτ hψ, fun v hv => e2 v hv, fun μ _ => by
        have e : (D.toSegment hD).d0 σ' - (Q.toDiscrete hD).S0h φ' = 0 := Subtype.ext (by
          rw [Submodule.coe_sub, coe_toSegment_d0, Discretization.coe_S0h, e3, sub_self]; rfl)
        rw [e, inner_zero_left]⟩
    subst this
    rfl
  · have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hlam
    obtain ⟨hσh, hφh, huh, hlh, d1, d2, d3⟩ := hdisc
    have hwc := Feec.BGG.Discrete.weakConsistency_of_potential_of_bound H B zero_le_one hC hh
      (by linarith) (Q.hpot hC hh hcons) (Q.happ0 hh hcons) hΛ
      (z := (D.toSegment hD).S1 u) fun w => by
        rw [toSegment_d1]; exact hz w
    have key := Feec.BGG.Discrete.error_estimate_of_weakConsistency H B h54 hh (by linarith)
      (Q.happ0 hh hcons) hwc ((innerSL ℝ lam).toLinearMap ∘ₗ D.d1.domain.subtype) hΛ
      (fun μ => by
        simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
          innerSL_apply_apply, Submodule.coe_subtype]
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right hlam (norm_nonneg _)))
      F (fun τ _ ψ _ => hsol.1 τ ψ) (fun v _ => hsol.2.1 v) (Subtype.ext hsol.2.2)
      hσh hφh huh (lh := ⟨lamh, Q.le1 hlh⟩) (fun τ hτ ψ hψ => d1 τ ψ hτ hψ)
      (fun v hv => d2 v hv) (fun μ _ => by
        have e : (D.toSegment hD).d0 σh - (Q.toDiscrete hD).S0h φh = 0 := Subtype.ext (by
          rw [Submodule.coe_sub, coe_toSegment_d0, Discretization.coe_S0h, d3, sub_self]; rfl)
        rw [e, inner_zero_left])
    have hL : Q.errorSq σ σh φ φh u uh = Feec.BGG.graphSq (D.toSegment hD).d0 (σ - σh) +
        Feec.BGG.graphSq (D.toSegment hD).dt0 (φ - φh) + (Q.toDiscrete hD).gnSq (u - uh) := by
      unfold Discretization.errorSq Feec.BGG.Discrete.gnSq
      rw [graphSq_d0, graphSq_dt0]
      simp only [Discretization.S1h_apply, toSegment_dt1, Submodule.coe_sub]
      have hn : ‖u - uh‖ = ‖(u : Wt1) - uh‖ := rfl
      rw [hn]
      ring
    have hP0 : D.d0 ⟨Q.π0 σ, Q.le0 (Q.π0_mem σ)⟩ = Q.π1 (D.d0 σ) := Q.comm0 σ
    have hR : Feec.BGG.graphSq (D.toSegment hD).d0 ((Q.toDiscrete hD).P0 σ - σ) +
        Feec.BGG.graphSq (D.toSegment hD).dt0 ((Q.toDiscrete hD).Pt0 φ - φ) +
          (Q.toDiscrete hD).gnSq ((Q.toDiscrete hD).Pt1 u - u) =
        Q.projErrorSq σ φ u := by
      unfold Discretization.projErrorSq Feec.BGG.Discrete.gnSq
      rw [graphSq_d0, graphSq_dt0]
      simp only [Discretization.S1h_apply, toSegment_dt1, Submodule.coe_sub,
        Discretization.coe_P0, Discretization.coe_Pt0, Discretization.coe_Pt1,
        LinearPMap.map_sub]
      have hn : ‖(Q.toDiscrete hD).Pt1 u - u‖ = ‖Q.πt1 u - u‖ := rfl
      rw [hn]
      have e0 : D.d0 ((Q.toDiscrete hD).P0 σ) = Q.π1 (D.d0 σ) := Q.comm0 σ
      have e1 : D.dt0 ((Q.toDiscrete hD).Pt0 φ) = Q.πt1 (D.dt0 φ) := Q.commt0 φ
      have e2 : D.dt1 ((Q.toDiscrete hD).Pt1 u) = Q.πt2 (D.dt1 u) := Q.commt1 u
      rw [e0, e1, e2]
      ring
    rw [hL]
    refine key.trans ?_
    rw [hR]
    have hwk : Feec.BGG.Discrete.weakConsistencyConst C C C 1 C ‖(D.toSegment hD).S1 u‖ Λ =
        Λ * a + ‖D.S1 u‖ * b := by
      unfold Feec.BGG.Discrete.weakConsistencyConst
      simp only [a, b, toSegment_S1]
      ring
    rw [hwk]
    have hP := (show 0 ≤ Q.projErrorSq σ φ u by unfold Discretization.projErrorSq; positivity)
    have hsq : (Λ * a + ‖D.S1 u‖ * b) ^ 2 ≤ 2 * a ^ 2 * Λ ^ 2 + 2 * b ^ 2 * ‖D.S1 u‖ ^ 2 := by
      nlinarith [sq_nonneg (Λ * a - ‖D.S1 u‖ * b)]
    have hS1 : ‖(D.toSegment hD).S1 u - (Q.toDiscrete hD).S1h u‖ = ‖D.S1 u - Q.π2 (D.S1 u)‖ := rfl
    rw [hS1]
    set R := ‖D.S1 u - Q.π2 (D.S1 u)‖ ^ 2
    have hR0 : 0 ≤ R := sq_nonneg _
    have h2 : 0 ≤ h ^ 2 := sq_nonneg h
    have hX : Q.projErrorSq σ φ u + h ^ 2 * Λ ^ 2 + h ^ 2 * (Λ * a + ‖D.S1 u‖ * b) ^ 2 + R ≤
        (1 + 2 * a ^ 2 + 2 * b ^ 2) *
          (Q.projErrorSq σ φ u + h ^ 2 * (Λ ^ 2 + ‖D.S1 u‖ ^ 2) + R) := by
      have := mul_le_mul_of_nonneg_left hsq h2
      nlinarith [mul_nonneg h2 (sq_nonneg Λ), mul_nonneg h2 (sq_nonneg ‖D.S1 u‖),
        mul_nonneg (sq_nonneg a) hP, mul_nonneg (sq_nonneg b) hP, mul_nonneg (sq_nonneg a) hR0,
        mul_nonneg (sq_nonneg b) hR0, mul_nonneg (mul_nonneg h2 (sq_nonneg Λ)) (sq_nonneg b),
        mul_nonneg (mul_nonneg h2 (sq_nonneg ‖D.S1 u‖)) (sq_nonneg a)]
    calc E * (Q.projErrorSq σ φ u + h ^ 2 * Λ ^ 2 + h ^ 2 * (Λ * a + ‖D.S1 u‖ * b) ^ 2 + R)
        ≤ E * ((1 + 2 * a ^ 2 + 2 * b ^ 2) *
          (Q.projErrorSq σ φ u + h ^ 2 * (Λ ^ 2 + ‖D.S1 u‖ ^ 2) + R)) :=
          mul_le_mul_of_nonneg_left hX hE
      _ = _ := by ring

end FEEC.WeakSymmetryData
