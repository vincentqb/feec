module

public import Feec.HilbertComplex.Approximation.HeatFEEC
public import Feec.HilbertComplex.Approximation.StaticCrime

/-!
# The heat FEEC theorem with variational crimes

The Hodge heat equation on discrete differential spaces with their own inner products and reading
maps `iₕ`, with the heat Ritz projection with crimes `Rₕ (y, z) = P_ℌₕ iₕ* y - Gₕ iₕ* z`.

## Main results

* `ApproxComplexCrime.HeatFamily.heatFEEC`: the dissipative FEEC verdict under static convergence.
* `ApproxComplexCrime.HeatFamily.rate_heat_of_static`: the heat rate from a static rate.
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι}
  {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
  [∀ i, CompleteSpace (W i)]

/-! ### The discrete Hodge Laplacian of a differential space -/

namespace ApproxComplexCrime.Family

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (S : ApproxComplexCrime.Family.{u} H κ)

/-- The discrete Hodge Laplacian `Δₕ = 𝐝ₕ 𝐝ₕ* + 𝐝ₕ* 𝐝ₕ` of `(Xₕ, 𝐝ₕ)`. -/
def laplacian (h : κ) : S.X h →L[𝕜] S.X h :=
  S.D h ∘L (S.D h).adjoint + (S.D h).adjoint ∘L S.D h

theorem laplacian_apply (h : κ) (v : S.X h) :
    S.laplacian h v = S.D h ((S.D h).adjoint v) + (S.D h).adjoint (S.D h v) :=
  rfl

theorem re_inner_laplacian_self (h : κ) (v : S.X h) :
    RCLike.re ⟪S.laplacian h v, v⟫_𝕜 = ‖(S.D h).adjoint v‖ ^ 2 + ‖S.D h v‖ ^ 2 := by
  rw [laplacian_apply, inner_add_left,
    ← ContinuousLinearMap.adjoint_inner_right (S.D h) ((S.D h).adjoint v) v,
    ContinuousLinearMap.adjoint_inner_left (S.D h) v (S.D h v), _root_.map_add,
    inner_self_eq_norm_sq, inner_self_eq_norm_sq]

/-- The discrete Green operator `Gₕ`, the solution operator of the mixed problem of `(Xₕ, 𝐝ₕ)`. -/
def green (h : κ) : S.X h →L[𝕜] S.X h :=
  (S.cpx h).solutionOp (loop_rel () ()) (loop_rel () ()) (closedRangeAt_diffComplex _ _ ())
    (closedRangeAt_diffComplex _ _ ())

/-- The orthogonal projection `P_ℌₕ` of `Xₕ` onto the discrete harmonic forms. -/
def harmonicProj (h : κ) : S.X h →L[𝕜] S.X h :=
  ((S.cpx h).harmonic ()).starProjection

theorem laplacian_green (h : κ) (v : S.X h) :
    S.laplacian h (S.green h v) = v - S.harmonicProj h v := by
  obtain ⟨h₁, h₂, h₃, h₄, e⟩ := (S.cpx h).hodgeLaplacian_solutionOp (loop_rel () ())
    (loop_rel () ()) (closedRangeAt_diffComplex _ _ ()) (closedRangeAt_diffComplex _ _ ()) v
  have e' : S.D h (((S.cpx h).d () ())† ⟨_, h₂⟩) + ((S.cpx h).d () ())† ⟨_, h₃⟩ =
      v - ((S.cpx h).harmonic ()).starProjection v := e
  rw [adjoint_diffComplex_d_apply, adjoint_diffComplex_d_apply] at e'
  exact e'

theorem laplacian_harmonicProj (h : κ) (v : S.X h) : S.laplacian h (S.harmonicProj h v) = 0 := by
  obtain ⟨h1, h2⟩ := (mem_diffComplex_harmonic (S.D h) (S.D_D h)).1
    (((S.cpx h).harmonic ()).starProjection_apply_mem v)
  rw [laplacian_apply, harmonicProj, h1, h2, _root_.map_zero, _root_.map_zero, add_zero]

theorem green_adjoint_incl (h : κ) (f : PiLp 2 W) :
    S.green h ((S.incl h).adjoint f) = (S.cpx h).mixedI1 () () (S.mixedSol h f) :=
  rfl

theorem harmonicProj_adjoint_incl (h : κ) (f : PiLp 2 W) :
    S.harmonicProj h ((S.incl h).adjoint f) = (S.cpx h).mixedI2 () () (S.mixedSol h f) :=
  ((S.cpx h).harmonic_mixedSolution (loop_rel () ()) (loop_rel () ())
    (closedRangeAt_diffComplex _ _ ()) (closedRangeAt_diffComplex _ _ ()) _).symm

variable (hcr : ∀ i, H.ClosedRangeAt i)

theorem norm_greenOp_sub_le (h : κ) (f : PiLp 2 W) :
    ‖H.greenOp hcr f - S.incl h (S.green h ((S.incl h).adjoint f))‖ ≤ S.staticError hcr h f := by
  rw [green_adjoint_incl]
  have := S.readError_nonneg h (H.totalMixedSolution hcr f) (S.mixedSol h f)
  unfold staticError readError
  change ‖H.total.mixedI1 () () (H.totalMixedSolution hcr f) - _‖ ≤ _
  linarith [norm_nonneg (H.total.mixedI0 () () (H.totalMixedSolution hcr f) -
      S.incl h ((S.cpx h).mixedI0 () () (S.mixedSol h f))),
    norm_nonneg (H.total.mixedD0 () () (H.totalMixedSolution hcr f) -
      S.incl h ((S.cpx h).mixedD0 () () (S.mixedSol h f))),
    norm_nonneg (H.total.mixedD1 () () () (H.totalMixedSolution hcr f) -
      S.incl h ((S.cpx h).mixedD1 () () () (S.mixedSol h f))),
    norm_nonneg (H.total.mixedI2 () () (H.totalMixedSolution hcr f) -
      S.incl h ((S.cpx h).mixedI2 () () (S.mixedSol h f)))]

theorem norm_harmonicProj_sub_le (h : κ) (f : PiLp 2 W) :
    ‖(H.total.harmonic ()).starProjection f -
      S.incl h (S.harmonicProj h ((S.incl h).adjoint f))‖ ≤ S.staticError hcr h f := by
  rw [harmonicProj_adjoint_incl, ← harmonic_totalMixedSolution]
  unfold staticError readError
  change ‖H.total.mixedI2 () () (H.totalMixedSolution hcr f) - _‖ ≤ _
  linarith [norm_nonneg (H.total.mixedI0 () () (H.totalMixedSolution hcr f) -
      S.incl h ((S.cpx h).mixedI0 () () (S.mixedSol h f))),
    norm_nonneg (H.total.mixedD0 () () (H.totalMixedSolution hcr f) -
      S.incl h ((S.cpx h).mixedD0 () () (S.mixedSol h f))),
    norm_nonneg (H.total.mixedI1 () () (H.totalMixedSolution hcr f) -
      S.incl h ((S.cpx h).mixedI1 () () (S.mixedSol h f))),
    norm_nonneg (H.total.mixedD1 () () () (H.totalMixedSolution hcr f) -
      S.incl h ((S.cpx h).mixedD1 () () () (S.mixedSol h f)))]

theorem norm_green_adjoint_incl_le {cP : ℝ} (hP : S.IsPoincare cP) (hcP : 1 ≤ cP) (h : κ)
    (f : PiLp 2 W) :
    ‖S.green h ((S.incl h).adjoint f)‖ ≤ 16 * cP ^ 2 * S.boundConst * ‖f‖ := by
  rw [green_adjoint_incl]
  exact (norm_mixedComponents_le (S.cpx h) _).2.2.1.trans (S.norm_mixedSol_le hP hcP h f)

theorem norm_one_sub_J_green_adjoint_incl_le {cP : ℝ} (hP : S.IsPoincare cP) (hcP : 1 ≤ cP)
    (h : κ) (f : PiLp 2 W) :
    ‖(1 - S.J h) (S.green h ((S.incl h).adjoint f))‖ ≤
      S.graphDefect h * (16 * cP ^ 2 * S.boundConst * ‖f‖) := by
  rw [green_adjoint_incl]
  refine (S.norm_one_sub_J_domainIncl_le h (S.mixedSol h f).snd.fst).trans
    (mul_le_mul_of_nonneg_left (le_trans ?_ (S.norm_mixedSol_le hP hcP h f))
      (S.graphDefect_nonneg h))
  exact (WithLp.norm_fst_le (x := (S.mixedSol h f).snd)).trans
    (WithLp.norm_snd_le (x := S.mixedSol h f))

variable {S hcr} in
theorem tendsto_incl_green {l : Filter κ}
    (hconv : ∀ f, Tendsto (fun h => S.staticError hcr h f) l (𝓝 0)) (f : PiLp 2 W) :
    Tendsto (fun h => S.incl h (S.green h ((S.incl h).adjoint f))) l (𝓝 (H.greenOp hcr f)) :=
  tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
    (fun h => (norm_sub_rev _ _).trans_le (S.norm_greenOp_sub_le hcr h f)) (hconv f))

variable {S hcr} in
theorem tendsto_incl_harmonicProj {l : Filter κ}
    (hconv : ∀ f, Tendsto (fun h => S.staticError hcr h f) l (𝓝 0)) (f : PiLp 2 W) :
    Tendsto (fun h => S.incl h (S.harmonicProj h ((S.incl h).adjoint f))) l
      (𝓝 ((H.total.harmonic ()).starProjection f)) :=
  tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
    (fun h => (norm_sub_rev _ _).trans_le (S.norm_harmonicProj_sub_le hcr h f)) (hconv f))

end ApproxComplexCrime.Family

/-! ### The regular states of a heat rate -/

variable (H : HilbertComplex 𝕜 c W) in
/-- The regular states: `y ∈ D(Δ²)` with `y`, `A y`, `A² y` regular of bound `L`, `‖A² y‖ ≤ L`. -/
def heatReg (Reg : ℝ → Set (PiLp 2 W)) (L : ℝ) : Set (PiLp 2 W) :=
  {y | y ∈ (-H.hodgeLaplacian).sqDomain ∧ y ∈ Reg L ∧
    DissipFEEC.genExt (-H.hodgeLaplacian) y ∈ Reg L ∧
    DissipFEEC.genExt (-H.hodgeLaplacian) (DissipFEEC.genExt (-H.hodgeLaplacian) y) ∈ Reg L ∧
    ‖DissipFEEC.genExt (-H.hodgeLaplacian) (DissipFEEC.genExt (-H.hodgeLaplacian) y)‖ ≤ L}

/-! ### The heat FEEC discretization with crimes -/

namespace ApproxComplexCrime.HeatFamily

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplexCrime.HeatFamily.{u} H κ)

/-- The heat FEEC discretization with crimes: `Lₕ = -Δₕ` on `Xₕ`, read by `iₕ`. -/
abbrev toHeat : DissipFEEC (-H.hodgeLaplacian) κ where
  isMDissipative := H.isMDissipative_neg_hodgeLaplacian
  K := F.K
  isClosed_K := F.isClosed_K
  l := F.l
  X := F.toFamily.X
  L h := -F.toFamily.laplacian h
  dissipative h v := by
    rw [_root_.neg_apply, inner_neg_left, _root_.map_neg, F.toFamily.re_inner_laplacian_self]
    nlinarith [sq_nonneg ‖(F.toFamily.D h).adjoint v‖, sq_nonneg ‖F.toFamily.D h v‖]
  incl := F.toFamily.incl
  proj := F.toFamily.proj
  proj_incl := F.toFamily.proj_incl
  bound := F.toFamily.bound

theorem toHeat_L (h : κ) : F.toHeat.L h = -F.toFamily.laplacian h := rfl

theorem toHeat_incl (h : κ) : F.toHeat.incl h = F.toFamily.incl h := rfl

/-! ### The heat Ritz projection with crimes -/

section Ritz

variable (hcr : ∀ i, H.ClosedRangeAt i)

/-- The heat Ritz projection with crimes `Rₕ (y, z) = P_ℌₕ iₕ* y - Gₕ iₕ* z`. -/
def ritzR (h : κ) : PiLp 2 W × PiLp 2 W →L[𝕜] F.toFamily.X h :=
  F.toFamily.harmonicProj h ∘L (F.toFamily.incl h).adjoint ∘L ContinuousLinearMap.fst 𝕜 _ _ -
    F.toFamily.green h ∘L (F.toFamily.incl h).adjoint ∘L ContinuousLinearMap.snd 𝕜 _ _

theorem ritzR_apply (h : κ) (g : PiLp 2 W × PiLp 2 W) :
    F.ritzR h g = F.toFamily.harmonicProj h ((F.toFamily.incl h).adjoint g.1) -
      F.toFamily.green h ((F.toFamily.incl h).adjoint g.2) :=
  rfl

/-- The defect operator `Δₕ (y, z) = 2 P_ℌₕ iₕ* (1 - P_ℌ) y + iₕ* G z - Gₕ iₕ* z`. -/
def ritzDefect (h : κ) : PiLp 2 W × PiLp 2 W →L[𝕜] F.toFamily.X h :=
  (2 : 𝕜) • (F.toFamily.harmonicProj h ∘L (F.toFamily.incl h).adjoint ∘L
      (1 - (H.total.harmonic ()).starProjection) ∘L ContinuousLinearMap.fst 𝕜 _ _) +
    ((F.toFamily.incl h).adjoint ∘L H.greenOp hcr -
      F.toFamily.green h ∘L (F.toFamily.incl h).adjoint) ∘L ContinuousLinearMap.snd 𝕜 _ _

theorem ritzDefect_apply (h : κ) (g : PiLp 2 W × PiLp 2 W) :
    F.ritzDefect hcr h g = (2 : 𝕜) • F.toFamily.harmonicProj h
        ((F.toFamily.incl h).adjoint (g.1 - (H.total.harmonic ()).starProjection g.1)) +
      ((F.toFamily.incl h).adjoint (H.greenOp hcr g.2) -
        F.toFamily.green h ((F.toFamily.incl h).adjoint g.2)) :=
  rfl

theorem heatGen_ritzR (h : κ) (g : PiLp 2 W × PiLp 2 W) :
    F.toHeat.L h (F.ritzR h g) = (F.toFamily.incl h).adjoint g.2 -
      F.toFamily.harmonicProj h ((F.toFamily.incl h).adjoint g.2) := by
  show -(F.toFamily.laplacian h (F.ritzR h g)) = _
  rw [ritzR_apply, _root_.map_sub, F.toFamily.laplacian_harmonicProj, F.toFamily.laplacian_green]
  abel

theorem heatRitz_defect_eq (h : κ) (y : PiLp 2 W) :
    F.ritzR h (DissipFEEC.genExt (-H.hodgeLaplacian) y,
        DissipFEEC.genExt (-H.hodgeLaplacian) (DissipFEEC.genExt (-H.hodgeLaplacian) y)) -
        F.toHeat.L h (F.ritzR h (y, DissipFEEC.genExt (-H.hodgeLaplacian) y)) =
      F.ritzR h (DissipFEEC.genExt (-H.hodgeLaplacian) y,
          DissipFEEC.genExt (-H.hodgeLaplacian) (DissipFEEC.genExt (-H.hodgeLaplacian) y)) -
        ((F.toFamily.incl h).adjoint (DissipFEEC.genExt (-H.hodgeLaplacian) y) -
          F.toFamily.harmonicProj h
            ((F.toFamily.incl h).adjoint (DissipFEEC.genExt (-H.hodgeLaplacian) y))) := by
  rw [heatGen_ritzR]

theorem ritzDefect_lift (h : κ) {a : PiLp 2 W} (ha : a ∈ H.hodgeLaplacian.domain)
    (hPa : (H.total.harmonic ()).starProjection a = 0) :
    F.ritzDefect hcr h (a, DissipFEEC.genExt (-H.hodgeLaplacian) a) =
      F.ritzR h (a, DissipFEEC.genExt (-H.hodgeLaplacian) a) -
        ((F.toFamily.incl h).adjoint a -
          F.toFamily.harmonicProj h ((F.toFamily.incl h).adjoint a)) := by
  have hG : H.greenOp hcr (DissipFEEC.genExt (-H.hodgeLaplacian) a) = -a := by
    rw [H.genExt_neg_hodgeLaplacian ha, _root_.map_neg, H.greenOp_hodgeLaplacian hcr ⟨a, ha⟩]
    change -(a - (H.total.harmonic ()).starProjection a) = -a
    rw [hPa, sub_zero]
  rw [ritzDefect_apply, ritzR_apply, hPa, sub_zero, hG, _root_.map_neg, two_smul]
  change _ = F.toFamily.harmonicProj h ((F.toFamily.incl h).adjoint a) - _ - _
  abel

variable {cP : ℝ} (hcP : 1 ≤ cP) (hP : F.toFamily.IsPoincare cP)

include hcP hP in
theorem norm_ritzDefect_le (h : κ) (g : PiLp 2 W × PiLp 2 W) :
    ‖F.ritzDefect hcr h g‖ ≤
      2 * F.toFamily.boundConst *
          F.toFamily.staticError hcr h (g.1 - (H.total.harmonic ()).starProjection g.1) +
        F.toFamily.boundConst * F.toFamily.staticError hcr h g.2 +
        F.toFamily.graphDefect h * (16 * cP ^ 2 * F.toFamily.boundConst * ‖g.2‖) := by
  set P := (H.total.harmonic ()).starProjection
  have hC := F.toFamily.boundConst_nonneg
  have h1 : ‖F.toFamily.harmonicProj h ((F.toFamily.incl h).adjoint (g.1 - P g.1))‖ ≤
      F.toFamily.boundConst * F.toFamily.staticError hcr h (g.1 - P g.1) := by
    have e : P (g.1 - P g.1) = 0 := by
      rw [_root_.map_sub, Submodule.starProjection_eq_self_iff.2
        (Submodule.starProjection_apply_mem _ _), sub_self]
    have := F.toFamily.norm_harmonicProj_sub_le hcr h (g.1 - P g.1)
    rw [e, zero_sub, norm_neg] at this
    exact (F.toFamily.norm_le_norm_incl h _).trans (mul_le_mul_of_nonneg_left this hC)
  have h2 : ‖(F.toFamily.incl h).adjoint (H.greenOp hcr g.2) -
      F.toFamily.green h ((F.toFamily.incl h).adjoint g.2)‖ ≤
      F.toFamily.boundConst * F.toFamily.staticError hcr h g.2 +
        F.toFamily.graphDefect h * (16 * cP ^ 2 * F.toFamily.boundConst * ‖g.2‖) := by
    have e : (F.toFamily.incl h).adjoint (H.greenOp hcr g.2) -
        F.toFamily.green h ((F.toFamily.incl h).adjoint g.2) =
        (F.toFamily.incl h).adjoint (H.greenOp hcr g.2 -
          F.toFamily.incl h (F.toFamily.green h ((F.toFamily.incl h).adjoint g.2))) -
          (1 - F.toFamily.J h) (F.toFamily.green h ((F.toFamily.incl h).adjoint g.2)) := by
      simp only [Family.J, _root_.map_sub, _root_.sub_apply, one_apply_eq_self,
        ContinuousLinearMap.comp_apply]
      abel
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add ((F.toFamily.norm_adjoint_incl_apply_le h _).trans
      (mul_le_mul_of_nonneg_left (F.toFamily.norm_greenOp_sub_le hcr h g.2) hC)) ?_)
    exact F.toFamily.norm_one_sub_J_green_adjoint_incl_le hP hcP h g.2
  rw [ritzDefect_apply]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, RCLike.norm_ofNat]
  linarith

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **The graph lift** `ℓ y = (y, -Δ y)` of `D(Δ²)`, read by `ρ (y, z) = P_ℌ y - G z`. -/
def heatLift : F.toHeat.Lift (PiLp 2 W × PiLp 2 W) :=
  DissipFEEC.Lift.graph F.toHeat (H.heatRead hcr) fun _ hy => H.heatRead_lift hcr hy.1

include hcP hP in
/-- The heat Ritz projection with crimes for the graph lift of `D(Δ²)`. -/
def heatRitz : F.toHeat.Ritz (F.heatLift hcr) where
  R := F.ritzR
  Δ := F.ritzDefect hcr
  Δ' _ := 0
  defect_eq h y hy := by
    obtain ⟨hy1, hy2⟩ := DissipFEEC.mem_sqDomain_iff.1 hy
    have hPa :
        (H.total.harmonic ()).starProjection (DissipFEEC.genExt (-H.hodgeLaplacian) y) = 0 := by
      rw [H.genExt_neg_hodgeLaplacian hy1, _root_.map_neg,
        H.starProjection_harmonic_total_hodgeLaplacian, neg_zero]
    exact (F.heatRitz_defect_eq h y).trans
      ((F.ritzDefect_lift hcr h hy2 hPa).symm.trans (add_zero _).symm)
  bound := by
    set C := F.toFamily.boundConst
    have hC := F.toFamily.boundConst_nonneg
    set B := ‖H.greenOp hcr‖
    have hB := norm_nonneg (H.greenOp hcr)
    have hc2 : 0 ≤ 16 * cP ^ 2 * C := by positivity
    refine ⟨4 * C + C * B + 16 * cP ^ 2 * C, fun h => ⟨?_, ?_, by rw [norm_zero]; positivity⟩⟩
    · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g => ?_
      rw [ritzR_apply]
      have h1 : ‖F.toFamily.harmonicProj h ((F.toFamily.incl h).adjoint g.1)‖ ≤ C * ‖g‖ :=
        (Submodule.norm_starProjection_apply_le _ _).trans
          ((F.toFamily.norm_adjoint_incl_apply_le h _).trans
          (mul_le_mul_of_nonneg_left (norm_fst_le g) hC))
      have h2 : ‖F.toFamily.green h ((F.toFamily.incl h).adjoint g.2)‖ ≤ 16 * cP ^ 2 * C * ‖g‖ :=
        (F.toFamily.norm_green_adjoint_incl_le hP hcP h g.2).trans
          (mul_le_mul_of_nonneg_left (norm_snd_le g) hc2)
      have := norm_sub_le (F.toFamily.harmonicProj h ((F.toFamily.incl h).adjoint g.1))
        (F.toFamily.green h ((F.toFamily.incl h).adjoint g.2))
      nlinarith [norm_nonneg g, mul_nonneg (mul_nonneg hC hB) (norm_nonneg g),
        mul_nonneg hC (norm_nonneg g)]
    · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g => ?_
      rw [ritzDefect_apply]
      set P := (H.total.harmonic ()).starProjection
      have hP' : ‖g.1 - P g.1‖ ≤ 2 * ‖g‖ := (norm_sub_le _ _).trans (by
        have := Submodule.norm_starProjection_apply_le (H.total.harmonic ()) g.1
        linarith [norm_fst_le g])
      have h1 : ‖F.toFamily.harmonicProj h ((F.toFamily.incl h).adjoint (g.1 - P g.1))‖ ≤
          C * (2 * ‖g‖) :=
        (Submodule.norm_starProjection_apply_le _ _).trans
          ((F.toFamily.norm_adjoint_incl_apply_le h _).trans
          (mul_le_mul_of_nonneg_left hP' hC))
      have h2 : ‖(F.toFamily.incl h).adjoint (H.greenOp hcr g.2)‖ ≤ C * (B * ‖g‖) :=
        (F.toFamily.norm_adjoint_incl_apply_le h _).trans (mul_le_mul_of_nonneg_left
          (((H.greenOp hcr).le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_snd_le g) hB)) hC)
      have h3 : ‖F.toFamily.green h ((F.toFamily.incl h).adjoint g.2)‖ ≤ 16 * cP ^ 2 * C * ‖g‖ :=
        (F.toFamily.norm_green_adjoint_incl_le hP hcP h g.2).trans
          (mul_le_mul_of_nonneg_left (norm_snd_le g) hc2)
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, RCLike.norm_ofNat]
      have := norm_sub_le ((F.toFamily.incl h).adjoint (H.greenOp hcr g.2))
        (F.toFamily.green h ((F.toFamily.incl h).adjoint g.2))
      nlinarith [norm_nonneg g, mul_nonneg (mul_nonneg hC hB) (norm_nonneg g),
        mul_nonneg hC (norm_nonneg g)]

variable (hconv : ∀ f, Tendsto (fun h => F.toFamily.staticError hcr h f) F.l (𝓝 0))

include hcP hP hconv in
/-- The heat core with crimes, with data `D(Δ²)`. -/
def heatCore : F.toHeat.Core :=
  (F.heatRitz hcr hcP hP).toCore
    (fun g => by
      have h1 := Family.tendsto_incl_harmonicProj hconv g.1
      have h2 := Family.tendsto_incl_green hconv g.2
      refine (h1.sub h2).congr fun h => ?_
      change _ = F.toFamily.incl h (F.ritzR h g)
      rw [ritzR_apply, _root_.map_sub])
    (fun g => by
      refine squeeze_zero (fun _ => norm_nonneg _)
        (fun h => F.norm_ritzDefect_le hcr hcP hP h g) ?_
      show Tendsto _ F.l _
      have h1 := hconv (g.1 - (H.total.harmonic ()).starProjection g.1)
      have h2 := hconv g.2
      have h3 := F.tendsto_graphDefect
      simpa using ((h1.const_mul (2 * F.toFamily.boundConst)).add
        (h2.const_mul F.toFamily.boundConst)).add
        (h3.mul_const (16 * cP ^ 2 * F.toFamily.boundConst * ‖g.2‖)))
    (fun _ => tendsto_const_nhds.congr fun _ => norm_zero.symm)

theorem heatCore_data : (F.heatCore hcr hcP hP hconv).Data = (-H.hodgeLaplacian).sqDomain :=
  rfl

theorem dense_heatCore_data : (F.heatCore hcr hcP hP hconv).Data.topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.1 H.isMDissipative_neg_hodgeLaplacian.dense_sqDomain

/-- **The heat FEEC theorem with crimes**: with closed range, a uniform discrete Poincaré inequality
and static convergence for every datum give the dissipative FEEC verdict on the heat core. -/
theorem heatFEEC : F.toHeat.Verdict (F.heatCore hcr hcP hP hconv) :=
  dissipFEEC F.toHeat (F.heatCore hcr hcP hP hconv)

end Ritz

/-! ### Rates: the static rate with crimes along the orbit -/

section Rate

variable (hcr : ∀ i, H.ClosedRangeAt i)

variable {cP : ℝ} (hcP : 1 ≤ cP) (hP : F.toFamily.IsPoincare cP) {Reg : ℝ → Set (PiLp 2 W)}
  {m : κ → ℝ}
  (hm : ∀ h, 0 ≤ m h) {α K : ℝ} (hK0 : 0 ≤ K)
  (hK : ∀ {L : ℝ} {f : PiLp 2 W}, 0 ≤ L → f ∈ Reg L → ∀ h,
    F.toFamily.staticError hcr h f ≤ K * L * m h ^ α)
  (hJ : ∀ h, F.toFamily.graphDefect h ≤ K * m h ^ α) {L : ℝ} (hL : 0 ≤ L)

include hK hL in
theorem norm_sub_ritzR_le {y : PiLp 2 W} (hy : y ∈ H.heatReg Reg L) (h : κ) :
    ‖y - F.toFamily.incl h (F.ritzR h (y, DissipFEEC.genExt (-H.hodgeLaplacian) y))‖ ≤
      2 * K * L * m h ^ α := by
  set a := DissipFEEC.genExt (-H.hodgeLaplacian) y
  have hy' : (H.total.harmonic ()).starProjection y - H.greenOp hcr a = y :=
    H.heatRead_lift hcr hy.1.1
  have e : y - F.toFamily.incl h (F.ritzR h (y, a)) =
      ((H.total.harmonic ()).starProjection y -
        F.toFamily.incl h (F.toFamily.harmonicProj h ((F.toFamily.incl h).adjoint y))) -
        (H.greenOp hcr a -
          F.toFamily.incl h (F.toFamily.green h ((F.toFamily.incl h).adjoint a))) := by
    have e1 : y - F.toFamily.incl h (F.ritzR h (y, a)) =
        ((H.total.harmonic ()).starProjection y - H.greenOp hcr a) -
          F.toFamily.incl h (F.ritzR h (y, a)) := by rw [hy']
    rw [e1, ritzR_apply, _root_.map_sub]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1 := (F.toFamily.norm_harmonicProj_sub_le hcr h y).trans (hK hL hy.2.1 h)
  have h2 := (F.toFamily.norm_greenOp_sub_le hcr h a).trans (hK hL hy.2.2.1 h)
  linarith

include hcP hP hm hK0 hK hJ hL in
theorem norm_ritzDefect_lift_le {y : PiLp 2 W} (hy : y ∈ H.heatReg Reg L) (h : κ) :
    ‖F.ritzDefect hcr h (DissipFEEC.genExt (-H.hodgeLaplacian) y,
      DissipFEEC.genExt (-H.hodgeLaplacian) (DissipFEEC.genExt (-H.hodgeLaplacian) y))‖ ≤
      (3 * F.toFamily.boundConst + 16 * cP ^ 2 * F.toFamily.boundConst) * K * L * m h ^ α := by
  set C := F.toFamily.boundConst
  have hC := F.toFamily.boundConst_nonneg
  have hPa :
      (H.total.harmonic ()).starProjection (DissipFEEC.genExt (-H.hodgeLaplacian) y) = 0 := by
    rw [H.genExt_neg_hodgeLaplacian hy.1.1, _root_.map_neg,
      H.starProjection_harmonic_total_hodgeLaplacian, neg_zero]
  refine (F.norm_ritzDefect_le hcr hcP hP h _).trans ?_
  dsimp only
  rw [hPa, sub_zero]
  have hmα := Real.rpow_nonneg (hm h) α
  have h1 := hK hL hy.2.2.1 h
  have h2 := hK hL hy.2.2.2.1 h
  have h3 : F.toFamily.graphDefect h * (16 * cP ^ 2 * C *
      ‖DissipFEEC.genExt (-H.hodgeLaplacian) (DissipFEEC.genExt (-H.hodgeLaplacian) y)‖) ≤
      K * m h ^ α * (16 * cP ^ 2 * C * L) :=
    mul_le_mul (hJ h) (mul_le_mul_of_nonneg_left hy.2.2.2.2 (by positivity)) (by positivity)
      (mul_nonneg hK0 hmα)
  have h1' := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * C)
  have h2' := mul_le_mul_of_nonneg_left h2 hC
  nlinarith

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

include hcP hP hm hK0 hK hJ hL in
/-- The heat rate class with crimes on `[0, T]`. -/
def heatRateClass (T : ℝ) : F.toHeat.RateClass T :=
  (F.heatRitz hcr hcP hP).toRateClass (DissipFEEC.RegScale.trajectory F.toHeat T
      (-H.hodgeLaplacian).sqDomain (H.heatReg Reg L) (fun _ => L) (fun _ => L))
    (fun _ hx => hx.1) m hm α (2 * K)
    ((3 * F.toFamily.boundConst + 16 * cP ^ 2 * F.toFamily.boundConst) * K) (by linarith)
    (mul_nonneg (by have := F.toFamily.boundConst_nonneg; positivity) hK0)
    (fun y hy h => by
      show _ ≤ 2 * K * m h ^ α * L
      exact (F.norm_sub_ritzR_le hcr hK hL hy h).trans_eq (by ring))
    (fun y hy h => by
      show _ + ‖(0 : PiLp 2 W × PiLp 2 W →L[𝕜] F.toFamily.X h) _‖ ≤ _ * m h ^ α * L
      rw [_root_.zero_apply, norm_zero, add_zero]
      exact (F.norm_ritzDefect_lift_le hcr hcP hP hm hK0 hK hJ hL hy h).trans_eq (by ring))

include hcP hP hm hK0 hK hJ hL in
/-- **The heat rate with crimes**: with closed range and a uniform discrete Poincaré inequality, if
`e(f) ≤ K L mᵅ` on regular data and `‖1 - Jₕ‖_{Vₕ} ≤ K mᵅ`, the error from `Rₕ (x, -Δ x)` is
`O((1 + t) K L mᵅ)` on orbits that stay in the regular states with bound `L`. -/
theorem rate_heat_of_static {T : ℝ} {x : PiLp 2 W} (hx : x ∈ (-H.hodgeLaplacian).sqDomain)
    (hreg : ∀ t ∈ Icc 0 T, F.toHeat.S t x ∈ H.heatReg Reg L) (h : κ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖F.toHeat.S t x - F.toHeat.sol h (F.ritzR h (x, DissipFEEC.genExt (-H.hodgeLaplacian) x)) t‖ ≤
      (2 * K + F.toFamily.boundConst *
        ((3 * F.toFamily.boundConst + 16 * cP ^ 2 * F.toFamily.boundConst) * K) * t) *
          L * m h ^ α := by
  set R := F.heatRateClass hcr hcP hP hm hK0 hK hJ hL T
  have hxR : x ∈ R.Data := ⟨hx, fun t ht => ⟨hreg t ht, le_rfl⟩⟩
  have hp : R.p x h 0 = F.ritzR h (x, DissipFEEC.genExt (-H.hodgeLaplacian) x) := by
    change F.ritzR h ((F.heatLift hcr).lift (F.toHeat.S 0 x)) = _
    rw [DissipFEEC.S_def, C0Semigroup.S_zero_apply]
    rfl
  have hr := dissipFEEC_rate F.toHeat R hxR h (R.p x h 0) ht
  rw [sub_self, norm_zero, mul_zero, add_zero] at hr
  rw [← hp]
  refine hr.trans ?_
  change (2 * K * 1 + ‖F.toFamily.incl h‖ *
    ((3 * F.toFamily.boundConst + 16 * cP ^ 2 * F.toFamily.boundConst) * K * 1) * t) *
      (m h ^ α * L) ≤ _
  have hι := F.toFamily.norm_incl_le h
  have hC := F.toFamily.boundConst_nonneg
  have hmα := Real.rpow_nonneg (hm h) α
  have hD : 0 ≤ (3 * F.toFamily.boundConst + 16 * cP ^ 2 * F.toFamily.boundConst) * K :=
    mul_nonneg (by positivity) hK0
  have h0 : ‖F.toFamily.incl h‖ *
      ((3 * F.toFamily.boundConst + 16 * cP ^ 2 * F.toFamily.boundConst) * K * 1) * t ≤
      F.toFamily.boundConst *
        ((3 * F.toFamily.boundConst + 16 * cP ^ 2 * F.toFamily.boundConst) * K) * t := by
    rw [mul_one]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hι hD) ht.1
  have := mul_le_mul_of_nonneg_right (add_le_add_left h0 (2 * K * 1)) (mul_nonneg hmα hL)
  nlinarith

end Rate

end ApproxComplexCrime.HeatFamily

end Feec.HilbertComplex
