module

public import Feec.HilbertComplex.Approximation.CochainProjection
public import Feec.HilbertComplex.Approximation.Convergence
public import Feec.HilbertComplex.InvariantCore

/-!
# The constrained FEEC theorem

A **constrained FEEC discretization** (`Feec.HilbertComplex.ConstrainedFEEC`) of a Hilbert
complex `H` (any finite index type `ι`, any `ComplexShape`; e.g. a window of a complex on `ℤ` or
a short complex on `Fin 3`) bundles

* a closed **constraint subspace** `K` of the total space `W = ⊕ Wⁱ`;
* a family `Vₕ` (indexed by any type `κ`, along a filter `l`, e.g. `h → 0` or `N → ∞`) of
  finite-dimensional **subcomplexes** with **commuting cochain projections** `πₕ`, uniformly
  bounded in `W`;
* the **approximation property**: every `ζ` of the graph space `Γ(𝐝)` is approximated by `Vₕ`.

Its continuous problem is the Hodge wave equation `ξ' = L ξ` with `L = 𝐝 - 𝐝†` (the sign
convention of `Feec.HilbertComplex.wave`; with `L' = 𝐝† - 𝐝` it reads `ξ' = -L' ξ`), solved by
the isometric group `e^{tL}` (Stone); its discrete problem is the semi-discrete equation (4.10)
in `Vₕ`, with `ξₕ(0) = Pₕ ξ₀` (`ConstrainedFEEC.discrete`, `Pₕ` the elliptic projection (4.11)).

## Main results

The **constrained FEEC theorem** `constrainedFEEC` bundles:

1. `constrainedFEEC_wellPosed`: for `ξ₀ ∈ D(L)`, `t ↦ e^{tL} ξ₀` is a classical solution, the
   only strong and the only weak solution, and it conserves energy ([QuennevilleBelair2015],
   Thm 4.6, Thm 4.7).
2. `constrainedFEEC_propagates_iff`: constraints propagate for all data in `K` iff `K` reduces
   `L` (Stone; [QuennevilleBelair2015], Prop. 4.17, with necessity); `constrainedFEEC_propagates`:
   strong solutions from `K` then stay in `K`; `constrainedFEEC_propagates_iff_domain` (data in
   `D(L) ∩ K`, when it is dense in `K`) and `constrainedFEEC_propagates_iff_of_grading`
   (forward strong solutions, for a graded complex).
3. `constrainedFEEC_converges`: `ξₕ → ξ` uniformly on `[0, T]` for `ξ₀ ∈ D(L)`, and for every
   `ξ₀ ∈ W` as soon as `ξₕ(0) → ξ₀` ([QuennevilleBelair2015], Thm 4.14 and the remark after it);
   `constrainedFEEC_rate`: for data in a **rate class** (`ConstrainedFEEC.RateClass`: `D(L²)`
   data whose orbit is approximated in `Γ(𝐝)` to order `C hᵅ ‖ξ₀‖_class`, e.g. `D(L³)` or
   Sobolev data under the approximation estimates of an instance),
   `‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + t)² C hᵅ ‖ξ₀‖_class`, with `C_P = √12 ‖A‖` the uniform bound
   of the elliptic projections ([QuennevilleBelair2015], Prop. 4.13, Thm 4.14).
4. `constrainedFEEC_residual`: if `K` reduces `L`, the **constraint residual** of the discrete
   solution is bounded by the error, `dist(ξₕ(t), K) ≤ ‖ξ(t) - ξₕ(t)‖`, so it tends to `0`
   uniformly on `[0, T]`, with the rate of item 3 (`constrainedFEEC_residual_rate`);
   `constrainedFEEC_residual_not_isReducing`: if `K` does not reduce `L`, then for every `T > 0`
   there are data in `K` (or in `Kᗮ`, the complementary constraint) whose exact solution leaves
   the constraint `Q` at some `t ∈ [0, T]`, and the residuals `dist(ξₕ(t), Q)` of every
   convergent discretization tend to `dist(ξ(t), Q) > 0`; with data in `D(L)` when `D(L) ∩ K` and
   `D(L) ∩ Kᗮ` are dense in `K`, `Kᗮ` (`ConstrainedFEEC.exists_not_mem_of_not_isReducing_domain`).
   For a graded complex and an `R`-invariant `K` (e.g. a product constraint) with `D(L) ∩ K` dense
   in `K`, the data lie in `D(L) ∩ K` itself and `Q = K`
   (`constrainedFEEC_residual_not_isReducing_of_grading`).

Further: `constrainedFEEC_discretePoincare` (the uniform discrete Poincaré inequality given by the
cochain projections, [AFW2010], Thm 3.6) and the non-vacuity witness
`constrainedFEEC_nonvacuous`: on `𝕜 --id--> 𝕜 → 0` with `Vₕ = W` and `πₕ = id`, both branches of
item 4 occur: `K = W` reduces `L`, and `K = 𝕜 × 0 × 0` does not, so some datum of `D(L) ∩ K` has
discrete residuals with a positive limit; it also gives a rate class.

## Hypotheses

The density of `D(L) ∩ K` in `K` in the converse of item 4 with data in `D(L)` cannot be
dropped: if `D(L) ∩ K = 0`, no datum of `D(L) ∩ K` leaves `K`. Without a grading the converse is
stated for `K` or `Kᗮ`: forward invariance of a closed subspace under an isometric group does not
make it reducing (translations on `L²(ℝ)` leave `L²(0, ∞)` invariant in one time direction only),
while forward invariance of both `K` and `Kᗮ` does (`ConstrainedFEEC.isReducing_of_forall_nonneg`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (approximation property, bounded cochain projections, Thm 3.6, Thm 3.9)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 5 (Thm 5.3)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4 (Thms 4.6, 4.7), §4.6 ((4.10), (4.11), Prop. 4.13, Thm 4.14), §4.10 (Prop. 4.17)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

namespace Feec.HilbertComplex

open _root_.Feec.HodgeWave

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

/-- A **constrained FEEC discretization** of the Hodge wave equation of the Hilbert complex `H`:
a closed constraint subspace `K` of the total space, and a family `Vₕ` (`h : κ`, along the
filter `l`) of finite-dimensional subcomplexes with commuting cochain projections `πₕ`,
uniformly bounded in `W`, which approximate every element of the graph space `Γ(𝐝)` (the
approximation property). See [AFW2010], §3.3, [Arnold2018], Ch. 5 and
[QuennevilleBelair2015], §4.6, §4.7. -/
structure ConstrainedFEEC (H : HilbertComplex 𝕜 c W) (κ : Type*) where
  /-- the constraint subspace -/
  K : Submodule 𝕜 (PiLp 2 W)
  isClosed_K : IsClosed (K : Set (PiLp 2 W))
  /-- the filter along which the discretization is refined (e.g. `h → 0`) -/
  l : Filter κ
  /-- the discrete subcomplexes -/
  V : κ → H.Subcomplex
  [finiteDimensional : ∀ h i, FiniteDimensional 𝕜 ((V h).V i)]
  /-- the commuting cochain projections -/
  π : ∀ h, (V h).CochainProjection
  bound_π : ∃ C, ∀ h i x, ‖(π h).π i x‖ ≤ C * ‖x‖
  /-- the approximation property in the graph norm -/
  dense : ∀ ζ : H.totalD.GraphSpace, ∀ δ > 0, ∀ᶠ h in l, ∃ w ∈ (V h).graphSub, ‖ζ - w‖ < δ

attribute [instance] ConstrainedFEEC.finiteDimensional

/-- The uniform bound `C_P = √12 ‖A‖` of the elliptic projections of all subcomplexes of `H`
([QuennevilleBelair2015], Prop. 4.13). -/
def ellipticConst (H : HilbertComplex 𝕜 c W) : ℝ := ‖shiftedForm H.totalD‖ / ((1 / 2) / √3)

theorem ellipticConst_nonneg (H : HilbertComplex 𝕜 c W) : 0 ≤ ellipticConst H := by
  unfold ellipticConst; positivity

/-- The graph-space lift `x ↦ (x, 𝐝 x)` of `x ∈ D(L)`. -/
def waveLift (H : HilbertComplex 𝕜 c W) (x : H.wave.domain) : H.totalD.GraphSpace :=
  H.totalD.toGraphSpace ⟨x, (H.mem_wave_domain.1 x.2).1⟩

@[simp] theorem graphFst_waveLift (H : HilbertComplex 𝕜 c W) (x : H.wave.domain) :
    H.totalD.graphFst (waveLift H x) = x := rfl

namespace ConstrainedFEEC

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ConstrainedFEEC H κ)

instance : CompleteSpace F.K := F.isClosed_K.completeSpace_coe

instance : F.K.HasOrthogonalProjection := .ofCompleteSpace _

/-- The discrete spaces `Vₕ` in the graph space `Γ(𝐝)`. -/
abbrev Kh (h : κ) : Submodule 𝕜 H.totalD.GraphSpace := (F.V h).graphSub

/-- A constrained FEEC discretization is approximating (uniformly bounded elliptic projections,
[QuennevilleBelair2015], Prop. 4.13, and the approximation property). -/
theorem isApproximating : IsApproximating F.l F.Kh :=
  Subcomplex.isApproximating F.dense

theorem norm_ellipticProjection_le (h : κ) (ζ : H.totalD.GraphSpace) :
    ‖ellipticProjection (F.Kh h) ζ‖ ≤ ellipticConst H * ‖ζ‖ :=
  (F.V h).norm_ellipticProjection_le ζ

/-- **Quasi-optimality of the elliptic projection**: `‖ζ - Pₕ ζ‖ ≤ (1 + C_P) ‖ζ - w‖` for every
`w ∈ Vₕ`. -/
theorem norm_sub_ellipticProjection_le (h : κ) (ζ : H.totalD.GraphSpace) {w : H.totalD.GraphSpace}
    (hw : w ∈ F.Kh h) : ‖ζ - ellipticProjection (F.Kh h) ζ‖ ≤ (1 + ellipticConst H) * ‖ζ - w‖ :=
  Feec.HodgeWave.norm_sub_ellipticProjection_le H.totalD_mapsTo H.totalD_comp_totalD (F.Kh h)
    (fun _ hξ => (F.V h).graphD_mem_graphSub hξ) ζ hw

/-! ### The discrete solutions -/

section Discrete

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

theorem exists_discrete (h : κ) (ζ : H.totalD.GraphSpace) :
    ∃ ξh ξh' : ℝ → H.totalD.GraphSpace, ξh 0 = ellipticProjection (F.Kh h) ζ ∧
      IsSemidiscreteSolution (F.Kh h) univ ξh ξh' := by
  obtain ⟨ξh, ξh', h0, -, -, hs⟩ :=
    exists_isSemidiscreteSolution (F.Kh h) (ellipticProjection_mem (F.Kh h) ζ) 0
  exact ⟨ξh, ξh', h0, hs⟩

/-- The **semi-discrete solution** `ξₕ` of (4.10) in `Vₕ` with `ξₕ(0) = Pₕ ζ`, for all times.
[QuennevilleBelair2015], (4.10) -/
def discrete (h : κ) (ζ : H.totalD.GraphSpace) : ℝ → H.totalD.GraphSpace :=
  (F.exists_discrete h ζ).choose

/-- The time derivative of `ConstrainedFEEC.discrete`. -/
def discreteDeriv (h : κ) (ζ : H.totalD.GraphSpace) : ℝ → H.totalD.GraphSpace :=
  (F.exists_discrete h ζ).choose_spec.choose

theorem discrete_zero (h : κ) (ζ : H.totalD.GraphSpace) :
    F.discrete h ζ 0 = ellipticProjection (F.Kh h) ζ :=
  (F.exists_discrete h ζ).choose_spec.choose_spec.1

theorem isSemidiscreteSolution_discrete (h : κ) (ζ : H.totalD.GraphSpace) (I : Set ℝ) :
    IsSemidiscreteSolution (F.Kh h) I (F.discrete h ζ) (F.discreteDeriv h ζ) :=
  (F.exists_discrete h ζ).choose_spec.choose_spec.2.mono (subset_univ I)

/-- Every semi-discrete solution on `[0, T]` with `ξₕ(0) = Pₕ ζ` is `ConstrainedFEEC.discrete`. -/
theorem eqOn_discrete (h : κ) (ζ : H.totalD.GraphSpace) {T : ℝ} {ξh ξh' : ℝ → H.totalD.GraphSpace}
    (hξh : IsSemidiscreteSolution (F.Kh h) (Icc 0 T) ξh ξh')
    (h0 : ξh 0 = ellipticProjection (F.Kh h) ζ) : EqOn ξh (F.discrete h ζ) (Icc 0 T) :=
  hξh.eqOn (F.isSemidiscreteSolution_discrete h ζ _) (h0.trans (F.discrete_zero h ζ).symm)

end Discrete

end ConstrainedFEEC

/-! ### Auxiliary facts on the wave group -/

section Aux

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] (H : HilbertComplex 𝕜 c W)

omit [Fintype ι] [∀ i, CompleteSpace (W i)] [∀ i, NormedSpace ℝ (W i)]
  [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
private theorem apply_of_eq' {A B : PiLp 2 W →ₗ.[𝕜] PiLp 2 W} (h : A = B) (x : A.domain) :
    A x = B ⟨x, h ▸ x.2⟩ := by
  subst h; rfl

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem mem_domain_sub_adjoint {x : PiLp 2 W} (hx : x ∈ H.wave.domain) :
    x ∈ (H.totalD - H.totalD†).domain := by
  rw [← wave_eq]; exact hx

/-- The orbit of `x ∈ D(L)` is a classical solution of `U' = L U` on `[0, T]`. -/
theorem isClassicalSolution_waveGroup_orbit {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (T : ℝ) :
    Evolution.IsClassicalSolution H.wave (Icc 0 T) 0 fun t => H.waveGroup.S t x := by
  have hg : H.waveGroup.toC0Semigroup.generator = H.wave := H.generator_waveGroup
  have hO := H.waveGroup.toC0Semigroup.isClassicalSolution_orbit (U₀ := x) (by rw [hg]; exact hx)
    0 T
  rw [hg] at hO
  simpa using hO

/-- `D(L)` is invariant under the wave group. -/
theorem waveGroup_mem_domain {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (t : ℝ) :
    H.waveGroup.S t x ∈ H.wave.domain := by
  have hd : H.waveGroup.generator.domain = H.wave.domain := by rw [generator_waveGroup]
  have h2 : H.waveGroup.S t x ∈ H.waveGroup.generator.domain :=
    H.waveGroup.mapsTo_domain ⟨x, hd ▸ hx⟩ t
  rwa [hd] at h2

/-- The derivative of the orbit of `x ∈ D(L)` is `e^{tL} L x`. -/
theorem hasDerivAt_waveGroup {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (t : ℝ) :
    HasDerivAt (fun s => H.waveGroup.S s x) (H.waveGroup.S t (H.wave ⟨x, hx⟩)) t := by
  have hg := H.generator_waveGroup
  have h := H.waveGroup.hasDerivAt_apply ⟨x, by rw [hg]; exact hx⟩ t
  rwa [apply_of_eq' hg] at h

/-- **Exact solutions in `C¹(Γ(𝐝))` for `D(L²)` data**, with both the solution and its
derivative identified: `ξ(t) = (e^{tL} x, 𝐝 e^{tL} x)` and `ξ'(t) = (e^{tL} L x, …)`. -/
theorem exists_isGraphSolution_waveGroup {x : PiLp 2 W} (hx : x ∈ H.wave.domain)
    (hLx : H.wave ⟨x, hx⟩ ∈ H.wave.domain) {b : ℝ} (hb : 0 < b) :
    ∃ ξ ξ' : ℝ → H.totalD.GraphSpace, IsGraphSolution (Icc 0 b) ξ ξ' ∧
      (∀ t, H.totalD.graphFst (ξ t) = H.waveGroup.S t x) ∧
      ∀ t ∈ Icc 0 b, H.totalD.graphFst (ξ' t) = H.waveGroup.S t (H.wave ⟨x, hx⟩) := by
  have h₀ := mem_domain_sub_adjoint H hx
  have e : H.wave ⟨x, hx⟩ = (H.totalD - H.totalD†) ⟨x, h₀⟩ := apply_of_eq' H.wave_eq _
  have hL₀ : (H.totalD - H.totalD†) ⟨x, h₀⟩ ∈ (H.totalD - H.totalD†).domain := by
    rw [← e]; exact mem_domain_sub_adjoint H hLx
  obtain ⟨ξ, ξ', hξ, hξS⟩ := Feec.HodgeWave.exists_isGraphSolution H.dense_totalDomain
    H.isClosed_totalD H.totalD_mapsTo H.totalD_comp_totalD h₀ hL₀ 0 b
  rw [HodgeWave.waveGroup_totalD] at hξS
  have hS : ∀ t, H.totalD.graphFst (ξ t) = H.waveGroup.S t x := fun t => by
    rw [hξS, sub_zero]
  refine ⟨ξ, ξ', hξ, hS, fun t ht => ?_⟩
  have h1 : HasDerivWithinAt (fun s => H.totalD.graphFst (ξ s)) (H.totalD.graphFst (ξ' t))
      (Icc 0 b) t :=
    (H.totalD.graphFst.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hξ.deriv t ht)
  have h2 : HasDerivWithinAt (fun s => H.totalD.graphFst (ξ s))
      (H.waveGroup.S t (H.wave ⟨x, hx⟩)) (Icc 0 b) t := by
    simp only [hS]
    exact (hasDerivAt_waveGroup H hx t).hasDerivWithinAt
  exact (uniqueDiffOn_Icc hb t ht).eq_deriv _ h1 h2

/-- If a set `P` is invariant under `e^{sL}` for `s ∈ [0, T]` (`T > 0`), it is invariant for
all `s ≥ 0`. -/
theorem forall_nonneg_of_forall_Icc {P : Set (PiLp 2 W)} {T : ℝ} (hT : 0 < T)
    (hP : ∀ x ∈ P, ∀ s ∈ Icc 0 T, H.waveGroup.S s x ∈ P) :
    ∀ x ∈ P, ∀ t, 0 ≤ t → H.waveGroup.S t x ∈ P := by
  have key : ∀ n : ℕ, ∀ x ∈ P, ∀ t ∈ Icc 0 (n * T), H.waveGroup.S t x ∈ P := by
    intro n
    induction n with
    | zero =>
      intro x hx t ht
      have h2 := ht.2
      simp only [Nat.cast_zero, zero_mul] at h2
      have : t = 0 := le_antisymm h2 ht.1
      subst this
      exact hP x hx 0 ⟨le_rfl, hT.le⟩
    | succ n ih =>
      intro x hx t ht
      by_cases htT : t ≤ T
      · exact hP x hx t ⟨ht.1, htT⟩
      · replace htT := not_le.1 htT
        have e : H.waveGroup.S t x = H.waveGroup.S (t - T) (H.waveGroup.S T x) := by
          rw [← C0Group.map_add_apply, sub_add_cancel]
        rw [e]
        refine ih _ (hP x hx T ⟨hT.le, le_rfl⟩) _ ⟨by linarith, ?_⟩
        have := ht.2
        push_cast at this
        linarith
  intro x hx t ht
  obtain ⟨n, hn⟩ := exists_nat_ge (t / T)
  refine key n x hx t ⟨ht, ?_⟩
  rwa [div_le_iff₀ hT] at hn

end Aux

/-! ### 1. Well-posedness -/

section Main

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ConstrainedFEEC H κ)

/-- **Well-posedness** (Stone): for `ξ₀ ∈ D(L)`, the orbit `t ↦ e^{tL} ξ₀` of the wave group is a
classical solution of `ξ' = L ξ` on `[0, T]`, every strong and every weak solution with initial
value `ξ₀` equals it, and it conserves energy. [QuennevilleBelair2015], Thm 4.6, Thm 4.7 -/
theorem constrainedFEEC_wellPosed {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (T : ℝ) :
    Evolution.IsClassicalSolution H.wave (Icc 0 T) 0 (fun t => H.waveGroup.S t x) ∧
    (∀ U, U 0 = x → Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U →
      EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
    (∀ U, U 0 = x → HodgeWave.IsWeakSolution H (Icc 0 T) 0 U →
      EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
    ∀ t, ‖H.waveGroup.S t x‖ = ‖x‖ := by
  have hO := isClassicalSolution_waveGroup_orbit H hx T
  obtain ⟨U, hU0, -, hUs, hUw, -⟩ := HodgeWave.existsUnique_hom H hx 0 T
  have hOU : EqOn (fun t => H.waveGroup.S t x) U (Icc 0 T) :=
    hUs _ (by simp) hO.toIsStrongSolution
  refine ⟨hO, fun V hV0 hV => fun t ht => (hUs V hV0 hV ht).trans (hOU ht).symm,
    fun V hV0 hV => fun t ht => (hUw V hV0 hV ht).trans (hOU ht).symm,
    fun t => H.isIsometric_waveGroup t x⟩

/-! ### 2. Constraint propagation -/

/-- **Constraints propagate iff `K` is reducing**: `K` reduces `L` iff `e^{tL} K ⊆ K` for all
`t`, i.e. iff the (mild) solution of every datum in `K` stays in `K`. [QuennevilleBelair2015],
Prop. 4.17, with necessity. -/
theorem constrainedFEEC_propagates_iff :
    H.wave.IsReducing F.K ↔ ∀ t, ∀ x ∈ F.K, H.waveGroup.S t x ∈ F.K :=
  (H.isReducing_iff_waveGroup_invariant F.K).trans C0Group.map_le_iff_forall

/-- **Constraint propagation for strong solutions**: if `K` reduces `L`, every strong solution
of `ξ' = L ξ` on `[0, T]` with `ξ(0) ∈ K` stays in `K`. [QuennevilleBelair2015], Prop. 4.17 -/
theorem constrainedFEEC_propagates (hK : H.wave.IsReducing F.K) {T : ℝ} {U : ℝ → PiLp 2 W}
    (h0 : U 0 ∈ F.K) (hU : Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U) :
    ∀ t ∈ Icc 0 T, U t ∈ F.K :=
  hU.mem_of_isReducing H.isSkewAdjoint_wave.isDissipative hK h0 fun _ _ => F.K.zero_mem

/-- Invariance of `D(L) ∩ K` gives invariance of `K` when `D(L) ∩ K` is dense in `K`. -/
theorem waveGroup_mem_of_dense {P : Set (PiLp 2 W)} {Q : Set (PiLp 2 W)} (hQ : IsClosed Q)
    (hdense : ∀ k ∈ Q, k ∈ closure (P ∩ Q)) {t : ℝ}
    (h : ∀ x ∈ P, x ∈ Q → H.waveGroup.S t x ∈ Q) : ∀ x ∈ Q, H.waveGroup.S t x ∈ Q := by
  intro x hx
  have hsub : P ∩ Q ⊆ (H.waveGroup.S t) ⁻¹' Q := fun y hy => h y hy.1 hy.2
  exact closure_minimal hsub (hQ.preimage (H.waveGroup.S t).continuous) (hdense x hx)

/-- **Constraints propagate iff `K` is reducing, for data in `D(L) ∩ K`**, when `D(L) ∩ K` is
dense in `K`. [QuennevilleBelair2015], Prop. 4.17 -/
theorem constrainedFEEC_propagates_iff_domain
    (hdense : ∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) :
    H.wave.IsReducing F.K ↔
      ∀ t, ∀ x ∈ H.wave.domain, x ∈ F.K → H.waveGroup.S t x ∈ F.K := by
  rw [constrainedFEEC_propagates_iff]
  exact ⟨fun h t x _ hx => h t x hx,
    fun h t => waveGroup_mem_of_dense F.isClosed_K hdense (h t)⟩

/-- **Forward constraint propagation characterizes reducing constraints on graded complexes**:
for a grading `p` and an `R`-invariant `K` with `D(L) ∩ K` dense in `K`, `K` reduces `L` iff every
strong solution on `[0, T]` from `K` stays in `K`. [QuennevilleBelair2015], Prop. 4.17 -/
theorem constrainedFEEC_propagates_iff_of_grading {p : ι → Bool}
    (hp : ∀ i j, c.Rel i j → p j ≠ p i) (hRK : ∀ x ∈ F.K, reversal 𝕜 p x ∈ F.K)
    (hdense : ∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) :
    H.wave.IsReducing F.K ↔ ∀ (T : ℝ) (U : ℝ → PiLp 2 W), U 0 ∈ F.K →
      Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U → ∀ t ∈ Icc 0 T, U t ∈ F.K :=
  H.isReducing_iff_forall_isStrongSolution hp F.K hRK hdense

/-! ### 3. Convergence -/

/-- **Convergence of the constrained FEEC discretization** ([QuennevilleBelair2015], Thm 4.14 and
the convergence remark after it): for `ξ₀ ∈ D(L)` the semi-discrete solutions with
`ξₕ(0) = Pₕ ξ₀` converge to `e^{tL} ξ₀` uniformly on `[0, T]`; for `ξ₀ ∈ W`, every family of
semi-discrete solutions with `ξₕ(0) → ξ₀` converges to `e^{tL} ξ₀` uniformly on `[0, T]`, and such
families exist. -/
theorem constrainedFEEC_converges (T : ℝ) :
    (∀ x : H.wave.domain, TendstoUniformlyOn
      (fun h t => H.totalD.graphFst (F.discrete h (waveLift H x) t))
      (fun t => H.waveGroup.S t x) F.l (Icc 0 T)) ∧
    ∀ x : PiLp 2 W,
      (∀ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
        (∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
        Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x) →
        TendstoUniformlyOn (fun h t => H.totalD.graphFst (ξh h t))
          (fun t => H.waveGroup.S t x) F.l (Icc 0 T)) ∧
      ∃ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
        (∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) ∧
        Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x) := by
  refine ⟨fun x => ?_, fun x => ⟨fun ξh ξh' hξh h0 => ?_, ?_⟩⟩
  · have hx := mem_domain_sub_adjoint H x.2
    have hc := Feec.HodgeWave.tendstoUniformlyOn_ellipticProjection H.dense_totalDomain
      H.isClosed_totalD H.totalD_mapsTo H.totalD_comp_totalD F.isApproximating (a := 0) (b := T)
      ⟨x, hx⟩ (fun h => F.isSemidiscreteSolution_discrete h _ _)
      (fun h => F.discrete_zero h _)
    rw [HodgeWave.waveGroup_totalD] at hc
    simp only [sub_zero] at hc
    exact hc
  · have hc := Feec.HodgeWave.tendstoUniformlyOn_of_tendsto H.dense_totalDomain
      H.isClosed_totalD H.totalD_mapsTo H.totalD_comp_totalD F.isApproximating x hξh h0
    rw [HodgeWave.waveGroup_totalD] at hc
    simp only [sub_zero] at hc
    exact hc
  · obtain ⟨v, hvK, hv⟩ := Feec.HodgeWave.exists_tendsto_init (l := F.l) (K := F.Kh)
      H.dense_totalD_domain F.isApproximating x
    refine ⟨fun h => F.discrete h (v h), fun h => F.discreteDeriv h (v h),
      fun h => F.isSemidiscreteSolution_discrete h _ _, ?_⟩
    simp only [F.discrete_zero, ellipticProjection_of_mem _ (hvK _)]
    exact hv

/-- A **rate class** of a constrained FEEC discretization: data `x ∈ D(L²)` (the class `Data`,
with a class norm `‖x‖_class`) whose orbit `ξ(t) = e^{tL} x` and its derivative
`ξ'(t) = e^{tL} L x`, read in the graph space `Γ(𝐝)`, are approximated by `Vₕ` to order
`C hᵅ ‖x‖_class` for `t ≥ 0`. Instances supply it from regularity (`D(L³)`, Sobolev classes)
and approximation estimates; the constrained FEEC theorem turns it into the error bound
`constrainedFEEC_rate`. [QuennevilleBelair2015], Thm 4.14, Thm 4.15; [AFW2010], §3.3 -/
structure ConstrainedFEEC.RateClass (F : ConstrainedFEEC H κ) where
  /-- the data of the class -/
  Data : Set (PiLp 2 W)
  /-- the norm of the class -/
  classNorm : PiLp 2 W → ℝ
  /-- the mesh size of `Vₕ` -/
  meshSize : κ → ℝ
  /-- the order of approximation -/
  α : ℝ
  /-- the constant of the approximation estimate -/
  C : ℝ
  mem_domain : ∀ x ∈ Data, x ∈ H.wave.domain
  mem_domain_sq : ∀ x (hx : x ∈ H.wave.domain), x ∈ Data → H.wave ⟨x, hx⟩ ∈ H.wave.domain
  approx : ∀ x ∈ Data, ∀ h t, 0 ≤ t → ∀ v : H.totalD.GraphSpace,
    H.totalD.graphFst v = H.waveGroup.S t x →
      ∃ w ∈ F.Kh h, ‖v - w‖ ≤ C * meshSize h ^ α * classNorm x
  approx_deriv : ∀ x (hx : x ∈ H.wave.domain), x ∈ Data → ∀ h t, 0 ≤ t →
    ∀ v : H.totalD.GraphSpace, H.totalD.graphFst v = H.waveGroup.S t (H.wave ⟨x, hx⟩) →
      ∃ w ∈ F.Kh h, ‖v - w‖ ≤ C * meshSize h ^ α * classNorm x

/-- **The rate of the constrained FEEC discretization** for data in a rate class:
`‖e^{tL} ξ₀ - ξₕ(t)‖ ≤ (1 + C_P) (1 + t)² C hᵅ ‖ξ₀‖_class` for `t ≥ 0`, with `ξₕ(0) = Pₕ ξ₀` and
`C_P = √12 ‖A‖` (`ellipticConst`). [QuennevilleBelair2015], Prop. 4.13, Thm 4.14 -/
theorem constrainedFEEC_rate (R : F.RateClass) {x : PiLp 2 W} (hxR : x ∈ R.Data) (h : κ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖H.waveGroup.S t x -
        H.totalD.graphFst (F.discrete h (waveLift H ⟨x, R.mem_domain x hxR⟩) t)‖ ≤
      (1 + ellipticConst H) * (1 + t) ^ 2 * (R.C * R.meshSize h ^ R.α * R.classNorm x) := by
  have hx := R.mem_domain x hxR
  set b := t + 1
  have hb : 0 < b := by positivity
  obtain ⟨ξ, ξ', hξ, hξS, hξ'S⟩ :=
    exists_isGraphSolution_waveGroup H hx (R.mem_domain_sq x hx hxR) hb
  set ζ₀ := waveLift H ⟨x, hx⟩
  have hξ0 : ξ 0 = ζ₀ := H.totalD.graphFst_injective (by
    rw [hξS, C0Group.S_zero_apply]; rfl)
  set δ := (1 + ellipticConst H) * (R.C * R.meshSize h ^ R.α * R.classNorm x) with hδdef
  set P := ellipticProjection (F.Kh h) with hP
  have he : ∀ s ∈ Icc 0 b, ‖H.totalD.graphFst (P (ξ s) - ξ s)‖ ≤ δ := fun s hs => by
    obtain ⟨w, hw, hwb⟩ := R.approx x hxR h s hs.1 (ξ s) (hξS s)
    refine (norm_graphFst_le _).trans ?_
    rw [norm_sub_rev]
    exact (F.norm_sub_ellipticProjection_le h _ hw).trans
      (mul_le_mul_of_nonneg_left hwb (add_nonneg zero_le_one (ellipticConst_nonneg H)))
  have he' : ∀ s ∈ Icc 0 b, ‖H.totalD.graphFst (P (ξ' s) - ξ' s)‖ ≤ δ := fun s hs => by
    obtain ⟨w, hw, hwb⟩ := R.approx_deriv x hx hxR h s hs.1 (ξ' s) (hξ'S s hs)
    refine (norm_graphFst_le _).trans ?_
    rw [norm_sub_rev]
    exact (F.norm_sub_ellipticProjection_le h _ hw).trans
      (mul_le_mul_of_nonneg_left hwb (add_nonneg zero_le_one (ellipticConst_nonneg H)))
  have htb : t ∈ Icc 0 b := ⟨ht, le_add_of_nonneg_right zero_le_one⟩
  have hbound := hξ.norm_sub_le (F.isSemidiscreteSolution_discrete h ζ₀ (Icc 0 b)) t htb
  rw [← hP] at hbound
  have e0 : H.totalD.graphFst (P (ξ 0) - F.discrete h ζ₀ 0) = 0 := by
    rw [F.discrete_zero, ← hP, hξ0, sub_self]; exact H.totalD.graphFst.map_zero
  have eL : H.totalD.graphFst (ξ t - F.discrete h ζ₀ t) =
      H.waveGroup.S t x - H.totalD.graphFst (F.discrete h ζ₀ t) := by
    rw [H.totalD.graphFst.map_sub, hξS]
  rw [e0, eL, norm_zero, zero_add, sub_zero] at hbound
  have hint : ∫ s in (0 : ℝ)..t, ‖H.totalD.graphFst (P (ξ' s) - ξ' s)‖ ≤ t * δ := by
    have hcont : ContinuousOn (fun s => ‖H.totalD.graphFst (P (ξ' s) - ξ' s)‖) (Icc 0 t) :=
      (H.totalD.graphFst.continuous.comp_continuousOn
        ((P.continuous.comp_continuousOn hξ.continuousOn_deriv).sub
          hξ.continuousOn_deriv)).norm.mono (Icc_subset_Icc le_rfl htb.2)
    have := intervalIntegral.integral_mono_on ht (hcont.intervalIntegrable_of_Icc ht)
      (intervalIntegrable_const (μ := MeasureTheory.volume)) fun s hs =>
        he' s ⟨hs.1, hs.2.trans htb.2⟩
    simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] using this
  have h1 := he t htb
  have h2 := he 0 ⟨le_rfl, hb.le⟩
  have i1 : t * ‖H.totalD.graphFst (P (ξ 0) - ξ 0)‖ ≤ t * δ := mul_le_mul_of_nonneg_left h2 ht
  have i2 : (1 + t) * ∫ s in (0 : ℝ)..t, ‖H.totalD.graphFst (P (ξ' s) - ξ' s)‖ ≤
      (1 + t) * (t * δ) := mul_le_mul_of_nonneg_left hint (by linarith only [ht])
  calc _ ≤ _ := hbound
    _ ≤ δ + t * δ + (1 + t) * (t * δ) := by linarith only [h1, i1, i2]
    _ = (1 + ellipticConst H) * (1 + t) ^ 2 *
        (R.C * R.meshSize h ^ R.α * R.classNorm x) := by rw [hδdef]; ring

/-- For mesh sizes `hₖ → 0` and `α > 0`, the rate bound tends to `0` uniformly on `[0, T]`. -/
theorem ConstrainedFEEC.RateClass.tendsto_rate (R : F.RateClass) (hα : 0 < R.α)
    (hmesh : Tendsto R.meshSize F.l (𝓝 0)) (x : PiLp 2 W) (y : ℝ) :
    Tendsto (fun h => y * (R.C * R.meshSize h ^ R.α * R.classNorm x)) F.l (𝓝 0) := by
  have h1 : Tendsto (fun h => R.meshSize h ^ R.α) F.l (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 R.α (Or.inr hα.le)).tendsto).comp hmesh
    rwa [Real.zero_rpow hα.ne'] at this
  have := ((h1.const_mul R.C).mul_const (R.classNorm x)).const_mul y
  simpa using this

/-! ### 4. The constraint residual -/

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- **The constraint residual is bounded by the error**: if `ξ(t) ∈ K`, then
`dist(ξₕ(t), K) ≤ ‖ξ(t) - ξₕ(t)‖`. -/
theorem ConstrainedFEEC.infDist_le_norm_sub {y z : PiLp 2 W} (hy : y ∈ F.K) :
    infDist z (F.K : Set (PiLp 2 W)) ≤ ‖y - z‖ := by
  rw [norm_sub_rev, ← dist_eq_norm]; exact infDist_le_dist_of_mem hy

/-- **Residual of a reducing constraint**: if `K` reduces `L` and `ξ₀ ∈ D(L) ∩ K`, the
constraint residual of the discrete solution is bounded by the error,
`dist(ξₕ(t), K) ≤ ‖e^{tL} ξ₀ - ξₕ(t)‖`, and tends to `0` uniformly on `[0, T]`. -/
theorem constrainedFEEC_residual (hK : H.wave.IsReducing F.K) (x : H.wave.domain)
    (hxK : (x : PiLp 2 W) ∈ F.K) (T : ℝ) :
    (∀ h t, infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t)) (F.K : Set (PiLp 2 W)) ≤
      ‖H.waveGroup.S t x - H.totalD.graphFst (F.discrete h (waveLift H x) t)‖) ∧
    TendstoUniformlyOn
      (fun h t => infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t))
        (F.K : Set (PiLp 2 W))) (fun _ => 0) F.l (Icc 0 T) := by
  have hmem : ∀ t, H.waveGroup.S t x ∈ F.K := fun t =>
    (constrainedFEEC_propagates_iff F).1 hK t x hxK
  have hle := fun h t => F.infDist_le_norm_sub (z := H.totalD.graphFst
    (F.discrete h (waveLift H x) t)) (hmem t)
  refine ⟨hle, ?_⟩
  have hc := (constrainedFEEC_converges F T).1 x
  rw [Metric.tendstoUniformlyOn_iff] at hc ⊢
  intro ε hε
  filter_upwards [hc ε hε] with h hh t ht
  have := hh t ht
  rw [dist_eq_norm] at this
  rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg infDist_nonneg]
  exact (hle h t).trans_lt this

/-- **Rate of the constraint residual**: for a reducing `K` and data in `K ∩` a rate class,
`dist(ξₕ(t), K) ≤ (1 + C_P) (1 + t)² C hᵅ ‖ξ₀‖_class`. -/
theorem constrainedFEEC_residual_rate (hK : H.wave.IsReducing F.K) (R : F.RateClass)
    {x : PiLp 2 W} (hxR : x ∈ R.Data) (hxK : x ∈ F.K) (h : κ) {t : ℝ} (ht : 0 ≤ t) :
    infDist (H.totalD.graphFst (F.discrete h (waveLift H ⟨x, R.mem_domain x hxR⟩) t))
        (F.K : Set (PiLp 2 W)) ≤
      (1 + ellipticConst H) * (1 + t) ^ 2 * (R.C * R.meshSize h ^ R.α * R.classNorm x) :=
  (F.infDist_le_norm_sub ((constrainedFEEC_propagates_iff F).1 hK t x hxK)).trans
    (constrainedFEEC_rate F R hxR h ht)

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- The residual of every convergent discretization tends to the distance of the exact solution
to the constraint. -/
theorem ConstrainedFEEC.tendsto_infDist {Q : Set (PiLp 2 W)} {y : PiLp 2 W} {f : κ → PiLp 2 W}
    (hf : Tendsto f F.l (𝓝 y)) : Tendsto (fun h => infDist (f h) Q) F.l (𝓝 (infDist y Q)) :=
  ((continuous_infDist_pt Q).tendsto y).comp hf

/-- **Forward invariance of `K` and `Kᗮ` makes `K` reducing**: if `e^{tL} K ⊆ K` and
`e^{tL} Kᗮ ⊆ Kᗮ` for `t ≥ 0`, then `K` reduces `L` (`e^{-tL} = (e^{tL})*`). -/
theorem ConstrainedFEEC.isReducing_of_forall_nonneg
    (h1 : ∀ x ∈ F.K, ∀ t, 0 ≤ t → H.waveGroup.S t x ∈ F.K)
    (h2 : ∀ x ∈ F.Kᗮ, ∀ t, 0 ≤ t → H.waveGroup.S t x ∈ F.Kᗮ) : H.wave.IsReducing F.K := by
  refine (constrainedFEEC_propagates_iff F).2 fun t x hx => ?_
  rcases le_total 0 t with ht | ht
  · exact h1 x hx t ht
  · rw [← Submodule.orthogonal_orthogonal F.K, Submodule.mem_orthogonal]
    intro u hu
    have hu' : H.waveGroup.S (-t) u ∈ F.Kᗮ := h2 u hu (-t) (by linarith)
    rw [← inner_conj_symm, H.isIsometric_waveGroup.inner_S_left,
      Submodule.inner_right_of_mem_orthogonal hx hu', _root_.map_zero]

/-- **Non-reducing constraints are violated** (time-symmetric form): if `K` does not reduce `L`,
then for every `T > 0` some datum of `K` leaves `K`, or some datum of `Kᗮ` leaves `Kᗮ`, at a
time `t ∈ [0, T]`. -/
theorem ConstrainedFEEC.exists_not_mem_of_not_isReducing (hK : ¬ H.wave.IsReducing F.K) {T : ℝ}
    (hT : 0 < T) :
    (∃ x ∈ F.K, ∃ t ∈ Icc 0 T, H.waveGroup.S t x ∉ F.K) ∨
      ∃ x ∈ F.Kᗮ, ∃ t ∈ Icc 0 T, H.waveGroup.S t x ∉ F.Kᗮ := by
  by_contra hc
  simp only [not_or, not_exists, not_and, not_not] at hc
  exact hK (F.isReducing_of_forall_nonneg (forall_nonneg_of_forall_Icc H hT (P := F.K) hc.1)
    (forall_nonneg_of_forall_Icc H hT (P := F.Kᗮ) hc.2))

/-- **Non-reducing constraints are violated by data in `D(L)`**, when `D(L) ∩ K` is dense in `K`
and `D(L) ∩ Kᗮ` is dense in `Kᗮ`. -/
theorem ConstrainedFEEC.exists_not_mem_of_not_isReducing_domain (hK : ¬ H.wave.IsReducing F.K)
    {T : ℝ} (hT : 0 < T) (hdense : ∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K))
    (hdense' : ∀ k ∈ F.Kᗮ, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.Kᗮ)) :
    (∃ x ∈ H.wave.domain, x ∈ F.K ∧ ∃ t ∈ Icc 0 T, H.waveGroup.S t x ∉ F.K) ∨
      ∃ x ∈ H.wave.domain, x ∈ F.Kᗮ ∧ ∃ t ∈ Icc 0 T, H.waveGroup.S t x ∉ F.Kᗮ := by
  by_contra hc
  simp only [not_or, not_exists, not_and, not_not] at hc
  have key : ∀ Q : Submodule 𝕜 (PiLp 2 W), IsClosed (Q : Set (PiLp 2 W)) →
      (∀ k ∈ Q, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ Q)) →
      (∀ x ∈ H.wave.domain, x ∈ Q → ∀ t ∈ Icc 0 T, H.waveGroup.S t x ∈ Q) →
      ∀ x ∈ Q, ∀ t, 0 ≤ t → H.waveGroup.S t x ∈ Q := by
    intro Q hQ hd h x hx t ht
    have hP := forall_nonneg_of_forall_Icc H hT
      (P := (H.wave.domain : Set (PiLp 2 W)) ∩ Q)
      fun y hy s hs => ⟨waveGroup_mem_domain H hy.1 s, h y hy.1 hy.2 s hs⟩
    exact waveGroup_mem_of_dense hQ hd (fun y hy hyQ => (hP y ⟨hy, hyQ⟩ t ht).2) x hx
  exact hK (F.isReducing_of_forall_nonneg (key F.K F.isClosed_K hdense hc.1)
    (key F.Kᗮ (Submodule.isClosed_orthogonal _) hdense' hc.2))

/-- **Residual of a non-reducing constraint**: if `K` does not reduce `L`, then for every
`T > 0` the constraint `Q = K` or the complementary constraint `Q = Kᗮ` has a datum `x ∈ Q`
whose exact solution leaves `Q` at some `t ∈ [0, T]`, and for every family of semi-discrete
solutions with `ξₕ(0) → x` (such families exist, `constrainedFEEC_converges`) the residual
`dist(ξₕ(t), Q)` tends to `dist(e^{tL} x, Q) > 0`. -/
theorem constrainedFEEC_residual_not_isReducing (hK : ¬ H.wave.IsReducing F.K) {T : ℝ}
    (hT : 0 < T) :
    ∃ Q : Submodule 𝕜 (PiLp 2 W), (Q = F.K ∨ Q = F.Kᗮ) ∧ ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
      H.waveGroup.S t x ∉ Q ∧ 0 < infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)) ∧
      ∀ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
        (∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
        Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x) →
        Tendsto (fun h => infDist (H.totalD.graphFst (ξh h t)) (Q : Set (PiLp 2 W))) F.l
          (𝓝 (infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)))) := by
  have hQ : ∀ Q : Submodule 𝕜 (PiLp 2 W), (Q = F.K ∨ Q = F.Kᗮ) →
      IsClosed (Q : Set (PiLp 2 W)) := by
    rintro Q (rfl | rfl)
    exacts [F.isClosed_K, Submodule.isClosed_orthogonal _]
  have conc : ∀ Q : Submodule 𝕜 (PiLp 2 W), (Q = F.K ∨ Q = F.Kᗮ) → ∀ x ∈ Q, ∀ t ∈ Icc 0 T,
      H.waveGroup.S t x ∉ Q → ∃ Q' : Submodule 𝕜 (PiLp 2 W), (Q' = F.K ∨ Q' = F.Kᗮ) ∧
        ∃ x ∈ Q', ∃ t ∈ Icc 0 T,
        H.waveGroup.S t x ∉ Q' ∧ 0 < infDist (H.waveGroup.S t x) (Q' : Set (PiLp 2 W)) ∧
        ∀ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
          (∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
          Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x) →
          Tendsto (fun h => infDist (H.totalD.graphFst (ξh h t)) (Q' : Set (PiLp 2 W))) F.l
            (𝓝 (infDist (H.waveGroup.S t x) (Q' : Set (PiLp 2 W)))) := by
    intro Q hQK x hx t ht hout
    refine ⟨Q, hQK, x, hx, t, ht, hout,
      ((hQ Q hQK).notMem_iff_infDist_pos ⟨0, Q.zero_mem⟩).1 hout, fun ξh ξh' hξh h0 => ?_⟩
    exact F.tendsto_infDist
      ((((constrainedFEEC_converges F T).2 x).1 ξh ξh' hξh h0).tendsto_at ht)
  rcases F.exists_not_mem_of_not_isReducing hK hT with ⟨x, hx, t, ht, hout⟩ | ⟨x, hx, t, ht, hout⟩
  · exact conc F.K (Or.inl rfl) x hx t ht hout
  · exact conc F.Kᗮ (Or.inr rfl) x hx t ht hout

/-- **Residual of a non-reducing constraint on a graded complex** (the literal converse): for a
grading `p`, an `R`-invariant `K` with `D(L) ∩ K` dense in `K` that does not reduce `L`, and every
`T > 0`, there is a datum `ξ₀ ∈ D(L) ∩ K` whose exact solution leaves `K` at some `t ∈ [0, T]`;
the residuals `dist(ξₕ(t), K)` of the discrete solutions with `ξₕ(0) = Pₕ ξ₀` tend to
`dist(e^{tL} ξ₀, K) > 0`, so they stay eventually above `dist(e^{tL} ξ₀, K) / 2`.
[QuennevilleBelair2015], Prop. 4.17 (necessity of the projection hypothesis) -/
theorem constrainedFEEC_residual_not_isReducing_of_grading {p : ι → Bool}
    (hp : ∀ i j, c.Rel i j → p j ≠ p i) (hRK : ∀ x ∈ F.K, reversal 𝕜 p x ∈ F.K)
    (hdense : ∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K))
    (hK : ¬ H.wave.IsReducing F.K) {T : ℝ} (hT : 0 < T) :
    ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc 0 T,
      H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) ∧
      Tendsto (fun h => infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t))
        (F.K : Set (PiLp 2 W))) F.l (𝓝 (infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)))) ∧
      ∀ᶠ h in F.l, infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) / 2 <
        infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t)) (F.K : Set (PiLp 2 W)) := by
  have hex : ∃ x ∈ H.wave.domain, x ∈ F.K ∧ ∃ t ∈ Icc 0 T, H.waveGroup.S t x ∉ F.K := by
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    refine hK ((H.isReducing_iff_forall_nonneg hp F.K hRK hdense).2 fun t ht x hx hxK => ?_)
    have hP := forall_nonneg_of_forall_Icc H hT
      (P := (H.wave.domain : Set (PiLp 2 W)) ∩ F.K)
      fun y hy s hs => ⟨waveGroup_mem_domain H hy.1 s, hc y hy.1 hy.2 s hs⟩
    exact (hP x ⟨hx, hxK⟩ t ht).2
  obtain ⟨x, hx, hxK, t, ht, hout⟩ := hex
  have hpos := (F.isClosed_K.notMem_iff_infDist_pos ⟨0, F.K.zero_mem⟩).1 hout
  have hlim := F.tendsto_infDist (Q := (F.K : Set (PiLp 2 W)))
    (((constrainedFEEC_converges F T).1 ⟨x, hx⟩).tendsto_at ht)
  exact ⟨⟨x, hx⟩, hxK, t, ht, hout, hpos, hlim, (tendsto_order.1 hlim).1 _ (half_lt_self hpos)⟩

/-! ### The discrete Poincaré inequality -/

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- **The uniform discrete Poincaré inequality** given by the uniformly bounded cochain
projections: if `‖z‖ ≤ c_P ‖d z‖` on `(𝔷ⁱ)ᗮ ∩ D(d i j)`, there is `C ≥ 0` with
`‖x‖ ≤ C c_P ‖d x‖` for every `h` and every `x ∈ Vₕⁱ` orthogonal to the discrete cycles.
[AFW2010], Thm 3.6; [Arnold2018], Thm 5.3 -/
theorem constrainedFEEC_discretePoincare {i j : ι} (hij : c.Rel i j) {cP : ℝ}
    (hP : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖) :
    ∃ C, 0 ≤ C ∧ ∀ h, ∀ x (hx : x ∈ (F.V h).V i), (∀ y ∈ (F.V h).cyclesW i, ⟪y, x⟫_𝕜 = 0) →
      ‖x‖ ≤ C * cP * ‖H.d i j ⟨x, (F.V h).le_domain i j hx⟩‖ := by
  obtain ⟨C, hC⟩ := F.bound_π
  refine ⟨max C 0, le_max_right _ _, fun h x hx hxo => ?_⟩
  exact (F.π h).norm_le_of_forall_inner_eq_zero hij hP (le_max_right _ _)
    (fun y => (hC h i y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
    hx hxo

/-! ### The constrained FEEC theorem -/

/-- **The constrained FEEC theorem.** For a constrained FEEC discretization `F` (a Hilbert complex
on any finite window, a closed constraint `K`, finite-dimensional subcomplexes `Vₕ` with uniformly
bounded commuting cochain projections and the approximation property) of the Hodge wave equation
`ξ' = L ξ`:

1. (**well-posedness**, Stone) for `ξ₀ ∈ D(L)`, `t ↦ e^{tL} ξ₀` is a classical solution on
   `[0, T]`, the only strong and the only weak solution, and conserves energy;
2. (**propagation**) the solutions of all data in `K` stay in `K` iff `K` reduces `L`;
3. (**convergence**) the semi-discrete solutions `ξₕ` with `ξₕ(0) = Pₕ ξ₀` converge to
   `e^{tL} ξ₀` uniformly on `[0, T]` for `ξ₀ ∈ D(L)` (and for `ξ₀ ∈ W` whenever `ξₕ(0) → ξ₀`), at
   the rate `(1 + C_P) (1 + t)² C hᵅ ‖ξ₀‖_class` for data in every rate class;
4. (**constraint residual**) if `K` reduces `L`, then for `ξ₀ ∈ D(L) ∩ K`,
   `dist(ξₕ(t), K) ≤ ‖e^{tL} ξ₀ - ξₕ(t)‖ → 0` uniformly on `[0, T]`; if `K` does not reduce `L`,
   then for every `T > 0` some datum of `K` (or of `Kᗮ`) leaves the constraint at some
   `t ∈ [0, T]`, and the residuals of every convergent discretization tend to a positive limit.

[QuennevilleBelair2015], Thms 4.6, 4.7, 4.14, Prop. 4.17; [AFW2010], §3.3; [Arnold2018], Ch. 5 -/
theorem constrainedFEEC :
    -- 1. well-posedness
    (∀ x ∈ H.wave.domain, ∀ T : ℝ,
      Evolution.IsClassicalSolution H.wave (Icc 0 T) 0 (fun t => H.waveGroup.S t x) ∧
      (∀ U, U 0 = x → Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U →
        EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
      (∀ U, U 0 = x → HodgeWave.IsWeakSolution H (Icc 0 T) 0 U →
        EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
      ∀ t, ‖H.waveGroup.S t x‖ = ‖x‖) ∧
    -- 2. constraint propagation
    (H.wave.IsReducing F.K ↔ ∀ t, ∀ x ∈ F.K, H.waveGroup.S t x ∈ F.K) ∧
    -- 3. convergence, with rates
    (∀ T : ℝ, (∀ x : H.wave.domain, TendstoUniformlyOn
        (fun h t => H.totalD.graphFst (F.discrete h (waveLift H x) t))
        (fun t => H.waveGroup.S t x) F.l (Icc 0 T)) ∧
      ∀ x : PiLp 2 W, ∀ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
        (∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
        Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x) →
        TendstoUniformlyOn (fun h t => H.totalD.graphFst (ξh h t))
          (fun t => H.waveGroup.S t x) F.l (Icc 0 T)) ∧
    (∀ (R : F.RateClass) (x : PiLp 2 W) (hxR : x ∈ R.Data) (h : κ) (t : ℝ), 0 ≤ t →
      ‖H.waveGroup.S t x -
          H.totalD.graphFst (F.discrete h (waveLift H ⟨x, R.mem_domain x hxR⟩) t)‖ ≤
        (1 + ellipticConst H) * (1 + t) ^ 2 * (R.C * R.meshSize h ^ R.α * R.classNorm x)) ∧
    -- 4. the constraint residual
    (H.wave.IsReducing F.K → ∀ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K → ∀ T : ℝ,
      (∀ h t, infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t))
          (F.K : Set (PiLp 2 W)) ≤
        ‖H.waveGroup.S t x - H.totalD.graphFst (F.discrete h (waveLift H x) t)‖) ∧
      TendstoUniformlyOn
        (fun h t => infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t))
          (F.K : Set (PiLp 2 W))) (fun _ => 0) F.l (Icc 0 T)) ∧
    (¬ H.wave.IsReducing F.K → ∀ T : ℝ, 0 < T →
      ∃ Q : Submodule 𝕜 (PiLp 2 W), (Q = F.K ∨ Q = F.Kᗮ) ∧ ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
        H.waveGroup.S t x ∉ Q ∧ 0 < infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)) ∧
        ∀ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
          (∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
          Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x) →
          Tendsto (fun h => infDist (H.totalD.graphFst (ξh h t)) (Q : Set (PiLp 2 W))) F.l
            (𝓝 (infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W))))) :=
  ⟨fun _ hx T => constrainedFEEC_wellPosed hx T, constrainedFEEC_propagates_iff F,
    fun T => ⟨(constrainedFEEC_converges F T).1, fun x => ((constrainedFEEC_converges F T).2 x).1⟩,
    fun R _ hxR h _ ht => constrainedFEEC_rate F R hxR h ht,
    fun hK x hxK T => constrainedFEEC_residual F hK x hxK T,
    fun hK _ hT => constrainedFEEC_residual_not_isReducing F hK hT⟩

end Main

/-! ### Non-vacuity -/

namespace ConstrainedFEEC

open ShortHilbertComplex

variable (𝕜) in
/-- The short complex `𝕜 --id--> 𝕜 → 0`. -/
def idShort : ShortHilbertComplex 𝕜 𝕜 𝕜 PUnit :=
  ShortHilbertComplex.ofOp (((ContinuousLinearMap.id 𝕜 𝕜 : 𝕜 →L[𝕜] 𝕜) : 𝕜 →ₗ[𝕜] 𝕜).toPMap ⊤)
    (by simp [dense_univ]) (ContinuousLinearMap.id 𝕜 𝕜).isClosed_toPMap_top

variable (𝕜) in
/-- The complex `𝕜 --id--> 𝕜 → 0` on the window `Fin 3`. -/
abbrev idComplex : HilbertComplex 𝕜 ComplexShape.fin3 (W3 𝕜 𝕜 PUnit) :=
  (idShort 𝕜).toHilbertComplex

theorem idComplex_domain (i j : Fin 3) : ((idComplex 𝕜).d i j).domain = ⊤ := by
  fin_cases i <;> fin_cases j <;> rfl

/-- `D(L)` is the whole space for `𝕜 --id--> 𝕜 → 0`. -/
theorem mem_idComplex_wave_domain (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    x ∈ (idComplex 𝕜).wave.domain := by
  refine (idShort 𝕜).mem_wave_domain.2 ⟨trivial, trivial, ?_, ?_⟩
  · change (x 1 : 𝕜) ∈ ((((ContinuousLinearMap.id 𝕜 𝕜 : 𝕜 →L[𝕜] 𝕜) : 𝕜 →ₗ[𝕜] 𝕜).toPMap ⊤)†).domain
    rw [ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense _ (by simp [dense_univ])]
    trivial
  · rw [show (idShort 𝕜).d₁ = 0 from rfl, LinearPMap.adjoint_zero]
    trivial

instance instFiniteDimensionalW3 : ∀ i, FiniteDimensional 𝕜 (W3 𝕜 𝕜 PUnit i)
  | 0 => inferInstanceAs (FiniteDimensional 𝕜 𝕜)
  | 1 => inferInstanceAs (FiniteDimensional 𝕜 𝕜)
  | 2 => inferInstanceAs (FiniteDimensional 𝕜 PUnit)

variable (𝕜) in
/-- The whole complex as a (trivially conforming) subcomplex. -/
def topSub : (idComplex 𝕜).Subcomplex where
  V _ := ⊤
  le_domain i j := (idComplex_domain i j).ge
  mapsTo _ _ _ _ := Submodule.mem_top

variable (𝕜) in
/-- The identity cochain projection onto `topSub`. -/
def topProj : (topSub 𝕜).CochainProjection where
  π _ := LinearMap.id
  mem _ _ := Submodule.mem_top
  proj _ _ _ := rfl
  comm _ _ _ := rfl

variable (𝕜) in
/-- The constrained FEEC discretization of `𝕜 --id--> 𝕜 → 0` with `Vₕ = W`, `πₕ = id`, and a
closed constraint `K`. -/
def idFEEC (K : Submodule 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit)))
    (hK : _root_.IsClosed (K : Set (PiLp 2 (W3 𝕜 𝕜 PUnit)))) :
    ConstrainedFEEC (idComplex 𝕜) ℕ where
  K := K
  isClosed_K := hK
  l := atTop
  V _ := topSub 𝕜
  π _ := topProj 𝕜
  bound_π := ⟨1, fun _ _ x => by simp [topProj]⟩
  dense ζ δ hδ := Eventually.of_forall fun _ =>
    ⟨ζ, fun _ => Submodule.mem_top, by simpa using hδ⟩

variable (𝕜) in
/-- The constraint `𝕜 × 0 × 0`. -/
abbrev firstSub : Submodule 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit)) :=
  totalSub (family3 (⊤ : Submodule 𝕜 𝕜) (⊥ : Submodule 𝕜 𝕜) (⊥ : Submodule 𝕜 PUnit))

variable (𝕜) in
/-- The datum `(1, 0, 0)`. -/
def firstDatum : PiLp 2 (W3 𝕜 𝕜 PUnit) :=
  WithLp.toLp 2 fun i => match i with
    | 0 => (1 : 𝕜)
    | 1 => (0 : 𝕜)
    | 2 => PUnit.unit

theorem firstDatum_mem : firstDatum 𝕜 ∈ firstSub 𝕜 :=
  mem_totalSub_family3.2 ⟨Submodule.mem_top (R := 𝕜) (M := 𝕜),
    (Submodule.mem_bot (M := 𝕜) 𝕜).2 rfl, (Submodule.mem_bot (M := PUnit) 𝕜).2 rfl⟩

/-- `𝕜 × 0 × 0` does not reduce the wave operator of `𝕜 --id--> 𝕜 → 0`: `L (1, 0, 0)` has
first component `1`. -/
theorem not_isReducing_firstSub : ¬ (idComplex 𝕜).wave.IsReducing (firstSub 𝕜) := by
  intro h
  have hm := (((idComplex 𝕜).isSkewAdjoint_wave.isReducing_iff).1 h).2
    ⟨firstDatum 𝕜, mem_idComplex_wave_domain _⟩ firstDatum_mem
  have h1 : ((idComplex 𝕜).wave ⟨firstDatum 𝕜, mem_idComplex_wave_domain _⟩ : PiLp 2 _) 1 =
      (0 : 𝕜) := (Submodule.mem_bot (M := 𝕜) 𝕜).1 (mem_totalSub_family3.1 hm).2.1
  have e := (idShort 𝕜).wave_apply_one ⟨firstDatum 𝕜, mem_idComplex_wave_domain _⟩
  have e2 : (idShort 𝕜).d₁† ⟨(firstDatum 𝕜 : PiLp 2 (W3 𝕜 𝕜 PUnit)) 2,
      (mem_idComplex_wave_domain (firstDatum 𝕜)).2 2 1⟩ = 0 :=
    LinearPMap.adjoint_apply_eq_zero_of_eq_zero rfl _
  rw [e2, sub_zero] at e
  have e1 : (idShort 𝕜).d₀ ⟨(firstDatum 𝕜 : PiLp 2 (W3 𝕜 𝕜 PUnit)) 0,
      (mem_idComplex_wave_domain (firstDatum 𝕜)).1 0 1⟩ = (1 : 𝕜) := rfl
  rw [e1] at e
  have : (1 : 𝕜) = 0 := e.symm.trans h1
  exact one_ne_zero this

theorem idRate_bound (N : ℕ) (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) {v : (idComplex 𝕜).totalD.GraphSpace} :
    ‖v - v‖ ≤ 1 * (1 / ((N : ℝ) + 1)) ^ (1 : ℝ) * ‖x‖ := by
  rw [sub_self, norm_zero]; positivity

/-- A rate class of `idFEEC 𝕜 (firstSub 𝕜)`: all of `W` (here `D(L²) = W`), with `h = 1/(N+1)`,
`α = 1`, `C = 1` and `‖x‖_class = ‖x‖` (the discretization is exact). -/
def idRate : (idFEEC 𝕜 (firstSub 𝕜) isClosed_totalSub).RateClass where
  Data := univ
  classNorm := norm
  meshSize N := 1 / ((N : ℝ) + 1)
  α := 1
  C := 1
  mem_domain x _ := mem_idComplex_wave_domain x
  mem_domain_sq _ _ _ := mem_idComplex_wave_domain _
  approx x _ N _ _ v _ := ⟨v, fun _ => Submodule.mem_top, idRate_bound N x⟩
  approx_deriv x _ _ N _ _ v _ := ⟨v, fun _ => Submodule.mem_top, idRate_bound N x⟩

/-- **Non-vacuity of the constrained FEEC theorem**: on `𝕜 --id--> 𝕜 → 0` with `Vₕ = W` and
`πₕ = id` (all hypotheses of `ConstrainedFEEC` hold), both branches of item 4 occur. The constraint
`K = W` reduces `L`; the constraint `K = 𝕜 × 0 × 0` is closed, invariant under the grading, with
`D(L) ∩ K = K`, and does not reduce `L`; so for every `T > 0` some datum of `D(L) ∩ K` leaves `K`
at some `t ∈ [0, T]` and the discrete residuals tend to a positive limit. A rate class with
`α = 1`, `h = 1/(N+1)`, contains all of `D(L²) = W`. -/
theorem _root_.Feec.HilbertComplex.constrainedFEEC_nonvacuous :
    (idComplex 𝕜).wave.IsReducing (idFEEC 𝕜 ⊤ (by rw [Submodule.top_coe]; exact isClosed_univ)).K ∧
    ¬ (idComplex 𝕜).wave.IsReducing (idFEEC 𝕜 (firstSub 𝕜) isClosed_totalSub).K ∧
    (∀ T : ℝ, 0 < T → ∃ x : (idComplex 𝕜).wave.domain, (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) ∈ firstSub 𝕜 ∧
      ∃ t ∈ Icc 0 T, (idComplex 𝕜).waveGroup.S t x ∉ firstSub 𝕜 ∧
        0 < infDist ((idComplex 𝕜).waveGroup.S t x) (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit))) ∧
        Tendsto (fun N => infDist ((idComplex 𝕜).totalD.graphFst
            ((idFEEC 𝕜 (firstSub 𝕜) isClosed_totalSub).discrete N (waveLift _ x) t))
            (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit)))) atTop
          (𝓝 (infDist ((idComplex 𝕜).waveGroup.S t x)
            (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit)))))) ∧
    ∃ R : (idFEEC 𝕜 (firstSub 𝕜) isClosed_totalSub).RateClass,
      R.Data = univ ∧ R.α = 1 ∧ ∀ N, R.meshSize N = 1 / ((N : ℝ) + 1) := by
  set F := idFEEC 𝕜 (firstSub 𝕜) isClosed_totalSub
  refine ⟨(constrainedFEEC_propagates_iff _).2 fun _ _ _ => Submodule.mem_top,
    not_isReducing_firstSub, fun T hT => ?_, ?_⟩
  · obtain ⟨x, hxK, t, ht, hout, hpos, hlim, -⟩ :=
      constrainedFEEC_residual_not_isReducing_of_grading F
        (p := fun i : Fin 3 => decide (Odd i.val)) fin3_parity
        (fun x hx => reversal_mem_totalSub hx)
        (fun k hk => subset_closure ⟨mem_idComplex_wave_domain k, hk⟩) not_isReducing_firstSub hT
    exact ⟨x, hxK, t, ht, hout, hpos, hlim⟩
  · exact ⟨idRate, rfl, rfl, fun _ => rfl⟩

end ConstrainedFEEC

end Feec.HilbertComplex
