module

public import Feec.Models.Cube.Inhomogeneous
public import Feec.Models.Cube.WhitneyRate
public import Feec.FiniteElement.PolyComplex
public import Feec.TimeStepping.Trajectory

/-!
# `O(h + Δt²)` error of the Crank–Nicolson Whitney scheme with Dirichlet DOFs

The fully discrete scheme of [QuennevilleBelair2015], Ch. 7 (as run by `fem4gr`) is the
Crank–Nicolson step with prescribed boundary DOFs `TimeStepping.IsDirichletCNStep` on the
three-row Whitney space `DState3 (whitneyRow N)` of the level-`(N + 1)` Freudenthal mesh of
`Q = (0, ½)³` (`Feec.Models.Cube.Inhomogeneous`). This module proves its convergence at rate
`O(h_N + Δt²)` for smooth solutions, the same rate for the five `fem4gr` constraint monitors
when the solution is TSD, and `V̊ₕ ≠ 0`.

## The error argument

* **Abstract estimate** (`exists_comparison_consistency`, `norm_cn_error_le`,
  `norm_cn_error_le_of_eq`): for an isometric embedding `emb : Vₕ → X`, a discrete differential `D`
  with `D V̊ₕ ⊆ V̊ₕ`, `D D = 0`, the skew matrix `⟪A x, y⟫ = ⟪D x, y⟫ − ⟪x, D y⟫`, a solution
  `U ∈ C³([0, T]; X)` of the weak form `⟪U', emb v⟫ = ⟪DU, emb v⟫ − ⟪U, emb (D v)⟫` on `V̊ₕ` and
  approximants `wₙ` of `U(tₙ)` with `‖𝐝 (wₙ − U(tₙ))‖ ≤ a` and
  `‖(wₙ₊₁ − U(tₙ₊₁)) − (wₙ − U(tₙ))‖ ≤ a Δt`, the comparison fields `ũₙ = wₙ − q (emb wₙ − U(tₙ))`
  with the **boundary correction** `q = P_{D V̊ₕ}` (the `L²` projection onto the discrete
  boundaries) keep the boundary DOFs of `wₙ`, do not increase the error, and are orthogonal to
  `emb (D V̊ₕ)`, so the adjoint terms `⟪U − ũ, D v⟫` of the consistency error vanish: no inverse
  estimate (which would lose `h⁻¹`) is needed. The canonical interpolant alone gives only
  `|⟪U − Π U, D v⟫| ≤ ‖U − Π U‖ ‖D v‖`, which is `O(1) ‖v‖` after an inverse estimate; the
  correction is a partial elliptic projection that only acts on `D V̊ₕ` (`D q = 0`). With the
  trapezoidal remainder `Feec.TimeStepping.norm_trapezoid_le`, `‖τₙ‖ ≤ Δt (L₃ Δt² / 2 + 2 a)`, hence
  `‖u_M − ũ_M‖ ≤ ‖u₀ − w₀‖ + a + T (L₃ Δt² / 2 + 2 a)`.
* **The setting on a subcomplex** (`dEmb`, `discreteD_mem_interior`, `discreteD_discreteD`,
  `inner_of_mem_graph_waveMax`, three rows: `dEmb3`, `discreteD3`, `inner3_of_mem_graph_waveMax`):
  a strong solution of `U' = L_max U = 𝐝 U − 𝐝_min† U` solves the weak form, since
  `⟪𝐝_min† U, v⟫ = ⟪U, 𝐝_min v⟫` on `V̊ₕ ⊆ D(𝐝_min)`.
* **The linear canonical interpolant** (`FEMInterp.canonicalInterp`, `canonicalInterp_le`): the
  glued Whitney interpolant `glue ∘ globalInterp` as a linear map with the `O(h)` estimates of `FEM.exists_mem_whitney_le`; linearity
  gives the estimate for time differences.
* **Smooth forms** (`formalAdjD`, `complex_d_formL2Q`, `adjoint_complexMin_d_formL2Q`): on `Q`,
  `d` of a smooth form is the classical one, and the adjoint of `d_min` is the formal adjoint
  `dᵗ = −δ` (`(d_min)† = (dᵗ)_max`).

## The concrete statements

* `RowSolution T L`: a smooth solution of one row of (4.14) on `[0, T] × cl Q` (Ch. 7 sign
  convention `σ' = div E`, `E' = grad σ − curl B`, `B' = curl E`, as the forms
  `σ' = −dᵗE`, `E' = dσ − dᵗB`, `B' = dE`): `C²` in space, `C³` in time with jointly continuous
  time derivatives, `‖Du‖, ‖D du‖ ≤ L` on `cl Q`, these `L`-Lipschitz in time (bounded mixed
  derivatives `∂ₜ Du`), and `|∂ₜ³ u| ≤ L`. No boundary condition is imposed: the boundary DOFs
  of the scheme are those of the interpolant of the exact solution.
* **`whitney_cn_error_le`**: for three rows of such a solution, the iterates from `u₀ = Π_h U(0)`
  with the boundary DOFs of `Π_h U(tₙ)` satisfy `‖u_M − ũ_M‖ ≤ C L (1 + T) (h_N + Δt²)` and
  `‖u_M − U(t_M)‖ ≤ C L (1 + T) (h_N + Δt²)` for `M Δt ≤ T`, `C = cnConst` explicit and
  independent of `N`, `Δt`, `T`.
* **`whitney_cn_monitors_le`**: if the solution is TSD at `t_M` (`IsTSDAt`), the monitors
  `½ (E − Eᵀ)`, `½ (B − Bᵀ)`, `tr E / √3`, `tr B / √3` and `σ` of `u_M` are
  `≤ C L (1 + T) (h_N + Δt²)` (they vanish for `U`, `monitors_exactField_eq_zero`).
* **`whitneyInterior3_ne_bot`**: `V̊ₕ ≠ 0` on every mesh (an interior edge function,
  `whitneyMin_one_ne_bot`).
* **Whole-space TSD solutions** (`WholeSpaceTSD.Smooth`, `WholeSpaceTSD.Smooth.row`,
  `WholeSpaceTSD.Smooth.isTSDAt`, `WholeSpaceTSD.Smooth.whitney_cn_error_monitors_le`): every
  whole-space TSD solution with bounded derivatives gives three row solutions
  `(0, Σⱼ E_{rj} dxⱼ, Σⱼ (−1)ʲ B_{rj} dx_{{j}ᶜ})` (`oneForm`, `twoForm`, with
  `d oneForm = twoForm curl`, `dᵗ twoForm = oneForm curl`, `dᵗ oneForm = −div`), TSD at every
  time, so the error and all five monitors are `O(h_N + Δt²)`.
* `cnStep`: the Crank–Nicolson step exists for every data (`whitney_existsUnique_cnStep3`).

What the statements assume is only the smoothness of the exact solution (`RowSolution`,
`WholeSpaceTSD.Smooth`), no theory absent from Mathlib. Not covered: the discrete divergence
monitor (its constant depends on the mesh), rates for data of finite Sobolev regularity.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7 (the Crank–Nicolson runs, the constraint monitors), §4.10 ((4.14))
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (interpolation
  estimates)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open Set Filter MeasureTheory

namespace Feec.Models.Cube.Inhomogeneous

/-! ## The error of the Crank–Nicolson scheme with Dirichlet DOFs, abstractly -/

section Abstract

variable {V X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The **Riesz map** `R : X → V` of a map `emb : V → X` (its adjoint): `⟪R y, x⟫ = ⟪y, emb x⟫`. -/
def rieszMap (emb : V →ₗ[ℝ] X) : X →ₗ[ℝ] V where
  toFun y := (InnerProductSpace.toDual ℝ V).symm
    (LinearMap.toContinuousLinearMap ((innerₛₗ ℝ y).comp emb))
  map_add' y y' := ext_inner_right ℝ fun x => by
    rw [inner_add_left, InnerProductSpace.toDual_symm_apply, InnerProductSpace.toDual_symm_apply,
      InnerProductSpace.toDual_symm_apply]
    simp
  map_smul' c y := ext_inner_right ℝ fun x => by
    rw [RingHom.id_apply, real_inner_smul_left, InnerProductSpace.toDual_symm_apply,
      InnerProductSpace.toDual_symm_apply]
    simp

theorem inner_rieszMap (emb : V →ₗ[ℝ] X) (y : X) (x : V) : ⟪rieszMap emb y, x⟫ = ⟪y, emb x⟫ := by
  change ⟪(InnerProductSpace.toDual ℝ V).symm _, x⟫ = _
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

variable (emb : V →ₗ[ℝ] X) (D : V →ₗ[ℝ] V) (V₀ : Submodule ℝ V)

/-- The **discrete boundaries** `D V̊ₕ` (the range of the discrete differential on the fields with
vanishing boundary DOFs). -/
def bdrySub : Submodule ℝ V := V₀.map D

/-- The **boundary correction** `q y = P_{D V̊ₕ} R y`: the `L²` projection of `y ∈ X` onto the
discrete boundaries `D V̊ₕ`, as an element of `V`. -/
def bdryCorr : X →ₗ[ℝ] V :=
  ((bdrySub D V₀).starProjection : V →ₗ[ℝ] V) ∘ₗ rieszMap emb

variable {emb D V₀}

theorem bdryCorr_mem (y : X) : bdryCorr emb D V₀ y ∈ bdrySub D V₀ := by
  simp only [bdryCorr, LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe]
  exact Submodule.starProjection_apply_mem _ _

omit [FiniteDimensional ℝ V] in
theorem bdrySub_le (hD₀ : ∀ v ∈ V₀, D v ∈ V₀) : bdrySub D V₀ ≤ V₀ := by
  rintro _ ⟨v, hv, rfl⟩
  exact hD₀ v hv

omit [FiniteDimensional ℝ V] in
theorem D_eq_zero_of_mem_bdrySub (hDD : ∀ v ∈ V₀, D (D v) = 0) {b : V} (hb : b ∈ bdrySub D V₀) :
    D b = 0 := by
  obtain ⟨v, hv, rfl⟩ := hb
  exact hDD v hv

theorem inner_bdryCorr (y : X) {b : V} (hb : b ∈ bdrySub D V₀) :
    ⟪bdryCorr emb D V₀ y, b⟫ = ⟪y, emb b⟫ := by
  simp only [bdryCorr, LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe]
  rw [Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.2 hb, inner_rieszMap]

omit [FiniteDimensional ℝ V] in
theorem norm_emb (hemb : ∀ x y, ⟪emb x, emb y⟫ = ⟪x, y⟫) (x : V) : ‖emb x‖ = ‖x‖ := by
  have h := hemb x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- `y − q y ⊥ emb (D V̊ₕ)`. -/
theorem inner_sub_bdryCorr (hemb : ∀ x y, ⟪emb x, emb y⟫ = ⟪x, y⟫) (y : X) {b : V}
    (hb : b ∈ bdrySub D V₀) : ⟪y - emb (bdryCorr emb D V₀ y), emb b⟫ = 0 := by
  rw [inner_sub_left, hemb, inner_bdryCorr y hb, sub_self]

/-- **The correction does not increase the error**: `‖y − emb (q y)‖ ≤ ‖y‖` and `‖q y‖ ≤ ‖y‖`. -/
theorem norm_sub_bdryCorr_le (hemb : ∀ x y, ⟪emb x, emb y⟫ = ⟪x, y⟫) (y : X) :
    ‖y - emb (bdryCorr emb D V₀ y)‖ ≤ ‖y‖ ∧ ‖bdryCorr emb D V₀ y‖ ≤ ‖y‖ := by
  set z := emb (bdryCorr emb D V₀ y)
  have h0 : ⟪y - z, z⟫ = 0 := inner_sub_bdryCorr hemb y (bdryCorr_mem y)
  have hp : ‖y‖ ^ 2 = ‖y - z‖ ^ 2 + ‖z‖ ^ 2 := by
    have := norm_add_sq_real (y - z) z
    rw [sub_add_cancel, h0, mul_zero, add_zero] at this
    exact this
  have hz : ‖z‖ = ‖bdryCorr emb D V₀ y‖ := norm_emb hemb _
  constructor
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    nlinarith [sq_nonneg ‖z‖]
  · rw [← hz]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    nlinarith [sq_nonneg ‖y - z‖]

/-- **Comparison fields and consistency errors of the Dirichlet Crank–Nicolson scheme**, abstractly.
Let `emb : V → X` be an isometric embedding of a finite-dimensional space `V` (the finite element
space `Vₕ`, all DOFs) into an inner product space `X` (`L²`), `D` the discrete differential with
`D V̊ₕ ⊆ V̊ₕ` and `D D = 0` on `V̊ₕ`, and `A` the scheme matrix with
`⟪A x, y⟫ = ⟪D x, y⟫ − ⟪x, D y⟫`. Let `U ∈ C³([0, T]; X)` with `‖U'''‖ ≤ L₃` solve the continuous
system weakly against `V̊ₕ`, `⟪U', emb v⟫ = ⟪DU, emb v⟫ − ⟪U, emb (D v)⟫`, and let `wₙ ∈ Vₕ` be
approximants of `U(tₙ)` (`tₙ = n Δt`) with `‖emb (D wₙ) − DU(tₙ)‖ ≤ a` and
`‖δₙ₊₁ − δₙ‖ ≤ a Δt` for `δₙ = emb wₙ − U(tₙ)` (interpolants of a smooth solution).
Then the comparison fields `ũₙ = wₙ − q δₙ` (`q` the `L²` projection onto `D V̊ₕ`) have the
boundary DOFs of `wₙ`, are no farther from `U(tₙ)` than `wₙ`, satisfy
`⟪U(tₙ) − emb ũₙ, emb (D v)⟫ = 0` for `v ∈ V̊ₕ` (no inverse estimate is needed for the adjoint
terms), and solve the scheme with step `Δt / 2` up to consistency errors `τₙ ∈ V̊ₕ` with
`‖τₙ‖ ≤ Δt (L₃ Δt² / 2 + 2 a)`. -/
theorem exists_comparison_consistency (hemb : ∀ x y, ⟪emb x, emb y⟫ = ⟪x, y⟫)
    (hD₀ : ∀ v ∈ V₀, D v ∈ V₀) (hDD : ∀ v ∈ V₀, D (D v) = 0) {A : V →ₗ[ℝ] V}
    (hA : ∀ x y, ⟪A x, y⟫ = ⟪D x, y⟫ - ⟪x, D y⟫) {Δt T L₃ a : ℝ} (hΔt : 0 < Δt)
    {U U₁ U₂ U₃ DU : ℝ → X}
    (hU₁ : ∀ t ∈ Icc 0 T, HasDerivWithinAt U (U₁ t) (Icc 0 T) t)
    (hU₂ : ∀ t ∈ Icc 0 T, HasDerivWithinAt U₁ (U₂ t) (Icc 0 T) t)
    (hU₃ : ∀ t ∈ Icc 0 T, HasDerivWithinAt U₂ (U₃ t) (Icc 0 T) t)
    (hL₃ : ∀ t ∈ Icc 0 T, ‖U₃ t‖ ≤ L₃)
    (hweak : ∀ t ∈ Icc 0 T, ∀ v ∈ V₀, ⟪U₁ t, emb v⟫ = ⟪DU t, emb v⟫ - ⟪U t, emb (D v)⟫)
    {w : ℕ → V}
    (hA2 : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖emb (D (w n)) - DU (n * Δt)‖ ≤ a)
    (hA3 : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * Δt ≤ T →
      ‖(emb (w (n + 1)) - U ((n + 1 : ℕ) * Δt)) - (emb (w n) - U (n * Δt))‖ ≤ a * Δt) :
    ∃ ũ τ : ℕ → V, (∀ n, ũ n - w n ∈ V₀) ∧
      (∀ n : ℕ, ‖ũ n - w n‖ ≤ ‖emb (w n) - U (n * Δt)‖) ∧
      (∀ n : ℕ, ‖emb (ũ n) - U (n * Δt)‖ ≤ ‖emb (w n) - U (n * Δt)‖) ∧
      (∀ n : ℕ, ∀ v ∈ V₀, ⟪U (n * Δt) - emb (ũ n), emb (D v)⟫ = 0) ∧
      (∀ n, ∀ v ∈ V₀, ⟪ũ (n + 1) - ũ n, v⟫ =
        Δt / 2 * ⟪A (ũ (n + 1) + ũ n), v⟫ + ⟪(0 : V), v⟫ + ⟪τ n, v⟫) ∧
      (∀ n, τ n ∈ V₀) ∧
      (∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * Δt ≤ T → ‖τ n‖ ≤ Δt * (L₃ * Δt ^ 2 / 2 + 2 * a)) := by
  set δ : ℕ → X := fun n => emb (w n) - U (n * Δt)
  set ũ : ℕ → V := fun n => w n - bdryCorr emb D V₀ (δ n)
  set τ : ℕ → V := fun n =>
    V₀.starProjection (ũ (n + 1) - ũ n - (Δt / 2) • A (ũ (n + 1) + ũ n))
  have hqV₀ : ∀ y, bdryCorr emb D V₀ y ∈ V₀ := fun y => bdrySub_le hD₀ (bdryCorr_mem y)
  have hDũ : ∀ n, D (ũ n) = D (w n) := fun n => by
    simp only [ũ, map_sub, D_eq_zero_of_mem_bdrySub hDD (bdryCorr_mem _), sub_zero]
  have hρ : ∀ n : ℕ, emb (ũ n) - U (n * Δt) = δ n - emb (bdryCorr emb D V₀ (δ n)) := fun n => by
    simp only [ũ, δ, map_sub]; abel
  have horth : ∀ n : ℕ, ∀ v ∈ V₀, ⟪U (n * Δt) - emb (ũ n), emb (D v)⟫ = 0 := fun n v hv => by
    have h := inner_sub_bdryCorr (D := D) (V₀ := V₀) hemb (δ n) (Submodule.mem_map_of_mem hv)
    rw [← neg_sub, inner_neg_left, hρ, h, neg_zero]
  refine ⟨ũ, τ, fun n => ?_, fun n => ?_, fun n => ?_, horth, fun n v hv => ?_,
    fun n => Submodule.starProjection_apply_mem _ _, fun n hn => ?_⟩
  · simp only [ũ, sub_sub_cancel_left]
    exact V₀.neg_mem (hqV₀ _)
  · simp only [ũ, sub_sub_cancel_left, norm_neg]
    exact (norm_sub_bdryCorr_le hemb (δ n)).2
  · rw [hρ]; exact (norm_sub_bdryCorr_le hemb (δ n)).1
  · have e : ⟪τ n, v⟫ = ⟪ũ (n + 1) - ũ n - (Δt / 2) • A (ũ (n + 1) + ũ n), v⟫ := by
      simp only [τ]
      rw [Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 hv]
    rw [e]
    simp only [inner_sub_left, real_inner_smul_left, inner_zero_left]
    ring
  -- the bound on `τₙ`
  set ε := Δt * (L₃ * Δt ^ 2 / 2 + 2 * a)
  have hn0 : (0 : ℝ) ≤ n * Δt := mul_nonneg (Nat.cast_nonneg n) hΔt.le
  have hn1 : (n : ℝ) * Δt ≤ ((n + 1 : ℕ) : ℝ) * Δt := by push_cast; nlinarith
  have hnT : (n : ℝ) * Δt ≤ T := hn1.trans hn
  have htn : (n : ℝ) * Δt ∈ Icc 0 T := ⟨hn0, hnT⟩
  have htn' : ((n + 1 : ℕ) : ℝ) * Δt ∈ Icc 0 T := ⟨hn0.trans hn1, hn⟩
  have hsub : Icc ((n : ℝ) * Δt) (((n + 1 : ℕ) : ℝ) * Δt) ⊆ Icc 0 T :=
    Icc_subset_Icc hn0 hn
  have hc : ∀ {g g' : ℝ → X}, (∀ t ∈ Icc 0 T, HasDerivWithinAt g (g' t) (Icc 0 T) t) →
      ContinuousOn g (Icc ((n : ℝ) * Δt) (((n + 1 : ℕ) : ℝ) * Δt)) :=
    fun hg t ht => (hg t (hsub ht)).continuousWithinAt.mono hsub
  have hr : ∀ {g g' : ℝ → X}, (∀ t ∈ Icc 0 T, HasDerivWithinAt g (g' t) (Icc 0 T) t) →
      ∀ t ∈ Ico ((n : ℝ) * Δt) (((n + 1 : ℕ) : ℝ) * Δt), HasDerivWithinAt g (g' t) (Ici t) t :=
    fun hg t ht => (hg t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE (ht.2.trans_le hn)) (Icc_subset_Icc_left (hn0.trans ht.1)))
  have hTay : ‖U (((n + 1 : ℕ) : ℝ) * Δt) - U (n * Δt) -
      ((((n + 1 : ℕ) : ℝ) * Δt - n * Δt) / 2) • (U₁ (((n + 1 : ℕ) : ℝ) * Δt) + U₁ (n * Δt))‖ ≤
      L₃ * (((n + 1 : ℕ) : ℝ) * Δt - n * Δt) ^ 3 / 2 := by
    refine (TimeStepping.norm_trapezoid_le hn1 (hc hU₁) (hc hU₂) (hc hU₃) (hr hU₁) (hr hU₂)
      (hr hU₃) fun t ht => hL₃ t (hsub (Ico_subset_Icc_self ht))).trans ?_
    have := pow_nonneg (sub_nonneg.2 hn1) 3
    nlinarith [(norm_nonneg _).trans (hL₃ _ htn)]
  have hdt : ((n + 1 : ℕ) : ℝ) * Δt - n * Δt = Δt := by push_cast; ring
  rw [hdt] at hTay
  -- the key bound: `⟪z, v⟫ ≤ ε ‖v‖` on `V̊ₕ`
  have key : ∀ v ∈ V₀, ⟪ũ (n + 1) - ũ n - (Δt / 2) • A (ũ (n + 1) + ũ n), v⟫ ≤ ε * ‖v‖ := by
    intro v hv
    set Tn := U (((n + 1 : ℕ) : ℝ) * Δt) - U (n * Δt) -
      (Δt / 2) • (U₁ (((n + 1 : ℕ) : ℝ) * Δt) + U₁ (n * Δt))
    set ρ : ℕ → X := fun k => δ k - emb (bdryCorr emb D V₀ (δ k))
    set e : ℕ → X := fun k => emb (D (w k)) - DU (k * Δt)
    have hρ1 : ρ (n + 1) - ρ n =
        (δ (n + 1) - δ n) - emb (bdryCorr emb D V₀ (δ (n + 1) - δ n)) := by
      simp only [ρ, map_sub]; abel
    have hρb : ‖ρ (n + 1) - ρ n‖ ≤ a * Δt := by
      rw [hρ1]
      exact (norm_sub_bdryCorr_le hemb _).1.trans (hA3 n hn)
    have hw1 := hweak _ htn' v hv
    have hw0 := hweak _ htn v hv
    have o1 := horth (n + 1) v hv
    have o0 := horth n v hv
    have hA' := hA (ũ (n + 1) + ũ n) v
    have i1 : ⟪ũ (n + 1) - ũ n, v⟫ = ⟪emb (ũ (n + 1)) - emb (ũ n), emb v⟫ := by
      rw [← hemb, map_sub]
    have i2 : ⟪D (ũ (n + 1) + ũ n), v⟫ = ⟪emb (D (w (n + 1))) + emb (D (w n)), emb v⟫ := by
      rw [map_add, hDũ, hDũ, ← hemb, map_add]
    have i3 : ⟪ũ (n + 1) + ũ n, D v⟫ = ⟪emb (ũ (n + 1)) + emb (ũ n), emb (D v)⟫ := by
      rw [← hemb, map_add]
    have hu1 : emb (ũ (n + 1)) = U (((n + 1 : ℕ) : ℝ) * Δt) + ρ (n + 1) := by
      simp only [ρ]; rw [← hρ (n + 1)]; abel
    have hu0 : emb (ũ n) = U (n * Δt) + ρ n := by simp only [ρ]; rw [← hρ n]; abel
    have hid : ⟪ũ (n + 1) - ũ n - (Δt / 2) • A (ũ (n + 1) + ũ n), v⟫ =
        ⟪Tn, emb v⟫ + ⟪ρ (n + 1) - ρ n, emb v⟫ - Δt / 2 * ⟪e (n + 1) + e n, emb v⟫ := by
      rw [inner_sub_left, real_inner_smul_left, hA', i1, i2, i3]
      simp only [inner_sub_left, hu1, hu0, inner_add_left] at o1 o0
      have r1 : ⟪ρ (n + 1), emb (D v)⟫ = 0 := by linarith
      have r0 : ⟪ρ n, emb (D v)⟫ = 0 := by linarith
      simp only [Tn, e, inner_sub_left, inner_add_left, real_inner_smul_left, hw1, hw0, hu1, hu0,
        r1, r0]
      ring
    rw [hid]
    have hy : ‖emb v‖ = ‖v‖ := norm_emb hemb v
    have b1 : ⟪Tn, emb v⟫ ≤ L₃ * Δt ^ 3 / 2 * ‖v‖ := by
      rw [← hy]
      exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hTay (norm_nonneg _))
    have b2 : ⟪ρ (n + 1) - ρ n, emb v⟫ ≤ a * Δt * ‖v‖ := by
      rw [← hy]
      exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hρb (norm_nonneg _))
    have he : ‖e (n + 1) + e n‖ ≤ 2 * a := by
      have h1 := hA2 (n + 1) (by exact_mod_cast hn)
      have h0 := hA2 n hnT
      exact (norm_add_le _ _).trans (by simp only [e]; push_cast at h1 ⊢; linarith)
    have b3 : -(Δt / 2 * ⟪e (n + 1) + e n, emb v⟫) ≤ Δt / 2 * (2 * a) * ‖v‖ := by
      have h1 := abs_real_inner_le_norm (e (n + 1) + e n) (emb v)
      have h2 := neg_abs_le ⟪e (n + 1) + e n, emb v⟫
      have h3 : ‖e (n + 1) + e n‖ * ‖emb v‖ ≤ 2 * a * ‖emb v‖ :=
        mul_le_mul_of_nonneg_right he (norm_nonneg _)
      rw [hy] at h3 h1
      have : 0 ≤ Δt / 2 := by linarith
      nlinarith
    have : ε * ‖v‖ = L₃ * Δt ^ 3 / 2 * ‖v‖ + a * Δt * ‖v‖ + Δt / 2 * (2 * a) * ‖v‖ := by
      simp only [ε]; ring
    linarith
  have hτmem : τ n ∈ V₀ := Submodule.starProjection_apply_mem _ _
  have hττ : ‖τ n‖ ^ 2 =
      ⟪ũ (n + 1) - ũ n - (Δt / 2) • A (ũ (n + 1) + ũ n), τ n⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => rw [show τ n = V₀.starProjection
      (ũ (n + 1) - ũ n - (Δt / 2) • A (ũ (n + 1) + ũ n)) from rfl]
    rw [Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 hτmem]
  have hk := key _ hτmem
  rw [← hττ] at hk
  rcases (norm_nonneg (τ n)).eq_or_lt with h0 | hpos
  · rw [← h0]
    have : 0 ≤ L₃ := (norm_nonneg _).trans (hL₃ _ htn)
    have ha : 0 ≤ a := (norm_nonneg _).trans (hA2 n hnT)
    positivity
  · nlinarith

/-- **Error of the Dirichlet Crank–Nicolson scheme**, abstractly: in the setting of
`exists_comparison_consistency`, if `uₙ` are the iterates of the scheme with step `Δt / 2`
(`s = Δt / 2`), no load, boundary DOFs `gₙ₊₁` those of `wₙ₊₁` (`gₙ₊₁ − wₙ₊₁ ∈ V̊ₕ`) and initial
value with the boundary DOFs of `w₀`, and `‖emb wₙ − U(tₙ)‖ ≤ a`, then for `M Δt ≤ T` there are
comparison fields `ũₙ` with the boundary DOFs of `wₙ` and `‖emb ũₙ − U(tₙ)‖ ≤ a` such that
`‖u_M − ũ_M‖ ≤ ‖u₀ − w₀‖ + a + T (L₃ Δt² / 2 + 2 a)` and
`‖emb u_M − U(t_M)‖ ≤ ‖u₀ − w₀‖ + 2 a + T (L₃ Δt² / 2 + 2 a)`. -/
theorem norm_cn_error_le (hemb : ∀ x y, ⟪emb x, emb y⟫ = ⟪x, y⟫)
    (hD₀ : ∀ v ∈ V₀, D v ∈ V₀) (hDD : ∀ v ∈ V₀, D (D v) = 0) {A : V →ₗ[ℝ] V}
    (hA : ∀ x y, ⟪A x, y⟫ = ⟪D x, y⟫ - ⟪x, D y⟫) {Δt T L₃ a : ℝ} (hΔt : 0 < Δt)
    {U U₁ U₂ U₃ DU : ℝ → X}
    (hU₁ : ∀ t ∈ Icc 0 T, HasDerivWithinAt U (U₁ t) (Icc 0 T) t)
    (hU₂ : ∀ t ∈ Icc 0 T, HasDerivWithinAt U₁ (U₂ t) (Icc 0 T) t)
    (hU₃ : ∀ t ∈ Icc 0 T, HasDerivWithinAt U₂ (U₃ t) (Icc 0 T) t)
    (hL₃ : ∀ t ∈ Icc 0 T, ‖U₃ t‖ ≤ L₃)
    (hweak : ∀ t ∈ Icc 0 T, ∀ v ∈ V₀, ⟪U₁ t, emb v⟫ = ⟪DU t, emb v⟫ - ⟪U t, emb (D v)⟫)
    {w : ℕ → V}
    (hA1 : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖emb (w n) - U (n * Δt)‖ ≤ a)
    (hA2 : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖emb (D (w n)) - DU (n * Δt)‖ ≤ a)
    (hA3 : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * Δt ≤ T →
      ‖(emb (w (n + 1)) - U ((n + 1 : ℕ) * Δt)) - (emb (w n) - U (n * Δt))‖ ≤ a * Δt)
    {M : ℕ} (hM : (M : ℝ) * Δt ≤ T) {u g : ℕ → V}
    (hstep : ∀ n < M, TimeStepping.IsDirichletCNStep V₀ A (Δt / 2) 0 (g (n + 1)) (u n)
      (u (n + 1)))
    (hg : ∀ n < M, g (n + 1) - w (n + 1) ∈ V₀) (hu0 : u 0 - w 0 ∈ V₀) :
    ∃ ũ : ℕ → V, (∀ n, ũ n - w n ∈ V₀) ∧
      (∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖emb (ũ n) - U (n * Δt)‖ ≤ a) ∧
      ‖u M - ũ M‖ ≤ ‖u 0 - w 0‖ + a + T * (L₃ * Δt ^ 2 / 2 + 2 * a) ∧
      ‖emb (u M) - U (M * Δt)‖ ≤ ‖u 0 - w 0‖ + 2 * a + T * (L₃ * Δt ^ 2 / 2 + 2 * a) := by
  obtain ⟨ũ, τ, hũw, hũn, hũe, -, hτ, -, hτb⟩ :=
    exists_comparison_consistency hemb hD₀ hDD hA hΔt hU₁ hU₂ hU₃ hL₃ hweak hA2 hA3
  have hT0 : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg M) hΔt.le).trans hM
  have hL0 : 0 ≤ L₃ := (norm_nonneg _).trans (hL₃ 0 ⟨le_rfl, hT0⟩)
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (hA1 0 (by simpa using hT0))
  have hAs : ∀ x ∈ V₀, Δt / 2 * ⟪A x, x⟫ ≤ 0 := fun x _ => by
    rw [hA, real_inner_comm x, sub_self, mul_zero]
  set c := L₃ * Δt ^ 2 / 2 + 2 * a
  have hc : 0 ≤ c := by positivity
  have hind : ∀ m ≤ M, u m - ũ m ∈ V₀ ∧
      ‖u m - ũ m‖ ≤ ‖u 0 - ũ 0‖ + ∑ n ∈ Finset.range m, ‖τ n‖ := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨?_, by simp⟩
      have := V₀.sub_mem hu0 (hũw 0)
      rwa [sub_sub_sub_cancel_right] at this
    | succ m ih =>
      intro hm
      obtain ⟨hmem, hle⟩ := ih (by omega)
      have hst := hstep m (by omega)
      have hũg : ũ (m + 1) - g (m + 1) ∈ V₀ := by
        have := V₀.sub_mem (hũw (m + 1)) (hg m (by omega))
        rwa [sub_sub_sub_cancel_right] at this
      refine ⟨?_, ?_⟩
      · have := V₀.sub_mem hst.1 hũg
        rwa [sub_sub_sub_cancel_right] at this
      · have h1 := TimeStepping.IsDirichletCNStep.norm_sub_le hAs hst hũg hmem (hτ m)
        rw [Finset.sum_range_succ]
        linarith
  obtain ⟨-, hM'⟩ := hind M le_rfl
  have hsum : ∑ n ∈ Finset.range M, ‖τ n‖ ≤ T * c := by
    calc ∑ n ∈ Finset.range M, ‖τ n‖ ≤ ∑ _n ∈ Finset.range M, Δt * c :=
          Finset.sum_le_sum fun n hn => hτb n (by
            have : n + 1 ≤ M := Finset.mem_range.1 hn
            exact (mul_le_mul_of_nonneg_right (by exact_mod_cast this) hΔt.le).trans hM)
      _ = M * Δt * c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ T * c := mul_le_mul_of_nonneg_right hM hc
  have h0 : ‖u 0 - ũ 0‖ ≤ ‖u 0 - w 0‖ + a := by
    have e : u 0 - ũ 0 = (u 0 - w 0) - (ũ 0 - w 0) := by abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have := (hũn 0).trans (hA1 0 (by simpa using hT0))
    linarith
  have hfin : ‖u M - ũ M‖ ≤ ‖u 0 - w 0‖ + a + T * c := by linarith
  refine ⟨ũ, hũw, fun n hn => (hũe n).trans (hA1 n hn), hfin, ?_⟩
  have e : emb (u M) - U (M * Δt) = emb (u M - ũ M) + (emb (ũ M) - U (M * Δt)) := by
    rw [map_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_emb hemb]
  have := (hũe M).trans (hA1 M hM)
  linarith

/-- `norm_cn_error_le` started from `u₀ = w₀`, in the form `K (1 + T) (h + Δt²)`: if `2 a ≤ K h`
and `L₃ / 2 ≤ K`, then `‖u_M − ũ_M‖, ‖emb u_M − U(t_M)‖ ≤ K (1 + T) (h + Δt²)`. -/
theorem norm_cn_error_le_of_eq (hemb : ∀ x y, ⟪emb x, emb y⟫ = ⟪x, y⟫)
    (hD₀ : ∀ v ∈ V₀, D v ∈ V₀) (hDD : ∀ v ∈ V₀, D (D v) = 0) {A : V →ₗ[ℝ] V}
    (hA : ∀ x y, ⟪A x, y⟫ = ⟪D x, y⟫ - ⟪x, D y⟫) {Δt T L₃ a : ℝ} (hΔt : 0 < Δt)
    {U U₁ U₂ U₃ DU : ℝ → X}
    (hU₁ : ∀ t ∈ Icc 0 T, HasDerivWithinAt U (U₁ t) (Icc 0 T) t)
    (hU₂ : ∀ t ∈ Icc 0 T, HasDerivWithinAt U₁ (U₂ t) (Icc 0 T) t)
    (hU₃ : ∀ t ∈ Icc 0 T, HasDerivWithinAt U₂ (U₃ t) (Icc 0 T) t)
    (hL₃ : ∀ t ∈ Icc 0 T, ‖U₃ t‖ ≤ L₃)
    (hweak : ∀ t ∈ Icc 0 T, ∀ v ∈ V₀, ⟪U₁ t, emb v⟫ = ⟪DU t, emb v⟫ - ⟪U t, emb (D v)⟫)
    {w : ℕ → V}
    (hA1 : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖emb (w n) - U (n * Δt)‖ ≤ a)
    (hA2 : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖emb (D (w n)) - DU (n * Δt)‖ ≤ a)
    (hA3 : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * Δt ≤ T →
      ‖(emb (w (n + 1)) - U ((n + 1 : ℕ) * Δt)) - (emb (w n) - U (n * Δt))‖ ≤ a * Δt)
    {M : ℕ} (hM : (M : ℝ) * Δt ≤ T) {u g : ℕ → V}
    (hstep : ∀ n < M, TimeStepping.IsDirichletCNStep V₀ A (Δt / 2) 0 (g (n + 1)) (u n)
      (u (n + 1)))
    (hg : ∀ n < M, g (n + 1) - w (n + 1) ∈ V₀) (hu0 : u 0 = w 0) {K h : ℝ}
    (hKa : 2 * a ≤ K * h) (hKL : L₃ / 2 ≤ K) :
    ∃ ũ : ℕ → V, (∀ n, ũ n - w n ∈ V₀) ∧
      ‖u M - ũ M‖ ≤ K * (1 + T) * (h + Δt ^ 2) ∧
      ‖emb (u M) - U (M * Δt)‖ ≤ K * (1 + T) * (h + Δt ^ 2) := by
  obtain ⟨ũ, hũ, -, hfin, hemb'⟩ := norm_cn_error_le hemb hD₀ hDD hA hΔt hU₁ hU₂ hU₃ hL₃ hweak
    hA1 hA2 hA3 hM hstep hg (by rw [hu0, sub_self]; exact V₀.zero_mem)
  rw [hu0, sub_self, norm_zero, zero_add] at hfin hemb'
  have hT0 : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg M) hΔt.le).trans hM
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (hA1 0 (by simpa using hT0))
  have hL0 : 0 ≤ L₃ := (norm_nonneg _).trans (hL₃ 0 ⟨le_rfl, hT0⟩)
  have hK0 : 0 ≤ K := (by linarith : 0 ≤ L₃ / 2).trans hKL
  have hd2 : 0 ≤ Δt ^ 2 := sq_nonneg _
  have key : 2 * a + T * (L₃ * Δt ^ 2 / 2 + 2 * a) ≤ K * (1 + T) * (h + Δt ^ 2) := by
    have h1 : L₃ * Δt ^ 2 / 2 ≤ K * Δt ^ 2 := by nlinarith
    have h2 : T * (L₃ * Δt ^ 2 / 2 + 2 * a) ≤ T * (K * Δt ^ 2 + K * h) :=
      mul_le_mul_of_nonneg_left (by linarith) hT0
    have h3 : 0 ≤ K * Δt ^ 2 := mul_nonneg hK0 hd2
    nlinarith
  exact ⟨ũ, hũ, by linarith, by linarith⟩

end Abstract

/-! ## The scheme on a finite element subcomplex: the setting of the abstract estimate -/

section SubcomplexScheme

open HilbertComplex

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex ℝ c W} (S : H.Subcomplex)

/-- The inclusion `Vₕ = ∏ Vₕⁱ → ∏ Wⁱ` (an isometry, `inner_dEmb`). -/
def dEmb : DState S →ₗ[ℝ] PiLp 2 W where
  toFun x := WithLp.toLp 2 fun i => (x i : W i)
  map_add' x y := PiLp.ext fun i => by simp
  map_smul' a x := PiLp.ext fun i => by simp

omit [Fintype ι] in
@[simp] theorem dEmb_apply (x : DState S) (i : ι) : dEmb S x i = (x i : W i) := rfl

theorem inner_dEmb (x y : DState S) : ⟪dEmb S x, dEmb S y⟫ = ⟪x, y⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  rfl

omit [Fintype ι] in
theorem dEmb_mem_totalDomain (x : DState S) : dEmb S x ∈ H.totalDomain := fun i j =>
  S.le_domain i j (x i).2

/-- `𝐝 (emb x) = emb (𝐝ₕ x)`. -/
theorem totalD_dEmb (x : DState S) :
    H.totalD ⟨dEmb S x, dEmb_mem_totalDomain S x⟩ = dEmb S (discreteD S x) := by
  refine PiLp.ext fun j => ?_
  rw [totalD_apply]
  simp only [dEmb_apply, discreteD, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_sum, Subcomplex.coe_dLin_apply]
  rfl

/-- `𝐝ₕ 𝐝ₕ = 0`. -/
theorem discreteD_discreteD (x : DState S) : discreteD S (discreteD S x) = 0 := by
  refine PiLp.ext fun k => ?_
  simp only [discreteD, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, map_sum,
    PiLp.zero_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => S.dLin_comp_dLin i j k _

variable {Hmin : HilbertComplex ℝ c W} (hle : ∀ i j, Hmin.d i j ≤ H.d i j) (S₀ : Hmin.Subcomplex)

include hle in
/-- `𝐝ₕ V̊ₕ ⊆ V̊ₕ` when the fields with vanishing boundary DOFs form a subcomplex of the complex
with boundary conditions. -/
theorem discreteD_mem_interior {v : DState S} (hv : v ∈ interior S S₀.V) :
    discreteD S v ∈ interior S S₀.V := by
  intro j
  simp only [discreteD, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, Submodule.coe_sum,
    Subcomplex.coe_dLin_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  have e : H.d i j (S.toDomain i j (v i)) = Hmin.d i j ⟨(v i : W i), S₀.le_domain i j (hv i)⟩ :=
    ((hle i j).2 rfl).symm
  rw [e]
  exact S₀.mapsTo i j _ (hv i)

omit [Fintype ι] in
theorem dEmb_mem_totalDomain_min {v : DState S} (hv : v ∈ interior S S₀.V) :
    dEmb S v ∈ Hmin.totalDomain := fun i j => S₀.le_domain i j (hv i)

include hle in
/-- On `V̊ₕ` the complex with boundary conditions acts as `𝐝ₕ`. -/
theorem totalD_min_dEmb {v : DState S} (hv : v ∈ interior S S₀.V) :
    Hmin.totalD ⟨dEmb S v, dEmb_mem_totalDomain_min S S₀ hv⟩ = dEmb S (discreteD S v) := by
  rw [← totalD_dEmb]
  refine PiLp.ext fun j => ?_
  rw [totalD_apply, totalD_apply]
  exact Finset.sum_congr rfl fun i _ => (hle i j).2 rfl

include hle in
/-- **A strong solution of `U' = L_max U` solves the scheme's weak form on `V̊ₕ`**: if
`(U, U') ∈ graph (𝐝 − 𝐝_min†)` then `⟪U', emb v⟫ = ⟪𝐝 U, emb v⟫ − ⟪U, emb (𝐝ₕ v)⟫` for every
`v ∈ V̊ₕ` (`⟪𝐝_min† U, v⟫ = ⟪U, 𝐝_min v⟫`). -/
theorem inner_of_mem_graph_waveMax {U U' : PiLp 2 W}
    (hU : (U, U') ∈ (waveMax Hmin H).graph) {v : DState S} (hv : v ∈ interior S S₀.V) :
    ∃ hD : U ∈ H.totalDomain, ⟪U', dEmb S v⟫ =
      ⟪H.totalD ⟨U, hD⟩, dEmb S v⟫ - ⟪U, dEmb S (discreteD S v)⟫ := by
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hU
  have hy1' : (y : PiLp 2 W) = U := hy1
  have hd : U ∈ H.totalDomain := hy1' ▸ y.2.1
  have hd' : U ∈ Hmin.dual.totalD.domain := hy1' ▸ y.2.2
  refine ⟨hd, ?_⟩
  have e : U' = H.totalD ⟨U, hd⟩ - Hmin.dual.totalD ⟨U, hd'⟩ := by
    have hy2' : waveMax Hmin H y = U' := hy2
    rw [← hy2']
    calc waveMax Hmin H y = H.totalD ⟨(y : PiLp 2 W), y.2.1⟩ -
          Hmin.dual.totalD ⟨(y : PiLp 2 W), y.2.2⟩ := rfl
      _ = _ := by congr 2 <;> exact Subtype.ext hy1'
  have hx := dEmb_mem_totalDomain_min S S₀ hv
  have h2 := Hmin.inner_totalD_dual ⟨dEmb S v, hx⟩ ⟨U, hd'⟩
  rw [totalD_min_dEmb S hle S₀ hv] at h2
  rw [e, inner_sub_left]
  congr 1
  rw [real_inner_comm, ← h2, real_inner_comm]

/-! ### Three rows -/

/-- The three-row inclusion `Vₕ³ → (∏ Wⁱ)³`. -/
def dEmb3 : DState3 S →ₗ[ℝ] PiLp 2 fun _ : Fin 3 => PiLp 2 W where
  toFun u := WithLp.toLp 2 fun r => dEmb S (u r)
  map_add' u v := PiLp.ext fun r => by simp
  map_smul' a u := PiLp.ext fun r => by simp

@[simp] theorem dEmb3_apply (u : DState3 S) (r : Fin 3) : dEmb3 S u r = dEmb S (u r) := rfl

theorem inner_dEmb3 (u v : DState3 S) : ⟪dEmb3 S u, dEmb3 S v⟫ = ⟪u, v⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun r _ => inner_dEmb S (u r) (v r)

/-- The row-wise discrete differential. -/
def discreteD3 : DState3 S →ₗ[ℝ] DState3 S where
  toFun u := WithLp.toLp 2 fun r => discreteD S (u r)
  map_add' u v := PiLp.ext fun r => by simp
  map_smul' a u := PiLp.ext fun r => by simp

@[simp] theorem discreteD3_apply (u : DState3 S) (r : Fin 3) :
    discreteD3 S u r = discreteD S (u r) := rfl

theorem inner_discreteWave3 [∀ i, FiniteDimensional ℝ (S.V i)] (u v : DState3 S) :
    ⟪discreteWave3 S u, v⟫ = ⟪discreteD3 S u, v⟫ - ⟪u, discreteD3 S v⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun r _ => inner_discreteWave S (u r) (v r)

include hle in
theorem discreteD3_mem_interior3 {v : DState3 S} (hv : v ∈ interior3 S S₀.V) :
    discreteD3 S v ∈ interior3 S S₀.V := fun r => discreteD_mem_interior S hle S₀ (hv r)

theorem discreteD3_discreteD3 (v : DState3 S) : discreteD3 S (discreteD3 S v) = 0 :=
  PiLp.ext fun r => by simp [discreteD_discreteD]

include hle in
/-- The weak form for three rows, each a strong solution of `U' = L_max U`, with
`DU = (𝐝 U_r)_r`. -/
theorem inner3_of_mem_graph_waveMax {U U' : PiLp 2 fun _ : Fin 3 => PiLp 2 W}
    (hU : ∀ r, (U r, U' r) ∈ (waveMax Hmin H).graph) (hd : ∀ r, U r ∈ H.totalDomain)
    {v : DState3 S} (hv : v ∈ interior3 S S₀.V) :
    ⟪U', dEmb3 S v⟫ = ⟪(WithLp.toLp 2 fun r => H.totalD ⟨U r, hd r⟩ :
      PiLp 2 fun _ : Fin 3 => PiLp 2 W), dEmb3 S v⟫ - ⟪U, dEmb3 S (discreteD3 S v)⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  obtain ⟨hD, h⟩ := inner_of_mem_graph_waveMax S hle S₀ (hU r) (hv r)
  simpa using h

end SubcomplexScheme

/-! ## The canonical Whitney interpolant as a linear map -/

namespace FEMInterp

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex Feec.ExteriorFibre
  Feec.Models.Cube.FEM

variable {n : ℕ} [NeZero n]

/-- A linear map into `L²(Θ)`, as a linear map into `L²(Θ')` for `Θ = Θ'`. -/
def linearMapOfEq {Θ Θ' : Set (Fin n → ℝ)} (h : Θ = Θ') {j : ℤ}
    (f : contForms n →ₗ[ℝ] L2F ℝ Θ (formIdx n j)) :
    contForms n →ₗ[ℝ] L2F ℝ Θ' (formIdx n j) := by
  subst h; exact f

omit [NeZero n] in
/-- Any property of a subcomplex together with a linear map is transported by
`maximalSubcomplexOfEq` and `linearMapOfEq`. -/
theorem linearMapOfEq_induction {Θ Θ' : Set (Fin n → ℝ)} (h : Θ = Θ') (hΘ : IsOpen Θ)
    (hΘ' : IsOpen Θ') (S : ((deRham ℝ n).maximalComplex hΘ).Subcomplex) {j : ℤ}
    (f : contForms n →ₗ[ℝ] L2F ℝ Θ (formIdx n j))
    (P : ∀ Ω : Set (Fin n → ℝ), ∀ hΩ : IsOpen Ω, ((deRham ℝ n).maximalComplex hΩ).Subcomplex →
      (contForms n →ₗ[ℝ] L2F ℝ Ω (formIdx n j)) → Prop)
    (hP : P Θ hΘ S f) :
    P Θ' hΘ' ((deRham ℝ n).maximalSubcomplexOfEq h hΘ hΘ' S) (linearMapOfEq h f) := by
  subst h; exact hP

/-- **The canonical Whitney interpolant** `Π_h : C⁰Λʲ → Vₕʲ` of the level-`(N + 1)` Freudenthal
mesh of `Q = (0, ½)ⁿ` ([Arnold2018], Ch. 7): the glued global interpolant
`glue ∘ globalInterp` (the degrees of freedom `∫_f w` on the `j`-faces `f`), as a linear map into
`L²Λʲ(Q)` (transported along `mesh_domain`). -/
def canonicalInterp (N : ℕ) (j : ℤ) : contForms n →ₗ[ℝ] L2F ℝ (cubeDomain n) (formIdx n j) :=
  linearMapOfEq (mesh_domain n N)
    ((whitneyElement n).glue (mesh n N) j ∘ₗ
      ((whitneyElement n).globalSpace (mesh n N) j.toNat).subtype ∘ₗ
        (whitneyElement n).globalInterp (mesh n N) j.toNat)

theorem canonicalInterp_mem (N : ℕ) (j : ℤ) (w : contForms n) :
    canonicalInterp N j w ∈ (whitney n N).V j :=
  linearMapOfEq_induction (mesh_domain n N) (isOpen_mesh_domain n N) (isOpen_cubeDomain n)
    (whitneySubcomplex (mesh n N) (isOpen_mesh_domain n N)) _
    (fun _ _ S f => ∀ w, f w ∈ S.V j)
    (fun w => ⟨(whitneyElement n).globalInterp (mesh n N) j.toNat w, rfl⟩) w

/-- **The `O(h)` estimates of the canonical Whitney interpolant** ([Arnold2018], Ch. 7): for a
`C²` form `w` of degree `j` with `‖Dw‖, ‖D dw‖ ≤ L` on `cl Q`, `‖w − Π_h w‖ ≤ B_j L h_N` and
`‖d (w − Π_h w)‖ ≤ B_j L h_N` (`B_j = interpBound n j`). Unlike the existential
`exists_mem_whitney_le`, `Π_h` is the linear map `canonicalInterp`, which the Crank–Nicolson
consistency argument needs for time differences. -/
theorem canonicalInterp_le (N : ℕ) (j : ℤ) :
      ∀ k : ℕ, (k : ℤ) = j → ∀ {w : FormField n} (hw : ContDiff ℝ 2 w), (∀ y, IsDeg k (w y)) →
        ∀ {L : ℝ}, 0 ≤ L → (∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ w y‖ ≤ L) →
        (∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ (extDeriv w) y‖ ≤ L) →
        ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) j
            ⟨w, hw.continuous⟩ - canonicalInterp N j ⟨w, hw.continuous⟩‖ ≤
            interpBound n j * L * meshSize N ∧
        ∀ j' (hx : formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) j
            ⟨w, hw.continuous⟩ ∈ ((complex n).d j j').domain),
          ‖(complex n).d j j' ⟨_ - canonicalInterp N j ⟨w, hw.continuous⟩,
            Submodule.sub_mem _ hx ((whitney n N).le_domain j j' (canonicalInterp_mem N j _))⟩‖ ≤
            interpBound n j * L * meshSize N := by
  rcases lt_or_ge j 0 with hj | hj
  · intro k hk
    omega
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  refine linearMapOfEq_induction (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n) (whitneySubcomplex (mesh n N) (isOpen_mesh_domain n N))
    ((whitneyElement n).glue (mesh n N) k ∘ₗ
      ((whitneyElement n).globalSpace (mesh n N) (k : ℤ).toNat).subtype ∘ₗ
        (whitneyElement n).globalInterp (mesh n N) (k : ℤ).toNat)
    (fun Θ hΘ S P => ∀ hb : Bornology.IsBounded Θ,
      ∀ hvol : volume.real Θ = volume.real (cubeDomain n), ∀ hP : ∀ w, P w ∈ S.V k,
      ∀ k' : ℕ, (k' : ℤ) = k → ∀ {w : FormField n} (hw : ContDiff ℝ 2 w),
        (∀ y, IsDeg k' (w y)) → ∀ {L : ℝ}, 0 ≤ L →
        (∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ w y‖ ≤ L) →
        (∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ (extDeriv w) y‖ ≤ L) →
        ‖formL2 hΘ.measurableSet hb k ⟨w, hw.continuous⟩ - P ⟨w, hw.continuous⟩‖ ≤
            interpBound n k * L * meshSize N ∧
        ∀ j' (hx : formL2 hΘ.measurableSet hb k ⟨w, hw.continuous⟩ ∈
            (((deRham ℝ n).maximalComplex hΘ).d k j').domain),
          ‖((deRham ℝ n).maximalComplex hΘ).d k j'
            ⟨(formL2 hΘ.measurableSet hb k ⟨w, hw.continuous⟩ - P ⟨w, hw.continuous⟩ :
              L2F ℝ Θ (formIdx n k)), Submodule.sub_mem _ hx (S.le_domain k j' (hP _))⟩‖ ≤
            interpBound n k * L * meshSize N) ?_ (isBounded_cubeDomain n) rfl
    (canonicalInterp_mem N k)
  intro hb hvol _ k' hk' w hw hdeg L hL0 hL hL'
  set M := mesh n N
  have hΩo := isOpen_mesh_domain n N
  have hcl : closure M.domain = closure (cubeDomain n) := by rw [mesh_domain]
  have hshape := fun T hT => mesh_shape n N (T := T) hT
  have hk : k' = k := by exact_mod_cast hk'
  subst hk
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have hdw : ContDiff ℝ 1 (extDeriv w) := contDiff_extDeriv (m := 1) hw
  have hh := (meshSize_pos N).le
  have hA0 := mul_nonneg (interpConst_nonneg n k') (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (interpConst_nonneg n (k' + 1)) (mul_nonneg hh hL0)
  have e : interpBound n k' * L * meshSize N =
      interpConst n k' * (meshSize N * L) + interpConst n (k' + 1) * (meshSize N * L) := by
    simp only [interpBound, Int.toNat_natCast]; ring
  refine ⟨?_, fun j' hx => ?_⟩
  · have h := norm_formL2_sub_glue_le M hΩo.measurableSet k' hw1 (C₀ := 2) (h := meshSize N)
      (by norm_num) hh hL0 (fun y hy => hL y (hcl ▸ hy))
      (fun T hT => (hshape T hT).1) (fun T hT => (hshape T hT).2.le)
    have h' : ‖formL2 hΩo.measurableSet hb k' ⟨w, hw.continuous⟩ -
        (whitneyElement n).glue M k' ((whitneyElement n).globalInterp M k' ⟨w, hw.continuous⟩ :
          (whitneyElement n).Piecewise M k')‖ ≤ interpConst n k' * (meshSize N * L) := by
      refine h.trans (le_of_eq ?_)
      rw [hvol, interpConst]; ring
    refine h'.trans ?_
    rw [e]; linarith
  by_cases hj' : (k' : ℤ) + 1 = j'
  · subst hj'
    obtain ⟨hmem, hval⟩ := (whitneyElement n).glue_globalInterp_mem_maximal M hΩo k' ⟨w, hw1⟩
    obtain ⟨hmw, hvw⟩ := formL2_mem_maximal M hΩo k' hw1 hdeg
    have hd := deRham_maximalComplex_d (𝕜 := ℝ) (n := n) hΩo (k' : ℤ)
    have e1 : ((deRham ℝ n).maximalComplex hΩo).d k' (k' + 1) ⟨_, Submodule.sub_mem _ hx
        ((whitneySubcomplex M hΩo).le_domain k' (k' + 1)
          ⟨(whitneyElement n).globalInterp M k' ⟨w, hw.continuous⟩, rfl⟩)⟩ =
        (extDerivOp ℝ n k').maximal M.domain ⟨_, hmw⟩ -
          (extDerivOp ℝ n k').maximal M.domain ⟨_, hmem⟩ := by
      rw [LinearPMap.apply_eq_of_eq' hd, ← LinearPMap.map_sub]
      rfl
    have h := norm_formL2_sub_glue_le M hΩo.measurableSet (k' + 1) hdw (C₀ := 2)
      (h := meshSize N) (by norm_num) hh hL0 (fun y hy => hL' y (hcl ▸ hy))
      (fun T hT => (hshape T hT).1) (fun T hT => (hshape T hT).2.le)
    have e2 : (extDerivOp ℝ n k').maximal M.domain ⟨_, hmem⟩ =
        (whitneyElement n).glue M ((k' + 1 : ℕ) : ℤ) ((whitneyElement n).globalInterp M (k' + 1)
          ⟨extDeriv w, hdw.continuous⟩ : (whitneyElement n).Piecewise M (k' + 1)) := hval
    change ‖((deRham ℝ n).maximalComplex hΩo).d k' (k' + 1) ⟨_, Submodule.sub_mem _ hx
        ((whitneySubcomplex M hΩo).le_domain k' (k' + 1)
          ⟨(whitneyElement n).globalInterp M k' ⟨w, hw.continuous⟩, rfl⟩)⟩‖ ≤ _
    rw [e1, hvw]
    erw [e2]
    have h' := h.trans (le_of_eq (show _ = interpConst n (k' + 1) * (meshSize N * L) by
      rw [hvol, interpConst]; push_cast; ring))
    exact h'.trans (by rw [e]; linarith)
  · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj'), norm_zero]
    exact mul_nonneg (mul_nonneg (interpBound_nonneg n _) hL0) hh

end FEMInterp

/-! ## Smooth forms on the cube: `d`, its formal adjoint, and `L²` norms -/

section SmoothForms

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.ExteriorFibre

variable {n : ℕ}

/-- The formal adjoint `dᵗ = −δ` of the exterior derivative on form fields,
`(dᵗψ)_s = −Σ_{j ∉ s} ε(j, s) ∂_j ψ_{s ∪ j}` (`Feec.Domain.extDAdj`). -/
def formalAdjD (ψ : FormField n) : FormField n := fun x s =>
  extDAdj (𝕜 := ℝ) (fun s y => ψ y s) s x

theorem continuous_formalAdjD {ψ : FormField n} (hψ : ContDiff ℝ 1 ψ) :
    Continuous (formalAdjD ψ) := by
  refine continuous_pi fun s => ?_
  simp only [formalAdjD, extDAdj]
  refine (continuous_finsetSum _ fun j _ => continuous_const.mul ?_).neg
  exact ((contDiff_pi.1 hψ (insert j s)).continuous_fderiv one_ne_zero).clm_apply
    continuous_const

/-- The `L²(Q)` class of a continuous form, in degree `k`. -/
abbrev formL2Q (k : ℤ) (w : FormField n) (hw : Continuous w) :
    L2F ℝ (cubeDomain n) (formIdx n k) :=
  formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k ⟨w, hw⟩

theorem formL2Q_sub (k : ℤ) {w w' : FormField n} (hw : Continuous w) (hw' : Continuous w') :
    formL2Q k w hw - formL2Q k w' hw' = formL2Q k (w - w') (hw.sub hw') := by
  rw [← map_sub]; rfl

theorem formL2Q_neg (k : ℤ) {w : FormField n} (hw : Continuous w) :
    -formL2Q k w hw = formL2Q k (-w) hw.neg := by
  rw [← map_neg]; rfl

/-- `‖w|_Q‖ ≤ #Λᵏ |Q|^{1/2} B` if `|w| ≤ B` on `Q`. -/
theorem norm_formL2Q_le (k : ℤ) {w : FormField n} (hw : Continuous w) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ x ∈ cubeDomain n, ∀ s, |w x s| ≤ B) :
    ‖formL2Q k w hw‖ ≤
      Fintype.card (formIdx n k) * (volume.real (cubeDomain n) ^ (1 / 2 : ℝ) * B) := by
  have : IsFiniteMeasure (volume.restrict (cubeDomain n)) :=
    isFiniteMeasure_restrict.2 (isBounded_cubeDomain n).measure_lt_top.ne
  refine L2F.norm_le_card_mul _ (by positivity) fun s => ?_
  refine (Lp.norm_le_of_ae_bound hB ?_).trans (le_of_eq ?_)
  · filter_upwards [coeFn_formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
      ⟨w, hw⟩ s, ae_restrict_mem (isOpen_cubeDomain n).measurableSet] with x h1 hx
    rw [h1, Real.norm_eq_abs]
    exact h x hx s.1
  · rw [measureUnivNNReal, Measure.restrict_apply_univ, ENNReal.toReal_ofNat, one_div]
    rfl

variable [NeZero n]

/-- **`d` of a smooth form in every pair of degrees**: for a `C¹` form `w` of degree `k = j`,
`w|_Q ∈ D(d j j')` and `d j j' (w|_Q) = (dw)|_Q` if `j' = j + 1`, `0` otherwise. -/
theorem complex_d_formL2Q {j : ℤ} (j' : ℤ) {k : ℕ} (hk : (k : ℤ) = j) {w : FormField n}
    (hw : ContDiff ℝ 1 w) (hdeg : ∀ y, IsDeg k (w y)) :
    formL2Q j w hw.continuous ∈ ((complex n).d j j').domain ∧
      ∀ h' : formL2Q j w hw.continuous ∈ ((complex n).d j j').domain,
        (complex n).d j j' ⟨_, h'⟩ =
          if j + 1 = j' then formL2Q j' (extDeriv w) (continuous_extDeriv hw) else 0 := by
  subst hk
  by_cases hj : (k : ℤ) + 1 = j'
  · subst hj
    obtain ⟨h, hval⟩ := formL2_mem_domain k hw hdeg
    exact ⟨h, fun h' => by simp only [↓reduceIte]; exact hval⟩
  · have htop := HilbertComplex.domain_eq_top_of_not_rel (complex n) (i := (k : ℤ)) (j := j')
      (by simpa using hj)
    refine ⟨htop ▸ Submodule.mem_top, fun h' => ?_⟩
    simp only [hj, ↓reduceIte]
    exact HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj) _

omit [NeZero n] in
/-- `formExt (formComp ψ) = ψ` for a form of the right degree. -/
theorem formExt_formComp {j : ℤ} {k : ℕ} (hk : (k : ℤ) = j) {ψ : FormField n}
    (hdeg : ∀ y, IsDeg k (ψ y)) :
    formExt (formComp (k := j) ψ) = fun s y => ψ y s := by
  funext s y
  unfold formExt
  split_ifs with h
  · rfl
  · exact (hdeg y s (fun h' => h (by rw [← hk]; exact_mod_cast h'))).symm

omit [NeZero n] in
/-- **The adjoint of `d_min` on a smooth form is the formal adjoint** (integration by parts
against `H̊Λ(Q)`, `(d_min)† = (dᵗ)_max`): for a `C¹` form `ψ` of degree `k = j'`,
`ψ|_Q ∈ D((d_min j j')†)` and `(d_min j j')† (ψ|_Q) = (dᵗψ)|_Q` if `j' = j + 1`, `0` otherwise. -/
theorem adjoint_complexMin_d_formL2Q (j : ℤ) {j' : ℤ} {k : ℕ} (hk : (k : ℤ) = j')
    {ψ : FormField n} (hψ : ContDiff ℝ 1 ψ) (hdeg : ∀ y, IsDeg k (ψ y)) :
    formL2Q j' ψ hψ.continuous ∈ ((complexMin n).d j j')†.domain ∧
      ∀ h' : formL2Q j' ψ hψ.continuous ∈ ((complexMin n).d j j')†.domain,
        ((complexMin n).d j j')† ⟨_, h'⟩ =
          if j + 1 = j' then formL2Q j (formalAdjD ψ) (continuous_formalAdjD hψ) else 0 := by
  by_cases hj : j + 1 = j'
  · subst hj
    have hd : ((complexMin n).d j (j + 1))† = (extDerivOp ℝ n j).formalAdj.maximal (cubeDomain n) :=
      deRham_dual_minimalComplex_d (𝕜 := ℝ) (n := n) (isOpen_cubeDomain n) j
    have hcomp : ∀ t : formIdx n (j + 1), ContDiff ℝ 1 (formComp (k := j + 1) ψ t) :=
      fun t => contDiff_pi.1 hψ t.1
    have hmem : ∀ t : formIdx n (j + 1),
        MemLp (formComp (k := j + 1) ψ t) 2 (volume.restrict (cubeDomain n)) := fun t =>
      memLp_of_continuous (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n)
        (hcomp t).continuous
    have hfa : ∀ r : formIdx n j, (extDerivOp ℝ n j).formalAdj.apply (formComp (k := j + 1) ψ) r =
        formComp (k := j) (formalAdjD ψ) r := fun r => by
      funext x
      rw [formalAdj_extDerivOp_apply, formExt_formComp hk hdeg]
      rfl
    have hAψ : ∀ r : formIdx n j, MemLp ((extDerivOp ℝ n j).formalAdj.apply
        (formComp (k := j + 1) ψ) r) 2 (volume.restrict (cubeDomain n)) := fun r => by
      rw [hfa]
      exact memLp_of_continuous (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n)
        (continuous_formComp (continuous_formalAdjD hψ) r)
    obtain ⟨hm, hv⟩ := (extDerivOp ℝ n j).formalAdj.smooth_mem_maximal_domain
      (isOpen_cubeDomain n) (formalAdj_extDerivOp_isOrderLE j) hcomp hmem hAψ
    refine ⟨hd ▸ hm, fun h' => ?_⟩
    simp only [↓reduceIte]
    rw [LinearPMap.apply_eq_of_eq' hd]
    refine hv.trans (PiLp.ext fun r => ?_)
    exact MemLp.toLp_congr (hAψ r) (memLp_of_continuous (isOpen_cubeDomain n).measurableSet
      (isBounded_cubeDomain n) (continuous_formComp (continuous_formalAdjD hψ) r))
      (Eventually.of_forall fun x => congrFun (hfa r) x)
  · have h0 : (complexMin n).d j j' = 0 := HilbertComplex.shape _ _ _ (by simpa using hj)
    refine ⟨(by rw [h0, LinearPMap.adjoint_zero]; exact Submodule.mem_top), fun h' => ?_⟩
    simp only [hj, ↓reduceIte]
    exact LinearPMap.adjoint_apply_eq_zero_of_eq_zero h0 _

end SmoothForms

/-! ## One row of (4.14) on the cube: the de Rham window `HΛ⁰ → HΛ¹ → L²Λ²` -/

section Row

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.ExteriorFibre HilbertComplex

/-- The `L²` space of one row `(σ_r, E_r, B_r)`: `L²Λ⁰(Q) × L²Λ¹(Q) × L²Λ²(Q)`. -/
abbrev RowSpace : Type :=
  PiLp 2 fun i : Fin 3 => L2F ℝ (cubeDomain 3) (formIdx 3 ((0 : ℤ) + ((i : ℕ) : ℤ)))

/-- The window `HΛ⁰(Q) → HΛ¹(Q) → L²Λ²(Q)` (no boundary conditions). -/
abbrev rowComplex := (complex 3).window 0 3

/-- The window `H̊Λ⁰(Q) → H̊Λ¹(Q) → L²Λ²(Q)` of the minimal complex (vanishing traces). -/
abbrev rowComplexMin := (complexMin 3).window 0 3

theorem complexMin_d_le_complex_d {n : ℕ} (j j' : ℤ) :
    (complexMin n).d j j' ≤ (complex n).d j j' := by
  by_cases h : j + 1 = j'
  · subst h
    rw [deRham_minimalComplex_d, deRham_maximalComplex_d]
    exact extDerivOp_minimal_le_maximal (isOpen_cubeDomain n) j
  · rw [HilbertComplex.shape _ j j' (by simpa using h),
      HilbertComplex.shape _ j j' (by simpa using h)]

theorem rowComplexMin_d_le (i j : Fin 3) : rowComplexMin.d i j ≤ rowComplex.d i j :=
  complexMin_d_le_complex_d _ _

/-- A row of continuous forms (degrees `0, 1, 2`) as a point of `RowSpace`. -/
def rowField (f : Fin 3 → FormField 3) (hf : ∀ i, Continuous (f i)) : RowSpace :=
  WithLp.toLp 2 fun i => formL2Q ((0 : ℤ) + ((i : ℕ) : ℤ)) (f i) (hf i)

@[simp] theorem rowField_apply (f : Fin 3 → FormField 3) (hf : ∀ i, Continuous (f i)) (i : Fin 3) :
    rowField f hf i = formL2Q ((0 : ℤ) + ((i : ℕ) : ℤ)) (f i) (hf i) := rfl

theorem degIdx (i : Fin 3) : (((i : ℕ) : ℕ) : ℤ) = (0 : ℤ) + ((i : ℕ) : ℤ) := (zero_add _).symm

/-- **A smooth row solving the row of (4.14) pointwise solves `U' = L_max U`**: if the forms
`f = (σ, E, B)` (degrees `0, 1, 2`, `C¹`) and `f₁` satisfy `f₁₀ = −dᵗf₁`, `f₁₁ = d f₀ − dᵗ f₂`,
`f₁₂ = d f₁` (Ch. 7 sign convention: `σ' = div E`, `E' = grad σ − curl B`, `B' = curl E`), then
`(f|_Q, f₁|_Q) ∈ graph (𝐝_max − 𝐝_min†)` on the row window. -/
theorem rowField_mem_graph_waveMax {f f₁ : Fin 3 → FormField 3} (hf : ∀ i, ContDiff ℝ 1 (f i))
    (hdeg : ∀ (i : Fin 3) y, IsDeg (i : ℕ) (f i y)) (hf₁ : ∀ i, Continuous (f₁ i))
    (h0 : f₁ 0 = -formalAdjD (f 1)) (h1 : f₁ 1 = extDeriv (f 0) - formalAdjD (f 2))
    (h2 : f₁ 2 = extDeriv (f 1)) :
    (rowField f fun i => (hf i).continuous, rowField f₁ hf₁) ∈
      (waveMax rowComplexMin rowComplex).graph := by
  have hD : ∀ i j, (rowField f fun i => (hf i).continuous) i ∈ (rowComplex.d i j).domain :=
    fun i j => (complex_d_formL2Q _ (degIdx i) (hf i) (hdeg i)).1
  have hA : ∀ i j, (rowField f fun i => (hf i).continuous) j ∈ ((rowComplexMin.d i j)†).domain :=
    fun i j => (adjoint_complexMin_d_formL2Q _ (degIdx j) (hf j) (hdeg j)).1
  have hx := mem_waveMax_domain.2 ⟨hD, hA⟩
  refine (LinearPMap.mem_graph_iff _).2 ⟨⟨_, hx⟩, rfl, PiLp.ext fun j => ?_⟩
  change _ = rowField f₁ hf₁ j
  have e1 : ∀ i, rowComplex.d i j ⟨(rowField f fun i => (hf i).continuous) i, hD i j⟩ =
      if ((0 : ℤ) + ((i : ℕ) : ℤ)) + 1 = (0 : ℤ) + ((j : ℕ) : ℤ) then
        formL2Q _ (extDeriv (f i)) (continuous_extDeriv (hf i)) else 0 := fun i =>
    (complex_d_formL2Q _ (degIdx i) (hf i) (hdeg i)).2 _
  have e2 : ∀ k, (rowComplexMin.d j k)† ⟨(rowField f fun i => (hf i).continuous) k, hA j k⟩ =
      if ((0 : ℤ) + ((j : ℕ) : ℤ)) + 1 = (0 : ℤ) + ((k : ℕ) : ℤ) then
        formL2Q _ (formalAdjD (f k)) (continuous_formalAdjD (hf k)) else 0 := fun k =>
    (adjoint_complexMin_d_formL2Q _ (degIdx k) (hf k) (hdeg k)).2 _
  have e := waveMax_apply (H := rowComplexMin) (H' := rowComplex) ⟨_, hx⟩ j
  change _ = ∑ i, rowComplex.d i j ⟨(rowField f fun i => (hf i).continuous) i, hD i j⟩ -
    ∑ k, (rowComplexMin.d j k)† ⟨(rowField f fun i => (hf i).continuous) k, hA j k⟩ at e
  rw [e, Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_congr rfl fun k _ => e2 k,
    rowField_apply]
  fin_cases j
  · simp [Fin.sum_univ_three, h0, formL2Q_neg]
  · simp [Fin.sum_univ_three, h1, formL2Q_sub]
  · simp [Fin.sum_univ_three, h2]

end Row

/-! ## Smooth solutions of one row and their `L²` time derivatives -/

section RowSolution

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.ExteriorFibre HilbertComplex

theorem hasDerivAt_toLp {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, NormedAddCommGroup (β i)]
    [∀ i, NormedSpace ℝ (β i)] {F : ℝ → ∀ i, β i} {F' : ∀ i, β i} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s => F s i) (F' i) t) :
    HasDerivAt (fun s => (WithLp.toLp 2 (F s) : PiLp 2 β)) (WithLp.toLp 2 F') t := by
  have h' : HasDerivAt F F' t := hasDerivAt_pi.2 h
  have := (PiLp.continuousLinearEquiv 2 ℝ β).symm.hasFDerivAt.comp_hasDerivAt t h'
  simpa [Function.comp_def] using this

/-- **Classical time derivatives of forms are `L²(Q)` time derivatives**. -/
theorem hasDerivAt_formL2Q (k : ℤ) {u u₁ : ℝ → FormField 3} (hu : ∀ t, Continuous (u t))
    (hu₁ : ∀ s, Continuous fun p : ℝ × (Fin 3 → ℝ) => u₁ p.1 p.2 s)
    (hd : ∀ t y s, HasDerivAt (fun τ => u τ y s) (u₁ t y s) t) (t : ℝ) :
    HasDerivAt (fun τ => formL2Q k (u τ) (hu τ))
      (formL2Q k (u₁ t) (continuous_pi fun s =>
        (hu₁ s).comp (continuous_const.prodMk continuous_id))) t :=
  hasDerivAt_smoothField (isOpen_cubeDomain 3) (isBounded_cubeDomain 3)
    (f := fun τ (s : formIdx 3 k) y => u τ y s.1) (f' := fun τ (s : formIdx 3 k) y => u₁ τ y s.1)
    (fun τ s => continuous_formComp (hu τ) s) (fun s => hu₁ s.1)
    (fun τ s y => hd τ y s.1) t

/-- A **smooth solution of one row of (4.14)** (Ch. 7 sign convention) on `[0, T] × cl Q`, as
forms `u t i` of degree `i` (`σ_r`, the `1`-form `E_r`, the `2`-form `B_r`): `C²` in space, `C³`
in time with jointly continuous time derivatives, solving `σ' = −dᵗE`, `E' = dσ − dᵗB`,
`B' = dE` pointwise (`dᵗ = −δ`, so `σ' = div E`, `E' = grad σ − curl B`, `B' = curl E`), with
the bounds `‖Du‖, ‖D du‖ ≤ L` on `cl Q`, `L`-Lipschitz dependence of `Du`, `D du` on `t ∈ [0, T]`
(bounded mixed derivatives `∂ₜ Du`), and `|∂ₜ³ u| ≤ L` on `[0, T] × Q`. The fields and their
time derivatives are defined for all `t ∈ ℝ` (whole-space solutions restrict to such rows,
`WholeSpaceTSD.Smooth.row`); the bounds are only required on `[0, T]`. -/
structure RowSolution (T L : ℝ) where
  /-- the fields and their first three time derivatives -/
  u : ℝ → Fin 3 → FormField 3
  u₁ : ℝ → Fin 3 → FormField 3
  u₂ : ℝ → Fin 3 → FormField 3
  u₃ : ℝ → Fin 3 → FormField 3
  isDeg : ∀ t (i : Fin 3) y, IsDeg (i : ℕ) (u t i y)
  contDiff : ∀ t i, ContDiff ℝ 2 (u t i)
  continuous₁ : ∀ i s, Continuous fun p : ℝ × (Fin 3 → ℝ) => u₁ p.1 i p.2 s
  continuous₂ : ∀ i s, Continuous fun p : ℝ × (Fin 3 → ℝ) => u₂ p.1 i p.2 s
  continuous₃ : ∀ i s, Continuous fun p : ℝ × (Fin 3 → ℝ) => u₃ p.1 i p.2 s
  hasDerivAt₁ : ∀ t i y s, HasDerivAt (fun τ => u τ i y s) (u₁ t i y s) t
  hasDerivAt₂ : ∀ t i y s, HasDerivAt (fun τ => u₁ τ i y s) (u₂ t i y s) t
  hasDerivAt₃ : ∀ t i y s, HasDerivAt (fun τ => u₂ τ i y s) (u₃ t i y s) t
  pde₀ : ∀ t, u₁ t 0 = -formalAdjD (u t 1)
  pde₁ : ∀ t, u₁ t 1 = extDeriv (u t 0) - formalAdjD (u t 2)
  pde₂ : ∀ t, u₁ t 2 = extDeriv (u t 1)
  bound : ∀ t ∈ Icc 0 T, ∀ i, ∀ y ∈ closure (cubeDomain 3),
    ‖fderiv ℝ (u t i) y‖ ≤ L ∧ ‖fderiv ℝ (extDeriv (u t i)) y‖ ≤ L
  lipschitz : ∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T, ∀ i, ∀ y ∈ closure (cubeDomain 3),
    ‖fderiv ℝ (u t' i) y - fderiv ℝ (u t i) y‖ ≤ L * |t' - t| ∧
      ‖fderiv ℝ (extDeriv (u t' i)) y - fderiv ℝ (extDeriv (u t i)) y‖ ≤ L * |t' - t|
  bound₃ : ∀ t ∈ Icc 0 T, ∀ i, ∀ y ∈ cubeDomain 3, ∀ s, |u₃ t i y s| ≤ L

namespace RowSolution

variable {T L : ℝ} (X : RowSolution T L)

theorem continuous (t : ℝ) (i : Fin 3) : Continuous (X.u t i) := (X.contDiff t i).continuous

theorem continuous_u₁ (t : ℝ) (i : Fin 3) : Continuous (X.u₁ t i) :=
  continuous_pi fun s => (X.continuous₁ i s).comp (continuous_const.prodMk continuous_id)

theorem continuous_u₂ (t : ℝ) (i : Fin 3) : Continuous (X.u₂ t i) :=
  continuous_pi fun s => (X.continuous₂ i s).comp (continuous_const.prodMk continuous_id)

theorem continuous_u₃ (t : ℝ) (i : Fin 3) : Continuous (X.u₃ t i) :=
  continuous_pi fun s => (X.continuous₃ i s).comp (continuous_const.prodMk continuous_id)

/-- The row `U(t) = (σ_r, E_r, B_r)(t)|_Q ∈ L²Λ⁰ × L²Λ¹ × L²Λ²`. -/
def field (t : ℝ) : RowSpace := rowField (X.u t) (X.continuous t)

/-- `U'(t)`. -/
def field₁ (t : ℝ) : RowSpace := rowField (X.u₁ t) (X.continuous_u₁ t)

/-- `U''(t)`. -/
def field₂ (t : ℝ) : RowSpace := rowField (X.u₂ t) (X.continuous_u₂ t)

/-- `U'''(t)`. -/
def field₃ (t : ℝ) : RowSpace := rowField (X.u₃ t) (X.continuous_u₃ t)

theorem hasDerivAt_field (t : ℝ) : HasDerivAt X.field (X.field₁ t) t :=
  hasDerivAt_toLp fun i => hasDerivAt_formL2Q _ (fun τ => X.continuous τ i)
    (fun s => X.continuous₁ i s) (fun τ y s => X.hasDerivAt₁ τ i y s) t

theorem hasDerivAt_field₁ (t : ℝ) : HasDerivAt X.field₁ (X.field₂ t) t :=
  hasDerivAt_toLp fun i => hasDerivAt_formL2Q _ (fun τ => X.continuous_u₁ τ i)
    (fun s => X.continuous₂ i s) (fun τ y s => X.hasDerivAt₂ τ i y s) t

theorem hasDerivAt_field₂ (t : ℝ) : HasDerivAt X.field₂ (X.field₃ t) t :=
  hasDerivAt_toLp fun i => hasDerivAt_formL2Q _ (fun τ => X.continuous_u₂ τ i)
    (fun s => X.continuous₃ i s) (fun τ y s => X.hasDerivAt₃ τ i y s) t

/-- **The row is a strong solution of `U' = L_max U`** on the window `HΛ⁰ → HΛ¹ → L²Λ²` with
the adjoint of the window with vanishing traces. -/
theorem mem_graph_waveMax (t : ℝ) :
    (X.field t, X.field₁ t) ∈ (waveMax rowComplexMin rowComplex).graph :=
  rowField_mem_graph_waveMax (fun i => (X.contDiff t i).of_le (by norm_num)) (X.isDeg t)
    (X.continuous_u₁ t) (X.pde₀ t) (X.pde₁ t) (X.pde₂ t)

theorem field_mem_totalDomain (t : ℝ) : X.field t ∈ rowComplex.totalDomain := fun i j =>
  (complex_d_formL2Q _ (degIdx i) ((X.contDiff t i).of_le (by norm_num)) (X.isDeg t i)).1

end RowSolution

end RowSolution

/-! ## Row interpolants and their errors -/

section RowInterp

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.ExteriorFibre HilbertComplex

/-- The canonical Whitney interpolant into `Vₕ^{0 + i}` (`FEMInterp.canonicalInterp`: the
glued interpolant `glue ∘ globalInterp` of the Freudenthal mesh, whose boundary DOFs are the
integrals of the interpolated form over the boundary faces). -/
def rowInterp (N : ℕ) (i : Fin 3) :
    contForms 3 →ₗ[ℝ] L2F ℝ (cubeDomain 3) (formIdx 3 ((0 : ℤ) + ((i : ℕ) : ℤ))) :=
  FEMInterp.canonicalInterp (n := 3) N ((0 : ℤ) + ((i : ℕ) : ℤ))

theorem rowInterp_mem (N : ℕ) (i : Fin 3) (w : contForms 3) :
    rowInterp N i w ∈ (whitneyRow N).V i :=
  FEMInterp.canonicalInterp_mem N _ w

/-- The row interpolant `Π_h (σ, E, B)`, a linear map into the Whitney row. -/
def rowInterpL (N : ℕ) : (Fin 3 → contForms 3) →ₗ[ℝ] DState (whitneyRow N) where
  toFun g := WithLp.toLp 2 fun i => ⟨rowInterp N i (g i), rowInterp_mem N i (g i)⟩
  map_add' g g' := PiLp.ext fun i => Subtype.ext (by simp)
  map_smul' a g := PiLp.ext fun i => Subtype.ext (by simp)

/-- The `L²` class of a row of continuous forms, as a linear map. -/
def rowFieldL : (Fin 3 → contForms 3) →ₗ[ℝ] RowSpace where
  toFun g := WithLp.toLp 2 fun i =>
    formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) _ (g i)
  map_add' g g' := PiLp.ext fun i => by simp
  map_smul' a g := PiLp.ext fun i => by simp

/-- The constant `Σᵢ B_{0+i}` of the row interpolation error. -/
def rowBound : ℝ := ∑ i : Fin 3, interpBound 3 ((0 : ℤ) + ((i : ℕ) : ℤ))

theorem rowBound_nonneg : 0 ≤ rowBound :=
  Finset.sum_nonneg fun _ _ => interpBound_nonneg 3 _

/-- **Row interpolation error** in `L²` and for `𝐝`: for `C²` forms `g` (degrees `0, 1, 2`) with
`‖Dg‖, ‖D dg‖ ≤ L` on `cl Q`, `‖Π_h g − g‖ ≤ (Σᵢ Bᵢ) L h_N` and
`‖𝐝 (Π_h g − g)‖ ≤ 3 (Σᵢ Bᵢ) L h_N`. -/
theorem rowInterp_bounds (N : ℕ) {g : Fin 3 → FormField 3} (hg : ∀ i, ContDiff ℝ 2 (g i))
    (hdeg : ∀ (i : Fin 3) y, IsDeg (i : ℕ) (g i y)) {L : ℝ} (hL0 : 0 ≤ L)
    (hb : ∀ i, ∀ y ∈ closure (cubeDomain 3),
      ‖fderiv ℝ (g i) y‖ ≤ L ∧ ‖fderiv ℝ (extDeriv (g i)) y‖ ≤ L) :
    ‖dEmb (whitneyRow N) (rowInterpL N fun i => ⟨g i, (hg i).continuous⟩) -
        rowFieldL (fun i => ⟨g i, (hg i).continuous⟩)‖ ≤ rowBound * L * meshSize N ∧
      ∀ hx : dEmb (whitneyRow N) (rowInterpL N fun i => ⟨g i, (hg i).continuous⟩) -
          rowFieldL (fun i => ⟨g i, (hg i).continuous⟩) ∈ rowComplex.totalDomain,
        ‖rowComplex.totalD ⟨_, hx⟩‖ ≤ 3 * (rowBound * L * meshSize N) := by
  set x := dEmb (whitneyRow N) (rowInterpL N fun i => ⟨g i, (hg i).continuous⟩) -
    rowFieldL (fun i => ⟨g i, (hg i).continuous⟩)
  have spec := fun i : Fin 3 =>
    FEMInterp.canonicalInterp_le (n := 3) N ((0 : ℤ) + ((i : ℕ) : ℤ))
      (i : ℕ) (degIdx i) (hg i) (hdeg i) hL0 (fun y hy => (hb i y hy).1) (fun y hy => (hb i y hy).2)
  have hxi : ∀ i, x i =
      -(formL2Q _ (g i) (hg i).continuous - rowInterp N i ⟨g i, (hg i).continuous⟩) :=
    fun i => by simp [x, rowInterpL, rowFieldL, dEmb]
  have hh := (meshSize_pos N).le
  have hle : ∀ i : Fin 3, interpBound 3 ((0 : ℤ) + ((i : ℕ) : ℤ)) * L * meshSize N ≤
      rowBound * L * meshSize N := fun i =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun i : Fin 3 => interpBound 3 ((0 : ℤ) + ((i : ℕ) : ℤ)))
        (fun _ _ => interpBound_nonneg 3 _) (Finset.mem_univ i)) hL0) hh
  have hsum : ∑ i : Fin 3, interpBound 3 ((0 : ℤ) + ((i : ℕ) : ℤ)) * L * meshSize N =
      rowBound * L * meshSize N := by
    rw [rowBound, Finset.sum_mul, Finset.sum_mul]
  refine ⟨(PiLp.norm_le_sum_norm x).trans ?_, fun hx => ?_⟩
  · rw [← hsum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hxi, norm_neg]
    exact (spec i).1
  · have hj : ∀ j, ‖rowComplex.totalD ⟨x, hx⟩ j‖ ≤ rowBound * L * meshSize N := fun j => by
      rw [totalD_apply]
      refine (norm_sum_le _ _).trans ?_
      rw [← hsum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hdom := (complex_d_formL2Q ((0 : ℤ) + ((j : ℕ) : ℤ)) (degIdx i)
        ((hg i).of_le (by norm_num)) (hdeg i)).1
      have e : rowComplex.d i j ⟨x i, hx i j⟩ = -(complex 3).d ((0 : ℤ) + ((i : ℕ) : ℤ))
          ((0 : ℤ) + ((j : ℕ) : ℤ)) ⟨formL2Q _ (g i) (hg i).continuous -
            rowInterp N i ⟨g i, (hg i).continuous⟩, Submodule.sub_mem _ hdom
              ((whitney 3 N).le_domain _ _ (rowInterp_mem N i _))⟩ := by
        rw [← LinearPMap.map_neg]
        congr 1
        exact Subtype.ext (hxi i)
      rw [e, norm_neg]
      exact (spec i).2 _ hdom
    refine (PiLp.norm_le_sum_norm _).trans ?_
    calc ∑ j : Fin 3, ‖rowComplex.totalD ⟨x, hx⟩ j‖ ≤ ∑ _j : Fin 3, rowBound * L * meshSize N :=
          Finset.sum_le_sum fun j _ => hj j
      _ = 3 * (rowBound * L * meshSize N) := by simp

end RowInterp

/-! ## The interpolation estimates for a smooth row solution -/

section RowSolutionBounds

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.ExteriorFibre HilbertComplex

theorem extDeriv_sub_of_contDiff {n : ℕ} {a b : FormField n} (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b) : extDeriv (a - b) = extDeriv a - extDeriv b := by
  funext x
  have e : a - b = a + (-1 : ℝ) • b := by funext y; simp [sub_eq_add_neg]
  have hb' : DifferentiableAt ℝ ((-1 : ℝ) • b) x :=
    (hb.differentiable one_ne_zero x).const_smul (-1 : ℝ)
  rw [e, extDeriv_add_apply (η := (-1 : ℝ) • b) (ha.differentiable one_ne_zero x) hb',
    extDeriv_smul_const_apply _ (hb.differentiable one_ne_zero x)]
  simp [sub_eq_add_neg]

/-- The constant `Σᵢ #Λ^{0+i} |Q|^{1/2}` of the bound `‖U‖ ≤ (Σᵢ #Λⁱ |Q|^{1/2}) sup |u|`. -/
def rowL2Const : ℝ := ∑ i : Fin 3,
  (Fintype.card (formIdx 3 ((0 : ℤ) + ((i : ℕ) : ℤ))) : ℝ) *
    volume.real (cubeDomain 3) ^ (1 / 2 : ℝ)

theorem rowL2Const_nonneg : 0 ≤ rowL2Const := Finset.sum_nonneg fun _ _ => by positivity

theorem norm_rowField_le {f : Fin 3 → FormField 3} (hf : ∀ i, Continuous (f i)) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ i, ∀ y ∈ cubeDomain 3, ∀ s, |f i y s| ≤ B) :
    ‖rowField f hf‖ ≤ rowL2Const * B := by
  refine (PiLp.norm_le_sum_norm _).trans ?_
  rw [rowL2Const, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [rowField_apply]
  refine (norm_formL2Q_le _ (hf i) hB (h i)).trans (le_of_eq ?_)
  ring

namespace RowSolution

variable {T L : ℝ} (X : RowSolution T L)

theorem norm_field₃_le {t : ℝ} (ht : t ∈ Icc 0 T) (hL0 : 0 ≤ L) :
    ‖X.field₃ t‖ ≤ rowL2Const * L :=
  norm_rowField_le _ hL0 fun i y hy s => X.bound₃ t ht i y hy s

/-- The row interpolant `Π_h U(t)` in the Whitney row of the level-`(N + 1)` mesh. -/
def interp (N : ℕ) (t : ℝ) : DState (whitneyRow N) :=
  rowInterpL N fun i => ⟨X.u t i, X.continuous t i⟩

/-- `‖Π_h U(t) − U(t)‖ ≤ (Σᵢ Bᵢ) L h_N` on `[0, T]`. -/
theorem norm_interp_sub_le (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (hL0 : 0 ≤ L) :
    ‖dEmb (whitneyRow N) (X.interp N t) - X.field t‖ ≤ rowBound * L * meshSize N :=
  (rowInterp_bounds N (X.contDiff t) (X.isDeg t) hL0 (X.bound t ht)).1

/-- `‖emb (𝐝ₕ Π_h U(t)) − 𝐝 U(t)‖ ≤ 3 (Σᵢ Bᵢ) L h_N` on `[0, T]`. -/
theorem norm_d_interp_sub_le (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (hL0 : 0 ≤ L) :
    ‖dEmb (whitneyRow N) (discreteD (whitneyRow N) (X.interp N t)) -
        rowComplex.totalD ⟨X.field t, X.field_mem_totalDomain t⟩‖ ≤
      3 * (rowBound * L * meshSize N) := by
  have hx := Submodule.sub_mem _ (dEmb_mem_totalDomain (whitneyRow N) (X.interp N t))
    (X.field_mem_totalDomain t)
  have e : dEmb (whitneyRow N) (discreteD (whitneyRow N) (X.interp N t)) -
      rowComplex.totalD ⟨X.field t, X.field_mem_totalDomain t⟩ =
      rowComplex.totalD ⟨_, hx⟩ := by
    rw [← totalD_dEmb, ← LinearPMap.map_sub]
    rfl
  rw [e]
  exact (rowInterp_bounds N (X.contDiff t) (X.isDeg t) hL0 (X.bound t ht)).2 hx

/-- **The interpolation error is `L`-Lipschitz in time, times `h_N`**:
`‖(Π_h − I)(U(t') − U(t))‖ ≤ (Σᵢ Bᵢ) L |t' − t| h_N` (the interpolant is linear). -/
theorem norm_interp_sub_sub_le (N : ℕ) {t t' : ℝ} (ht : t ∈ Icc 0 T) (ht' : t' ∈ Icc 0 T)
    (hL0 : 0 ≤ L) :
    ‖(dEmb (whitneyRow N) (X.interp N t') - X.field t') -
        (dEmb (whitneyRow N) (X.interp N t) - X.field t)‖ ≤
      rowBound * (L * |t' - t|) * meshSize N := by
  have hg : ∀ i, ContDiff ℝ 2 (X.u t' i - X.u t i) := fun i =>
    (X.contDiff t' i).sub (X.contDiff t i)
  have hdeg : ∀ (i : Fin 3) y, IsDeg (i : ℕ) ((X.u t' i - X.u t i) y) := fun i y s hs => by
    simp [X.isDeg t' i y s hs, X.isDeg t i y s hs]
  have hb : ∀ i, ∀ y ∈ closure (cubeDomain 3),
      ‖fderiv ℝ (X.u t' i - X.u t i) y‖ ≤ L * |t' - t| ∧
        ‖fderiv ℝ (extDeriv (X.u t' i - X.u t i)) y‖ ≤ L * |t' - t| := fun i y hy => by
    have h1 : ContDiff ℝ 1 (X.u t' i) := (X.contDiff t' i).of_le (by norm_num)
    have h0 : ContDiff ℝ 1 (X.u t i) := (X.contDiff t i).of_le (by norm_num)
    rw [extDeriv_sub_of_contDiff h1 h0, fderiv_sub (h1.differentiable one_ne_zero y)
      (h0.differentiable one_ne_zero y),
      fderiv_sub ((contDiff_extDeriv (m := 1) (X.contDiff t' i)).differentiable one_ne_zero y)
        ((contDiff_extDeriv (m := 1) (X.contDiff t i)).differentiable one_ne_zero y)]
    exact X.lipschitz t ht t' ht' i y hy
  set g : Fin 3 → FormField 3 := fun i => X.u t' i - X.u t i with hgdef
  have e : (dEmb (whitneyRow N) (X.interp N t') - X.field t') -
      (dEmb (whitneyRow N) (X.interp N t) - X.field t) =
      dEmb (whitneyRow N) (rowInterpL N fun i => ⟨g i, (hg i).continuous⟩) -
        rowFieldL (fun i => ⟨g i, (hg i).continuous⟩) := by
    have e1 : (fun i => (⟨g i, (hg i).continuous⟩ : contForms 3)) =
        (fun i => ⟨X.u t' i, X.continuous t' i⟩) - fun i => ⟨X.u t i, X.continuous t i⟩ := by
      funext i; exact Subtype.ext rfl
    rw [e1, map_sub, map_sub, map_sub]
    change _ = (dEmb (whitneyRow N) (X.interp N t') - dEmb (whitneyRow N) (X.interp N t)) -
      (X.field t' - X.field t)
    abel
  rw [e]
  exact (rowInterp_bounds N hg hdeg (mul_nonneg hL0 (abs_nonneg _)) hb).1

end RowSolution

end RowSolutionBounds

/-! ## The `O(h + Δt²)` error of the three-row Whitney scheme -/

section WhitneyError

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.ExteriorFibre HilbertComplex

variable {T L : ℝ}

/-- The exact three-row field `U(t) = (U_r(t))_r` in `(L²Λ⁰ × L²Λ¹ × L²Λ²)³`. -/
def exactField (X : Fin 3 → RowSolution T L) (t : ℝ) : PiLp 2 fun _ : Fin 3 => RowSpace :=
  WithLp.toLp 2 fun r => (X r).field t

/-- The canonical Whitney interpolant `Π_h U(t)` of the three rows. -/
def exactInterp (X : Fin 3 → RowSolution T L) (N : ℕ) (t : ℝ) : DState3 (whitneyRow N) :=
  WithLp.toLp 2 fun r => (X r).interp N t

/-- The constant of `whitney_cn_error_le`: `18 Σᵢ Bᵢ + 3 Σᵢ #Λⁱ |Q|^{1/2}`, independent of `N`,
`Δt`, `T` and the solution. -/
def cnConst : ℝ := 18 * rowBound + 3 * rowL2Const

/-- `U'(t)` of the three rows. -/
def exactField₁ (X : Fin 3 → RowSolution T L) (t : ℝ) : PiLp 2 fun _ : Fin 3 => RowSpace :=
  WithLp.toLp 2 fun r => (X r).field₁ t

/-- The second time derivative of the three rows. -/
def exactField₂ (X : Fin 3 → RowSolution T L) (t : ℝ) : PiLp 2 fun _ : Fin 3 => RowSpace :=
  WithLp.toLp 2 fun r => (X r).field₂ t

/-- The third time derivative of the three rows. -/
def exactField₃ (X : Fin 3 → RowSolution T L) (t : ℝ) : PiLp 2 fun _ : Fin 3 => RowSpace :=
  WithLp.toLp 2 fun r => (X r).field₃ t

/-- `𝐝 U(t)` of the three rows (the weak `d` of the window `HΛ⁰ → HΛ¹ → L²Λ²`). -/
def exactD (X : Fin 3 → RowSolution T L) (t : ℝ) : PiLp 2 fun _ : Fin 3 => RowSpace :=
  WithLp.toLp 2 fun r => rowComplex.totalD ⟨(X r).field t, (X r).field_mem_totalDomain t⟩

variable (X : Fin 3 → RowSolution T L)

theorem hasDerivAt_exactField (t : ℝ) : HasDerivAt (exactField X) (exactField₁ X t) t :=
  hasDerivAt_toLp fun r => (X r).hasDerivAt_field t

theorem hasDerivAt_exactField₁ (t : ℝ) : HasDerivAt (exactField₁ X) (exactField₂ X t) t :=
  hasDerivAt_toLp fun r => (X r).hasDerivAt_field₁ t

theorem hasDerivAt_exactField₂ (t : ℝ) : HasDerivAt (exactField₂ X) (exactField₃ X t) t :=
  hasDerivAt_toLp fun r => (X r).hasDerivAt_field₂ t

theorem norm_exactField₃_le {t : ℝ} (ht : t ∈ Icc 0 T) (hL0 : 0 ≤ L) :
    ‖exactField₃ X t‖ ≤ 3 * (rowL2Const * L) := by
  refine (PiLp.norm_le_sum_norm _).trans ?_
  calc ∑ r : Fin 3, ‖exactField₃ X t r‖ ≤ ∑ _r : Fin 3, rowL2Const * L :=
        Finset.sum_le_sum fun r _ => (X r).norm_field₃_le ht hL0
    _ = 3 * (rowL2Const * L) := by simp

/-- **The exact solution solves the three-row scheme's weak form on `V̊ₕ`** (integration by parts
against the fields with vanishing boundary DOFs). -/
theorem inner_exactField₁ (N : ℕ) (t : ℝ) {v : DState3 (whitneyRow N)}
    (hv : v ∈ whitneyInterior3 N) :
    ⟪exactField₁ X t, dEmb3 (whitneyRow N) v⟫ = ⟪exactD X t, dEmb3 (whitneyRow N) v⟫ -
      ⟪exactField X t, dEmb3 (whitneyRow N) (discreteD3 (whitneyRow N) v)⟫ :=
  inner3_of_mem_graph_waveMax (whitneyRow N) rowComplexMin_d_le ((whitneyMin 3 N).window 0 3)
    (U := exactField X t) (U' := exactField₁ X t) (fun r => (X r).mem_graph_waveMax t)
    (fun r => (X r).field_mem_totalDomain t) hv

theorem norm_exactInterp_sub_le (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (hL0 : 0 ≤ L) :
    ‖dEmb3 (whitneyRow N) (exactInterp X N t) - exactField X t‖ ≤
      3 * (rowBound * L * meshSize N) := by
  refine (PiLp.norm_le_sum_norm _).trans ?_
  calc ∑ r : Fin 3, ‖(dEmb3 (whitneyRow N) (exactInterp X N t) - exactField X t) r‖ ≤
        ∑ _r : Fin 3, rowBound * L * meshSize N :=
        Finset.sum_le_sum fun r _ => (X r).norm_interp_sub_le N ht hL0
    _ = 3 * (rowBound * L * meshSize N) := by simp

theorem norm_d_exactInterp_sub_le (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (hL0 : 0 ≤ L) :
    ‖dEmb3 (whitneyRow N) (discreteD3 (whitneyRow N) (exactInterp X N t)) - exactD X t‖ ≤
      3 * (3 * (rowBound * L * meshSize N)) := by
  refine (PiLp.norm_le_sum_norm _).trans ?_
  calc ∑ r : Fin 3, ‖(dEmb3 (whitneyRow N) (discreteD3 (whitneyRow N) (exactInterp X N t)) -
        exactD X t) r‖ ≤ ∑ _r : Fin 3, 3 * (rowBound * L * meshSize N) :=
        Finset.sum_le_sum fun r _ => (X r).norm_d_interp_sub_le N ht hL0
    _ = 3 * (3 * (rowBound * L * meshSize N)) := by simp

theorem norm_exactInterp_sub_sub_le (N : ℕ) {t t' : ℝ} (ht : t ∈ Icc 0 T) (ht' : t' ∈ Icc 0 T)
    (hL0 : 0 ≤ L) :
    ‖(dEmb3 (whitneyRow N) (exactInterp X N t') - exactField X t') -
        (dEmb3 (whitneyRow N) (exactInterp X N t) - exactField X t)‖ ≤
      3 * (rowBound * (L * |t' - t|) * meshSize N) := by
  refine (PiLp.norm_le_sum_norm _).trans ?_
  calc ∑ r : Fin 3, ‖((dEmb3 (whitneyRow N) (exactInterp X N t') - exactField X t') -
        (dEmb3 (whitneyRow N) (exactInterp X N t) - exactField X t)) r‖ ≤
        ∑ _r : Fin 3, rowBound * (L * |t' - t|) * meshSize N :=
        Finset.sum_le_sum fun r _ => (X r).norm_interp_sub_sub_le N ht ht' hL0
    _ = 3 * (rowBound * (L * |t' - t|) * meshSize N) := by simp

/-- **`O(h + Δt²)` convergence of the Crank–Nicolson Whitney scheme with Dirichlet DOFs**
([QuennevilleBelair2015], Ch. 7): let `U = (U_r)_r` be a smooth solution of (4.14) on
`[0, T] × cl Q` (three `RowSolution`s with bound `L`, no boundary condition imposed), and let
`uₙ` be the iterates of the three-row scheme `(P₁)³ × (P₁⁻Λ¹)³ × (P₁⁻Λ²)³` on the level-`(N + 1)`
Freudenthal mesh with step `Δt` (`s = Δt / 2`), started from the canonical interpolant
`u₀ = Π_h U(0)` and with the boundary DOFs of `Π_h U(tₙ)` prescribed at every step (any `gₙ` with
`gₙ − Π_h U(tₙ) ∈ V̊ₕ`). Then for `M Δt ≤ T` the comparison fields `ũₙ` (with the boundary DOFs of
`Π_h U(tₙ)`, `exists_comparison_consistency`) satisfy
`‖u_M − ũ_M‖ ≤ C L (1 + T) (h_N + Δt²)` and the discrete solution satisfies
`‖u_M − U(t_M)‖ ≤ C L (1 + T) (h_N + Δt²)`, with `C = cnConst` independent of `N`, `Δt`, `T`. -/
theorem whitney_cn_error_le (N : ℕ) {Δt : ℝ} (hΔt : 0 < Δt) (hL0 : 0 ≤ L) {M : ℕ}
    (hM : (M : ℝ) * Δt ≤ T) {u g : ℕ → DState3 (whitneyRow N)}
    (hstep : ∀ n < M, TimeStepping.IsDirichletCNStep (whitneyInterior3 N)
      (discreteWave3 (whitneyRow N)) (Δt / 2) 0 (g (n + 1)) (u n) (u (n + 1)))
    (hg : ∀ n < M, g (n + 1) - exactInterp X N ((n + 1 : ℕ) * Δt) ∈ whitneyInterior3 N)
    (hu0 : u 0 = exactInterp X N 0) :
    ∃ ũ : ℕ → DState3 (whitneyRow N),
      (∀ n : ℕ, ũ n - exactInterp X N (n * Δt) ∈ whitneyInterior3 N) ∧
      ‖u M - ũ M‖ ≤ cnConst * L * (1 + T) * (meshSize N + Δt ^ 2) ∧
      ‖dEmb3 (whitneyRow N) (u M) - exactField X (M * Δt)‖ ≤
        cnConst * L * (1 + T) * (meshSize N + Δt ^ 2) := by
  have hh := (meshSize_pos N).le
  have hB := rowBound_nonneg
  have hR := rowL2Const_nonneg
  have hx0 : 0 ≤ rowBound * L * meshSize N := mul_nonneg (mul_nonneg hB hL0) hh
  have hmem : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → (n : ℝ) * Δt ∈ Icc 0 T := fun n hn =>
    ⟨mul_nonneg (Nat.cast_nonneg n) hΔt.le, hn⟩
  have hA3 : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * Δt ≤ T →
      ‖(dEmb3 (whitneyRow N) (exactInterp X N ((n + 1 : ℕ) * Δt)) -
          exactField X ((n + 1 : ℕ) * Δt)) -
        (dEmb3 (whitneyRow N) (exactInterp X N (n * Δt)) - exactField X (n * Δt))‖ ≤
        9 * (rowBound * L * meshSize N) * Δt := by
    intro n hn
    have hn1 : (n : ℝ) * Δt ≤ ((n + 1 : ℕ) : ℝ) * Δt := by push_cast; nlinarith
    have hd : |((n + 1 : ℕ) : ℝ) * Δt - n * Δt| = Δt := by
      rw [show ((n + 1 : ℕ) : ℝ) * Δt - n * Δt = Δt by push_cast; ring, abs_of_pos hΔt]
    have := norm_exactInterp_sub_sub_le X N (hmem n (hn1.trans hn)) (hmem (n + 1) hn) hL0
    rw [hd] at this
    refine this.trans ?_
    have : 0 ≤ rowBound * L * meshSize N * Δt := mul_nonneg hx0 hΔt.le
    nlinarith
  exact norm_cn_error_le_of_eq (emb := dEmb3 (whitneyRow N))
    (D := discreteD3 (whitneyRow N)) (V₀ := whitneyInterior3 N) (A := discreteWave3 (whitneyRow N))
    (T := T) (L₃ := 3 * (rowL2Const * L)) (a := 9 * (rowBound * L * meshSize N))
    (w := fun n => exactInterp X N (n * Δt)) (M := M) (u := u) (g := g) (U := exactField X)
    (U₁ := exactField₁ X) (U₂ := exactField₂ X) (U₃ := exactField₃ X) (DU := exactD X)
    (Δt := Δt) (K := cnConst * L) (h := meshSize N) (inner_dEmb3 (whitneyRow N))
    (fun v hv => discreteD3_mem_interior3 (whitneyRow N) rowComplexMin_d_le
      ((whitneyMin 3 N).window 0 3) hv)
    (fun v _ => discreteD3_discreteD3 (whitneyRow N) v) (inner_discreteWave3 (whitneyRow N)) hΔt
    (fun t _ => (hasDerivAt_exactField X t).hasDerivWithinAt)
    (fun t _ => (hasDerivAt_exactField₁ X t).hasDerivWithinAt)
    (fun t _ => (hasDerivAt_exactField₂ X t).hasDerivWithinAt)
    (fun t ht => norm_exactField₃_le X ht hL0) (fun t _ v hv => inner_exactField₁ X N t hv)
    (fun n hn => (norm_exactInterp_sub_le X N (hmem n hn) hL0).trans (by linarith))
    (fun n hn => (norm_d_exactInterp_sub_le X N (hmem n hn) hL0).trans (by linarith))
    hA3 hM hstep hg (hu0.trans (congrArg (exactInterp X N) (by simp)))
    (by rw [cnConst]; nlinarith [mul_nonneg (mul_nonneg hR hL0) hh])
    (by rw [cnConst]; nlinarith [mul_nonneg hR hL0, mul_nonneg hB hL0])

/-- **`O(h + Δt²)` convergence of the one-row Crank–Nicolson Whitney scheme with Dirichlet
DOFs**: `whitney_cn_error_le` for a single row `P₁Λ⁰ × P₁⁻Λ¹ × P₁⁻Λ²` (the Hodge wave equation
of the de Rham window `HΛ⁰ → HΛ¹ → L²Λ²`): for a smooth `RowSolution` with bound `L`, the
iterates from `u₀ = Π_h U(0)` with the boundary DOFs of `Π_h U(tₙ)` satisfy
`‖u_M − U(t_M)‖ ≤ C L (1 + T) (h_N + Δt²)`, `C = cnConst`. -/
theorem RowSolution.whitney_cn_error_le_row (X : RowSolution T L) (N : ℕ) {Δt : ℝ}
    (hΔt : 0 < Δt) (hL0 : 0 ≤ L) {M : ℕ} (hM : (M : ℝ) * Δt ≤ T)
    {u g : ℕ → DState (whitneyRow N)}
    (hstep : ∀ n < M, TimeStepping.IsDirichletCNStep (whitneyInterior N)
      (discreteWave (whitneyRow N)) (Δt / 2) 0 (g (n + 1)) (u n) (u (n + 1)))
    (hg : ∀ n < M, g (n + 1) - X.interp N ((n + 1 : ℕ) * Δt) ∈ whitneyInterior N)
    (hu0 : u 0 = X.interp N 0) :
    ‖dEmb (whitneyRow N) (u M) - X.field (M * Δt)‖ ≤
      cnConst * L * (1 + T) * (meshSize N + Δt ^ 2) := by
  have hh := (meshSize_pos N).le
  have hB := rowBound_nonneg
  have hR := rowL2Const_nonneg
  have hx0 : 0 ≤ rowBound * L * meshSize N := mul_nonneg (mul_nonneg hB hL0) hh
  have hmem : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → (n : ℝ) * Δt ∈ Icc 0 T := fun n hn =>
    ⟨mul_nonneg (Nat.cast_nonneg n) hΔt.le, hn⟩
  have hA3 : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * Δt ≤ T →
      ‖(dEmb (whitneyRow N) (X.interp N ((n + 1 : ℕ) * Δt)) - X.field ((n + 1 : ℕ) * Δt)) -
        (dEmb (whitneyRow N) (X.interp N (n * Δt)) - X.field (n * Δt))‖ ≤
        3 * (rowBound * L * meshSize N) * Δt := by
    intro n hn
    have hn1 : (n : ℝ) * Δt ≤ ((n + 1 : ℕ) : ℝ) * Δt := by push_cast; nlinarith
    have hd : |((n + 1 : ℕ) : ℝ) * Δt - n * Δt| = Δt := by
      rw [show ((n + 1 : ℕ) : ℝ) * Δt - n * Δt = Δt by push_cast; ring, abs_of_pos hΔt]
    have := X.norm_interp_sub_sub_le N (hmem n (hn1.trans hn)) (hmem (n + 1) hn) hL0
    rw [hd] at this
    refine this.trans ?_
    have : 0 ≤ rowBound * L * meshSize N * Δt := mul_nonneg hx0 hΔt.le
    nlinarith
  obtain ⟨-, -, -, h⟩ := norm_cn_error_le_of_eq (emb := dEmb (whitneyRow N))
    (D := discreteD (whitneyRow N)) (V₀ := whitneyInterior N) (A := discreteWave (whitneyRow N))
    (T := T) (L₃ := rowL2Const * L) (a := 3 * (rowBound * L * meshSize N))
    (w := fun n => X.interp N (n * Δt)) (M := M) (u := u) (g := g) (U := X.field)
    (U₁ := X.field₁) (U₂ := X.field₂) (U₃ := X.field₃)
    (DU := fun t => rowComplex.totalD ⟨X.field t, X.field_mem_totalDomain t⟩)
    (Δt := Δt) (K := cnConst * L) (h := meshSize N) (inner_dEmb (whitneyRow N))
    (fun v hv => discreteD_mem_interior (whitneyRow N) rowComplexMin_d_le
      ((whitneyMin 3 N).window 0 3) hv)
    (fun v _ => discreteD_discreteD (whitneyRow N) v) (inner_discreteWave (whitneyRow N)) hΔt
    (fun t _ => (X.hasDerivAt_field t).hasDerivWithinAt)
    (fun t _ => (X.hasDerivAt_field₁ t).hasDerivWithinAt)
    (fun t _ => (X.hasDerivAt_field₂ t).hasDerivWithinAt)
    (fun t ht => X.norm_field₃_le ht hL0)
    (fun t _ v hv => (inner_of_mem_graph_waveMax (whitneyRow N) rowComplexMin_d_le
      ((whitneyMin 3 N).window 0 3) (X.mem_graph_waveMax t) hv).choose_spec)
    (fun n hn => (X.norm_interp_sub_le N (hmem n hn) hL0).trans (by linarith))
    (fun n hn => X.norm_d_interp_sub_le N (hmem n hn) hL0)
    hA3 hM hstep hg (hu0.trans (congrArg (X.interp N) (by simp)))
    (by rw [cnConst]; nlinarith [mul_nonneg (mul_nonneg hR hL0) hh])
    (by rw [cnConst]; nlinarith [mul_nonneg hR hL0, mul_nonneg hB hL0])
  exact h

end WhitneyError

/-! ## The interior Whitney spaces are nonzero -/

section NeBot

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Mesh

theorem finrank_whitneyMin_pos_of_mesh (N k : ℕ)
    (h : 0 < Module.finrank ℝ ((whitneyElement 3).V₀ (mesh 3 N) (k : ℤ))) :
    0 < Module.finrank ℝ ((whitneyMin 3 N).V (k : ℤ)) :=
  (deRham ℝ 3).minimalSubcomplexOfEq_induction (mesh_domain 3 N) (isOpen_mesh_domain 3 N)
    (isOpen_cubeDomain 3)
    (whitneySubcomplexMin (mesh 3 N) (isOpen_mesh_domain 3 N) (center 3) (strictStar_mesh 3 N))
    (fun _ _ S => 0 < Module.finrank ℝ (S.V (k : ℤ))) h

/-- **The interior Nédélec spaces are nonzero**: `V̊ₕ¹ ≠ 0` on every Freudenthal mesh of the cube
(an edge through the interior carries a degree of freedom,
`Feec.FiniteElement.finrank_whitney_V₀_freudenthalMesh_pos`). -/
theorem whitneyMin_one_ne_bot (N : ℕ) : (whitneyMin 3 N).V ((1 : ℕ) : ℤ) ≠ ⊥ := by
  intro h
  have := finrank_whitneyMin_pos_of_mesh N 1
    (finrank_whitney_V₀_freudenthalMesh_pos (n := 3) (b := 0) (s := 1 / 2) (by norm_num)
      (N := N + 1) le_rfl (by norm_num))
  rw [h, finrank_bot] at this
  exact lt_irrefl 0 this

/-- **`V̊ₕ ≠ 0`** for the three-row Whitney space with vanishing boundary DOFs, on every mesh (a
row with an interior edge function in its `E`-slot). -/
theorem whitneyInterior3_ne_bot (N : ℕ) : whitneyInterior3 N ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (whitneyMin_one_ne_bot N)
  have hvV : v ∈ (whitneyRow N).V 1 := whitneyMin_le_whitney N _ hv
  set x : DState (whitneyRow N) := PiLp.single 2 (1 : Fin 3) ⟨v, hvV⟩
  set u : DState3 (whitneyRow N) := PiLp.single 2 (0 : Fin 3) x
  have hu : u ∈ whitneyInterior3 N := by
    intro r i
    by_cases hr : r = 0
    · subst hr
      by_cases hi : i = 1
      · subst hi
        simpa [u, x] using hv
      · simp [u, x, hi]
    · simp [u, hr]
  intro hbot
  have h0 : u = 0 := by rw [hbot] at hu; exact (Submodule.mem_bot ℝ).1 hu
  have : (u 0 1 : (whitneyRow N).V 1).1 = v := by simp [u, x]
  rw [h0] at this
  exact hv0 (by simpa using this.symm)

end NeBot

/-! ## The constraint monitors of the discrete solution -/

section Monitors

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.ExteriorFibre HilbertComplex

/-- The entry `E_{rj}` of a three-row field in `(L²Λ⁰ × L²Λ¹ × L²Λ²)³` (the ambient version of
`entryE`). -/
def entryE' (r j : Fin 3) : (PiLp 2 fun _ : Fin 3 => RowSpace) →ₗ[ℝ] L2 ℝ (cubeDomain 3) where
  toFun y := (y r 1 : L2F ℝ (cubeDomain 3) _) (edgeIdx j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The entry `B_{rj}` (vector proxy of the `2`-form of row `r`) of a three-row field. -/
def entryB' (r j : Fin 3) : (PiLp 2 fun _ : Fin 3 => RowSpace) →ₗ[ℝ] L2 ℝ (cubeDomain 3) where
  toFun y := faceSign j • (y r 2 : L2F ℝ (cubeDomain 3) _) (faceIdx j)
  map_add' _ _ := by simp
  map_smul' a _ := by simp [smul_comm a]

/-- The field `σ` of a three-row field. -/
def sigmaPart' : (PiLp 2 fun _ : Fin 3 => RowSpace) →ₗ[ℝ]
    PiLp 2 fun _ : Fin 3 => L2F ℝ (cubeDomain 3) (formIdx 3 ((0 : ℤ) + ((0 : Fin 3) : ℕ))) where
  toFun y := WithLp.toLp 2 fun r => y r 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem norm_sigmaPart_eq (N : ℕ) (u : DState3 (whitneyRow N)) :
    ‖sigmaPart N u‖ = ‖sigmaPart' (dEmb3 (whitneyRow N) u)‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  rfl

theorem sum_norm_entryE'_sq_le (y : PiLp 2 fun _ : Fin 3 => RowSpace) :
    ∑ r, ∑ j, ‖entryE' r j y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_le_sum fun r _ => ?_
  have h1 := PiLp.sum_norm_sq_comp_le (y r 1 : L2F ℝ (cubeDomain 3) _) edgeIdx_injective
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (y r) 1) 2
  exact h1.trans h2

theorem sum_norm_entryB'_sq_le (y : PiLp 2 fun _ : Fin 3 => RowSpace) :
    ∑ r, ∑ j, ‖entryB' r j y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_le_sum fun r _ => ?_
  have h1 := PiLp.sum_norm_sq_comp_le (y r 2 : L2F ℝ (cubeDomain 3) _) faceIdx_injective
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (y r) 2) 2
  have hs : ∀ j, ‖entryB' r j y‖ = ‖(y r 2 : L2F ℝ (cubeDomain 3) _) (faceIdx j)‖ := fun j => by
    simp [entryB', faceSign, norm_smul]
  simp only [hs]
  exact h1.trans h2

theorem norm_sigmaPart'_le (y : PiLp 2 fun _ : Fin 3 => RowSpace) : ‖sigmaPart' y‖ ≤ ‖y‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum fun r _ =>
    pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (y r) 0) 2

variable {T L : ℝ}

/-- **A TSD state of the three-row form model** at time `t`: `σ = 0`, and the matrices
`E_{rj}` (component `dx_j` of the `1`-form of row `r`) and `B_{rj} = (−1)^j ω_{{j}ᶜ}` (vector
proxy of the `2`-form of row `r`) are symmetric and trace-free, pointwise. -/
structure IsTSDAt (X : Fin 3 → RowSolution T L) (t : ℝ) : Prop where
  sigma : ∀ r y s, (X r).u t 0 y s = 0
  symm_E : ∀ r j y, (X r).u t 1 y {j} = (X j).u t 1 y {r}
  trace_E : ∀ y, ∑ r, (X r).u t 1 y {r} = 0
  symm_B : ∀ r j y, faceSign j * (X r).u t 2 y {j}ᶜ = faceSign r * (X j).u t 2 y {r}ᶜ
  trace_B : ∀ y, ∑ r, faceSign r * (X r).u t 2 y {r}ᶜ = 0

variable (X : Fin 3 → RowSolution T L)

theorem entryE'_exactField (t : ℝ) (r j : Fin 3) :
    entryE' r j (exactField X t) =
      (memLp_of_continuous (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3)
        (show Continuous fun y => (X r).u t 1 y {j} from
          (continuous_apply _).comp ((X r).continuous t 1))).toLp
        (fun y => (X r).u t 1 y {j}) := rfl

theorem entryB'_exactField (t : ℝ) (r j : Fin 3) :
    entryB' r j (exactField X t) =
      (memLp_of_continuous (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3)
        (show Continuous fun y => faceSign j * (X r).u t 2 y {j}ᶜ from
          continuous_const.mul ((continuous_apply _).comp ((X r).continuous t 2)))).toLp
        (fun y => faceSign j * (X r).u t 2 y {j}ᶜ) := by
  change faceSign j • (memLp_of_continuous (isOpen_cubeDomain 3).measurableSet
    (isBounded_cubeDomain 3) (show Continuous fun y => (X r).u t 2 y {j}ᶜ from
      (continuous_apply _).comp ((X r).continuous t 2))).toLp (fun y => (X r).u t 2 y {j}ᶜ) = _
  rw [← MemLp.toLp_const_smul]
  rfl

theorem toLp_sum_three_eq_zero {f : Fin 3 → (Fin 3 → ℝ) → ℝ}
    (hf : ∀ r, MemLp (f r) 2 (volume.restrict (cubeDomain 3))) (h : ∀ y, ∑ r, f r y = 0) :
    ∑ r, (hf r).toLp (f r) = 0 := by
  rw [Fin.sum_univ_three, ← MemLp.toLp_add, ← MemLp.toLp_add]
  refine (MemLp.toLp_congr _ MemLp.zero (Eventually.of_forall fun y => ?_)).trans
    (MemLp.toLp_zero _)
  have := h y
  rw [Fin.sum_univ_three] at this
  simpa using this

/-- The five `fem4gr` monitors vanish on a TSD state. -/
theorem monitors_exactField_eq_zero {t : ℝ} (hX : IsTSDAt X t) :
    skewPart entryE' (exactField X t) = 0 ∧ skewPart entryB' (exactField X t) = 0 ∧
      tracePart entryE' (exactField X t) = 0 ∧ tracePart entryB' (exactField X t) = 0 ∧
      sigmaPart' (exactField X t) = 0 := by
  refine ⟨PiLp.ext fun p => ?_, PiLp.ext fun p => ?_, ?_, ?_,
    PiLp.ext fun r => PiLp.ext fun s => ?_⟩
  · change (1 / 2 : ℝ) • (entryE' p.1 p.2 (exactField X t) - entryE' p.2 p.1 (exactField X t)) = _
    have hE : entryE' p.1 p.2 (exactField X t) = entryE' p.2 p.1 (exactField X t) := by
      rw [entryE'_exactField, entryE'_exactField]
      exact MemLp.toLp_congr _ _ (Eventually.of_forall fun y => hX.symm_E p.1 p.2 y)
    rw [hE, sub_self, smul_zero]
    rfl
  · change (1 / 2 : ℝ) • (entryB' p.1 p.2 (exactField X t) - entryB' p.2 p.1 (exactField X t)) = _
    have hB : entryB' p.1 p.2 (exactField X t) = entryB' p.2 p.1 (exactField X t) := by
      rw [entryB'_exactField, entryB'_exactField]
      exact MemLp.toLp_congr _ _ (Eventually.of_forall fun y => hX.symm_B p.1 p.2 y)
    rw [hB, sub_self, smul_zero]
    rfl
  · simp only [tracePart, LinearMap.smul_apply, LinearMap.sum_apply, entryE'_exactField]
    rw [toLp_sum_three_eq_zero _ hX.trace_E, smul_zero]
  · simp only [tracePart, LinearMap.smul_apply, LinearMap.sum_apply, entryB'_exactField]
    rw [toLp_sum_three_eq_zero _ hX.trace_B, smul_zero]
  · change formL2Q _ ((X r).u t 0) _ s = 0
    exact (MemLp.toLp_congr (memLp_of_continuous (isOpen_cubeDomain 3).measurableSet
      (isBounded_cubeDomain 3) (continuous_formComp ((X r).continuous t 0) s)) MemLp.zero
      (Eventually.of_forall fun y => hX.sigma r y s.1)).trans (MemLp.toLp_zero _)

theorem skewPart_entryE_eq (N : ℕ) (u : DState3 (whitneyRow N)) :
    skewPart (entryE N) u = skewPart entryE' (dEmb3 (whitneyRow N) u) := rfl

theorem skewPart_entryB_eq (N : ℕ) (u : DState3 (whitneyRow N)) :
    skewPart (entryB N) u = skewPart entryB' (dEmb3 (whitneyRow N) u) := rfl

theorem tracePart_entryE_eq (N : ℕ) (u : DState3 (whitneyRow N)) :
    tracePart (entryE N) u = tracePart entryE' (dEmb3 (whitneyRow N) u) := by
  simp only [tracePart, LinearMap.smul_apply, LinearMap.sum_apply]; rfl

theorem tracePart_entryB_eq (N : ℕ) (u : DState3 (whitneyRow N)) :
    tracePart (entryB N) u = tracePart entryB' (dEmb3 (whitneyRow N) u) := by
  simp only [tracePart, LinearMap.smul_apply, LinearMap.sum_apply]; rfl

theorem norm_le_of_map_eq_zero {Y Z : Type*} [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    [SeminormedAddCommGroup Z] [NormedSpace ℝ Z] {c : Y →ₗ[ℝ] Z} (hc : ∀ y, ‖c y‖ ≤ ‖y‖)
    {x U : Y} (hU : c U = 0) : ‖c x‖ ≤ ‖x - U‖ := by
  have : c x = c (x - U) := by rw [map_sub, hU, sub_zero]
  rw [this]; exact hc _

/-- Each monitor of a discrete field is at most its distance to a TSD exact state. -/
theorem norm_monitors_le_of_isTSDAt (N : ℕ) (u : DState3 (whitneyRow N)) {t : ℝ}
    (hX : IsTSDAt X t) :
    ‖skewPart (entryE N) u‖ ≤ ‖dEmb3 (whitneyRow N) u - exactField X t‖ ∧
      ‖skewPart (entryB N) u‖ ≤ ‖dEmb3 (whitneyRow N) u - exactField X t‖ ∧
      ‖tracePart (entryE N) u‖ ≤ ‖dEmb3 (whitneyRow N) u - exactField X t‖ ∧
      ‖tracePart (entryB N) u‖ ≤ ‖dEmb3 (whitneyRow N) u - exactField X t‖ ∧
      ‖sigmaPart N u‖ ≤ ‖dEmb3 (whitneyRow N) u - exactField X t‖ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := monitors_exactField_eq_zero X hX
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [skewPart_entryE_eq]
    exact norm_le_of_map_eq_zero (norm_skewPart_le sum_norm_entryE'_sq_le) h1
  · rw [skewPart_entryB_eq]
    exact norm_le_of_map_eq_zero (norm_skewPart_le sum_norm_entryB'_sq_le) h2
  · rw [tracePart_entryE_eq]
    exact norm_le_of_map_eq_zero (norm_tracePart_le sum_norm_entryE'_sq_le) h3
  · rw [tracePart_entryB_eq]
    exact norm_le_of_map_eq_zero (norm_tracePart_le sum_norm_entryB'_sq_le) h4
  · rw [norm_sigmaPart_eq]
    exact norm_le_of_map_eq_zero norm_sigmaPart'_le h5

/-- **The `fem4gr` constraint monitors are `O(h + Δt²)` for TSD exact solutions**
([QuennevilleBelair2015], Ch. 7): in the setting of `whitney_cn_error_le`, if the exact solution
is TSD at `t_M` (`σ = 0`, `E`, `B` symmetric and trace-free), then "Skew of E/B" `½ (E − Eᵀ)`,
`½ (B − Bᵀ)`, "Trace of E/B" `tr E / √3`, `tr B / √3` and "Sigma Zero" `σ` of the discrete
solution `u_M` are all at most `C L (1 + T) (h_N + Δt²)`. -/
theorem whitney_cn_monitors_le (N : ℕ) {Δt : ℝ} (hΔt : 0 < Δt) (hL0 : 0 ≤ L) {M : ℕ}
    (hM : (M : ℝ) * Δt ≤ T) {u g : ℕ → DState3 (whitneyRow N)}
    (hstep : ∀ n < M, TimeStepping.IsDirichletCNStep (whitneyInterior3 N)
      (discreteWave3 (whitneyRow N)) (Δt / 2) 0 (g (n + 1)) (u n) (u (n + 1)))
    (hg : ∀ n < M, g (n + 1) - exactInterp X N ((n + 1 : ℕ) * Δt) ∈ whitneyInterior3 N)
    (hu0 : u 0 = exactInterp X N 0) (hX : IsTSDAt X (M * Δt)) :
    ‖skewPart (entryE N) (u M)‖ ≤ cnConst * L * (1 + T) * (meshSize N + Δt ^ 2) ∧
      ‖skewPart (entryB N) (u M)‖ ≤ cnConst * L * (1 + T) * (meshSize N + Δt ^ 2) ∧
      ‖tracePart (entryE N) (u M)‖ ≤ cnConst * L * (1 + T) * (meshSize N + Δt ^ 2) ∧
      ‖tracePart (entryB N) (u M)‖ ≤ cnConst * L * (1 + T) * (meshSize N + Δt ^ 2) ∧
      ‖sigmaPart N (u M)‖ ≤ cnConst * L * (1 + T) * (meshSize N + Δt ^ 2) := by
  obtain ⟨-, -, -, herr⟩ := whitney_cn_error_le X N hΔt hL0 hM hstep hg hu0
  obtain ⟨h1, h2, h3, h4, h5⟩ := norm_monitors_le_of_isTSDAt X N (u M) hX
  exact ⟨h1.trans herr, h2.trans herr, h3.trans herr, h4.trans herr, h5.trans herr⟩

end Monitors

/-! ## Whole-space TSD solutions as rows of forms -/

section MatrixRows

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.ExteriorFibre HilbertComplex
  Feec.Models.BoundedDomain

/-- The `1`-form `Σⱼ vⱼ dxⱼ` of a vector field (row `r` of a matrix field). -/
def oneForm (v : Fin 3 → (Fin 3 → ℝ) → ℝ) : FormField 3 := fun y s =>
  ∑ j, if s = {j} then v j y else 0
/-- The `2`-form with vector proxy `v` (`ω_{{j}ᶜ} = (−1)ʲ vⱼ`, `faceSign`). -/
def twoForm (v : Fin 3 → (Fin 3 → ℝ) → ℝ) : FormField 3 := fun y s =>
  ∑ j, if s = {j}ᶜ then faceSign j * v j y else 0
/-- The curl `(curl v)ₖ = ∂ₖ₊₁ vₖ₊₂ − ∂ₖ₊₂ vₖ₊₁` of a vector field. -/
def curlV (v : Fin 3 → (Fin 3 → ℝ) → ℝ) (k : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  partialDeriv (k + 1) (v (k + 2)) y - partialDeriv (k + 2) (v (k + 1)) y

theorem finset_fin3_cases (s : Finset (Fin 3)) : s = ∅ ∨ s = {0} ∨ s = {1} ∨ s = {2} ∨
    s = {0, 1} ∨ s = {0, 2} ∨ s = {1, 2} ∨ s = {0, 1, 2} := by
  revert s; decide

theorem compl_fin3 : ({0}ᶜ : Finset (Fin 3)) = {1, 2} ∧ ({1}ᶜ : Finset (Fin 3)) = {0, 2} ∧
    ({2}ᶜ : Finset (Fin 3)) = {0, 1} ∧ ({0, 1}ᶜ : Finset (Fin 3)) = {2} ∧
    ({0, 2}ᶜ : Finset (Fin 3)) = {1} ∧ ({1, 2}ᶜ : Finset (Fin 3)) = {0} ∧
    (∅ᶜ : Finset (Fin 3)) = {0, 1, 2} ∧ ({0, 1, 2}ᶜ : Finset (Fin 3)) = ∅ := by decide

theorem extDeriv_oneForm (v : Fin 3 → (Fin 3 → ℝ) → ℝ) :
    extDeriv (oneForm v) = twoForm (curlV v) := by
  funext y s
  simp only [extDeriv_apply, oneForm, twoForm, curlV]
  rcases finset_fin3_cases s with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [Fin.sum_univ_three, sgn, faceSign, partialDeriv] <;>
    ring_nf

theorem extDeriv_twoForm (v : Fin 3 → (Fin 3 → ℝ) → ℝ) :
    extDeriv (twoForm v) = fun y s => if s = Finset.univ then ∑ j,
      partialDeriv j (v j) y else 0 := by
  funext y s
  simp only [extDeriv_apply, twoForm]
  rcases finset_fin3_cases s with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [Fin.sum_univ_three, sgn, faceSign, partialDeriv]
  ring_nf

theorem formalAdjD_twoForm (v : Fin 3 → (Fin 3 → ℝ) → ℝ) :
    formalAdjD (twoForm v) = oneForm (curlV v) := by
  funext y s
  simp only [formalAdjD, extDAdj, oneForm, twoForm, curlV]
  rcases finset_fin3_cases s with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [Fin.sum_univ_three, sgn, faceSign, partialDeriv,
      compl_fin3] <;>
    ring_nf

theorem formalAdjD_oneForm (v : Fin 3 → (Fin 3 → ℝ) → ℝ) :
    formalAdjD (oneForm v) = fun y s => if s = ∅ then -∑ j, partialDeriv j (v j) y else 0 := by
  funext y s
  simp only [formalAdjD, extDAdj, oneForm]
  rcases finset_fin3_cases s with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [Fin.sum_univ_three, sgn, partialDeriv, compl_fin3]

theorem oneForm_neg (v : Fin 3 → (Fin 3 → ℝ) → ℝ) :
    oneForm (fun j y => -v j y) = -oneForm v := by
  funext y s
  simp only [oneForm, Pi.neg_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp

theorem oneForm_sub (v w : Fin 3 → (Fin 3 → ℝ) → ℝ) :
    oneForm (fun j y => v j y - w j y) = oneForm v - oneForm w := by
  funext y s
  simp only [oneForm, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp

theorem twoForm_sub (v w : Fin 3 → (Fin 3 → ℝ) → ℝ) :
    twoForm (fun j y => v j y - w j y) = twoForm v - twoForm w := by
  funext y s
  simp only [twoForm, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp [mul_sub]

theorem oneForm_apply_singleton (v : Fin 3 → (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) (j : Fin 3) :
    oneForm v y {j} = v j y := by
  simp [oneForm, Finset.singleton_inj]

theorem twoForm_apply_compl (v : Fin 3 → (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) (j : Fin 3) :
    twoForm v y {j}ᶜ = faceSign j * v j y := by
  simp [twoForm, Finset.singleton_inj]

theorem abs_faceSign (j : Fin 3) : |faceSign j| = 1 := by simp [faceSign]

/-- The component functions of `oneForm v`: `v j` at `{j}`, `0` elsewhere. -/
theorem oneForm_comp (v : Fin 3 → (Fin 3 → ℝ) → ℝ) (s : Finset (Fin 3)) :
    (∃ j, s = {j} ∧ (fun y => oneForm v y s) = v j) ∨ (fun y => oneForm v y s) = 0 := by
  by_cases h : ∃ j, s = {j}
  · obtain ⟨j, rfl⟩ := h
    exact Or.inl ⟨j, rfl, funext fun y => oneForm_apply_singleton v y j⟩
  · refine Or.inr (funext fun y => Finset.sum_eq_zero fun j _ => ?_)
    simp [show ¬ s = {j} from fun hs => h ⟨j, hs⟩]

theorem twoForm_comp (v : Fin 3 → (Fin 3 → ℝ) → ℝ) (s : Finset (Fin 3)) :
    (∃ j, s = {j}ᶜ ∧ (fun y => twoForm v y s) = fun y => faceSign j * v j y) ∨
      (fun y => twoForm v y s) = 0 := by
  by_cases h : ∃ j, s = {j}ᶜ
  · obtain ⟨j, rfl⟩ := h
    exact Or.inl ⟨j, rfl, funext fun y => twoForm_apply_compl v y j⟩
  · refine Or.inr (funext fun y => Finset.sum_eq_zero fun j _ => ?_)
    simp [show ¬ s = {j}ᶜ from fun hs => h ⟨j, hs⟩]

theorem isDeg_oneForm (v : Fin 3 → (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) : IsDeg 1 (oneForm v y) :=
  fun s hs => Finset.sum_eq_zero fun j _ => by
    simp [show ¬ s = {j} from fun h => hs (by rw [h, Finset.card_singleton])]

theorem isDeg_twoForm (v : Fin 3 → (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) : IsDeg 2 (twoForm v y) :=
  fun s hs => Finset.sum_eq_zero fun j _ => by
    simp [show ¬ s = {j}ᶜ from fun h => hs (by
      rw [h, Finset.card_compl, Finset.card_singleton]; rfl)]

theorem contDiff_oneForm {m : WithTop ℕ∞} {v : Fin 3 → (Fin 3 → ℝ) → ℝ}
    (hv : ∀ j, ContDiff ℝ m (v j)) : ContDiff ℝ m (oneForm v) :=
  contDiff_pi.2 fun s => ContDiff.sum fun j _ => by
    by_cases h : s = {j}
    · simpa [h] using hv j
    · simpa [h] using (contDiff_const : ContDiff ℝ m fun _ : Fin 3 → ℝ => (0 : ℝ))

theorem contDiff_twoForm {m : WithTop ℕ∞} {v : Fin 3 → (Fin 3 → ℝ) → ℝ}
    (hv : ∀ j, ContDiff ℝ m (v j)) : ContDiff ℝ m (twoForm v) :=
  contDiff_pi.2 fun s => ContDiff.sum fun j _ => by
    by_cases h : s = {j}ᶜ
    · simpa [h] using contDiff_const.mul (hv j)
    · simpa [h] using (contDiff_const : ContDiff ℝ m fun _ : Fin 3 → ℝ => (0 : ℝ))

/-- `‖D F‖ ≤ L` for a form field whose components have `‖D Fₛ‖ ≤ L`. -/
theorem norm_fderiv_form_le {F : FormField 3} {y : Fin 3 → ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (hd : ∀ s, DifferentiableAt ℝ (fun z => F z s) y)
    (h : ∀ s, ‖fderiv ℝ (fun z => F z s) y‖ ≤ L) : ‖fderiv ℝ F y‖ ≤ L := by
  have e : fderiv ℝ F y = ContinuousLinearMap.pi fun s => fderiv ℝ (fun z => F z s) y :=
    fderiv_pi (φ := fun s z => F z s) hd
  rw [e]
  exact ContinuousLinearMap.norm_pi_le_of_le h hL0

theorem norm_fderiv_oneForm_le {v : Fin 3 → (Fin 3 → ℝ) → ℝ} {y : Fin 3 → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L) (hd : ∀ j, DifferentiableAt ℝ (v j) y) (h : ∀ j, ‖fderiv ℝ (v j) y‖ ≤ L) :
    ‖fderiv ℝ (oneForm v) y‖ ≤ L := by
  refine norm_fderiv_form_le hL0 (fun s => ?_) fun s => ?_
  · rcases oneForm_comp v s with ⟨j, -, hj⟩ | h0
    · rw [hj]; exact hd j
    · rw [h0]; exact differentiableAt_const _
  · rcases oneForm_comp v s with ⟨j, -, hj⟩ | h0
    · rw [hj]; exact h j
    · rw [h0]
      simpa using hL0

theorem norm_fderiv_twoForm_le {v : Fin 3 → (Fin 3 → ℝ) → ℝ} {y : Fin 3 → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L) (hd : ∀ j, DifferentiableAt ℝ (v j) y) (h : ∀ j, ‖fderiv ℝ (v j) y‖ ≤ L) :
    ‖fderiv ℝ (twoForm v) y‖ ≤ L := by
  refine norm_fderiv_form_le hL0 (fun s => ?_) fun s => ?_
  · rcases twoForm_comp v s with ⟨j, -, hj⟩ | h0
    · rw [hj]; exact (hd j).const_mul _
    · rw [h0]; exact differentiableAt_const _
  · rcases twoForm_comp v s with ⟨j, -, hj⟩ | h0
    · rw [hj, fderiv_const_mul (hd j), norm_smul, Real.norm_eq_abs, abs_faceSign, one_mul]
      exact h j
    · rw [h0]
      simpa using hL0

end MatrixRows

/-! ## Whole-space TSD solutions with bounded derivatives -/

section SmoothTSD

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.ExteriorFibre HilbertComplex
  Feec.Models.BoundedDomain

/-- **Bounded higher derivatives of a whole-space TSD solution on `[0, T] × cl Q`**: `C²` in space,
`C³` in time (the second and third time derivatives `E₂, E₃, B₂, B₃` jointly continuous), with
`‖D E‖, ‖D curl E‖, ‖D B‖, ‖D curl B‖ ≤ L` on `cl Q`, these `L`-Lipschitz in `t ∈ [0, T]`, and
`|∂ₜ³ E|, |∂ₜ³ B| ≤ L` on `Q`. (The plane wave of Ch. 7 has them,
`Feec.Numerics.PlaneWaveCube`.) -/
structure WholeSpaceTSD.Smooth (W : WholeSpaceTSD) (T L : ℝ) where
  /-- the second and third time derivatives -/
  E₂ : ℝ → Ix → (Fin 3 → ℝ) → ℝ
  E₃ : ℝ → Ix → (Fin 3 → ℝ) → ℝ
  B₂ : ℝ → Ix → (Fin 3 → ℝ) → ℝ
  B₃ : ℝ → Ix → (Fin 3 → ℝ) → ℝ
  contDiff_E : ∀ t ij, ContDiff ℝ 2 (W.E t ij)
  contDiff_B : ∀ t ij, ContDiff ℝ 2 (W.B t ij)
  continuous_E₂ : ∀ ij, Continuous fun p : ℝ × (Fin 3 → ℝ) => E₂ p.1 ij p.2
  continuous_E₃ : ∀ ij, Continuous fun p : ℝ × (Fin 3 → ℝ) => E₃ p.1 ij p.2
  continuous_B₂ : ∀ ij, Continuous fun p : ℝ × (Fin 3 → ℝ) => B₂ p.1 ij p.2
  continuous_B₃ : ∀ ij, Continuous fun p : ℝ × (Fin 3 → ℝ) => B₃ p.1 ij p.2
  hasDerivAt_E₁ : ∀ t ij x, HasDerivAt (fun s => -curlM (W.B s) ij x) (E₂ t ij x) t
  hasDerivAt_E₂ : ∀ t ij x, HasDerivAt (fun s => E₂ s ij x) (E₃ t ij x) t
  hasDerivAt_B₁ : ∀ t ij x, HasDerivAt (fun s => curlM (W.E s) ij x) (B₂ t ij x) t
  hasDerivAt_B₂ : ∀ t ij x, HasDerivAt (fun s => B₂ s ij x) (B₃ t ij x) t
  bound : ∀ t ∈ Icc 0 T, ∀ ij, ∀ y ∈ closure (cubeDomain 3),
    ‖fderiv ℝ (W.E t ij) y‖ ≤ L ∧ ‖fderiv ℝ (curlM (W.E t) ij) y‖ ≤ L ∧
      ‖fderiv ℝ (W.B t ij) y‖ ≤ L ∧ ‖fderiv ℝ (curlM (W.B t) ij) y‖ ≤ L
  lipschitz : ∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T, ∀ ij, ∀ y ∈ closure (cubeDomain 3),
    ‖fderiv ℝ (W.E t' ij) y - fderiv ℝ (W.E t ij) y‖ ≤ L * |t' - t| ∧
      ‖fderiv ℝ (curlM (W.E t') ij) y - fderiv ℝ (curlM (W.E t) ij) y‖ ≤ L * |t' - t| ∧
      ‖fderiv ℝ (W.B t' ij) y - fderiv ℝ (W.B t ij) y‖ ≤ L * |t' - t| ∧
      ‖fderiv ℝ (curlM (W.B t') ij) y - fderiv ℝ (curlM (W.B t) ij) y‖ ≤ L * |t' - t|
  bound₃ : ∀ t ∈ Icc 0 T, ∀ ij, ∀ y ∈ cubeDomain 3, |E₃ t ij y| ≤ L ∧ |B₃ t ij y| ≤ L

namespace WholeSpaceTSD

variable {W : WholeSpaceTSD} {T L : ℝ}

theorem contDiff_curlM {Φ : Ix → (Fin 3 → ℝ) → ℝ} (hΦ : ∀ ij, ContDiff ℝ 2 (Φ ij)) (ij : Ix) :
    ContDiff ℝ 1 (curlM Φ ij) :=
  ((hΦ _).partialDeriv (m := 1) (by norm_num) _).sub ((hΦ _).partialDeriv (m := 1) (by norm_num) _)

/-- Row `r` of a whole-space TSD solution as forms `(0, E_r, B_r)`. -/
def rowForms (E B : Ix → (Fin 3 → ℝ) → ℝ) (r : Fin 3) : Fin 3 → FormField 3 :=
  ![0, oneForm fun j => E (r, j), twoForm fun j => B (r, j)]

theorem hasDerivAt_oneForm {E E' : ℝ → Ix → (Fin 3 → ℝ) → ℝ} {r : Fin 3} {t : ℝ} {y : Fin 3 → ℝ}
    (h : ∀ j, HasDerivAt (fun s => E s (r, j) y) (E' t (r, j) y) t) (s : Finset (Fin 3)) :
    HasDerivAt (fun τ => oneForm (fun j => E τ (r, j)) y s)
      (oneForm (fun j => E' t (r, j)) y s) t := by
  simp only [oneForm]
  refine HasDerivAt.fun_sum fun j _ => ?_
  by_cases hs : s = {j}
  · simpa [hs] using h j
  · simpa [hs] using hasDerivAt_const t (0 : ℝ)

theorem hasDerivAt_twoForm {B B' : ℝ → Ix → (Fin 3 → ℝ) → ℝ} {r : Fin 3} {t : ℝ} {y : Fin 3 → ℝ}
    (h : ∀ j, HasDerivAt (fun s => B s (r, j) y) (B' t (r, j) y) t) (s : Finset (Fin 3)) :
    HasDerivAt (fun τ => twoForm (fun j => B τ (r, j)) y s)
      (twoForm (fun j => B' t (r, j)) y s) t := by
  simp only [twoForm]
  refine HasDerivAt.fun_sum fun j _ => ?_
  by_cases hs : s = {j}ᶜ
  · simpa [hs] using (h j).const_mul (faceSign j)
  · simpa [hs] using hasDerivAt_const t (0 : ℝ)

theorem continuous_oneForm_joint {E : ℝ → Ix → (Fin 3 → ℝ) → ℝ} {r : Fin 3}
    (h : ∀ ij, Continuous fun p : ℝ × (Fin 3 → ℝ) => E p.1 ij p.2) (s : Finset (Fin 3)) :
    Continuous fun p : ℝ × (Fin 3 → ℝ) => oneForm (fun j => E p.1 (r, j)) p.2 s := by
  simp only [oneForm]
  refine continuous_finsetSum _ fun j _ => ?_
  by_cases hs : s = {j}
  · simpa [hs] using h (r, j)
  · simpa [hs] using continuous_const

theorem continuous_twoForm_joint {B : ℝ → Ix → (Fin 3 → ℝ) → ℝ} {r : Fin 3}
    (h : ∀ ij, Continuous fun p : ℝ × (Fin 3 → ℝ) => B p.1 ij p.2) (s : Finset (Fin 3)) :
    Continuous fun p : ℝ × (Fin 3 → ℝ) => twoForm (fun j => B p.1 (r, j)) p.2 s := by
  simp only [twoForm]
  refine continuous_finsetSum _ fun j _ => ?_
  by_cases hs : s = {j}ᶜ
  · simp only [hs, ↓reduceIte]
    exact continuous_const.mul (h (r, j))
  · simpa [hs] using continuous_const

end WholeSpaceTSD


namespace WholeSpaceTSD.Smooth

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.ExteriorFibre HilbertComplex
  Feec.Models.BoundedDomain

variable {W : WholeSpaceTSD} {T L : ℝ} (S : W.Smooth T L)

theorem extDeriv_zero : extDeriv (0 : FormField 3) = 0 := extDeriv_const (0 : Finset (Fin 3) → ℝ)

theorem extDeriv_twoForm_B (t : ℝ) (r : Fin 3) :
    extDeriv (twoForm fun j => W.B t (r, j)) = 0 := by
  rw [extDeriv_twoForm]
  funext y s
  simp [W.div_B t r y]

theorem norm_fderiv_oneForm_sub_le {v w : Fin 3 → (Fin 3 → ℝ) → ℝ} {y : Fin 3 → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L) (hv : ∀ j, DifferentiableAt ℝ (v j) y) (hw : ∀ j, DifferentiableAt ℝ (w j) y)
    (h : ∀ j, ‖fderiv ℝ (v j) y - fderiv ℝ (w j) y‖ ≤ L) :
    ‖fderiv ℝ (oneForm v) y - fderiv ℝ (oneForm w) y‖ ≤ L := by
  have hdv : DifferentiableAt ℝ (oneForm v) y := differentiableAt_pi.2 fun s => by
    rcases oneForm_comp v s with ⟨j, -, hj⟩ | h0
    · rw [hj]; exact hv j
    · rw [h0]; exact differentiableAt_const _
  have hdw : DifferentiableAt ℝ (oneForm w) y := differentiableAt_pi.2 fun s => by
    rcases oneForm_comp w s with ⟨j, -, hj⟩ | h0
    · rw [hj]; exact hw j
    · rw [h0]; exact differentiableAt_const _
  rw [← fderiv_sub hdv hdw, ← oneForm_sub]
  refine norm_fderiv_oneForm_le hL0 (fun j => (hv j).sub (hw j)) fun j => ?_
  rw [fderiv_fun_sub (hv j) (hw j)]
  exact h j

theorem norm_fderiv_twoForm_sub_le {v w : Fin 3 → (Fin 3 → ℝ) → ℝ} {y : Fin 3 → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L) (hv : ∀ j, DifferentiableAt ℝ (v j) y) (hw : ∀ j, DifferentiableAt ℝ (w j) y)
    (h : ∀ j, ‖fderiv ℝ (v j) y - fderiv ℝ (w j) y‖ ≤ L) :
    ‖fderiv ℝ (twoForm v) y - fderiv ℝ (twoForm w) y‖ ≤ L := by
  have hdv : DifferentiableAt ℝ (twoForm v) y := differentiableAt_pi.2 fun s => by
    rcases twoForm_comp v s with ⟨j, -, hj⟩ | h0
    · rw [hj]; exact (hv j).const_mul _
    · rw [h0]; exact differentiableAt_const _
  have hdw : DifferentiableAt ℝ (twoForm w) y := differentiableAt_pi.2 fun s => by
    rcases twoForm_comp w s with ⟨j, -, hj⟩ | h0
    · rw [hj]; exact (hw j).const_mul _
    · rw [h0]; exact differentiableAt_const _
  rw [← fderiv_sub hdv hdw, ← twoForm_sub]
  refine norm_fderiv_twoForm_le hL0 (fun j => (hv j).sub (hw j)) fun j => ?_
  rw [fderiv_fun_sub (hv j) (hw j)]
  exact h j

theorem abs_oneForm_le {v : Fin 3 → (Fin 3 → ℝ) → ℝ} {y : Fin 3 → ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (h : ∀ j, |v j y| ≤ L) (s : Finset (Fin 3)) : |oneForm v y s| ≤ L := by
  rcases oneForm_comp v s with ⟨j, -, hj⟩ | h0
  · rw [show oneForm v y s = v j y from congrFun hj y]; exact h j
  · rw [show oneForm v y s = 0 from congrFun h0 y, abs_zero]; exact hL0

theorem abs_twoForm_le {v : Fin 3 → (Fin 3 → ℝ) → ℝ} {y : Fin 3 → ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (h : ∀ j, |v j y| ≤ L) (s : Finset (Fin 3)) : |twoForm v y s| ≤ L := by
  rcases twoForm_comp v s with ⟨j, -, hj⟩ | h0
  · rw [show twoForm v y s = faceSign j * v j y from congrFun hj y, abs_mul, abs_faceSign,
      one_mul]
    exact h j
  · rw [show twoForm v y s = 0 from congrFun h0 y, abs_zero]; exact hL0

/-- **Row `r` of a whole-space TSD solution with bounded derivatives is a smooth row solution**
on `[0, T] × cl Q`: `(σ_r, E_r, B_r) = (0, Σⱼ E_{rj} dxⱼ, Σⱼ (−1)ʲ B_{rj} dx_{{j}ᶜ})`. -/
def row (hL0 : 0 ≤ L) (r : Fin 3) : RowSolution T L where
  u t := WholeSpaceTSD.rowForms (W.E t) (W.B t) r
  u₁ t := WholeSpaceTSD.rowForms (fun ij y => -curlM (W.B t) ij y) (curlM (W.E t)) r
  u₂ t := WholeSpaceTSD.rowForms (S.E₂ t) (S.B₂ t) r
  u₃ t := WholeSpaceTSD.rowForms (S.E₃ t) (S.B₃ t) r
  isDeg t i y := by
    fin_cases i
    · intro s _; rfl
    · exact isDeg_oneForm (fun j => W.E t (r, j)) y
    · exact isDeg_twoForm (fun j => W.B t (r, j)) y
  contDiff t i := by
    fin_cases i
    · exact contDiff_const
    · exact contDiff_oneForm fun j => S.contDiff_E t (r, j)
    · exact contDiff_twoForm fun j => S.contDiff_B t (r, j)
  continuous₁ i s := by
    fin_cases i
    · exact continuous_const
    · exact WholeSpaceTSD.continuous_oneForm_joint
        (E := fun t ij y => -curlM (W.B t) ij y) (fun ij => (W.continuous_curl_B ij).neg) s
    · exact WholeSpaceTSD.continuous_twoForm_joint (B := fun t => curlM (W.E t))
        W.continuous_curl_E s
  continuous₂ i s := by
    fin_cases i
    · exact continuous_const
    · exact WholeSpaceTSD.continuous_oneForm_joint S.continuous_E₂ s
    · exact WholeSpaceTSD.continuous_twoForm_joint S.continuous_B₂ s
  continuous₃ i s := by
    fin_cases i
    · exact continuous_const
    · exact WholeSpaceTSD.continuous_oneForm_joint S.continuous_E₃ s
    · exact WholeSpaceTSD.continuous_twoForm_joint S.continuous_B₃ s
  hasDerivAt₁ t i y s := by
    fin_cases i
    · exact hasDerivAt_const t _
    · exact WholeSpaceTSD.hasDerivAt_oneForm (E' := fun t ij y => -curlM (W.B t) ij y)
        (fun j => W.hasDerivAt_E t (r, j) y) s
    · exact WholeSpaceTSD.hasDerivAt_twoForm (B' := fun t => curlM (W.E t))
        (fun j => W.hasDerivAt_B t (r, j) y) s
  hasDerivAt₂ t i y s := by
    fin_cases i
    · exact hasDerivAt_const t _
    · exact WholeSpaceTSD.hasDerivAt_oneForm (E := fun t ij y => -curlM (W.B t) ij y)
        (fun j => S.hasDerivAt_E₁ t (r, j) y) s
    · exact WholeSpaceTSD.hasDerivAt_twoForm (B := fun t => curlM (W.E t))
        (fun j => S.hasDerivAt_B₁ t (r, j) y) s
  hasDerivAt₃ t i y s := by
    fin_cases i
    · exact hasDerivAt_const t _
    · exact WholeSpaceTSD.hasDerivAt_oneForm (fun j => S.hasDerivAt_E₂ t (r, j) y) s
    · exact WholeSpaceTSD.hasDerivAt_twoForm (fun j => S.hasDerivAt_B₂ t (r, j) y) s
  pde₀ t := by
    change (0 : FormField 3) = -formalAdjD (oneForm fun j => W.E t (r, j))
    rw [formalAdjD_oneForm]
    funext y s
    simp [W.div_E t r y]
  pde₁ t := by
    change oneForm (fun j y => -curlM (W.B t) (r, j) y) =
      extDeriv 0 - formalAdjD (twoForm fun j => W.B t (r, j))
    rw [formalAdjD_twoForm, extDeriv_zero, zero_sub, oneForm_neg]
    rfl
  pde₂ t := by
    change twoForm (fun j => curlM (W.E t) (r, j)) = extDeriv (oneForm fun j => W.E t (r, j))
    rw [extDeriv_oneForm]
    rfl
  bound t ht i y hy := by
    have hE := fun j => S.bound t ht (r, j) y hy
    fin_cases i
    · change ‖fderiv ℝ (0 : FormField 3) y‖ ≤ L ∧ ‖fderiv ℝ (extDeriv (0 : FormField 3)) y‖ ≤ L
      rw [extDeriv_zero, fderiv_zero, Pi.zero_apply, norm_zero]
      exact ⟨hL0, hL0⟩
    · change ‖fderiv ℝ (oneForm fun j => W.E t (r, j)) y‖ ≤ L ∧
        ‖fderiv ℝ (extDeriv (oneForm fun j => W.E t (r, j))) y‖ ≤ L
      rw [extDeriv_oneForm]
      exact ⟨norm_fderiv_oneForm_le hL0
          (fun j => (S.contDiff_E t (r, j)).differentiable (by norm_num) y) fun j => (hE j).1,
        norm_fderiv_twoForm_le hL0 (fun j => (WholeSpaceTSD.contDiff_curlM (S.contDiff_E t)
          (r, j)).differentiable one_ne_zero y) fun j => (hE j).2.1⟩
    · change ‖fderiv ℝ (twoForm fun j => W.B t (r, j)) y‖ ≤ L ∧
        ‖fderiv ℝ (extDeriv (twoForm fun j => W.B t (r, j))) y‖ ≤ L
      rw [extDeriv_twoForm_B, fderiv_zero, Pi.zero_apply, norm_zero]
      exact ⟨norm_fderiv_twoForm_le hL0
          (fun j => (S.contDiff_B t (r, j)).differentiable (by norm_num) y)
          fun j => (hE j).2.2.1, hL0⟩
  lipschitz t ht t' ht' i y hy := by
    have hE := fun j => S.lipschitz t ht t' ht' (r, j) y hy
    have hLt : 0 ≤ L * |t' - t| := mul_nonneg hL0 (abs_nonneg _)
    fin_cases i
    · change ‖fderiv ℝ (0 : FormField 3) y - fderiv ℝ (0 : FormField 3) y‖ ≤ L * |t' - t| ∧
        ‖fderiv ℝ (extDeriv (0 : FormField 3)) y - fderiv ℝ (extDeriv (0 : FormField 3)) y‖ ≤
          L * |t' - t|
      simp only [sub_self, norm_zero]
      exact ⟨hLt, hLt⟩
    · change ‖fderiv ℝ (oneForm fun j => W.E t' (r, j)) y -
          fderiv ℝ (oneForm fun j => W.E t (r, j)) y‖ ≤ L * |t' - t| ∧
        ‖fderiv ℝ (extDeriv (oneForm fun j => W.E t' (r, j))) y -
          fderiv ℝ (extDeriv (oneForm fun j => W.E t (r, j))) y‖ ≤ L * |t' - t|
      rw [extDeriv_oneForm, extDeriv_oneForm]
      exact ⟨norm_fderiv_oneForm_sub_le hLt
          (fun j => (S.contDiff_E t' (r, j)).differentiable (by norm_num) y)
          (fun j => (S.contDiff_E t (r, j)).differentiable (by norm_num) y) fun j => (hE j).1,
        norm_fderiv_twoForm_sub_le hLt
          (fun j => (WholeSpaceTSD.contDiff_curlM (S.contDiff_E t') (r, j)).differentiable
            one_ne_zero y)
          (fun j => (WholeSpaceTSD.contDiff_curlM (S.contDiff_E t) (r, j)).differentiable
            one_ne_zero y) fun j => (hE j).2.1⟩
    · change ‖fderiv ℝ (twoForm fun j => W.B t' (r, j)) y -
          fderiv ℝ (twoForm fun j => W.B t (r, j)) y‖ ≤ L * |t' - t| ∧
        ‖fderiv ℝ (extDeriv (twoForm fun j => W.B t' (r, j))) y -
          fderiv ℝ (extDeriv (twoForm fun j => W.B t (r, j))) y‖ ≤ L * |t' - t|
      rw [extDeriv_twoForm_B, extDeriv_twoForm_B, sub_self, norm_zero]
      exact ⟨norm_fderiv_twoForm_sub_le hLt
          (fun j => (S.contDiff_B t' (r, j)).differentiable (by norm_num) y)
          (fun j => (S.contDiff_B t (r, j)).differentiable (by norm_num) y)
          fun j => (hE j).2.2.1, hLt⟩
  bound₃ t ht i y hy s := by
    fin_cases i
    · change |(0 : ℝ)| ≤ L
      rw [abs_zero]; exact hL0
    · exact abs_oneForm_le hL0 (fun j => (S.bound₃ t ht (r, j) y hy).1) s
    · exact abs_twoForm_le hL0 (fun j => (S.bound₃ t ht (r, j) y hy).2) s

theorem faceSign_mul_self (j : Fin 3) : faceSign j * faceSign j = 1 := by
  simp only [faceSign, ← pow_add, ← two_mul, pow_mul]; norm_num

/-- **The rows of a whole-space TSD solution are TSD at every time.** -/
theorem isTSDAt (hL0 : 0 ≤ L) (t : ℝ) : IsTSDAt (fun r => S.row hL0 r) t where
  sigma r y s := rfl
  symm_E r j y := by
    change oneForm (fun j => W.E t (r, j)) y {j} = oneForm (fun j' => W.E t (j, j')) y {r}
    rw [oneForm_apply_singleton, oneForm_apply_singleton, W.symm_E]
  trace_E y := by
    change ∑ r, oneForm (fun j => W.E t (r, j)) y {r} = 0
    simp only [oneForm_apply_singleton]
    exact W.trace_E t y
  symm_B r j y := by
    change faceSign j * twoForm (fun j => W.B t (r, j)) y {j}ᶜ =
      faceSign r * twoForm (fun j' => W.B t (j, j')) y {r}ᶜ
    rw [twoForm_apply_compl, twoForm_apply_compl, ← mul_assoc, ← mul_assoc, faceSign_mul_self,
      faceSign_mul_self, W.symm_B]
  trace_B y := by
    change ∑ r, faceSign r * twoForm (fun j => W.B t (r, j)) y {r}ᶜ = 0
    simp only [twoForm_apply_compl, ← mul_assoc, faceSign_mul_self, one_mul]
    exact W.trace_B t y

/-- **`O(h + Δt²)` convergence and `O(h + Δt²)` monitors for every whole-space TSD solution with
bounded derivatives** ([QuennevilleBelair2015], Ch. 7): the Crank–Nicolson Whitney scheme on the
level-`(N + 1)` mesh of `Q`, started from the canonical interpolant of `(0, E, B)(0)` and with the
boundary DOFs of the interpolants prescribed, satisfies `‖u_M − U(t_M)‖ ≤ C L (1 + T) (h_N + Δt²)`,
and the five `fem4gr` monitors (skew and trace parts of `E` and `B`, and `σ`) of `u_M` obey the
same bound (they vanish for the exact solution). -/
theorem whitney_cn_error_monitors_le (hL0 : 0 ≤ L) (N : ℕ) {Δt : ℝ} (hΔt : 0 < Δt) {M : ℕ}
    (hM : (M : ℝ) * Δt ≤ T) {u g : ℕ → DState3 (whitneyRow N)}
    (hstep : ∀ n < M, TimeStepping.IsDirichletCNStep (whitneyInterior3 N)
      (discreteWave3 (whitneyRow N)) (Δt / 2) 0 (g (n + 1)) (u n) (u (n + 1)))
    (hg : ∀ n < M, g (n + 1) - exactInterp (fun r => S.row hL0 r) N ((n + 1 : ℕ) * Δt) ∈
      whitneyInterior3 N)
    (hu0 : u 0 = exactInterp (fun r => S.row hL0 r) N 0) :
    ‖dEmb3 (whitneyRow N) (u M) - exactField (fun r => S.row hL0 r) (M * Δt)‖ ≤
        cnConst * L * (1 + T) * (meshSize N + Δt ^ 2) ∧
      ‖skewPart (entryE N) (u M)‖ ≤ cnConst * L * (1 + T) * (meshSize N + Δt ^ 2) ∧
      ‖skewPart (entryB N) (u M)‖ ≤ cnConst * L * (1 + T) * (meshSize N + Δt ^ 2) ∧
      ‖tracePart (entryE N) (u M)‖ ≤ cnConst * L * (1 + T) * (meshSize N + Δt ^ 2) ∧
      ‖tracePart (entryB N) (u M)‖ ≤ cnConst * L * (1 + T) * (meshSize N + Δt ^ 2) ∧
      ‖sigmaPart N (u M)‖ ≤ cnConst * L * (1 + T) * (meshSize N + Δt ^ 2) :=
  ⟨(whitney_cn_error_le (fun r => S.row hL0 r) N hΔt hL0 hM hstep hg hu0).choose_spec.2.2,
    whitney_cn_monitors_le (fun r => S.row hL0 r) N hΔt hL0 hM hstep hg hu0
      (S.isTSDAt hL0 _)⟩

end WholeSpaceTSD.Smooth

end SmoothTSD
/-! ## The iterates of the scheme -/

section Iterates

/-- One Crank–Nicolson step of the three-row Whitney scheme. -/
def cnStep (N : ℕ) (s : ℝ) (f g' u : DState3 (whitneyRow N)) : DState3 (whitneyRow N) :=
  (whitney_existsUnique_cnStep3 N s f g' u).exists.choose

theorem sub_self_mem_submodule {V : Type*} [AddCommGroup V] [Module ℝ V] (K : Submodule ℝ V)
    (x : V) : x - x ∈ K := by
  rw [sub_self]; exact K.zero_mem

end Iterates

end Feec.Models.Cube.Inhomogeneous
