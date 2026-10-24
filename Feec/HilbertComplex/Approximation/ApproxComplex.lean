module

public import Feec.HilbertComplex.Approximation.ApproxConforming

/-!
# Approximating families of discrete Hilbert complexes

The complex-level front end of the approximating FEEC theorem (`Feec.HilbertComplex.approxFEEC`):
a Holst–Stern discretization ([HolstStern2012], §3) of a Hilbert complex `H` is turned into an
approximating FEEC discretization (`Feec.HilbertComplex.ApproxFEEC`) of its Hodge wave equation,
and every hypothesis of its core (`ApproxFEEC.Core.ofOperator`: approximation along the orbits
and vanishing consistency defect) is derived from the complex-level ones.

## Setting

An **approximating family of discrete complexes** (`Feec.HilbertComplex.ApproxComplex`, data
`ApproxComplex.Family`) has, for each `h`,

* a Hilbert complex `Vₕ` (`cpx h`, same index shape as `H`) of finite-dimensional spaces with their
  own inner products (its differentials are bounded, `d_domain_eq_top_of_finiteDimensional`);
* bounded **cochain maps** `iₕ : Vₕ → W` (`𝐝 iₕ = iₕ 𝐝ₕ`), not necessarily isometric, with left
  inverses `πₕ` (`πₕ iₕ = 1`), `‖iₕ‖`, `‖πₕ‖` uniformly bounded; `πₕ` need not commute with `𝐝`;
* the **inner-product defect** `‖1 - Jₕ‖ → 0`, `Jₕ = iₕ* iₕ` (`ApproxComplex.Family.J`);
* the **graph-norm approximation property** (`ApproxComplex.Family.GraphApprox`): every `ζ ∈ Γ(𝐝)`
  is approximated by lifts `(iₕ v, 𝐝 iₕ v)`. It follows from `L²` approximation `iₕ πₕ → 1` and a
  **commutation defect** `𝐝ₕ πₕ ζ₁ - πₕ ζ₂ → 0` on a dense set of `Γ(𝐝)`
  (`ApproxComplex.Family.graphApprox_of_commute`).

Since `iₕ` is an injective cochain map, `iₕ Vₕ` is a subcomplex of `H` and `𝐝ₕ = iₕ⁻¹ 𝐝 iₕ`:
the variational crimes allowed here are the inner product of `Vₕ` (`Jₕ ≠ 1`) and a left inverse
`πₕ` that need not be a cochain map, not a discrete differential independent of `𝐝`.

No consistency hypothesis along exact solutions is made. The comparison uses `iₕ*`, which
intertwines the adjoints exactly, `iₕ* 𝐝* = 𝐝ₕ* iₕ*` (`iₕ` being a cochain map), so no
adjoint-consistency hypothesis is needed. Operator-norm consistency is not used and would be too
strong in general (for the BGG scheme (6.5) of [QuennevilleBelair2015] the static strong consistency
bound fails, per the unformalized audit recorded in `Feec.HilbertComplex.BGG.WeakConsistency`; that
scheme enters through `ApproxFEEC` directly: its discrete differential uses `S₀,ₕ = π¹S⁰ ≠ S⁰`, and
its reading maps are not shown to be cochain maps).

## Main definitions

* `waveL`, `totalDL`: the Hodge wave operator `Lₕ = 𝐝ₕ - 𝐝ₕ*` and the differential of a
  finite-dimensional complex as bounded operators; `waveL_apply`: `Lₕ` is its wave operator,
  `ofBounded_waveL_S`: `e^{tLₕ}` is its wave group.
* `ApproxComplex.Family.ellProj`: the **modified elliptic projection**
  `Rₕ = (1 - Lₕ)⁻¹ Gₕ : Γ(𝐝) → Vₕ`, with `Gₕ (y, 𝐝y) = iₕ* (1 - L) y` on `D(L)`
  (`ApproxComplex.Family.G_waveLift`): the elliptic projection (4.11) of
  [QuennevilleBelair2015] with `iₕ*` in place of the orthogonal projection.
* `ApproxFEEC.ofComplex`: the approximating FEEC discretization (`Xₕ = Vₕ`, `Lₕ` the Hodge wave
  operator of `Vₕ`, `ιₕ = iₕ`); `ApproxFEEC.ofComplexCore`: its core `D(L²)` (dense), with the
  comparison trajectories `Rₕ (e^{tL} x, 𝐝 e^{tL} x)` (`Core.ofOperator`).

## Main results

* `ApproxComplex.Family.norm_ellProj_add_le`: `‖Rₕ ζ‖ + ‖𝐝ₕ Rₕ ζ‖ ≤ 16 C ‖ζ‖_Γ` (coercivity of
  `1 - Lₕ` in the discrete graph norm, `norm_add_norm_le_of_inner`, from `𝐝ₕ 𝐝ₕ = 0`).
* **The Strang lemma** `ApproxComplex.Family.norm_graphFst_sub_inclL_ellProj_le`:
  `‖ζ₁ - iₕ Rₕ ζ‖ ≤ (1 + 16 C²) ‖ζ - (iₕ w, 𝐝 iₕ w)‖_Γ + 16 C² ‖1 - Jₕ‖ ‖(iₕ w, 𝐝 iₕ w)‖_Γ` for
  every `w`: best approximation plus the inner-product defect.
* `ApproxComplex.Family.ellProj_defect`: the defect identity
  `Rₕ (L y) - Lₕ Rₕ y = Δₕ (L y) - Δₕ y`, `Δₕ = Rₕ - iₕ* graphFst`, and
  `ApproxComplex.Family.norm_defectOp_apply_le`:
  `‖Δₕ ζ‖ ≤ 16 C ‖1 - Jₕ‖ ‖ζ‖_Γ + C ‖ζ₁ - iₕ Rₕ ζ‖`; hence (`ApproxComplex.tendsto_inclL_ellProj`,
  `ApproxComplex.tendsto_defectOp`) all hypotheses of `Core.ofOperator` hold.
* `approxFEEC_ofComplex`: the four conclusions of `approxFEEC` for `ofComplex`, and, now
  expressible, **discrete constraints**: `Kₕ ⊆ Vₕ` is preserved by `e^{tLₕ}` iff it reduces the
  discrete wave operator; a reducing subcomplex of `Vₕ` (e.g. discrete Gauss laws) is preserved
  exactly and its `𝐝ₕ`-closed components are read in `W` as `𝐝`-closed; if `iₕ Kₕ ⊆ K` the
  residual is exactly `0`; with the Strang and defect bounds.
* **The conforming case**: `ConstrainedFEEC.toComplex` (subcomplexes with the `W` inner products,
  `iₕ` the inclusions, `Jₕ = 1`: zero inner-product defect, `ConstrainedFEEC.toFamily_J`; the
  graph-norm approximation through `graphApprox_of_commute` with commutation defect `0`), whose
  discrete solutions are those of the subcomplex scheme (4.10), `ConstrainedFEEC.toApprox`
  (`ConstrainedFEEC.toComplex_sol`), and whose modified elliptic projection is the elliptic
  projection (4.11) on `D(L)` (`ConstrainedFEEC.toXh_ellProj_waveLift`).

A witness with a genuine inner-product crime (non-isometric `iₕ`, positive inner-product defect,
nonzero consistency defect, inexact scheme) is
`Feec.HilbertComplex.ApproxComplex.scaled_nonvacuous`
(`Feec.HilbertComplex.Approximation.ApproxComplexWitness`). A nonzero commutation defect is not
exercised by any instance.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (Thm 3.9, Thm 3.10)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.6 ((4.10), (4.11))

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

open _root_.Feec.HodgeWave

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι}

/-! ### Finite-dimensional Hilbert complexes -/

section FiniteDim

variable {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] [∀ i, FiniteDimensional 𝕜 (V i)] (E : HilbertComplex 𝕜 c V)

omit [Fintype ι] in
/-- On finite-dimensional spaces the differentials are everywhere defined (dense subspaces of a
finite-dimensional space are closed, hence everything). -/
theorem d_domain_eq_top_of_finiteDimensional (i j : ι) : (E.d i j).domain = ⊤ := by
  have hc : IsClosed ((E.d i j).domain : Set (V i)) := Submodule.closed_of_finiteDimensional _
  rw [← SetLike.coe_set_eq, Submodule.top_coe, ← hc.closure_eq, (E.dense i j).closure_eq]

theorem mem_totalD_domain_of_finiteDimensional (v : PiLp 2 V) : v ∈ E.totalD.domain :=
  fun i j => by rw [E.d_domain_eq_top_of_finiteDimensional i j]; trivial

theorem mem_wave_domain_of_finiteDimensional (v : PiLp 2 V) : v ∈ E.wave.domain :=
  ⟨E.mem_totalD_domain_of_finiteDimensional v, E.dual.mem_totalD_domain_of_finiteDimensional v⟩

/-- The total differential `𝐝` of a finite-dimensional complex, as a bounded operator. -/
def totalDL : PiLp 2 V →L[𝕜] PiLp 2 V :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => E.totalD ⟨v, E.mem_totalD_domain_of_finiteDimensional v⟩
      map_add' := fun v w => by
        change E.totalD (⟨v, E.mem_totalD_domain_of_finiteDimensional v⟩ +
          ⟨w, E.mem_totalD_domain_of_finiteDimensional w⟩) = _
        rw [LinearPMap.map_add]
      map_smul' := fun a v => by
        change E.totalD (a • ⟨v, E.mem_totalD_domain_of_finiteDimensional v⟩) = _
        rw [LinearPMap.map_smul]; rfl }

theorem totalDL_apply (v : PiLp 2 V) (hv : v ∈ E.totalD.domain) :
    E.totalDL v = E.totalD ⟨v, hv⟩ := rfl

theorem totalDL_totalDL (v : PiLp 2 V) : E.totalDL (E.totalDL v) = 0 :=
  E.totalD_comp_totalD ⟨v, E.mem_totalD_domain_of_finiteDimensional v⟩

/-- The Hodge wave operator `L = 𝐝 - 𝐝*` of a finite-dimensional complex, as a bounded
operator. -/
def waveL : PiLp 2 V →L[𝕜] PiLp 2 V := E.totalDL - E.totalDL.adjoint

theorem waveL_apply' (v : PiLp 2 V) : E.waveL v = E.totalDL v - E.totalDL.adjoint v := rfl

theorem inner_waveL (v w : PiLp 2 V) :
    ⟪E.waveL v, w⟫_𝕜 = ⟪E.totalDL v, w⟫_𝕜 - ⟪v, E.totalDL w⟫_𝕜 := by
  rw [waveL_apply', inner_sub_left, ContinuousLinearMap.adjoint_inner_left]

theorem waveL_skew (v w : PiLp 2 V) : ⟪E.waveL v, w⟫_𝕜 = -⟪v, E.waveL w⟫_𝕜 := by
  rw [inner_waveL, waveL_apply', inner_sub_right, ContinuousLinearMap.adjoint_inner_right]
  ring

/-- **`waveL` is the Hodge wave operator of the complex.** -/
theorem waveL_apply (v : PiLp 2 V) :
    E.waveL v = E.wave ⟨v, E.mem_wave_domain_of_finiteDimensional v⟩ := by
  refine ext_inner_right 𝕜 fun w => ?_
  rw [inner_waveL, inner_wave_left E ⟨v, E.mem_wave_domain_of_finiteDimensional v⟩
    ⟨w, E.mem_totalD_domain_of_finiteDimensional w⟩]
  rfl

theorem re_inner_sub_waveL_self (v : PiLp 2 V) :
    RCLike.re ⟪v - E.waveL v, v⟫_𝕜 = ‖v‖ ^ 2 := by
  have hs : RCLike.re ⟪E.waveL v, v⟫_𝕜 = 0 := by
    have h := E.waveL_skew v v
    have : RCLike.re ⟪E.waveL v, v⟫_𝕜 = - RCLike.re ⟪E.waveL v, v⟫_𝕜 := by
      conv_rhs => rw [h, _root_.map_neg, ← inner_conj_symm, RCLike.conj_re]
      simp
    linarith
  rw [inner_sub_left, _root_.map_sub, hs, sub_zero, inner_self_eq_norm_sq]

/-- `1 - L` is injective (`L` is skew). -/
theorem injective_one_sub_waveL :
    Function.Injective ((1 - E.waveL : PiLp 2 V →L[𝕜] PiLp 2 V) : PiLp 2 V →ₗ[𝕜] PiLp 2 V) := by
  intro a b hab
  have h0 : (a - b) - E.waveL (a - b) = 0 := by
    have : ((1 - E.waveL : PiLp 2 V →L[𝕜] PiLp 2 V)) (a - b) = 0 := by
      rw [_root_.map_sub]; exact sub_eq_zero.2 hab
    simpa using this
  have h1 := E.re_inner_sub_waveL_self (a - b)
  rw [h0, inner_zero_left, _root_.map_zero] at h1
  have : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- The resolvent `(1 - L)⁻¹` (finite dimension: `1 - L` is invertible). -/
def oneSubWaveL : PiLp 2 V ≃L[𝕜] PiLp 2 V :=
  (LinearEquiv.ofInjectiveEndo _ E.injective_one_sub_waveL).toContinuousLinearEquiv

theorem oneSubWaveL_apply (v : PiLp 2 V) : E.oneSubWaveL v = v - E.waveL v := rfl

/-- **Coercivity of `1 - L` in the discrete graph norm**: if `|⟪r - L r, v⟫| ≤ M (‖v‖ + ‖𝐝 v‖)`
for every `v`, then `‖r‖ + ‖𝐝 r‖ ≤ 8 M` (test with `v = r - 𝐝 r`, using `𝐝 𝐝 = 0`). -/
theorem norm_add_norm_le_of_inner (r : PiLp 2 V) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ v, ‖⟪r - E.waveL r, v⟫_𝕜‖ ≤ M * (‖v‖ + ‖E.totalDL v‖)) :
    ‖r‖ + ‖E.totalDL r‖ ≤ 8 * M := by
  set D := E.totalDL
  have hDv : D (r - D r) = D r := by rw [_root_.map_sub, E.totalDL_totalDL, sub_zero]
  have hv := h (r - D r)
  rw [hDv] at hv
  have e1 : r - E.waveL r = (r - D r) + D.adjoint r := by rw [waveL_apply']; abel
  have e2 : ⟪D.adjoint r, r - D r⟫_𝕜 = ⟪r, D r⟫_𝕜 := by
    rw [ContinuousLinearMap.adjoint_inner_left, hDv]
  have hre : RCLike.re ⟪r - E.waveL r, r - D r⟫_𝕜 =
      ‖r‖ ^ 2 + ‖D r‖ ^ 2 - RCLike.re ⟪r, D r⟫_𝕜 := by
    rw [e1, inner_add_left, _root_.map_add, e2, inner_self_eq_norm_sq, @norm_sub_sq 𝕜]
    ring
  have hle : RCLike.re ⟪r - E.waveL r, r - D r⟫_𝕜 ≤ ‖⟪r - E.waveL r, r - D r⟫_𝕜‖ :=
    RCLike.re_le_norm _
  have hab : RCLike.re ⟪r, D r⟫_𝕜 ≤ ‖r‖ * ‖D r‖ := re_inner_le_norm _ _
  have hs : ‖r - D r‖ ≤ ‖r‖ + ‖D r‖ := norm_sub_le _ _
  have ha := norm_nonneg r
  have hb := norm_nonneg (D r)
  have hsq : (‖r‖ + ‖D r‖) ^ 2 ≤ 8 * M * (‖r‖ + ‖D r‖) := by
    have : M * (‖r - D r‖ + ‖D r‖) ≤ M * (2 * (‖r‖ + ‖D r‖)) :=
      mul_le_mul_of_nonneg_left (by linarith) hM
    nlinarith [sq_nonneg (‖r‖ - ‖D r‖)]
  nlinarith

end FiniteDim

section Group

variable {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] [∀ i, FiniteDimensional 𝕜 (V i)] [∀ i, NormedSpace ℝ (V i)]
  [∀ i, IsScalarTower ℝ 𝕜 (V i)] (E : HilbertComplex 𝕜 c V)

/-- **`e^{t waveL}` is the wave group of the complex.** -/
theorem ofBounded_waveL_S (t : ℝ) (v : PiLp 2 V) :
    (C0Group.ofBounded E.waveL).S t v = E.waveGroup.S t v := by
  have hv := E.mem_wave_domain_of_finiteDimensional v
  have hu : ∀ s, HasDerivAt (fun s => E.waveGroup.S s v) (E.waveL (E.waveGroup.S s v)) s :=
    fun s => by
      have h := hasDerivAt_waveGroup E hv s
      rwa [← wave_waveGroup hv s, ← E.waveL_apply] at h
  have h := eq_ofBounded_of_hasDerivAt E.waveL E.waveL_skew hu t
  rw [C0Group.S_zero_apply] at h
  exact h.symm

end Group

/-! ### Approximating families of discrete complexes -/

section Family

variable {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
  [∀ i, CompleteSpace (W i)]

/-- A **family of discrete Hilbert complexes with reading maps** for the Hilbert complex `H`
([HolstStern2012], §3): for each `h`, a Hilbert complex `Vₕ` (`cpx h`, same index shape as
`H`) of finite-dimensional spaces with their own inner products, injective bounded cochain maps
`iₕ : Vₕ → W` (`𝐝 iₕ = iₕ 𝐝ₕ`: `incl_mem`, `incl_d`), left inverses `πₕ : W → Vₕ`
(`πₕ iₕ = 1`), and uniform bounds on `‖iₕ‖`, `‖πₕ‖`. The maps `iₕ` need not be isometric and
`πₕ` need not commute with `𝐝`. -/
structure ApproxComplex.Family (H : HilbertComplex 𝕜 c W) (κ : Type*) where
  /-- the discrete spaces -/
  V : κ → ι → Type u
  [normedAddCommGroup : ∀ h i, NormedAddCommGroup (V h i)]
  [innerProductSpace : ∀ h i, InnerProductSpace 𝕜 (V h i)]
  [completeSpace : ∀ h i, CompleteSpace (V h i)]
  [finiteDimensional : ∀ h i, FiniteDimensional 𝕜 (V h i)]
  [normedSpaceReal : ∀ h i, NormedSpace ℝ (V h i)]
  [isScalarTower : ∀ h i, IsScalarTower ℝ 𝕜 (V h i)]
  /-- the discrete complexes -/
  cpx : ∀ h, HilbertComplex 𝕜 c (V h)
  /-- the cochain maps `iₕ` -/
  incl : ∀ h i, V h i →L[𝕜] W i
  incl_mem : ∀ h i j (v : V h i), incl h i v ∈ (H.d i j).domain
  incl_d : ∀ h i j (v : ((cpx h).d i j).domain),
    H.d i j ⟨incl h i v, incl_mem h i j v⟩ = incl h j ((cpx h).d i j v)
  /-- the left inverses `πₕ` -/
  proj : ∀ h i, W i →L[𝕜] V h i
  proj_incl : ∀ h i v, proj h i (incl h i v) = v
  bound : ∃ C, ∀ h i, ‖incl h i‖ ≤ C ∧ ‖proj h i‖ ≤ C

attribute [instance] ApproxComplex.Family.normedAddCommGroup
  ApproxComplex.Family.innerProductSpace ApproxComplex.Family.completeSpace
  ApproxComplex.Family.finiteDimensional ApproxComplex.Family.normedSpaceReal
  ApproxComplex.Family.isScalarTower

/-- `‖(fᵢ xᵢ)ᵢ‖ ≤ C ‖x‖` in `PiLp 2` when `‖fᵢ xᵢ‖ ≤ C ‖xᵢ‖` for each `i`. -/
theorem norm_piLp_le_of_le {A B : ι → Type*} [∀ i, SeminormedAddCommGroup (A i)]
    [∀ i, SeminormedAddCommGroup (B i)] {x : PiLp 2 A} {y : PiLp 2 B} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖y i‖ ≤ C * ‖x i‖) : ‖y‖ ≤ C * ‖x‖ := by
  have hsq : ‖y‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h i) 2
  have := norm_nonneg y
  nlinarith [mul_nonneg hC (norm_nonneg x)]

namespace ApproxComplex.Family

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (S : ApproxComplex.Family.{u} H κ)

/-- A nonnegative uniform bound of `‖iₕ‖`, `‖πₕ‖`. -/
def boundConst : ℝ := max S.bound.choose 0

omit [Fintype ι] in
theorem boundConst_nonneg : 0 ≤ S.boundConst := le_max_right _ _

omit [Fintype ι] in
theorem norm_incl_le (h : κ) (i : ι) : ‖S.incl h i‖ ≤ S.boundConst :=
  (S.bound.choose_spec h i).1.trans (le_max_left _ _)

omit [Fintype ι] in
theorem norm_proj_le (h : κ) (i : ι) : ‖S.proj h i‖ ≤ S.boundConst :=
  (S.bound.choose_spec h i).2.trans (le_max_left _ _)

/-- The total reading map `iₕ : Vₕ → W`, `(iₕ v)ⁱ = iₕⁱ vⁱ`. -/
def inclL (h : κ) : PiLp 2 (S.V h) →L[𝕜] PiLp 2 W :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 fun i => S.incl h i (v i)
      map_add' := fun v w => PiLp.ext fun i => by simp
      map_smul' := fun a v => PiLp.ext fun i => by simp }

@[simp] theorem inclL_apply (h : κ) (v : PiLp 2 (S.V h)) (i : ι) :
    S.inclL h v i = S.incl h i (v i) := rfl

/-- The total left inverse `πₕ : W → Vₕ`. -/
def projL (h : κ) : PiLp 2 W →L[𝕜] PiLp 2 (S.V h) :=
  LinearMap.mkContinuous
    { toFun := fun x => WithLp.toLp 2 fun i => S.proj h i (x i)
      map_add' := fun v w => PiLp.ext fun i => by simp
      map_smul' := fun a v => PiLp.ext fun i => by simp }
    S.boundConst fun x => norm_piLp_le_of_le S.boundConst_nonneg fun i =>
      ((S.proj h i).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (S.norm_proj_le h i) (norm_nonneg _))

@[simp] theorem projL_inclL (h : κ) (v : PiLp 2 (S.V h)) : S.projL h (S.inclL h v) = v :=
  PiLp.ext fun i => S.proj_incl h i (v i)

theorem norm_inclL_apply_le (h : κ) (v : PiLp 2 (S.V h)) :
    ‖S.inclL h v‖ ≤ S.boundConst * ‖v‖ :=
  norm_piLp_le_of_le S.boundConst_nonneg fun i => ((S.incl h i).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (S.norm_incl_le h i) (norm_nonneg _))

theorem norm_inclL_le (h : κ) : ‖S.inclL h‖ ≤ S.boundConst :=
  ContinuousLinearMap.opNorm_le_bound _ S.boundConst_nonneg (S.norm_inclL_apply_le h)

theorem norm_projL_le (h : κ) : ‖S.projL h‖ ≤ S.boundConst :=
  LinearMap.mkContinuous_norm_le _ S.boundConst_nonneg _

/-- **Stability of the reading map**: `‖v‖ ≤ C ‖iₕ v‖` (from `πₕ iₕ = 1`). -/
theorem norm_le_norm_inclL (h : κ) (v : PiLp 2 (S.V h)) :
    ‖v‖ ≤ S.boundConst * ‖S.inclL h v‖ :=
  calc ‖v‖ = ‖S.projL h (S.inclL h v)‖ := by rw [S.projL_inclL]
    _ ≤ ‖S.projL h‖ * ‖S.inclL h v‖ := (S.projL h).le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_right (S.norm_projL_le h) (norm_nonneg _)

theorem inclL_injective (h : κ) : Function.Injective (S.inclL h) := fun a b hab => by
  have := congrArg (S.projL h) hab
  rwa [S.projL_inclL, S.projL_inclL] at this

theorem inclL_mem (h : κ) (v : PiLp 2 (S.V h)) : S.inclL h v ∈ H.totalD.domain :=
  fun i j => S.incl_mem h i j (v i)

/-- The discrete total differential `𝐝ₕ` on `Vₕ`. -/
abbrev D (h : κ) : PiLp 2 (S.V h) →L[𝕜] PiLp 2 (S.V h) := (S.cpx h).totalDL

/-- The discrete Hodge wave operator `Lₕ = 𝐝ₕ - 𝐝ₕ*` (adjoint in the inner product of `Vₕ`). -/
abbrev L (h : κ) : PiLp 2 (S.V h) →L[𝕜] PiLp 2 (S.V h) := (S.cpx h).waveL

/-- **`iₕ` is a cochain map** (total form): `iₕ 𝐝ₕ v = 𝐝 iₕ v`. -/
theorem inclL_D (h : κ) (v : PiLp 2 (S.V h)) :
    S.inclL h (S.D h v) = H.totalD ⟨S.inclL h v, S.inclL_mem h v⟩ := by
  refine PiLp.ext fun j => ?_
  rw [totalD_apply, inclL_apply, D, totalDL_apply _ v
    ((S.cpx h).mem_totalD_domain_of_finiteDimensional v), totalD_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => (S.incl_d h i j ⟨v i, _⟩).symm

/-- The lift `v ↦ (iₕ v, 𝐝 iₕ v)` of `Vₕ` into the graph space `Γ(𝐝)`. -/
def graphIncl (h : κ) : PiLp 2 (S.V h) →L[𝕜] H.totalD.GraphSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => H.totalD.toGraphSpace ⟨S.inclL h v, S.inclL_mem h v⟩
      map_add' := fun v w => H.totalD.graphFst_injective (by
        rw [H.totalD.graphFst.map_add]; exact (S.inclL h).map_add v w)
      map_smul' := fun a v => H.totalD.graphFst_injective (by
        rw [RingHom.id_apply, H.totalD.graphFst.map_smul]; exact (S.inclL h).map_smul a v) }

theorem graphFst_graphIncl (h : κ) (v : PiLp 2 (S.V h)) :
    H.totalD.graphFst (S.graphIncl h v) = S.inclL h v := rfl

theorem graphSnd_graphIncl (h : κ) (v : PiLp 2 (S.V h)) :
    H.totalD.graphSnd (S.graphIncl h v) = S.inclL h (S.D h v) := by rw [S.inclL_D]; rfl

/-- The **inner-product operator** `Jₕ = iₕ* iₕ` (`⟪Jₕ v, w⟫ = ⟪iₕ v, iₕ w⟫`); `‖1 - Jₕ‖` is the
inner-product defect of [HolstStern2012], §3. -/
def J (h : κ) : PiLp 2 (S.V h) →L[𝕜] PiLp 2 (S.V h) := (S.inclL h).adjoint ∘L S.inclL h

theorem inner_J (h : κ) (v w : PiLp 2 (S.V h)) :
    ⟪S.J h v, w⟫_𝕜 = ⟪S.inclL h v, S.inclL h w⟫_𝕜 := by
  rw [J, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]

theorem norm_graphSnd_le (ζ : H.totalD.GraphSpace) : ‖H.totalD.graphSnd ζ‖ ≤ ‖ζ‖ := by
  have := norm_sq_graphSpace ζ
  nlinarith [norm_nonneg (H.totalD.graphFst ζ), norm_nonneg ζ, norm_nonneg (H.totalD.graphSnd ζ)]

/-- `‖v‖ + ‖𝐝ₕ v‖ ≤ 2 C ‖(iₕ v, 𝐝 iₕ v)‖_Γ`. -/
theorem norm_add_norm_D_le (h : κ) (v : PiLp 2 (S.V h)) :
    ‖v‖ + ‖S.D h v‖ ≤ 2 * S.boundConst * ‖S.graphIncl h v‖ := by
  have h1 := S.norm_le_norm_inclL h v
  have h2 := S.norm_le_norm_inclL h (S.D h v)
  have e1 : ‖S.inclL h v‖ ≤ ‖S.graphIncl h v‖ := by
    rw [← S.graphFst_graphIncl]; exact norm_graphFst_le _
  have e2 : ‖S.inclL h (S.D h v)‖ ≤ ‖S.graphIncl h v‖ := by
    rw [← S.graphSnd_graphIncl]; exact norm_graphSnd_le _
  have hC := S.boundConst_nonneg
  nlinarith [mul_le_mul_of_nonneg_left e1 hC, mul_le_mul_of_nonneg_left e2 hC]

/-! #### The modified elliptic projection -/

/-- The **discrete load** `Gₕ ζ = iₕ* ζ₁ - iₕ* ζ₂ + 𝐝ₕ* iₕ* ζ₁` of `ζ = (ζ₁, ζ₂) ∈ Γ(𝐝)`:
`⟪Gₕ ζ, v⟫ = ⟪ζ₁, iₕ v⟫ - ⟪ζ₂, iₕ v⟫ + ⟪ζ₁, iₕ 𝐝ₕ v⟫`, the shifted form of `ζ` tested with the
lift of `v` (cf. the right-hand side `iₕ* f` of the discrete problems of [HolstStern2012], §3). -/
def G (h : κ) : H.totalD.GraphSpace →L[𝕜] PiLp 2 (S.V h) :=
  (S.inclL h).adjoint ∘L H.totalD.graphFst - (S.inclL h).adjoint ∘L H.totalD.graphSnd +
    (S.D h).adjoint ∘L (S.inclL h).adjoint ∘L H.totalD.graphFst

theorem inner_G (h : κ) (ζ : H.totalD.GraphSpace) (v : PiLp 2 (S.V h)) :
    ⟪S.G h ζ, v⟫_𝕜 = ⟪H.totalD.graphFst ζ, S.inclL h v⟫_𝕜 -
      ⟪H.totalD.graphSnd ζ, S.inclL h v⟫_𝕜 + ⟪H.totalD.graphFst ζ, S.inclL h (S.D h v)⟫_𝕜 := by
  simp only [G, _root_.add_apply, _root_.sub_apply,
    ContinuousLinearMap.comp_apply, inner_add_left, inner_sub_left,
    ContinuousLinearMap.adjoint_inner_left]

/-- On the lift of `y ∈ D(L)`, `Gₕ (y, 𝐝 y) = iₕ* (y - L y)` (the weak form of `L`, and
`iₕ` a cochain map). -/
theorem G_waveLift (h : κ) (y : H.wave.domain) :
    S.G h (waveLift H y) = (S.inclL h).adjoint ((y : PiLp 2 W) - H.wave y) := by
  refine ext_inner_right 𝕜 fun v => ?_
  rw [inner_G, ContinuousLinearMap.adjoint_inner_left, inner_sub_left,
    inner_wave_left H y ⟨S.inclL h v, S.inclL_mem h v⟩, S.inclL_D h v]
  simp only [graphFst_waveLift]
  change _ = _ - (⟪H.totalD.graphSnd (waveLift H y), _⟫_𝕜 - _)
  ring

/-- On a lift `(iₕ w, 𝐝 iₕ w)`, `⟪Gₕ ·, v⟫` is the shifted form of `Vₕ` with `Jₕ` in place of
the identity. -/
theorem inner_G_graphIncl (h : κ) (w v : PiLp 2 (S.V h)) :
    ⟪S.G h (S.graphIncl h w), v⟫_𝕜 =
      ⟪S.J h w, v⟫_𝕜 - ⟪S.J h (S.D h w), v⟫_𝕜 + ⟪S.J h w, S.D h v⟫_𝕜 := by
  rw [inner_G, S.graphFst_graphIncl, S.graphSnd_graphIncl, S.inner_J, S.inner_J, S.inner_J]

theorem norm_inner_G_le (h : κ) (ζ : H.totalD.GraphSpace) (v : PiLp 2 (S.V h)) :
    ‖⟪S.G h ζ, v⟫_𝕜‖ ≤ 2 * S.boundConst * ‖ζ‖ * (‖v‖ + ‖S.D h v‖) := by
  rw [inner_G]
  have hC := S.boundConst_nonneg
  have a1 : ‖⟪H.totalD.graphFst ζ, S.inclL h v⟫_𝕜‖ ≤ ‖ζ‖ * (S.boundConst * ‖v‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (norm_graphFst_le _) (S.norm_inclL_apply_le h v)
      (norm_nonneg _) (norm_nonneg _))
  have a2 : ‖⟪H.totalD.graphSnd ζ, S.inclL h v⟫_𝕜‖ ≤ ‖ζ‖ * (S.boundConst * ‖v‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (norm_graphSnd_le _) (S.norm_inclL_apply_le h v)
      (norm_nonneg _) (norm_nonneg _))
  have a3 : ‖⟪H.totalD.graphFst ζ, S.inclL h (S.D h v)⟫_𝕜‖ ≤
      ‖ζ‖ * (S.boundConst * ‖S.D h v‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (norm_graphFst_le _)
      (S.norm_inclL_apply_le h _) (norm_nonneg _) (norm_nonneg _))
  have hz := norm_nonneg ζ
  have hv := norm_nonneg v
  calc _ ≤ ‖⟪H.totalD.graphFst ζ, S.inclL h v⟫_𝕜‖ + ‖⟪H.totalD.graphSnd ζ, S.inclL h v⟫_𝕜‖ +
        ‖⟪H.totalD.graphFst ζ, S.inclL h (S.D h v)⟫_𝕜‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ ‖ζ‖ * (S.boundConst * ‖v‖) + ‖ζ‖ * (S.boundConst * ‖v‖) +
        ‖ζ‖ * (S.boundConst * ‖S.D h v‖) := by linarith
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hz hC) (norm_nonneg (S.D h v))]

/-- The **modified elliptic projection** `Rₕ = (1 - Lₕ)⁻¹ Gₕ : Γ(𝐝) → Vₕ`: on `D(L)`,
`(1 - Lₕ) Rₕ y = iₕ* (1 - L) y`. In the conforming case (`iₕ` an inclusion, `iₕ*` the orthogonal
projection) it agrees on `D(L)` with the elliptic projection
(`ConstrainedFEEC.toXh_ellProj_waveLift`; [QuennevilleBelair2015], (4.11)); in general `iₕ*`
replaces the orthogonal projection (cf. [HolstStern2012], §3). -/
def ellProj (h : κ) : H.totalD.GraphSpace →L[𝕜] PiLp 2 (S.V h) :=
  ((S.cpx h).oneSubWaveL.symm : PiLp 2 (S.V h) →L[𝕜] PiLp 2 (S.V h)) ∘L S.G h

theorem ellProj_sub (h : κ) (ζ : H.totalD.GraphSpace) :
    S.ellProj h ζ - S.L h (S.ellProj h ζ) = S.G h ζ :=
  (S.cpx h).oneSubWaveL.apply_symm_apply (S.G h ζ)

theorem eq_ellProj (h : κ) {ζ : H.totalD.GraphSpace} {r : PiLp 2 (S.V h)}
    (hr : r - S.L h r = S.G h ζ) : r = S.ellProj h ζ :=
  (S.cpx h).oneSubWaveL.injective (by
    rw [oneSubWaveL_apply, oneSubWaveL_apply, hr, S.ellProj_sub])

/-- **Uniform stability of `Rₕ` in the discrete graph norm**:
`‖Rₕ ζ‖ + ‖𝐝ₕ Rₕ ζ‖ ≤ 16 C ‖ζ‖_Γ`. -/
theorem norm_ellProj_add_le (h : κ) (ζ : H.totalD.GraphSpace) :
    ‖S.ellProj h ζ‖ + ‖S.D h (S.ellProj h ζ)‖ ≤ 16 * S.boundConst * ‖ζ‖ := by
  have := (S.cpx h).norm_add_norm_le_of_inner (S.ellProj h ζ)
    (M := 2 * S.boundConst * ‖ζ‖) (by have := S.boundConst_nonneg; positivity)
    fun v => by rw [S.ellProj_sub]; exact S.norm_inner_G_le h ζ v
  linarith

theorem norm_ellProj_apply_le (h : κ) (ζ : H.totalD.GraphSpace) :
    ‖S.ellProj h ζ‖ ≤ 16 * S.boundConst * ‖ζ‖ :=
  le_trans (le_add_of_nonneg_right (norm_nonneg _)) (S.norm_ellProj_add_le h ζ)

theorem norm_ellProj_le (h : κ) : ‖S.ellProj h‖ ≤ 16 * S.boundConst :=
  ContinuousLinearMap.opNorm_le_bound _ (by have := S.boundConst_nonneg; positivity)
    (S.norm_ellProj_apply_le h)

/-- The discrete error `w - Rₕ ζ` in the discrete graph norm, for any `w ∈ Vₕ`: inner-product
defect times `‖w‖ + ‖𝐝ₕ w‖`, plus the graph-norm distance of `ζ` to the lift of `w`. -/
theorem norm_sub_ellProj_add_le (h : κ) (ζ : H.totalD.GraphSpace) (w : PiLp 2 (S.V h)) :
    ‖w - S.ellProj h ζ‖ + ‖S.D h (w - S.ellProj h ζ)‖ ≤
      8 * (‖1 - S.J h‖ * (‖w‖ + ‖S.D h w‖) + 2 * S.boundConst * ‖ζ - S.graphIncl h w‖) := by
  set δ := ‖1 - S.J h‖
  set e := w - S.ellProj h ζ
  have he : e - S.L h e = (w - S.L h w) - S.G h ζ := by
    simp only [e, _root_.map_sub]; rw [← S.ellProj_sub]; abel
  refine (S.cpx h).norm_add_norm_le_of_inner e (by
    have := S.boundConst_nonneg; positivity) fun v => ?_
  have hsplit : ⟪e - S.L h e, v⟫_𝕜 = ⟪(1 - S.J h) w, v⟫_𝕜 - ⟪(1 - S.J h) (S.D h w), v⟫_𝕜 +
      ⟪(1 - S.J h) w, S.D h v⟫_𝕜 + ⟪S.G h (S.graphIncl h w - ζ), v⟫_𝕜 := by
    rw [he, (S.G h).map_sub, inner_sub_left, inner_sub_left, inner_sub_left,
      inner_waveL, S.inner_G_graphIncl]
    simp only [_root_.sub_apply, one_apply_eq_self, inner_sub_left]
    ring
  rw [hsplit]
  have b1 : ‖⟪(1 - S.J h) w, v⟫_𝕜‖ ≤ δ * ‖w‖ * ‖v‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      ((1 - S.J h).le_opNorm w) (norm_nonneg _))
  have b2 : ‖⟪(1 - S.J h) (S.D h w), v⟫_𝕜‖ ≤ δ * ‖S.D h w‖ * ‖v‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      ((1 - S.J h).le_opNorm _) (norm_nonneg _))
  have b3 : ‖⟪(1 - S.J h) w, S.D h v⟫_𝕜‖ ≤ δ * ‖w‖ * ‖S.D h v‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      ((1 - S.J h).le_opNorm w) (norm_nonneg _))
  have b4 := S.norm_inner_G_le h (S.graphIncl h w - ζ) v
  rw [norm_sub_rev] at b4
  have hδ : 0 ≤ δ := norm_nonneg _
  have hw := norm_nonneg w
  have hDw := norm_nonneg (S.D h w)
  have hv := norm_nonneg v
  have hDv := norm_nonneg (S.D h v)
  calc _ ≤ ‖⟪(1 - S.J h) w, v⟫_𝕜‖ + ‖⟪(1 - S.J h) (S.D h w), v⟫_𝕜‖ +
        ‖⟪(1 - S.J h) w, S.D h v⟫_𝕜‖ + ‖⟪S.G h (S.graphIncl h w - ζ), v⟫_𝕜‖ :=
        (norm_add_le _ _).trans (by
          gcongr
          exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _))
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hδ hDw) hDv]

/-- **The Strang lemma for the modified elliptic projection** (cf. [HolstStern2012], Thm 3.9,
Thm 3.10): for every `w ∈ Vₕ`,
`‖ζ₁ - iₕ Rₕ ζ‖ ≤ (1 + 16 C²) ‖ζ - (iₕ w, 𝐝 iₕ w)‖_Γ + 16 C² ‖1 - Jₕ‖ ‖(iₕ w, 𝐝 iₕ w)‖_Γ`:
best approximation in the graph norm plus the inner-product defect. -/
theorem norm_graphFst_sub_inclL_ellProj_le (h : κ) (ζ : H.totalD.GraphSpace)
    (w : PiLp 2 (S.V h)) :
    ‖H.totalD.graphFst ζ - S.inclL h (S.ellProj h ζ)‖ ≤
      (1 + 16 * S.boundConst ^ 2) * ‖ζ - S.graphIncl h w‖ +
        16 * S.boundConst ^ 2 * ‖1 - S.J h‖ * ‖S.graphIncl h w‖ := by
  have e : H.totalD.graphFst ζ - S.inclL h (S.ellProj h ζ) =
      H.totalD.graphFst (ζ - S.graphIncl h w) + S.inclL h (w - S.ellProj h ζ) := by
    rw [H.totalD.graphFst.map_sub, (S.inclL h).map_sub, S.graphFst_graphIncl]; abel
  rw [e]
  have h1 : ‖H.totalD.graphFst (ζ - S.graphIncl h w)‖ ≤ ‖ζ - S.graphIncl h w‖ :=
    norm_graphFst_le _
  have h2 := S.norm_inclL_apply_le h (w - S.ellProj h ζ)
  have h3 := S.norm_sub_ellProj_add_le h ζ w
  have h4 := S.norm_add_norm_D_le h w
  have hC := S.boundConst_nonneg
  have hδ : 0 ≤ ‖1 - S.J h‖ := norm_nonneg _
  have h5 : ‖w - S.ellProj h ζ‖ ≤ 8 * (‖1 - S.J h‖ * (2 * S.boundConst * ‖S.graphIncl h w‖) +
      2 * S.boundConst * ‖ζ - S.graphIncl h w‖) := by
    have := mul_le_mul_of_nonneg_left h4 hδ
    nlinarith [norm_nonneg (S.D h (w - S.ellProj h ζ))]
  calc _ ≤ ‖H.totalD.graphFst (ζ - S.graphIncl h w)‖ + ‖S.inclL h (w - S.ellProj h ζ)‖ :=
        norm_add_le _ _
    _ ≤ ‖ζ - S.graphIncl h w‖ + S.boundConst * (8 * (‖1 - S.J h‖ *
          (2 * S.boundConst * ‖S.graphIncl h w‖) + 2 * S.boundConst * ‖ζ - S.graphIncl h w‖)) :=
        add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left h5 hC))
    _ = _ := by ring

/-! #### The consistency defect -/

/-- The **defect operator** `Δₕ = Rₕ - iₕ* graphFst : Γ(𝐝) → Vₕ`. -/
def defectOp (h : κ) : H.totalD.GraphSpace →L[𝕜] PiLp 2 (S.V h) :=
  S.ellProj h - (S.inclL h).adjoint ∘L H.totalD.graphFst

theorem norm_defectOp_le (h : κ) : ‖S.defectOp h‖ ≤ 17 * S.boundConst := by
  refine (norm_sub_le (S.ellProj h) ((S.inclL h).adjoint ∘L H.totalD.graphFst)).trans ?_
  have h1 := S.norm_ellProj_le h
  have h2 : ‖(S.inclL h).adjoint ∘L H.totalD.graphFst‖ ≤ S.boundConst := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [ContinuousLinearMap.adjoint.norm_map (S.inclL h)]
    have h3 : ‖H.totalD.graphFst‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ζ => by
        rw [one_mul]; exact norm_graphFst_le ζ
    have := S.norm_inclL_le h
    nlinarith [norm_nonneg (S.inclL h), norm_nonneg H.totalD.graphFst]
  linarith

/-- **The defect identity** of the modified elliptic projection along `D(L²)`:
`Rₕ (L y) - Lₕ Rₕ y = Δₕ (L y) - Δₕ y` (lifts to `Γ(𝐝)`). -/
theorem ellProj_defect (h : κ) (y : H.wave.domain) (hLy : H.wave y ∈ H.wave.domain) :
    S.ellProj h (waveLift H ⟨_, hLy⟩) - S.L h (S.ellProj h (waveLift H y)) =
      S.defectOp h (waveLift H ⟨_, hLy⟩) + (-S.defectOp h) (waveLift H y) := by
  have e := S.ellProj_sub h (waveLift H y)
  rw [S.G_waveLift] at e
  have e' : S.L h (S.ellProj h (waveLift H y)) = S.ellProj h (waveLift H y) -
      (S.inclL h).adjoint ((y : PiLp 2 W) - H.wave y) := by rw [← e]; abel
  rw [e', _root_.neg_apply, defectOp, _root_.sub_apply,
    _root_.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, graphFst_waveLift, graphFst_waveLift, _root_.map_sub]
  abel

/-- The defect is controlled by the inner-product defect and the reading error:
`‖Δₕ ζ‖ ≤ 16 C ‖1 - Jₕ‖ ‖ζ‖_Γ + C ‖ζ₁ - iₕ Rₕ ζ‖`. -/
theorem norm_defectOp_apply_le (h : κ) (ζ : H.totalD.GraphSpace) :
    ‖S.defectOp h ζ‖ ≤ 16 * S.boundConst * ‖1 - S.J h‖ * ‖ζ‖ +
      S.boundConst * ‖H.totalD.graphFst ζ - S.inclL h (S.ellProj h ζ)‖ := by
  have e : S.defectOp h ζ = (1 - S.J h) (S.ellProj h ζ) -
      (S.inclL h).adjoint (H.totalD.graphFst ζ - S.inclL h (S.ellProj h ζ)) := by
    simp only [defectOp, J, _root_.sub_apply, one_apply_eq_self,
      ContinuousLinearMap.comp_apply, _root_.map_sub]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · refine ((1 - S.J h).le_opNorm _).trans ?_
    have := S.norm_ellProj_apply_le h ζ
    have hδ : 0 ≤ ‖1 - S.J h‖ := norm_nonneg _
    nlinarith
  · refine ((S.inclL h).adjoint.le_opNorm _).trans ?_
    rw [ContinuousLinearMap.adjoint.norm_map (S.inclL h)]
    exact mul_le_mul_of_nonneg_right (S.norm_inclL_le h) (norm_nonneg _)

instance (h : κ) (K : Submodule 𝕜 (PiLp 2 (S.V h))) : K.HasOrthogonalProjection :=
  haveI := FiniteDimensional.complete 𝕜 K; .ofCompleteSpace K

instance (h : κ) (i : ι) (K : Submodule 𝕜 (S.V h i)) : K.HasOrthogonalProjection :=
  haveI := FiniteDimensional.complete 𝕜 K; .ofCompleteSpace K

theorem norm_le_graphFst_add_graphSnd (ζ : H.totalD.GraphSpace) :
    ‖ζ‖ ≤ ‖H.totalD.graphFst ζ‖ + ‖H.totalD.graphSnd ζ‖ := by
  have := norm_sq_graphSpace ζ
  nlinarith [norm_nonneg ζ, norm_nonneg (H.totalD.graphFst ζ), norm_nonneg (H.totalD.graphSnd ζ),
    mul_nonneg (norm_nonneg (H.totalD.graphFst ζ)) (norm_nonneg (H.totalD.graphSnd ζ))]

/-- The **approximation property in the graph norm** along `l` (the best-approximation term
`inf_v ‖u - iₕ v‖_V` of [HolstStern2012], Thm 3.9, tends to `0`): every `ζ ∈ Γ(𝐝)` is approximated
by lifts `(iₕ v, 𝐝 iₕ v)`. -/
def GraphApprox (l : Filter κ) : Prop :=
  ∀ ζ : H.totalD.GraphSpace, ∀ ε > 0, ∀ᶠ h in l, ∃ v : PiLp 2 (S.V h), ‖ζ - S.graphIncl h v‖ < ε

/-- **The graph-norm approximation property from `L²` approximation and a commutation defect**:
if `iₕ πₕ → 1` pointwise on `W` and the commutation defect `𝐝ₕ πₕ ζ₁ - πₕ ζ₂` of `πₕ` with `𝐝`
tends to `0` on a dense set `Z` of `Γ(𝐝)` (e.g. smooth data; it vanishes for a cochain
projection, [HolstStern2012], §3), then `GraphApprox` holds. -/
theorem graphApprox_of_commute {l : Filter κ}
    (hπ : ∀ x : PiLp 2 W, Tendsto (fun h => S.inclL h (S.projL h x)) l (𝓝 x))
    {Z : Set H.totalD.GraphSpace} (hZ : Dense Z)
    (hcomm : ∀ ζ ∈ Z, Tendsto (fun h => ‖S.D h (S.projL h (H.totalD.graphFst ζ)) -
      S.projL h (H.totalD.graphSnd ζ)‖) l (𝓝 0)) :
    S.GraphApprox l := by
  intro ζ ε hε
  obtain ⟨ζ', hζ', hd⟩ := hZ.exists_dist_lt ζ (half_pos hε)
  rw [dist_eq_norm] at hd
  set C := S.boundConst
  have hC := S.boundConst_nonneg
  have hε6 : 0 < ε / 6 := by positivity
  have hε6' : 0 < ε / (6 * (C + 1)) := by positivity
  filter_upwards [Metric.tendsto_nhds.1 (hπ (H.totalD.graphFst ζ')) _ hε6,
    Metric.tendsto_nhds.1 (hπ (H.totalD.graphSnd ζ')) _ hε6,
    Metric.tendsto_nhds.1 (hcomm ζ' hζ') _ hε6'] with h h1 h2 h3
  refine ⟨S.projL h (H.totalD.graphFst ζ'), ?_⟩
  set v := S.projL h (H.totalD.graphFst ζ')
  rw [dist_eq_norm, norm_sub_rev] at h1 h2
  rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg (norm_nonneg _)] at h3
  have e1 : H.totalD.graphFst (ζ' - S.graphIncl h v) =
      H.totalD.graphFst ζ' - S.inclL h (S.projL h (H.totalD.graphFst ζ')) := by
    rw [H.totalD.graphFst.map_sub, S.graphFst_graphIncl]
  have e2 : H.totalD.graphSnd (ζ' - S.graphIncl h v) =
      (H.totalD.graphSnd ζ' - S.inclL h (S.projL h (H.totalD.graphSnd ζ'))) -
        S.inclL h (S.D h v - S.projL h (H.totalD.graphSnd ζ')) := by
    rw [H.totalD.graphSnd.map_sub, S.graphSnd_graphIncl, (S.inclL h).map_sub]; abel
  have h4 : ‖S.inclL h (S.D h v - S.projL h (H.totalD.graphSnd ζ'))‖ ≤ C * (ε / (6 * (C + 1))) :=
    (S.norm_inclL_apply_le h _).trans (mul_le_mul_of_nonneg_left h3.le hC)
  have h5 : C * (ε / (6 * (C + 1))) ≤ ε / 6 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h6 : ‖ζ' - S.graphIncl h v‖ < ε / 2 := by
    refine (norm_le_graphFst_add_graphSnd _).trans_lt ?_
    rw [e1, e2]
    have := norm_sub_le (H.totalD.graphSnd ζ' - S.inclL h (S.projL h (H.totalD.graphSnd ζ')))
      (S.inclL h (S.D h v - S.projL h (H.totalD.graphSnd ζ')))
    linarith
  calc ‖ζ - S.graphIncl h v‖ = ‖(ζ - ζ') + (ζ' - S.graphIncl h v)‖ := by abel_nf
    _ ≤ ‖ζ - ζ'‖ + ‖ζ' - S.graphIncl h v‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hd h6
    _ = ε := add_halves ε

end ApproxComplex.Family

/-- An **approximating family of discrete Hilbert complexes** for `H` (the setting of
[HolstStern2012], §3, for the Hodge wave equation): a family of discrete complexes `Vₕ` with
cochain maps `iₕ` and left inverses `πₕ` (`ApproxComplex.Family`), a closed constraint `K`, a
filter `l`, and the two Holst–Stern hypotheses:

* the **inner-product defect** `‖1 - iₕ* iₕ‖ → 0` (`iₕ` need not be isometric);
* the **approximation property in the graph norm** (`GraphApprox`; from `L²` approximation and
  a commutation defect of `πₕ` tending to `0` on a dense set by
  `ApproxComplex.Family.graphApprox_of_commute`).

No consistency hypothesis along exact solutions is made: the consistency defect of the comparison
built from the modified elliptic projection is derived (`ApproxComplex.tendsto_defectOp`). -/
structure ApproxComplex (H : HilbertComplex 𝕜 c W) (κ : Type*) where
  /-- the discrete complexes and reading maps -/
  toFamily : ApproxComplex.Family.{u} H κ
  /-- the constraint subspace -/
  K : Submodule 𝕜 (PiLp 2 W)
  isClosed_K : IsClosed (K : Set (PiLp 2 W))
  /-- the filter along which the discretization is refined -/
  l : Filter κ
  tendsto_innerDefect : Tendsto (fun h => ‖1 - toFamily.J h‖) l (𝓝 0)
  graphApprox : toFamily.GraphApprox l

namespace ApproxComplex

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplex.{u} H κ)

/-- **Convergence of the modified elliptic projection**: `iₕ Rₕ ζ → ζ₁` for every `ζ ∈ Γ(𝐝)`
(the Strang lemma `norm_graphFst_sub_inclL_ellProj_le`, the graph-norm approximation property
and the inner-product defect). -/
theorem tendsto_inclL_ellProj (ζ : H.totalD.GraphSpace) :
    Tendsto (fun h => F.toFamily.inclL h (F.toFamily.ellProj h ζ)) F.l
      (𝓝 (H.totalD.graphFst ζ)) := by
  set S := F.toFamily
  rw [Metric.tendsto_nhds]
  intro ε hε
  set A := 1 + 16 * S.boundConst ^ 2
  set B := 16 * S.boundConst ^ 2
  have hA : 0 < A := by positivity
  have hB : 0 ≤ B := by positivity
  set η := ε / (2 * A)
  have hη : 0 < η := by positivity
  set M := B * (‖ζ‖ + η)
  have hM : 0 ≤ M := by positivity
  set θ := ε / (2 * (M + 1))
  have hθ : 0 < θ := by positivity
  filter_upwards [F.graphApprox ζ η hη, Metric.tendsto_nhds.1 F.tendsto_innerDefect θ hθ]
    with h ⟨w, hw⟩ hδ
  rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg (norm_nonneg _)] at hδ
  rw [dist_eq_norm, norm_sub_rev]
  refine (S.norm_graphFst_sub_inclL_ellProj_le h ζ w).trans_lt ?_
  have hgw : ‖S.graphIncl h w‖ ≤ ‖ζ‖ + η := by
    have := norm_sub_norm_le (S.graphIncl h w) ζ
    rw [norm_sub_rev] at this
    linarith
  have t1 : A * ‖ζ - S.graphIncl h w‖ < ε / 2 := by
    have : A * ‖ζ - S.graphIncl h w‖ < A * η := mul_lt_mul_of_pos_left hw hA
    have e : A * η = ε / 2 := by simp only [η]; field_simp
    linarith
  have t2 : B * ‖1 - S.J h‖ * ‖S.graphIncl h w‖ < ε / 2 := by
    have hδ0 : 0 ≤ ‖1 - S.J h‖ := norm_nonneg _
    have : B * ‖1 - S.J h‖ * ‖S.graphIncl h w‖ ≤ M * θ := by
      calc B * ‖1 - S.J h‖ * ‖S.graphIncl h w‖ ≤ B * θ * (‖ζ‖ + η) := by
            gcongr
        _ = M * θ := by ring
    have e : M * θ = ε / 2 * (M / (M + 1)) := by simp only [θ]; field_simp
    have : M / (M + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    nlinarith
  linarith

/-- **The derived consistency**: the defect operator `Δₕ = Rₕ - iₕ* graphFst` tends to `0`
pointwise on `Γ(𝐝)`. -/
theorem tendsto_defectOp (ζ : H.totalD.GraphSpace) :
    Tendsto (fun h => ‖F.toFamily.defectOp h ζ‖) F.l (𝓝 0) := by
  set S := F.toFamily
  have h1 := F.tendsto_innerDefect
  have h2 := tendsto_iff_norm_sub_tendsto_zero.1 (F.tendsto_inclL_ellProj ζ)
  have hb : Tendsto (fun h => 16 * S.boundConst * ‖1 - S.J h‖ * ‖ζ‖ +
      S.boundConst * ‖H.totalD.graphFst ζ - S.inclL h (S.ellProj h ζ)‖) F.l (𝓝 0) := by
    have := ((h1.const_mul (16 * S.boundConst)).mul_const ‖ζ‖).add
      (h2.const_mul S.boundConst)
    simp only [mul_zero, zero_mul, add_zero] at this
    refine this.congr fun h => ?_
    rw [norm_sub_rev (S.inclL h (S.ellProj h ζ))]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun h => S.norm_defectOp_apply_le h ζ) hb

end ApproxComplex

end Family

/-! ### The approximating FEEC discretization of an approximating family of complexes -/

section OfComplex

variable {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
  [∀ i, CompleteSpace (W i)]

namespace ApproxFEEC

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplex.{u} H κ)

/-- **The approximating FEEC discretization of an approximating family of discrete complexes**:
`Xₕ = Vₕ` (total space, with the inner product of `Vₕ`), `Lₕ` the Hodge wave operator of `Vₕ`
(`HilbertComplex.waveL_apply`), `ιₕ = iₕ`, `πₕ` the left inverses. -/
def ofComplex : ApproxFEEC H κ where
  K := F.K
  isClosed_K := F.isClosed_K
  l := F.l
  X h := PiLp 2 (F.toFamily.V h)
  L h := F.toFamily.L h
  isSkewAdjoint := H.isSkewAdjoint_wave
  skew h := (F.toFamily.cpx h).waveL_skew
  incl h := F.toFamily.inclL h
  proj h := F.toFamily.projL h
  proj_incl h v := F.toFamily.projL_inclL h v
  bound := ⟨F.toFamily.boundConst, fun h => ⟨F.toFamily.norm_inclL_le h,
    F.toFamily.norm_projL_le h⟩⟩

/-- The discrete group is the wave group of `Vₕ`. -/
theorem ofComplex_group (h : κ) (t : ℝ) (v : PiLp 2 (F.toFamily.V h)) :
    ((ofComplex F).group h).S t v = (F.toFamily.cpx h).waveGroup.S t v :=
  (F.toFamily.cpx h).ofBounded_waveL_S t v

theorem ofComplex_sol (h : κ) (v : PiLp 2 (F.toFamily.V h)) (t : ℝ) :
    (ofComplex F).sol h v t = F.toFamily.inclL h ((F.toFamily.cpx h).waveGroup.S t v) := by
  change (ofComplex F).incl h (((ofComplex F).group h).S t v) = _
  rw [ofComplex_group]; rfl

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **The core of `ofComplex`**: data `D(L²)`, comparison trajectories the modified elliptic
projections `Rₕ (e^{tL} x, 𝐝 e^{tL} x)` of the exact orbit (the Trotter–Kato bridge
`Core.ofOperator` with `Δₕ = Rₕ - iₕ* graphFst`, `Δₕ' = -Δₕ`). Every hypothesis of
`Core.ofOperator` is derived from the complex-level ones. -/
def ofComplexCore : (ofComplex F).Core :=
  Core.ofOperator (ofComplex F) F.toFamily.ellProj
    ⟨_, F.toFamily.norm_ellProj_le⟩ F.tendsto_inclL_ellProj
    F.toFamily.defectOp (fun h => -F.toFamily.defectOp h)
    ⟨_, fun h => ⟨F.toFamily.norm_defectOp_le h,
      (norm_neg (F.toFamily.defectOp h)).trans_le (F.toFamily.norm_defectOp_le h)⟩⟩
    F.toFamily.ellProj_defect F.tendsto_defectOp
    (fun ζ => (F.tendsto_defectOp ζ).congr fun _ => (norm_neg _).symm)

theorem dense_ofComplexCore_data : Dense ((ofComplexCore F).Data : Set (PiLp 2 W)) :=
  H.isSkewAdjoint_wave.dense_domainSq

theorem ofComplexCore_cmp_p (T : ℝ) (x : PiLp 2 W) (h : κ) (t : ℝ) :
    ((ofComplexCore F).cmp T).p x h t = F.toFamily.ellProj h (waveOrbit H x t) := rfl

end ApproxFEEC

open ApproxFEEC in
/-- **The approximating FEEC theorem for approximating families of discrete complexes.** For an
approximating family `F` of finite-dimensional Hilbert complexes `Vₕ` with cochain maps
`iₕ : Vₕ → W` (inner-product defect `‖1 - iₕ* iₕ‖ → 0`, graph-norm approximation), the
discretization `ofComplex F` (generator the Hodge wave operator of `Vₕ` in its own inner product)
with the core `ofComplexCore F` (comparison: the modified elliptic projection of the exact orbit)
satisfies:

1. the four conclusions of `approxFEEC` (`ApproxFEEC.Verdict`), on the dense core `D(L²)`;
2. the discrete generator is the Hodge wave operator of `Vₕ` and `e^{tLₕ}` its wave group;
3. **discrete constraints**: a subspace `Kₕ ⊆ Vₕ` is preserved by `e^{tLₕ}` for all `t` iff it
   reduces the discrete wave operator; a reducing subcomplex of `Vₕ` (e.g. discrete Gauss laws) is
   preserved exactly, and its `𝐝ₕ`-closed components are read in `W` as `𝐝`-closed (`iₕ` is a
   cochain map); if `iₕ Kₕ ⊆ K`, the residual `dist(ξₕ(t), K)` is exactly `0`;
4. the **Strang estimate** `‖ζ₁ - iₕ Rₕ ζ‖ ≤ (1 + 16C²) ‖ζ - (iₕ w, 𝐝 iₕ w)‖ +
   16C² ‖1 - Jₕ‖ ‖(iₕ w, 𝐝 iₕ w)‖` for every `w`, and the **consistency defect bound**
   `‖Δₕ ζ‖ ≤ 16C ‖1 - Jₕ‖ ‖ζ‖ + C ‖ζ₁ - iₕ Rₕ ζ‖`; both tend to `0`.

Cf. [HolstStern2012], Thm 3.9, Thm 3.10 (elliptic analogues) -/
theorem approxFEEC_ofComplex [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
    {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplex.{u} H κ) :
    (ofComplex F).Verdict (ofComplexCore F) ∧
    Dense ((ofComplexCore F).Data : Set (PiLp 2 W)) ∧
    -- 2. the discrete generator and group
    (∀ h v, (ofComplex F).L h v = (F.toFamily.cpx h).wave
      ⟨v, (F.toFamily.cpx h).mem_wave_domain_of_finiteDimensional v⟩) ∧
    (∀ h t v, ((ofComplex F).group h).S t v = (F.toFamily.cpx h).waveGroup.S t v) ∧
    -- 3. discrete constraints
    (∀ h (Kh : Submodule 𝕜 (PiLp 2 (F.toFamily.V h))),
      (F.toFamily.cpx h).wave.IsReducing Kh ↔
        ∀ t, ∀ v ∈ Kh, ((ofComplex F).group h).S t v ∈ Kh) ∧
    (∀ h (Sh : ∀ i, Submodule 𝕜 (F.toFamily.V h i)), (F.toFamily.cpx h).ReducingSubcomplex Sh →
      ∀ v ∈ totalSub Sh, ∀ t, ((ofComplex F).group h).S t v ∈ totalSub Sh ∧
        ∀ i, Sh i ≤ (F.toFamily.cpx h).cycles i → (ofComplex F).sol h v t i ∈ H.cycles i) ∧
    (∀ h (Kh : Submodule 𝕜 (PiLp 2 (F.toFamily.V h))), (F.toFamily.cpx h).wave.IsReducing Kh →
      Kh.map (F.toFamily.inclL h : PiLp 2 (F.toFamily.V h) →ₗ[𝕜] PiLp 2 W) ≤ F.K →
      ∀ v ∈ Kh, ∀ t, infDist ((ofComplex F).sol h v t) (F.K : Set (PiLp 2 W)) = 0) ∧
    -- 4. the Strang estimate and the consistency defect, with their limits
    (∀ h ζ w, ‖H.totalD.graphFst ζ - (ofComplex F).incl h (F.toFamily.ellProj h ζ)‖ ≤
      (1 + 16 * F.toFamily.boundConst ^ 2) * ‖ζ - F.toFamily.graphIncl h w‖ +
        16 * F.toFamily.boundConst ^ 2 * ‖1 - F.toFamily.J h‖ * ‖F.toFamily.graphIncl h w‖) ∧
    (∀ h ζ, ‖F.toFamily.defectOp h ζ‖ ≤
      16 * F.toFamily.boundConst * ‖1 - F.toFamily.J h‖ * ‖ζ‖ +
        F.toFamily.boundConst * ‖H.totalD.graphFst ζ -
          (ofComplex F).incl h (F.toFamily.ellProj h ζ)‖) ∧
    (∀ ζ, Tendsto (fun h => (ofComplex F).incl h (F.toFamily.ellProj h ζ)) F.l
      (𝓝 (H.totalD.graphFst ζ))) ∧
    (∀ ζ, Tendsto (fun h => ‖F.toFamily.defectOp h ζ‖) F.l (𝓝 0)) := by
  set S := F.toFamily
  have hiff : ∀ h (Kh : Submodule 𝕜 (PiLp 2 (S.V h))), (S.cpx h).wave.IsReducing Kh ↔
      ∀ t, ∀ v ∈ Kh, ((ofComplex F).group h).S t v ∈ Kh := fun h Kh => by
    rw [(S.cpx h).isReducing_iff_waveGroup_invariant Kh, C0Group.map_le_iff_forall]
    exact forall_congr' fun t => forall₂_congr fun v _ => by rw [ofComplex_group]; rfl
  refine ⟨approxFEEC _ _, dense_ofComplexCore_data F, fun h => (F.toFamily.cpx h).waveL_apply,
    ofComplex_group F, hiff,
    fun h Sh hS v hv t => ?_, fun h Kh hK hKK v hv t => ?_,
    S.norm_graphFst_sub_inclL_ellProj_le, S.norm_defectOp_apply_le, F.tendsto_inclL_ellProj,
    F.tendsto_defectOp⟩
  · have hmem : ((ofComplex F).group h).S t v ∈ totalSub Sh := by
      rw [ofComplex_group]; exact hS.waveGroup_mem t hv
    refine ⟨hmem, fun i hi => ?_⟩
    rw [ofComplex_sol]
    set u := (S.cpx h).waveGroup.S t v
    have hu : u ∈ totalSub Sh := hS.waveGroup_mem t hv
    obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1
      (show u i ∈ ((S.cpx h).d i (c.next i)).ker from hi (hu i))
    refine LinearPMap.mem_ker_iff.2 ⟨⟨_, S.incl_mem h i (c.next i) (u i)⟩, rfl, ?_⟩
    have e := S.incl_d h i (c.next i) y
    rw [hy0, _root_.map_zero] at e
    rw [← e]
    congr 2
    rw [hy]
  · have hmem := (hiff h Kh).1 hK t v hv
    refine Metric.infDist_zero_of_mem (hKK ⟨_, hmem, rfl⟩)

/-! ### The conforming case: constrained FEEC discretizations -/

namespace ConstrainedFEEC

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ConstrainedFEEC H κ)

/-- The discrete complexes `Vₕ` of a constrained FEEC discretization (subcomplexes with the `W`
inner products, `Subcomplex.toHilbertComplex`), with `iₕ` the inclusions and `πₕ` the cochain
projections. -/
def toFamily : ApproxComplex.Family H κ where
  V h i := ↥((F.V h).V i)
  completeSpace _ _ := FiniteDimensional.complete 𝕜 _
  cpx h := (F.V h).toHilbertComplex
  incl h i := ((F.V h).V i).subtypeL
  incl_mem h i j v := (F.V h).le_domain i j v.2
  incl_d _ _ _ _ := rfl
  proj h i := LinearMap.mkContinuous
    (LinearMap.codRestrict ((F.V h).V i) ((F.π h).π i) ((F.π h).mem i)) F.projConst
    fun x => F.norm_π_le h i x
  proj_incl h i v := Subtype.ext ((F.π h).proj i _ v.2)
  bound := ⟨max 1 F.projConst, fun h i =>
    ⟨(ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [one_mul]; exact le_rfl).trans (le_max_left _ _),
    (LinearMap.mkContinuous_norm_le _ F.projConst_nonneg _).trans (le_max_right _ _)⟩⟩

/-- `iₕ` is isometric: `Jₕ = 1`. -/
theorem toFamily_J (h : κ) : F.toFamily.J h = 1 := by
  refine ContinuousLinearMap.ext fun v => ext_inner_right 𝕜 fun w => ?_
  rw [ApproxComplex.Family.inner_J, one_apply_eq_self, PiLp.inner_apply,
    PiLp.inner_apply]
  rfl

theorem inclL_projL_toFamily (h : κ) (x : PiLp 2 W) :
    F.toFamily.inclL h (F.toFamily.projL h x) = F.piProj h x := rfl

/-- **The graph-norm approximation property of the conforming family**, from
`graphApprox_of_commute` with `L²` approximation `Πₕ → 1` and commutation defect
`𝐝ₕ Πₕ ζ₁ - Πₕ ζ₂ = 0` (`Πₕ` is a cochain projection). -/
theorem toFamily_graphApprox : F.toFamily.GraphApprox F.l := by
  refine F.toFamily.graphApprox_of_commute (fun x => ?_) dense_univ fun ζ _ => ?_
  · rw [Metric.tendsto_nhds]
    intro ε hε
    have hC := F.projConst_nonneg
    filter_upwards [F.dense x (ε / (2 * (1 + F.projConst))) (by positivity)] with h ⟨w, hw, hxw⟩
    rw [dist_eq_norm, inclL_projL_toFamily, norm_sub_rev]
    refine (F.norm_sub_piProj_le h x hw).trans_lt ?_
    calc (1 + F.projConst) * ‖x - w‖ ≤ (1 + F.projConst) * (ε / (2 * (1 + F.projConst))) :=
          mul_le_mul_of_nonneg_left hxw.le (by positivity)
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε
  · obtain ⟨x, rfl, -, -⟩ := H.totalD.exists_toGraphSpace_eq ζ
    have e : ∀ h, F.toFamily.D h (F.toFamily.projL h x) = F.toFamily.projL h (H.totalD x) :=
      fun h => by
        refine F.toFamily.inclL_injective h ?_
        rw [F.toFamily.inclL_D]
        exact F.totalD_piProj h x
    simp only [graphFst_toGraphSpace, graphSnd_toGraphSpace]
    exact (tendsto_const_nhds (x := (0 : ℝ))).congr fun h => by rw [e h, sub_self, norm_zero]

/-- **A constrained FEEC discretization is an approximating family of discrete complexes**,
with zero inner-product defect (`toFamily_J`) and graph-norm approximation from the commuting
projections (`toFamily_graphApprox`). -/
def toComplex : ApproxComplex H κ where
  toFamily := F.toFamily
  K := F.K
  isClosed_K := F.isClosed_K
  l := F.l
  tendsto_innerDefect := by
    simp only [F.toFamily_J, sub_self, norm_zero]; exact tendsto_const_nhds
  graphApprox := F.toFamily_graphApprox

/-- The identification of the total discrete space of `toFamily` with `Xₕ = ∏ Vₕⁱ ⊆ W`. -/
def toXh (h : κ) : PiLp 2 (F.toFamily.V h) →L[𝕜] F.Xh h :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ⟨F.toFamily.inclL h v, fun i => (v i).2⟩
      map_add' := fun v w => Subtype.ext ((F.toFamily.inclL h).map_add v w)
      map_smul' := fun a v => Subtype.ext ((F.toFamily.inclL h).map_smul a v) }

theorem coe_toXh (h : κ) (v : PiLp 2 (F.toFamily.V h)) :
    (F.toXh h v : PiLp 2 W) = F.toFamily.inclL h v := rfl

theorem inner_toXh (h : κ) (v w : PiLp 2 (F.toFamily.V h)) :
    ⟪F.toXh h v, F.toXh h w⟫_𝕜 = ⟪v, w⟫_𝕜 := by
  rw [Submodule.coe_inner, coe_toXh, coe_toXh, ← ApproxComplex.Family.inner_J, F.toFamily_J,
    one_apply_eq_self]

theorem toXh_surjective (h : κ) : Function.Surjective (F.toXh h) := fun y =>
  ⟨WithLp.toLp 2 fun i => ⟨(y : PiLp 2 W) i, y.2 i⟩, Subtype.ext rfl⟩

/-- The discrete wave operators agree: `Xₕ ≅ Vₕ` intertwines `Lₕ` with the discrete wave
operator (4.10). -/
theorem toXh_L (h : κ) (v : PiLp 2 (F.toFamily.V h)) :
    F.toXh h (F.toFamily.L h v) = F.discreteWave h (F.toXh h v) := by
  refine ext_inner_right 𝕜 fun y => ?_
  obtain ⟨w, rfl⟩ := F.toXh_surjective h y
  rw [F.inner_toXh, inner_waveL, F.inner_discreteWave, ← F.inner_toXh, ← F.inner_toXh,
    Submodule.coe_inner, Submodule.coe_inner]
  congr 1 <;> congr 1
  all_goals first | exact F.toFamily.inclL_D h v | exact F.toFamily.inclL_D h w

/-- **The conforming instance recovers the subcomplex scheme**: the discrete solutions of
`ofComplex F.toComplex` are those of `ConstrainedFEEC.toApprox` (the semi-discrete scheme
(4.10) of [QuennevilleBelair2015]), through `Vₕ ≅ Xₕ`. -/
theorem toComplex_sol (h : κ) (v : PiLp 2 (F.toFamily.V h)) (t : ℝ) :
    (ApproxFEEC.ofComplex F.toComplex).sol h v t = F.toApprox.sol h (F.toXh h v) t := by
  set B := F.toFamily.L h
  set u : ℝ → F.Xh h := fun s => F.toXh h ((C0Group.ofBounded B).S s v)
  have hu : ∀ s, HasDerivAt u (F.discreteWave h (u s)) s := fun s => by
    have hd := ((F.toXh h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
      (C0Group.hasDerivAt_exp_ofReal_smul_apply B v s)
    rw [← F.toXh_L]
    exact hd
  have e := eq_ofBounded_of_hasDerivAt (F.discreteWave h) (F.discreteWave_skew h) hu t
  have e0 : u 0 = F.toXh h v := by simp only [u, C0Group.S_zero_apply]
  rw [e0] at e
  change F.toFamily.inclL h ((C0Group.ofBounded B).S t v) = _
  rw [toApprox_sol_eq, ← coe_toXh]
  exact congrArg Subtype.val e

theorem toXh_injective (h : κ) : Function.Injective (F.toXh h) := fun _ _ hab =>
  F.toFamily.inclL_injective h (congrArg Subtype.val hab)

/-- `iₕ*` is the orthogonal projection `Qₕ` onto `Xₕ`. -/
theorem toXh_inclL_adjoint (h : κ) (z : PiLp 2 W) :
    F.toXh h ((F.toFamily.inclL h).adjoint z) = F.orthProj h z := by
  refine ext_inner_right 𝕜 fun y => ?_
  obtain ⟨w, rfl⟩ := F.toXh_surjective h y
  rw [F.inner_toXh, ContinuousLinearMap.adjoint_inner_left,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rfl

/-- **In the conforming case the modified elliptic projection is the elliptic projection** (4.11)
on `D(L)`: both solve `(1 - Lₕ) r = Qₕ (1 - L) y` (`discreteWave_ellipticProj`).
[QuennevilleBelair2015], (4.11) -/
theorem toXh_ellProj_waveLift (h : κ) (y : H.wave.domain) :
    F.toXh h (F.toFamily.ellProj h (waveLift H y)) = F.ellipticProj h (waveLift H y) := by
  obtain ⟨r, hr⟩ := F.toXh_surjective h (F.ellipticProj h (waveLift H y))
  rw [← hr]
  refine congrArg (F.toXh h) (F.toFamily.eq_ellProj h ?_).symm
  refine F.toXh_injective h ?_
  rw [F.toFamily.G_waveLift, F.toXh_inclL_adjoint, (F.toXh h).map_sub, F.toXh_L, hr,
    F.discreteWave_ellipticProj, (F.orthProj h).map_sub]
  abel

theorem toComplex_verdict :
    (ApproxFEEC.ofComplex F.toComplex).Verdict (ApproxFEEC.ofComplexCore F.toComplex) :=
  (approxFEEC_ofComplex F.toComplex).1

end ConstrainedFEEC

end OfComplex

end Feec.HilbertComplex
