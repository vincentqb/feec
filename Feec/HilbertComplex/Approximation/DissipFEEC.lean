module

public import Feec.Semigroup.DissipativeInvariance
public import Feec.Evolution.WellPosed
public import Feec.Evolution.Energy

/-!
# The dissipative FEEC theorem

The master theorem `Feec.HilbertComplex.approxFEEC` (`Feec.HilbertComplex.Approximation.ApproxFEEC`)
is stated for the Hodge wave operator `L = 𝐝 - 𝐝†` of a Hilbert complex, a skew-adjoint generator of
a unitary group. Boundary conditions that absorb energy (radiation conditions, impedance
conditions, damping) give generators that are only **m-dissipative**: `re ⟪A x, x⟫ ≤ 0` and
`μ - A` onto, i.e. (Lumer–Phillips, `LinearPMap.isMDissipative_iff_exists_contraction`) generators
of contraction semigroups `S(t)`, `t ≥ 0`. This file extends the theorem to them.

A **dissipative FEEC discretization** (`Feec.HilbertComplex.DissipFEEC`) of `ξ' = A ξ` for an
m-dissipative `A` on a Hilbert space `E` consists of a closed constraint subspace `K`, Hilbert
spaces `Xₕ` with their own inner products, bounded **dissipative** discrete generators `Lₕ`
(`re ⟪Lₕ v, v⟫ ≤ 0`, so `e^{tLₕ}` is a contraction for `t ≥ 0`: uniform stability), and uniformly
bounded reading maps `ιₕ : Xₕ → E` with uniformly bounded left inverses `πₕ`, exactly as for
`ApproxFEEC`. Comparisons, cores and rate classes (`DissipFEEC.Comparison`, `DissipFEEC.Core`,
`DissipFEEC.RateClass`) are those of `ApproxFEEC`, with the semigroup `S(t)` in place of the group.
The energy estimate behind convergence (`norm_sub_le_of_defect_of_dissipative`) needs only
`re ⟪Lₕ e, e⟫ ≤ 0`.

## Main results

The **dissipative FEEC theorem** `dissipFEEC` (statement `DissipFEEC.Verdict`) bundles:

1. well-posedness (Lumer–Phillips): for `ξ₀ ∈ D(A)`, `t ↦ S(t) ξ₀` is a classical solution, the
   only strong solution, its energy is nonincreasing and satisfies the energy identity
   `‖S(t) ξ₀‖² = ‖ξ₀‖² + ∫₀ᵗ 2 re ⟪S(s) A ξ₀, S(s) ξ₀⟫ ds` (`dissipFEEC_wellPosed`), whose
   integrand `2 re ⟪A S(s) ξ₀, S(s) ξ₀⟫` is `≤ 0`;
2. constraint propagation (`dissipFEEC_propagates_iff`): `S(t) K ⊆ K` for all `t ≥ 0` iff the
   resolvents `(μ - A)⁻¹` map `K` into `K`, iff for one `μ > 0` the stationary problem
   `μ u - A u = f` is solvable in `D(A) ∩ K` for all `f ∈ K` (the part of `A` in `K` is
   m-dissipative); `K` reduces `A` iff both `K` and `Kᗮ` are invariant;
3. convergence: on the core (`dissipFEEC_converges_core`), on its closure for every family `vₕ`
   with `ιₕ vₕ → ξ₀` (`dissipFEEC_converges`), with rates for a rate class
   (`dissipFEEC_rate`: `‖S(t) ξ₀ - ιₕ e^{tLₕ} v‖ ≤ (C + ‖ιₕ‖ C' t) hᵅ ‖ξ₀‖_c + ‖ιₕ‖ ‖pₕ(0) - v‖`);
4. the constraint residual `dist(ιₕ e^{tLₕ} vₕ, K)`: for invariant `K` it is bounded by the error
   and tends to `0` (`dissipFEEC_residual`); a solution leaving a closed nonempty `Q` has
   residuals tending to `dist(S(t) ξ₀, Q) > 0` (`dissipFEEC_residual_not_mem`); a non-invariant
   `K` is left by a datum of `K` at some `t ∈ [0, T]`, by a datum of `D(A) ∩ K` when that is dense in
   `K`, and the residuals of every convergent discretization of that datum have a positive limit
   (`dissipFEEC_exists_not_mem`, `dissipFEEC_residual_not_invariant`).

The **Trotter–Kato bridge** `DissipFEEC.Core.ofOperator` builds a core `D(A)` from bounded
`Rₕ : E → Xₕ` with `ιₕ Rₕ → 1` strongly and a defect identity `Rₕ A - Lₕ Rₕ = Δₕ A + Δₕ'` on `D(A)`
with uniformly bounded defects tending to `0` strongly (the orbit form of the consistency
hypothesis of the Trotter–Kato theorem; uniformity on `[0, T]` from compactness of the orbits).

`Core.ofOperator_data_closure`: that core is dense, so convergence holds for every datum.

The skew-adjoint case is `approxFEEC`: `ApproxFEEC.toDissipFEEC`
(`Feec.HilbertComplex.Approximation.ApproxFEEC`) reads an approximating FEEC discretization as a
dissipative one for the m-dissipative skew-adjoint `L`, whose Lumer–Phillips semigroup is the
wave group for `t ≥ 0`, and the forward-in-time clauses of `approxFEEC` (convergence on the core
and its closure, the rate, the residual of a reducing constraint) are proved from those of
`dissipFEEC` (`approxFEEC_converges_core`, `approxFEEC_converges`, `approxFEEC_rate`,
`approxFEEC_residual`). The clauses that use both time directions (reducing iff invariant for all
`t ∈ ℝ`, the non-reducing branches) use the group and are proved in `ApproxFEEC` directly.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.4 (Thm 4.3 Lumer–Phillips), §3.4 (Trotter–Kato approximation theorems)
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (Thm 3.9, Thm 3.10, elliptic analogues)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4 (Thms 4.6, 4.7), §4.10 (Prop. 4.17): the skew-adjoint case; the thesis has no dissipative
  generators

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology Metric

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

/-! ### The energy estimate for dissipative bounded generators -/

section Defect

variable {𝕜 : Type*} [RCLike 𝕜] {X E : Type*}
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X] [NormedSpace ℝ X]
  [IsScalarTower ℝ 𝕜 X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **The abstract consistency estimate for a dissipative generator** (energy method): for a
bounded `L` on `X` with `re ⟪L x, x⟫ ≤ 0`, a bounded `ι : X → E`, a target `u` and a comparison
trajectory `p` with right derivative `p'` on `[0, T]`,
`‖u(t) - ι e^{tL} p(0)‖ ≤ ‖u(t) - ι p(t)‖ + ‖ι‖ ∫₀ᵗ ‖p' - L p‖`. -/
theorem norm_sub_le_of_defect_of_dissipative (L : X →L[𝕜] X)
    (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) (ι : X →L[𝕜] E) {u : ℝ → E} {p p' : ℝ → X} {T : ℝ}
    (hpc : ContinuousOn p (Icc 0 T)) (hp'c : ContinuousOn p' (Icc 0 T))
    (hp : ∀ t ∈ Ico 0 T, HasDerivWithinAt p (p' t) (Ici t) t) :
    ∀ t ∈ Icc 0 T, ‖u t - ι ((C0Group.ofBounded L).S t (p 0))‖ ≤
      ‖u t - ι (p t)‖ + ‖ι‖ * ∫ s in (0 : ℝ)..t, ‖p' s - L (p s)‖ := by
  set G := C0Group.ofBounded L
  set e : ℝ → X := fun t => p t - G.S t (p 0)
  have hGd : ∀ t, HasDerivAt (fun s => G.S s (p 0)) (L (G.S t (p 0))) t := fun t =>
    C0Group.hasDerivAt_exp_ofReal_smul_apply L (p 0) t
  have hec : ContinuousOn e (Icc 0 T) :=
    hpc.sub (fun t _ => (hGd t).continuousAt.continuousWithinAt)
  have hed : ∀ t ∈ Ico 0 T, HasDerivWithinAt e (p' t - L (G.S t (p 0))) (Ici t) t :=
    fun t ht => (hp t ht).sub (hGd t).hasDerivWithinAt
  have hgc : ContinuousOn (fun s => ‖p' s - L (p s)‖) (Icc 0 T) :=
    (hp'c.sub (L.continuous.comp_continuousOn hpc)).norm
  have hle : ∀ t ∈ Ico 0 T, RCLike.re ⟪p' t - L (G.S t (p 0)), e t⟫_𝕜 ≤
      ‖p' t - L (p t)‖ * ‖e t‖ := by
    intro t _
    have hsplit : p' t - L (G.S t (p 0)) = (p' t - L (p t)) + L (e t) := by
      simp only [e, _root_.map_sub]; abel
    rw [hsplit, inner_add_left, _root_.map_add]
    have h1 : RCLike.re ⟪p' t - L (p t), e t⟫_𝕜 ≤ ‖p' t - L (p t)‖ * ‖e t‖ :=
      (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    linarith [hL (e t)]
  have hE := Evolution.Energy.norm_le_add_integral_of_re_inner_deriv_le (𝕜 := 𝕜) hec hed hgc
    (fun _ _ => norm_nonneg _) hle
  intro t ht
  have h0 : e 0 = 0 := by simp [e, G]
  have he := hE t ht
  rw [h0, norm_zero, zero_add] at he
  calc ‖u t - ι (G.S t (p 0))‖ = ‖(u t - ι (p t)) + ι (e t)‖ := by
        simp only [e, _root_.map_sub]; abel_nf
    _ ≤ ‖u t - ι (p t)‖ + ‖ι‖ * ‖e t‖ := (norm_add_le _ _).trans (by gcongr; exact ι.le_opNorm _)
    _ ≤ _ := by gcongr

/-- `e^{tL}` is a contraction for `t ≥ 0` when `L` is bounded and dissipative. -/
theorem norm_ofBounded_apply_le (L : X →L[𝕜] X) (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {t : ℝ}
    (ht : 0 ≤ t) (x : X) : ‖(C0Group.ofBounded L).S t x‖ ≤ ‖x‖ := by
  rw [C0Group.ofBounded_S]; exact LumerPhillips.norm_exp_smul_apply_le hL ht x

end Defect

/-! ### Uniform convergence on compact sets -/

section Compact

/-- **Pointwise convergence to `0` is uniform on compact sets** for a family of functions with a
uniform Lipschitz-type bound `f h ζ ≤ f h ζ' + M ‖ζ - ζ'‖` (finite cover by small balls). -/
theorem eventually_forall_lt_of_tendsto {κ F : Type*} [SeminormedAddCommGroup F] {l : Filter κ}
    {f : κ → F → ℝ} {M : ℝ} (hf : ∀ h ζ ζ', f h ζ ≤ f h ζ' + M * ‖ζ - ζ'‖)
    (hlim : ∀ ζ, Tendsto (fun h => f h ζ) l (𝓝 0)) {S : Set F} (hS : IsCompact S) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ h in l, ∀ ζ ∈ S, f h ζ < ε := by
  set M' := max M 0
  have hM' : 0 ≤ M' := le_max_right _ _
  set δ := ε / (2 * (M' + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨t, -, htf, hcov⟩ := hS.finite_cover_balls hδ
  have hev : ∀ᶠ h in l, ∀ z ∈ t, f h z < ε / 2 :=
    (htf.eventually_all).2 fun z _ => (tendsto_order.1 (hlim z)).2 _ (half_pos hε)
  filter_upwards [hev] with h hh ζ hζ
  obtain ⟨z, hz, hζz⟩ := mem_iUnion₂.1 (hcov hζ)
  rw [Metric.mem_ball, dist_eq_norm] at hζz
  have h1 := hf h ζ z
  have h2 : M * ‖ζ - z‖ ≤ M' * δ :=
    (mul_le_mul_of_nonneg_right (le_max_left M 0) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hζz.le hM')
  have h3 : M' * δ < ε / 2 := by
    have e : M' * δ = ε / 2 * (M' / (M' + 1)) := by
      simp only [δ]; field_simp
    rw [e]
    have : M' / (M' + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    nlinarith
  linarith [hh z hz]

/-- Uniformly bounded linear maps converging pointwise to `0` converge uniformly on compact
sets (the codomains may vary). -/
theorem eventually_forall_norm_lt_of_tendsto {𝕜 κ F : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {G : κ → Type*}
    [∀ h, SeminormedAddCommGroup (G h)] [∀ h, NormedSpace 𝕜 (G h)] {l : Filter κ}
    {A : ∀ h, F →L[𝕜] G h} {M : ℝ} (hM : ∀ h ζ, ‖A h ζ‖ ≤ M * ‖ζ‖)
    (hlim : ∀ ζ, Tendsto (fun h => ‖A h ζ‖) l (𝓝 0)) {S : Set F} (hS : IsCompact S) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ h in l, ∀ ζ ∈ S, ‖A h ζ‖ < ε :=
  eventually_forall_lt_of_tendsto (M := M) (fun h ζ ζ' => by
    have e : A h ζ = A h ζ' + A h (ζ - ζ') := by rw [_root_.map_sub]; abel
    rw [e]
    exact (norm_add_le _ _).trans (by linarith [hM h (ζ - ζ')])) hlim hS hε

/-- `∫₀ᵗ g ≤ M t` for `‖g‖ ≤ M` on `[0, t]` (no integrability needed). -/
theorem integral_le_mul_of_norm_le {g : ℝ → ℝ} {t M : ℝ} (ht : 0 ≤ t)
    (hg : ∀ s ∈ Icc 0 t, ‖g s‖ ≤ M) : ∫ s in (0 : ℝ)..t, g s ≤ M * t := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (f := g)
    (C := M) fun s hs => hg s (Ioc_subset_Icc_self (by rwa [uIoc_of_le ht] at hs))
  rw [sub_zero, abs_of_nonneg ht, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

end Compact

/-! ### Dissipative FEEC discretizations -/

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A **dissipative FEEC discretization** of `ξ' = A ξ` for an m-dissipative `A` on `E`: a closed
constraint `K`; Hilbert spaces `Xₕ` with their own inner products and bounded dissipative
generators `Lₕ` (`re ⟪Lₕ v, v⟫ ≤ 0`, so `e^{tLₕ}` is a contraction for `t ≥ 0`); uniformly bounded
`ιₕ : Xₕ → E`, `πₕ : E → Xₕ` with `πₕ ιₕ = 1`. As for `ApproxFEEC`, `ιₕ` need not be an
inclusion, an isometry or a cochain map. [HolstStern2012], §3; [Pazy1983], §3.4 -/
structure DissipFEEC {A : E →ₗ.[𝕜] E} (hA : A.IsMDissipative) (κ : Type*) where
  /-- the constraint subspace -/
  K : Submodule 𝕜 E
  isClosed_K : IsClosed (K : Set E)
  /-- the filter along which the discretization is refined -/
  l : Filter κ
  /-- the discrete spaces -/
  X : κ → Type u
  [normedAddCommGroup : ∀ h, NormedAddCommGroup (X h)]
  [innerProductSpace : ∀ h, InnerProductSpace 𝕜 (X h)]
  [completeSpace : ∀ h, CompleteSpace (X h)]
  [normedSpaceReal : ∀ h, NormedSpace ℝ (X h)]
  [isScalarTower : ∀ h, IsScalarTower ℝ 𝕜 (X h)]
  /-- the discrete generators -/
  L : ∀ h, X h →L[𝕜] X h
  dissipative : ∀ h x, RCLike.re ⟪L h x, x⟫_𝕜 ≤ 0
  /-- the maps reading discrete states in `E` -/
  incl : ∀ h, X h →L[𝕜] E
  /-- their left inverses -/
  proj : ∀ h, E →L[𝕜] X h
  proj_incl : ∀ h x, proj h (incl h x) = x
  bound : ∃ C, ∀ h, ‖incl h‖ ≤ C ∧ ‖proj h‖ ≤ C

attribute [instance] DissipFEEC.normedAddCommGroup DissipFEEC.innerProductSpace
  DissipFEEC.completeSpace DissipFEEC.normedSpaceReal DissipFEEC.isScalarTower

namespace DissipFEEC

variable {A : E →ₗ.[𝕜] E} {hA : A.IsMDissipative} {κ : Type*} (F : DissipFEEC.{u} hA κ)

instance [CompleteSpace E] : CompleteSpace F.K := F.isClosed_K.completeSpace_coe

instance [CompleteSpace E] : F.K.HasOrthogonalProjection := .ofCompleteSpace _

/-- A nonnegative uniform bound of `‖ιₕ‖`, `‖πₕ‖`. -/
def boundConst : ℝ := max F.bound.choose 0

theorem boundConst_nonneg : 0 ≤ F.boundConst := le_max_right _ _

theorem norm_incl_le (h : κ) : ‖F.incl h‖ ≤ F.boundConst :=
  (F.bound.choose_spec h).1.trans (le_max_left _ _)

theorem norm_proj_le (h : κ) : ‖F.proj h‖ ≤ F.boundConst :=
  (F.bound.choose_spec h).2.trans (le_max_left _ _)

/-- **Stability of the reading map**: `‖v‖ ≤ C ‖ιₕ v‖` (from `πₕ ιₕ = 1`). -/
theorem norm_le_norm_incl (h : κ) (v : F.X h) : ‖v‖ ≤ F.boundConst * ‖F.incl h v‖ :=
  calc ‖v‖ = ‖F.proj h (F.incl h v)‖ := by rw [F.proj_incl]
    _ ≤ ‖F.proj h‖ * ‖F.incl h v‖ := (F.proj h).le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_right (F.norm_proj_le h) (norm_nonneg _)

theorem norm_incl_apply_le (h : κ) (v : F.X h) : ‖F.incl h v‖ ≤ F.boundConst * ‖v‖ :=
  ((F.incl h).le_opNorm v).trans (mul_le_mul_of_nonneg_right (F.norm_incl_le h) (norm_nonneg _))

theorem norm_incl_proj_le (h : κ) (y : E) :
    ‖F.incl h (F.proj h y)‖ ≤ F.boundConst ^ 2 * ‖y‖ := by
  have h1 := F.norm_incl_apply_le h (F.proj h y)
  have h2 := ((F.proj h).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right (F.norm_proj_le h) (norm_nonneg _))
  have h0 := F.boundConst_nonneg
  calc _ ≤ F.boundConst * ‖F.proj h y‖ := h1
    _ ≤ F.boundConst * (F.boundConst * ‖y‖) := mul_le_mul_of_nonneg_left h2 h0
    _ = _ := by ring

/-- The discrete evolution `e^{t Lₕ}` (a contraction for `t ≥ 0`). -/
def group (h : κ) : C0Group 𝕜 (F.X h) := C0Group.ofBounded (F.L h)

theorem norm_group_apply_le (h : κ) {t : ℝ} (ht : 0 ≤ t) (v : F.X h) :
    ‖(F.group h).S t v‖ ≤ ‖v‖ :=
  norm_ofBounded_apply_le (F.L h) (F.dissipative h) ht v

/-- The discrete solution `ιₕ e^{t Lₕ} v`. -/
def sol (h : κ) (v : F.X h) (t : ℝ) : E := F.incl h ((F.group h).S t v)

@[simp] theorem sol_zero (h : κ) (v : F.X h) : F.sol h v 0 = F.incl h v := by
  simp [sol, group]

theorem norm_sol_sub_sol_le (h : κ) (v w : F.X h) {t : ℝ} (ht : 0 ≤ t) :
    ‖F.sol h v t - F.sol h w t‖ ≤ ‖F.incl h‖ * ‖v - w‖ := by
  rw [sol, sol, ← _root_.map_sub, ← _root_.map_sub]
  refine ((F.incl h).le_opNorm _).trans ?_
  gcongr
  exact F.norm_group_apply_le h ht _

/-- **Comparison trajectories** on `[0, T]`: for each datum of `Data`, discrete trajectories
`pₕ(t)` with right derivatives `pₕ'(t)` (as for `ApproxFEEC.Comparison`). -/
structure Comparison (T : ℝ) where
  /-- the data -/
  Data : Set E
  /-- the comparison trajectories -/
  p : E → ∀ h, ℝ → F.X h
  /-- their derivatives -/
  p' : E → ∀ h, ℝ → F.X h
  continuousOn : ∀ x ∈ Data, ∀ h, ContinuousOn (p x h) (Icc 0 T)
  continuousOn' : ∀ x ∈ Data, ∀ h, ContinuousOn (p' x h) (Icc 0 T)
  hasDerivWithinAt : ∀ x ∈ Data, ∀ h, ∀ t ∈ Ico 0 T,
    HasDerivWithinAt (p x h) (p' x h t) (Ici t) t

variable {F} in
/-- The **consistency defect** `pₕ' - Lₕ pₕ`. -/
def Comparison.defect {T : ℝ} (P : F.Comparison T) (x : E) (h : κ) (t : ℝ) : F.X h :=
  P.p' x h t - F.L h (P.p x h t)

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- A **rate class** on `[0, T]`: comparison trajectories with best approximation
`‖S(t) x - ιₕ pₕ(t)‖ ≤ C hᵅ ‖x‖_c` and consistency `‖pₕ' - Lₕ pₕ‖ ≤ C' hᵅ ‖x‖_c`. -/
structure RateClass (T : ℝ) extends F.Comparison T where
  /-- the norm of the class -/
  classNorm : E → ℝ
  /-- the mesh size -/
  meshSize : κ → ℝ
  /-- the order -/
  α : ℝ
  /-- the approximation constant -/
  C : ℝ
  /-- the consistency constant -/
  C' : ℝ
  approx : ∀ x ∈ Data, ∀ h, ∀ t ∈ Icc 0 T,
    ‖hA.semigroup.S t x - F.incl h (p x h t)‖ ≤ C * meshSize h ^ α * classNorm x
  consistency : ∀ x ∈ Data, ∀ h, ∀ t ∈ Icc 0 T,
    ‖toComparison.defect x h t‖ ≤ C' * meshSize h ^ α * classNorm x

/-- An **orbit-consistent core**: a subspace of data with comparisons on every horizon `[0, T]`
approximating the exact orbit `S(t) x` through `ιₕ`, with consistency defects tending to `0`,
both uniformly on `[0, T]`. [Pazy1983], §3.4 -/
structure Core where
  /-- the core -/
  Data : Submodule 𝕜 E
  /-- the comparisons -/
  cmp : ∀ T : ℝ, F.Comparison T
  data_eq : ∀ T, (cmp T).Data = Data
  tendsto_approx : ∀ T, ∀ x ∈ Data, TendstoUniformlyOn
    (fun h t => F.incl h ((cmp T).p x h t)) (fun t => hA.semigroup.S t x) F.l (Icc 0 T)
  tendsto_defect : ∀ T, ∀ x ∈ Data, TendstoUniformlyOn
    (fun h t => ‖(cmp T).defect x h t‖) (fun _ => 0) F.l (Icc 0 T)

/-- **Best approximation plus consistency** for dissipative discretizations. -/
theorem norm_sub_sol_le {T : ℝ} (P : F.Comparison T) {x : E} (hx : x ∈ P.Data) (h : κ) :
    ∀ t ∈ Icc 0 T, ‖hA.semigroup.S t x - F.sol h (P.p x h 0) t‖ ≤
      ‖hA.semigroup.S t x - F.incl h (P.p x h t)‖ +
        ‖F.incl h‖ * ∫ s in (0 : ℝ)..t, ‖P.defect x h s‖ :=
  norm_sub_le_of_defect_of_dissipative (F.L h) (F.dissipative h) (F.incl h)
    (P.continuousOn x hx h) (P.continuousOn' x hx h) (P.hasDerivWithinAt x hx h)

variable {F} in
/-- The comparison initial values of a core read in `E` converge to the datum. -/
theorem Core.tendsto_incl_p (Z : F.Core) {T : ℝ} (hT : 0 ≤ T) {x : E} (hx : x ∈ Z.Data) :
    Tendsto (fun h => F.incl h ((Z.cmp T).p x h 0)) F.l (𝓝 x) := by
  have h0 := (Z.tendsto_approx T x hx).tendsto_at (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)
  rwa [C0Semigroup.S_zero_apply] at h0

/-- **The approximation property, derived**: `ιₕ πₕ x → x` on the closure of a core. -/
theorem tendsto_incl_proj (Z : F.Core) {x : E} (hx : x ∈ Z.Data.topologicalClosure) :
    Tendsto (fun h => F.incl h (F.proj h x)) F.l (𝓝 x) := by
  set B := F.boundConst ^ 2 + 1
  have hB : 0 < B := by positivity
  have key : ∀ (h : κ) (y : E) (v : F.X h),
      ‖F.incl h (F.proj h y) - y‖ ≤ B * ‖y - F.incl h v‖ := fun h y v => by
    have e : F.incl h (F.proj h y) - y =
        F.incl h (F.proj h (y - F.incl h v)) - (y - F.incl h v) := by
      rw [_root_.map_sub, _root_.map_sub, F.proj_incl]; abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have := F.norm_incl_proj_le h (y - F.incl h v)
    linarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < ε / (2 * B) := by positivity
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ hε'
  rw [dist_eq_norm] at hxy
  have hc := (Metric.tendsto_nhds.1 (Z.tendsto_incl_p le_rfl (SetLike.mem_coe.1 hy))) _ hε'
  filter_upwards [hc] with h hh
  rw [dist_eq_norm] at hh ⊢
  set v := (Z.cmp 0).p y h 0
  have e : F.incl h (F.proj h x) - x =
      F.incl h (F.proj h (x - y)) - (x - y) + (F.incl h (F.proj h y) - y) := by
    rw [_root_.map_sub, _root_.map_sub]; abel
  rw [e]
  have h1 : ‖F.incl h (F.proj h (x - y)) - (x - y)‖ ≤ B * ‖x - y‖ := by
    have := key h (x - y) 0
    rwa [_root_.map_zero, sub_zero] at this
  have h2 := key h y v
  rw [norm_sub_rev] at hh
  have : B * ‖x - y‖ + B * ‖y - F.incl h v‖ < ε := by
    have a1 : B * ‖x - y‖ < B * (ε / (2 * B)) := mul_lt_mul_of_pos_left hxy hB
    have a2 : B * ‖y - F.incl h v‖ < B * (ε / (2 * B)) := mul_lt_mul_of_pos_left hh hB
    have : B * (ε / (2 * B)) = ε / 2 := by field_simp
    linarith
  exact (norm_add_le _ _).trans_lt (by linarith)

/-! ### The Trotter–Kato bridge -/

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
variable (A) in
open scoped Classical in
/-- `A` on `D(A)`, extended by `0`. -/
def genExt (x : E) : E :=
  if hx : x ∈ A.domain then A ⟨x, hx⟩ else 0

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem genExt_of_mem {x : E} (hx : x ∈ A.domain) : genExt A x = A ⟨x, hx⟩ := by
  unfold genExt; simp [hx]

/-- Comparison trajectories `pₕ(t) = Rₕ S(t) x` of a bounded `Rₕ : E → Xₕ` on `D(A)`, with
derivatives `Rₕ S(t) A x`. -/
def Comparison.ofOperator (R : ∀ h, E →L[𝕜] F.X h) (T : ℝ) : F.Comparison T where
  Data := A.domain
  p x h t := R h (hA.semigroup.S t x)
  p' x h t := R h (hA.semigroup.S t (genExt A x))
  continuousOn _ _ h := (R h).continuous.comp_continuousOn
    ((hA.semigroup.strongCont _).mono Icc_subset_Ici_self)
  continuousOn' _ _ h := (R h).continuous.comp_continuousOn
    ((hA.semigroup.strongCont _).mono Icc_subset_Ici_self)
  hasDerivWithinAt x hx h t ht := by
    have hd := hA.hasDerivWithinAt_semigroup ⟨x, hx⟩ ht.1
    rw [← genExt_of_mem hx] at hd
    exact ((R h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hd

/-- **The Trotter–Kato bridge** for dissipative discretizations: uniformly bounded `Rₕ : E → Xₕ`
with `ιₕ Rₕ y → y`, and a defect identity `Rₕ (A y) - Lₕ (Rₕ y) = Δₕ (A y) + Δₕ' y` on `D(A)`
with uniformly bounded `Δₕ`, `Δₕ'` tending to `0` pointwise, give the core `D(A)`; uniformity on
`[0, T]` comes from the compactness of the orbits `S([0, T]) x`, `S([0, T]) A x`.
[Pazy1983], §3.4 -/
def Core.ofOperator (R : ∀ h, E →L[𝕜] F.X h) (hR : ∃ C, ∀ h, ‖R h‖ ≤ C)
    (happrox : ∀ y, Tendsto (fun h => F.incl h (R h y)) F.l (𝓝 y))
    (Δ Δ' : ∀ h, E →L[𝕜] F.X h) (hΔ : ∃ C, ∀ h, ‖Δ h‖ ≤ C ∧ ‖Δ' h‖ ≤ C)
    (hdef : ∀ h (y : A.domain), R h (A y) - F.L h (R h y) = Δ h (A y) + Δ' h y)
    (hΔ0 : ∀ y, Tendsto (fun h => ‖Δ h y‖) F.l (𝓝 0))
    (hΔ'0 : ∀ y, Tendsto (fun h => ‖Δ' h y‖) F.l (𝓝 0)) : F.Core where
  Data := A.domain
  cmp T := Comparison.ofOperator F R T
  data_eq _ := rfl
  tendsto_approx T x _ := by
    obtain ⟨C, hC⟩ := hR
    set B : ∀ _ : κ, E →L[𝕜] E := fun h => ContinuousLinearMap.id 𝕜 E - F.incl h ∘L R h
    have hB : ∀ h y, ‖B h y‖ ≤ (1 + F.boundConst * max C 0) * ‖y‖ := fun h y => by
      have h2 : ‖F.incl h (R h y)‖ ≤ F.boundConst * (max C 0 * ‖y‖) :=
        (F.norm_incl_apply_le h _).trans (mul_le_mul_of_nonneg_left
          (((R h).le_opNorm y).trans (mul_le_mul_of_nonneg_right
            ((hC h).trans (le_max_left _ _)) (norm_nonneg _))) F.boundConst_nonneg)
      calc ‖B h y‖ ≤ ‖y‖ + ‖F.incl h (R h y)‖ := norm_sub_le _ _
        _ ≤ _ := by nlinarith [norm_nonneg y]
    have hlim : ∀ y, Tendsto (fun h => ‖B h y‖) F.l (𝓝 0) := fun y => by
      have := tendsto_iff_norm_sub_tendsto_zero.1 (happrox y)
      refine this.congr fun h => ?_
      rw [norm_sub_rev]; rfl
    have hcpt : IsCompact ((fun t => hA.semigroup.S t x) '' Icc 0 T) :=
      isCompact_Icc.image_of_continuousOn ((hA.semigroup.strongCont x).mono Icc_subset_Ici_self)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [eventually_forall_norm_lt_of_tendsto hB hlim hcpt hε] with h hh t ht
    have := hh _ (mem_image_of_mem _ ht)
    rw [dist_eq_norm]
    simpa [B, Comparison.ofOperator] using this
  tendsto_defect T x hx := by
    obtain ⟨C, hC⟩ := hΔ
    have hb1 : ∀ h y, ‖Δ h y‖ ≤ C * ‖y‖ := fun h y => ((Δ h).le_opNorm y).trans
      (mul_le_mul_of_nonneg_right (hC h).1 (norm_nonneg _))
    have hb2 : ∀ h y, ‖Δ' h y‖ ≤ C * ‖y‖ := fun h y => ((Δ' h).le_opNorm y).trans
      (mul_le_mul_of_nonneg_right (hC h).2 (norm_nonneg _))
    have hcpt1 : IsCompact ((fun t => hA.semigroup.S t x) '' Icc 0 T) :=
      isCompact_Icc.image_of_continuousOn ((hA.semigroup.strongCont x).mono Icc_subset_Ici_self)
    have hcpt2 : IsCompact ((fun t => hA.semigroup.S t (genExt A x)) '' Icc 0 T) :=
      isCompact_Icc.image_of_continuousOn ((hA.semigroup.strongCont _).mono Icc_subset_Ici_self)
    have hdefect : ∀ h, ∀ t ∈ Icc 0 T, ‖(Comparison.ofOperator F R T).defect x h t‖ ≤
        ‖Δ h (hA.semigroup.S t (genExt A x))‖ + ‖Δ' h (hA.semigroup.S t x)‖ := fun h t ht => by
      have e := hdef h ⟨_, hA.semigroup_mem_domain ⟨x, hx⟩ ht.1⟩
      rw [hA.apply_semigroup ⟨x, hx⟩ ht.1] at e
      change ‖R h (hA.semigroup.S t (genExt A x)) - F.L h (R h (hA.semigroup.S t x))‖ ≤ _
      rw [genExt_of_mem hx]
      rw [e]
      exact norm_add_le _ _
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [eventually_forall_norm_lt_of_tendsto hb1 hΔ0 hcpt2 (half_pos hε),
      eventually_forall_norm_lt_of_tendsto hb2 hΔ'0 hcpt1 (half_pos hε)] with h h1 h2 t ht
    rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg (norm_nonneg _)]
    have := hdefect h t ht
    linarith [h1 _ (mem_image_of_mem _ ht), h2 _ (mem_image_of_mem _ ht)]

/-- **The Trotter–Kato core is dense**: its data `D(A)` are dense (an m-dissipative operator is
densely defined), so `dissipFEEC_converges` applies to every datum. -/
theorem Core.ofOperator_data_closure (R : ∀ h, E →L[𝕜] F.X h) (hR : ∃ C, ∀ h, ‖R h‖ ≤ C)
    (happrox : ∀ y, Tendsto (fun h => F.incl h (R h y)) F.l (𝓝 y))
    (Δ Δ' : ∀ h, E →L[𝕜] F.X h) (hΔ : ∃ C, ∀ h, ‖Δ h‖ ≤ C ∧ ‖Δ' h‖ ≤ C)
    (hdef : ∀ h (y : A.domain), R h (A y) - F.L h (R h y) = Δ h (A y) + Δ' h y)
    (hΔ0 : ∀ y, Tendsto (fun h => ‖Δ h y‖) F.l (𝓝 0))
    (hΔ'0 : ∀ y, Tendsto (fun h => ‖Δ' h y‖) F.l (𝓝 0)) :
    (Core.ofOperator F R hR happrox Δ Δ' hΔ hdef hΔ0 hΔ'0).Data.topologicalClosure = ⊤ := by
  exact Submodule.dense_iff_topologicalClosure_eq_top.1 hA.dense_domain

end DissipFEEC

/-! ### The dissipative FEEC theorem -/

section Main

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
variable {A : E →ₗ.[𝕜] E} {hA : A.IsMDissipative} {κ : Type*} (F : DissipFEEC.{u} hA κ)

open DissipFEEC

variable (hA) in
/-- **1. Well-posedness and energy** (Lumer–Phillips): for `x ∈ D(A)`, `t ↦ S(t) x` is a
classical solution on `[0, T]`, the only strong solution, with nonincreasing energy and the
energy identity `‖S(t) x‖² = ‖x‖² + ∫₀ᵗ 2 re ⟪S(s) A x, S(s) x⟫ ds`. -/
theorem dissipFEEC_wellPosed (x : A.domain) (T : ℝ) :
    Evolution.IsClassicalSolution A (Icc 0 T) 0 (fun t => hA.semigroup.S t x) ∧
    (∀ U, U 0 = (x : E) → Evolution.IsStrongSolution A (Icc 0 T) 0 U →
      EqOn U (fun t => hA.semigroup.S t x) (Icc 0 T)) ∧
    (∀ s t, 0 ≤ s → s ≤ t → ‖hA.semigroup.S t x‖ ≤ ‖hA.semigroup.S s x‖) ∧
    ∀ t, 0 ≤ t → ‖hA.semigroup.S t x‖ ^ 2 = ‖(x : E)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, 2 * RCLike.re ⟪hA.semigroup.S s (A x), hA.semigroup.S s x⟫_𝕜 := by
  have hcl : Evolution.IsClassicalSolution A (Icc 0 T) 0 (fun t => hA.semigroup.S t x) := by
    have h := hA.semigroup.isClassicalSolution_orbit (hA.mem_semigroup_generator_domain x) 0 T
    rw [hA.generator_semigroup] at h
    simpa using h
  refine ⟨hcl, fun U hU0 hU => ?_, fun s t hs hst => ?_, fun t ht =>
    hA.norm_sq_semigroup_apply x ht⟩
  · exact hU.unique hA.dissipative hcl.toIsStrongSolution (by rw [hU0]; simp)
  · have e : hA.semigroup.S t x = hA.semigroup.S (t - s) (hA.semigroup.S s x) := by
      rw [← C0Semigroup.S_add_apply _ (by linarith) hs, sub_add_cancel]
    rw [e]
    exact ((hA.semigroup.S (t - s)).le_opNorm _).trans (by
      simpa using mul_le_mul_of_nonneg_right (hA.isContraction_semigroup _ (by linarith))
        (norm_nonneg (hA.semigroup.S s x)))

/-- **2. Constraint propagation**: for the closed constraint `K`, `S(t) K ⊆ K` for all `t ≥ 0`
iff the resolvents map `K` into `K`, iff the stationary problem is solvable within `K`. -/
theorem dissipFEEC_propagates_iff :
    ((∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K) ↔
      ∀ μ : ℝ, 0 < μ → ∀ y ∈ F.K, Operator.resolvent A (μ : 𝕜) y ∈ F.K) ∧
    ((∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K) ↔
      ∃ μ : ℝ, 0 < μ ∧ ∀ y ∈ F.K, ∃ u : A.domain, (u : E) ∈ F.K ∧ (μ : 𝕜) • (u : E) - A u = y) ∧
    (A.IsReducing F.K ↔ (∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K) ∧
      ∀ t, 0 ≤ t → ∀ x ∈ F.Kᗮ, hA.semigroup.S t x ∈ F.Kᗮ) :=
  ⟨hA.invariant_iff_resolvent F.isClosed_K, hA.invariant_iff_exists_solve F.isClosed_K,
    hA.isReducing_iff⟩

/-- **3a. Convergence on the core**, from the comparison initial values, uniformly on `[0, T]`. -/
theorem dissipFEEC_converges_core (Z : F.Core) (T : ℝ) {x : E} (hx : x ∈ Z.Data) :
    TendstoUniformlyOn (fun h t => F.sol h ((Z.cmp T).p x h 0) t)
      (fun t => hA.semigroup.S t x) F.l (Icc 0 T) := by
  have hxP : x ∈ (Z.cmp T).Data := by rw [Z.data_eq]; exact hx
  have ha := Metric.tendstoUniformlyOn_iff.1 (Z.tendsto_approx T x hx)
  have hd := Metric.tendstoUniformlyOn_iff.1 (Z.tendsto_defect T x hx)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set T' := max T 0
  set C := F.boundConst
  have hC := F.boundConst_nonneg
  set δ := ε / (2 * (C * T' + 1))
  have hδ : 0 < δ := by positivity
  filter_upwards [ha _ (half_pos hε), hd δ hδ] with h h1 h2 t ht
  rw [dist_eq_norm]
  have hb := F.norm_sub_sol_le (Z.cmp T) hxP h t ht
  have hint : ∫ s in (0 : ℝ)..t, ‖(Z.cmp T).defect x h s‖ ≤ δ * t :=
    integral_le_mul_of_norm_le ht.1 fun s hs => by
      have := h2 s ⟨hs.1, hs.2.trans ht.2⟩
      rw [dist_eq_norm, zero_sub, norm_neg] at this
      exact this.le
  have hT' : t ≤ T' := ht.2.trans (le_max_left _ _)
  have i1 : ‖F.incl h‖ * ∫ s in (0 : ℝ)..t, ‖(Z.cmp T).defect x h s‖ ≤ C * (δ * T') :=
    mul_le_mul (F.norm_incl_le h) (hint.trans (mul_le_mul_of_nonneg_left hT' hδ.le))
      (intervalIntegral.integral_nonneg ht.1 fun _ _ => norm_nonneg _) hC
  have i2 : C * (δ * T') < ε / 2 := by
    have e : C * (δ * T') = ε / 2 * (C * T' / (C * T' + 1)) := by
      simp only [δ]; field_simp
    rw [e]
    have hCT : 0 ≤ C * T' := mul_nonneg hC (le_max_right _ _)
    have : C * T' / (C * T' + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    nlinarith
  have := h1 t ht
  rw [dist_eq_norm] at this
  linarith

/-- **3b. Convergence on the closure of the core**, for every family `vₕ` with `ιₕ vₕ → x`,
uniformly on `[0, T]` (stability `‖v‖ ≤ C ‖ιₕ v‖`, contractivity of `S(t)` and `e^{tLₕ}`, and
density). -/
theorem dissipFEEC_converges (Z : F.Core) (T : ℝ) {x : E} (hx : x ∈ Z.Data.topologicalClosure)
    {v : ∀ h, F.X h} (hv : Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x)) :
    TendstoUniformlyOn (fun h t => F.sol h (v h) t) (fun t => hA.semigroup.S t x) F.l
      (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT | hT
  · rw [Icc_eq_empty (by linarith)]; exact tendstoUniformlyOn_empty
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set C := F.boundConst
  have hC := F.boundConst_nonneg
  set B := C ^ 2 + 1
  have hB : 0 < B := by positivity
  have hε' : 0 < ε / (4 * B) := by positivity
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ hε'
  rw [dist_eq_norm] at hxy
  have hy' : y ∈ Z.Data := SetLike.mem_coe.1 hy
  have hc := Metric.tendstoUniformlyOn_iff.1 (dissipFEEC_converges_core F Z T hy') _
    (show 0 < ε / 4 by positivity)
  filter_upwards [hc, (Metric.tendsto_nhds.1 (Z.tendsto_incl_p hT hy')) _ hε',
    Metric.tendsto_nhds.1 hv _ hε'] with h h1 h2 h3 t ht
  set w := (Z.cmp T).p y h 0
  rw [dist_eq_norm] at h2 h3 ⊢
  have a1 : ‖hA.semigroup.S t x - hA.semigroup.S t y‖ ≤ ‖x - y‖ := by
    rw [← _root_.map_sub]
    exact ((hA.semigroup.S t).le_opNorm _).trans (by
      simpa using mul_le_mul_of_nonneg_right (hA.isContraction_semigroup t ht.1)
        (norm_nonneg (x - y)))
  have a2 : ‖hA.semigroup.S t y - F.sol h w t‖ < ε / 4 := by
    have := h1 t ht; rwa [dist_eq_norm] at this
  have a3 : ‖F.sol h w t - F.sol h (v h) t‖ ≤ C * ‖w - v h‖ :=
    (F.norm_sol_sub_sol_le h _ _ ht.1).trans
      (mul_le_mul_of_nonneg_right (F.norm_incl_le h) (norm_nonneg _))
  have a4 : ‖w - v h‖ ≤ C * (‖F.incl h w - y‖ + ‖y - x‖ + ‖x - F.incl h (v h)‖) := by
    refine (F.norm_le_norm_incl h _).trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [_root_.map_sub]
    calc ‖F.incl h w - F.incl h (v h)‖ =
        ‖(F.incl h w - y) + (y - x) + (x - F.incl h (v h))‖ := by abel_nf
      _ ≤ _ := norm_add₃_le
  have e : hA.semigroup.S t x - F.sol h (v h) t =
      (hA.semigroup.S t x - hA.semigroup.S t y) + (hA.semigroup.S t y - F.sol h w t) +
        (F.sol h w t - F.sol h (v h) t) := by abel
  rw [e]
  refine norm_add₃_le.trans_lt ?_
  rw [norm_sub_rev] at h3
  have hyx : ‖y - x‖ < ε / (4 * B) := by rw [norm_sub_rev]; exact hxy
  have hsum : ‖F.incl h w - y‖ + ‖y - x‖ + ‖x - F.incl h (v h)‖ < 3 * (ε / (4 * B)) := by
    linarith
  have hCC : C * (C * (‖F.incl h w - y‖ + ‖y - x‖ + ‖x - F.incl h (v h)‖)) ≤
      C ^ 2 * (3 * (ε / (4 * B))) := by
    rw [← mul_assoc, ← pow_two]
    exact mul_le_mul_of_nonneg_left hsum.le (sq_nonneg _)
  have key : ε / (4 * B) + C ^ 2 * (3 * (ε / (4 * B))) ≤ 3 * (ε / 4) := by
    have e1 : ε / (4 * B) + C ^ 2 * (3 * (ε / (4 * B))) = ε / 4 * ((1 + 3 * C ^ 2) / B) := by
      field_simp
    rw [e1]
    have : (1 + 3 * C ^ 2) / B ≤ 3 := (div_le_iff₀ hB).2 (by simp only [B]; linarith)
    nlinarith
  have hxy' : ‖x - y‖ < ε / (4 * B) := hxy
  linarith [a3.trans (mul_le_mul_of_nonneg_left a4 hC)]

/-- **3c. The rate: best approximation plus consistency** (plus the initial mismatch). -/
theorem dissipFEEC_rate {T : ℝ} (R : F.RateClass T) {x : E} (hx : x ∈ R.Data) (h : κ)
    (v : F.X h) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖hA.semigroup.S t x - F.sol h v t‖ ≤
      (R.C + ‖F.incl h‖ * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖F.incl h‖ * ‖R.p x h 0 - v‖ := by
  have hb := F.norm_sub_sol_le R.toComparison hx h t ht
  have hint : ∫ s in (0 : ℝ)..t, ‖R.toComparison.defect x h s‖ ≤
      R.C' * R.meshSize h ^ R.α * R.classNorm x * t :=
    integral_le_mul_of_norm_le ht.1 fun s hs => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact R.consistency x hx h s ⟨hs.1, hs.2.trans ht.2⟩
  have h1 := R.approx x hx h t ht
  have h2 := mul_le_mul_of_nonneg_left hint (norm_nonneg (F.incl h))
  have h3 := F.norm_sol_sub_sol_le h (R.p x h 0) v ht.1
  have e : hA.semigroup.S t x - F.sol h v t =
      (hA.semigroup.S t x - F.sol h (R.p x h 0) t) + (F.sol h (R.p x h 0) t - F.sol h v t) := by
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have : (R.C + ‖F.incl h‖ * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) =
      R.C * R.meshSize h ^ R.α * R.classNorm x +
        ‖F.incl h‖ * (R.C' * R.meshSize h ^ R.α * R.classNorm x * t) := by ring
  rw [this]
  linarith

/-- **4a. The constraint residual is bounded by the error** (invariant `K`, datum in `K`,
`t ≥ 0`). -/
theorem dissipFEEC_residual_le (hK : ∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K)
    {x : E} (hxK : x ∈ F.K) (h : κ) (v : F.X h) {t : ℝ} (ht : 0 ≤ t) :
    infDist (F.sol h v t) (F.K : Set E) ≤ ‖hA.semigroup.S t x - F.sol h v t‖ := by
  rw [norm_sub_rev, ← dist_eq_norm]
  exact infDist_le_dist_of_mem (hK t ht x hxK)

/-- **4a. Residual of an invariant constraint**: for `x ∈ K` in the closure of the core and
every convergent family of discrete initial values, the residual tends to `0` uniformly on
`[0, T]`. -/
theorem dissipFEEC_residual (hK : ∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K)
    (Z : F.Core) (T : ℝ) {x : E} (hx : x ∈ Z.Data.topologicalClosure) (hxK : x ∈ F.K)
    {v : ∀ h, F.X h} (hv : Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x)) :
    TendstoUniformlyOn (fun h t => infDist (F.sol h (v h) t) (F.K : Set E))
      (fun _ => 0) F.l (Icc 0 T) := by
  have hc := Metric.tendstoUniformlyOn_iff.1 (dissipFEEC_converges F Z T hx hv)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hc ε hε] with h hh t ht
  have := hh t ht
  rw [dist_eq_norm] at this
  rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg infDist_nonneg]
  exact (dissipFEEC_residual_le F hK hxK h (v h) ht.1).trans_lt this

/-- **4b. Residual of a solution leaving a constraint** (per datum, any closed nonempty `Q`):
if `S(t) x ∉ Q`, the residuals `dist(ιₕ e^{tLₕ} vₕ, Q)` of every convergent family tend to
`dist(S(t) x, Q) > 0`. -/
theorem dissipFEEC_residual_not_mem (Z : F.Core) {Q : Set E} (hQ : IsClosed Q) (hQne : Q.Nonempty)
    {x : E} (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h}
    (hv : Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x)) {t : ℝ} (ht : 0 ≤ t)
    (hout : hA.semigroup.S t x ∉ Q) :
    0 < infDist (hA.semigroup.S t x) Q ∧
      Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l
        (𝓝 (infDist (hA.semigroup.S t x) Q)) :=
  ⟨(hQ.notMem_iff_infDist_pos hQne).1 hout, ((continuous_infDist_pt Q).tendsto _).comp
    ((dissipFEEC_converges F Z t hx hv).tendsto_at ⟨ht, le_rfl⟩)⟩

/-- **4c. A non-invariant constraint is left** by a datum of `K` at some `t ∈ [0, T]`; when
`D(A) ∩ K` is dense in `K`, by a datum of `D(A) ∩ K`. -/
theorem dissipFEEC_exists_not_mem (hK : ¬ ∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K)
    {T : ℝ} (hT : 0 < T) :
    (∃ x ∈ F.K, ∃ t ∈ Icc 0 T, hA.semigroup.S t x ∉ F.K) ∧
    ((∀ k ∈ F.K, k ∈ closure ((A.domain : Set E) ∩ F.K)) →
      ∃ x : A.domain, (x : E) ∈ F.K ∧ ∃ t ∈ Icc 0 T, hA.semigroup.S t x ∉ F.K) := by
  have h1 : ∃ x ∈ F.K, ∃ t ∈ Icc 0 T, hA.semigroup.S t x ∉ F.K := by
    by_contra hc
    push Not at hc
    exact hK fun t ht x hx => hA.semigroup.forall_nonneg_of_forall_Icc hT
      (P := (F.K : Set E)) (fun y hy s hs => hc y hy s hs) x hx t ht
  refine ⟨h1, fun hdense => ?_⟩
  by_contra hc
  push Not at hc
  refine hK fun t ht => ?_
  have hP : ∀ y ∈ (A.domain : Set E) ∩ F.K, ∀ s, 0 ≤ s →
      hA.semigroup.S s y ∈ (A.domain : Set E) ∩ F.K :=
    hA.semigroup.forall_nonneg_of_forall_Icc hT fun y hy s hs =>
      ⟨hA.semigroup_mem_domain ⟨y, hy.1⟩ hs.1, hc ⟨y, hy.1⟩ hy.2 s hs⟩
  exact hA.semigroup.mem_of_dense F.isClosed_K hdense fun y hy => (hP y hy t ht).2

/-- **4c. Residuals of a non-invariant constraint have a positive limit**: some datum of `K`
(of `D(A) ∩ K` when that is dense in `K`) leaves `K` at some `t ∈ [0, T]`, and, for that datum
in the closure of the core, the residuals of every convergent discretization tend to
`dist(S(t) x, K) > 0` and stay eventually above half of it. -/
theorem dissipFEEC_residual_not_invariant (Z : F.Core)
    (hK : ¬ ∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K) {T : ℝ} (hT : 0 < T) :
    ∃ x ∈ F.K, ∃ t ∈ Icc 0 T, hA.semigroup.S t x ∉ F.K ∧
      0 < infDist (hA.semigroup.S t x) (F.K : Set E) ∧
      (x ∈ Z.Data.topologicalClosure → ∀ v : ∀ h, F.X h,
        Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
        Tendsto (fun h => infDist (F.sol h (v h) t) (F.K : Set E)) F.l
          (𝓝 (infDist (hA.semigroup.S t x) (F.K : Set E))) ∧
        ∀ᶠ h in F.l, infDist (hA.semigroup.S t x) (F.K : Set E) / 2 <
          infDist (F.sol h (v h) t) (F.K : Set E)) := by
  obtain ⟨x, hxK, t, ht, hout⟩ := (dissipFEEC_exists_not_mem F hK hT).1
  have hpos := (F.isClosed_K.notMem_iff_infDist_pos ⟨0, F.K.zero_mem⟩).1 hout
  refine ⟨x, hxK, t, ht, hout, hpos, fun hxc v hv => ?_⟩
  have hlim := (dissipFEEC_residual_not_mem F Z F.isClosed_K ⟨0, F.K.zero_mem⟩ hxc hv ht.1
    hout).2
  exact ⟨hlim, (tendsto_order.1 hlim).1 _ (half_lt_self hpos)⟩

/-- The conclusion of the dissipative FEEC theorem (instances state their headline as
`F.Verdict Z`, proved by `dissipFEEC F Z`). -/
abbrev DissipFEEC.Verdict (Z : F.Core) : Prop :=
    -- 1. well-posedness and energy (Lumer–Phillips)
    (∀ x : A.domain, ∀ T : ℝ,
      Evolution.IsClassicalSolution A (Icc 0 T) 0 (fun t => hA.semigroup.S t x) ∧
      (∀ U, U 0 = (x : E) → Evolution.IsStrongSolution A (Icc 0 T) 0 U →
        EqOn U (fun t => hA.semigroup.S t x) (Icc 0 T)) ∧
      (∀ s t, 0 ≤ s → s ≤ t → ‖hA.semigroup.S t x‖ ≤ ‖hA.semigroup.S s x‖) ∧
      ∀ t, 0 ≤ t → ‖hA.semigroup.S t x‖ ^ 2 = ‖(x : E)‖ ^ 2 +
        ∫ s in (0 : ℝ)..t, 2 * RCLike.re ⟪hA.semigroup.S s (A x), hA.semigroup.S s x⟫_𝕜) ∧
    -- 2. propagation: invariance iff resolvent invariance iff solvability in `K`; reducing iff
    -- `K` and `Kᗮ` invariant
    (((∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K) ↔
      ∀ μ : ℝ, 0 < μ → ∀ y ∈ F.K, Operator.resolvent A (μ : 𝕜) y ∈ F.K) ∧
    ((∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K) ↔
      ∃ μ : ℝ, 0 < μ ∧ ∀ y ∈ F.K, ∃ u : A.domain, (u : E) ∈ F.K ∧ (μ : 𝕜) • (u : E) - A u = y) ∧
    (A.IsReducing F.K ↔ (∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K) ∧
      ∀ t, 0 ≤ t → ∀ x ∈ F.Kᗮ, hA.semigroup.S t x ∈ F.Kᗮ)) ∧
    -- 3a. convergence on the core
    (∀ T : ℝ, ∀ x ∈ Z.Data, TendstoUniformlyOn
      (fun h t => F.sol h ((Z.cmp T).p x h 0) t) (fun t => hA.semigroup.S t x) F.l (Icc 0 T)) ∧
    -- 3b. convergence on the closure of the core, every convergent initial family; one exists
    (∀ T : ℝ, ∀ x ∈ Z.Data.topologicalClosure,
      Tendsto (fun h => F.incl h (F.proj h x)) F.l (𝓝 x) ∧
      ∀ v : ∀ h, F.X h, Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
        TendstoUniformlyOn (fun h t => F.sol h (v h) t) (fun t => hA.semigroup.S t x) F.l
          (Icc 0 T)) ∧
    -- 3c. rates: best approximation + consistency (+ initial mismatch)
    (∀ (T : ℝ) (R : F.RateClass T), ∀ x ∈ R.Data, ∀ h, ∀ v : F.X h, ∀ t ∈ Icc 0 T,
      ‖hA.semigroup.S t x - F.sol h v t‖ ≤
        (R.C + ‖F.incl h‖ * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) +
          ‖F.incl h‖ * ‖R.p x h 0 - v‖) ∧
    -- 4a. invariant constraint: residual bounded by the error, tends to `0`
    ((∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K) → ∀ x ∈ F.K,
      (∀ h (v : F.X h) t, 0 ≤ t → infDist (F.sol h v t) (F.K : Set E) ≤
        ‖hA.semigroup.S t x - F.sol h v t‖) ∧
      (x ∈ Z.Data.topologicalClosure → ∀ T : ℝ, ∀ v : ∀ h, F.X h,
        Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
        TendstoUniformlyOn (fun h t => infDist (F.sol h (v h) t) (F.K : Set E))
          (fun _ => 0) F.l (Icc 0 T))) ∧
    -- 4b. per datum: a solution leaving `Q` has residual tending to `dist(S(t) x, Q) > 0`
    (∀ Q : Set E, IsClosed Q → Q.Nonempty → ∀ x ∈ Z.Data.topologicalClosure,
      ∀ v : ∀ h, F.X h, Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) → ∀ t, 0 ≤ t →
      hA.semigroup.S t x ∉ Q → 0 < infDist (hA.semigroup.S t x) Q ∧
        Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l
          (𝓝 (infDist (hA.semigroup.S t x) Q))) ∧
    -- 4c. a non-invariant constraint is left by a datum of `K` (of `D(A) ∩ K` if dense), whose
    -- residuals have a positive limit
    ((¬ ∀ t, 0 ≤ t → ∀ x ∈ F.K, hA.semigroup.S t x ∈ F.K) → ∀ T : ℝ, 0 < T →
      ((∀ k ∈ F.K, k ∈ closure ((A.domain : Set E) ∩ F.K)) →
        ∃ x : A.domain, (x : E) ∈ F.K ∧ ∃ t ∈ Icc 0 T, hA.semigroup.S t x ∉ F.K) ∧
      ∃ x ∈ F.K, ∃ t ∈ Icc 0 T, hA.semigroup.S t x ∉ F.K ∧
        0 < infDist (hA.semigroup.S t x) (F.K : Set E) ∧
        (x ∈ Z.Data.topologicalClosure → ∀ v : ∀ h, F.X h,
          Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
          Tendsto (fun h => infDist (F.sol h (v h) t) (F.K : Set E)) F.l
            (𝓝 (infDist (hA.semigroup.S t x) (F.K : Set E))) ∧
          ∀ᶠ h in F.l, infDist (hA.semigroup.S t x) (F.K : Set E) / 2 <
            infDist (F.sol h (v h) t) (F.K : Set E)))

/-- **The dissipative FEEC theorem.** For a dissipative FEEC discretization `F` of `ξ' = A ξ`
with `A` m-dissipative (discrete Hilbert spaces with their own inner products, bounded
dissipative generators, uniformly bounded reading maps with uniformly bounded left inverses;
variational crimes allowed) and an orbit-consistent core `Z`:

1. (**well-posedness**, Lumer–Phillips) for `ξ₀ ∈ D(A)`, `t ↦ S(t) ξ₀` is a classical solution
   and the only strong one; its energy is nonincreasing, with the energy identity;
2. (**propagation**) `S(t) K ⊆ K` for `t ≥ 0` iff `(μ - A)⁻¹ K ⊆ K` for `μ > 0`, iff the
   stationary problem is solvable in `D(A) ∩ K`; `K` reduces `A` iff `K` and `Kᗮ` are invariant;
3. (**convergence**) on the core, on its closure for every family with `ιₕ vₕ → ξ₀`, uniformly on
   `[0, T]`, and the rate `(C + ‖ιₕ‖ C' t) hᵅ ‖ξ₀‖_c + ‖ιₕ‖ ‖pₕ(0) - v‖`;
4. (**constraint residual**) for invariant `K`: bounded by the error, tends to `0`; a solution
   leaving `Q` has residuals with the positive limit `dist(S(t) ξ₀, Q)`; a non-invariant `K` is
   left by data of `K` (of `D(A) ∩ K` when dense in `K`), with residuals of positive limit.

Cf. [Pazy1983], §1.4 (Thm 4.3), §3.4; [HolstStern2012], Thm 3.9, Thm 3.10 (elliptic analogues) -/
theorem dissipFEEC (Z : F.Core) : F.Verdict Z :=
  ⟨fun x T => dissipFEEC_wellPosed hA x T, dissipFEEC_propagates_iff F,
    fun T _ hx => dissipFEEC_converges_core F Z T hx,
    fun T _ hx => ⟨tendsto_incl_proj F Z hx, fun _ hv => dissipFEEC_converges F Z T hx hv⟩,
    fun _ R _ hx h v _ ht => dissipFEEC_rate F R hx h v ht,
    fun hK _ hxK => ⟨fun h v _ ht => dissipFEEC_residual_le F hK hxK h v ht,
      fun hx T _ hv => dissipFEEC_residual F hK Z T hx hxK hv⟩,
    fun _ hQ hQne _ hx _ hv _ ht hout => dissipFEEC_residual_not_mem F Z hQ hQne hx hv ht hout,
    fun hK _ hT => ⟨(dissipFEEC_exists_not_mem F hK hT).2,
      dissipFEEC_residual_not_invariant F Z hK hT⟩⟩

end Main

end Feec.HilbertComplex
