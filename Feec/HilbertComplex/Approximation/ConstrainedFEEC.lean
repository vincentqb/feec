module

public import Feec.HilbertComplex.Approximation.ConformingFamily
public import Feec.HilbertComplex.Approximation.Convergence
public import Feec.HilbertComplex.Approximation.DiscreteCohomology
public import Feec.HilbertComplex.Approximation.GraphApprox
public import Feec.HilbertComplex.InvariantCore

/-!
# The constrained FEEC theorem

A **constrained FEEC discretization** (`Feec.HilbertComplex.ConstrainedFEEC`) of a Hilbert
complex `H` (any finite index type `ι`, any `ComplexShape`; e.g. a window of a complex on `ℤ` or
a short complex on `Fin 3`) is a **conforming family** (`Feec.HilbertComplex.ConformingFamily`,
the data of [AFW2010], §3.3 with the bounds in `W`) with a closed constraint
(`ConformingFamily.withConstraint`):

* a family `Vₕ` (indexed by any type `κ`, along a filter `l`, e.g. `h → 0` or `N → ∞`) of
  finite-dimensional **subcomplexes** with **commuting cochain projections** `πₕ`, uniformly
  bounded in `W`;
* the **approximation property**: `dist(w, Vₕⁱ) → 0` for every `w ∈ Wⁱ`, so every `x ∈ W = ⊕ Wⁱ`
  is approximated by `∏ Vₕⁱ` (`ConformingFamily.dense`). The commuting projections upgrade it to
  the graph norm of `Γ(𝐝)` (`ConstrainedFEEC.dense_graph`: `‖ζ - Πₕ ζ‖_Γ ≤ 2 (1 + C) δ`), which
  drives the convergence;
* a closed **constraint subspace** `K` of the total space `W`.

Every finite element family with uniformly bounded smoothed projections is a conforming family
(`Feec.Models.ConformingFamilies`: Whitney forms and every admissible sequence `P_rΛ`, `P_r⁻Λ` on
the cube, parallelepipeds and star-shaped domains), so the theorem below holds for each of them,
on every window and with every closed constraint.

Its continuous problem is the Hodge wave equation `ξ' = L ξ` with `L = 𝐝 - 𝐝†` (the sign
convention of `Feec.HilbertComplex.wave`; with `L' = 𝐝† - 𝐝` it reads `ξ' = -L' ξ`), solved by
the isometric group `e^{tL}` (Stone); its discrete problem is the semi-discrete equation (4.10)
in `Vₕ`, with `ξₕ(0) = Pₕ ξ₀` (`ConstrainedFEEC.discrete`, `Pₕ` the elliptic projection (4.11)).

## Main results

The **constrained FEEC theorem** `constrainedFEEC` (verdict `ConstrainedFEEC.Verdict`, a
structure with one named field per conclusion, stated here) is the special case `ιₕ` = inclusion,
`πₕ = Πₕ` of the approximating FEEC theorem, proved in
`Feec.HilbertComplex.Approximation.ApproxConforming` from the verdict of `approxFEEC` with the core
of the wave Ritz projection (`ConstrainedFEEC.waveRitz`, the elliptic projection). Its fields:

1. `wellPosed` (`constrainedFEEC_wellPosed`): for `ξ₀ ∈ D(L)`, `t ↦ e^{tL} ξ₀` is a classical
   solution, the only strong and the only weak solution, and it conserves energy
   ([QuennevilleBelair2015], Thm 4.6, Thm 4.7).
2. `propagates_iff` (`constrainedFEEC_propagates_iff`): constraints propagate for all data in `K`
   and all times `t ∈ ℝ` iff `K` reduces `L` (Stone; [QuennevilleBelair2015], Prop. 4.17, with
   necessity); `constrainedFEEC_propagates`: strong solutions from `K` then stay in `K`;
   `constrainedFEEC_propagates_iff_domain` (data in `D(L) ∩ K`, when it is dense in `K`) and
   `constrainedFEEC_propagates_iff_of_grading` (forward strong solutions, for a graded complex).
3. `converges`, `converges_of_tendsto`, `exists_tendsto`: `ξₕ → ξ` uniformly on `[0, T]` for
   `ξ₀ ∈ D(L)`, and for every `ξ₀ ∈ W` as soon as `ξₕ(0) → ξ₀` ([QuennevilleBelair2015], Thm 4.14
   and the remark after it); `rate`: for data in a **rate class** on `[0, T]`
   (`ConstrainedFEEC.RateClass F T`: `D(L²)` data whose orbit on `[0, T]` is approximated in
   `Γ(𝐝)` to order `C hᵅ ‖ξ₀‖_class`, with `C` and `‖·‖_class` allowed to depend on `T`; e.g.
   `D(L³)` or Sobolev data under the approximation estimates of an instance, or degreewise regular
   data, `ConstrainedFEEC.RateClass.ofDegreewise`, from the static estimate
   `ConstrainedFEEC.RateClass.exists_mem_Kh_le_of_degreewise`),
   `‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + t)² C hᵅ ‖ξ₀‖_class` for `t ∈ [0, T]`, with
   `C_P = √12 ‖A‖` the uniform bound of the elliptic projections (`constrainedFEEC_rate`;
   [QuennevilleBelair2015], Prop. 4.13, Thm 4.14).
4. `residual_le`, `residual_tendsto`: if `K` reduces `L`, the **constraint residual** of the
   discrete solution is bounded by the error, `dist(ξₕ(t), K) ≤ ‖ξ(t) - ξₕ(t)‖`
   (`ConstrainedFEEC.infDist_le_norm_sub`), so it tends to `0` uniformly on `[0, T]` and, on a
   rate class, is at most the rate of the error (`ConstrainedFEEC.Verdict.residual_rate`);
   `leaves`: if `K` does not reduce `L`, then for every `T > 0` there are data in `K` (or in `Kᗮ`,
   the complementary constraint) whose exact solution leaves the constraint `Q` at some
   `t ∈ [0, T]`, and the residuals `dist(ξₕ(t), Q)` of every convergent discretization tend to
   `dist(ξ(t), Q) > 0`. For a graded complex and an `R`-invariant `K` (e.g. a product constraint)
   with `D(L) ∩ K` dense in `K`, the data lie in `D(L) ∩ K` itself and `Q = K` (`leaves_graded`).
   Without a grading, when `D(L) ∩ K` is dense in `K`, some datum of `D(L) ∩ K` leaves `K` at some
   `t ∈ [-T, T]` (`leaves_symm`).
5. `cohomology` (`ConformingFamily.eventually_bijective_cohomologyMap`): wherever `H` has closed
   range and finite-dimensional harmonic forms, the projections `πₕ` eventually induce
   isomorphisms `Hⁱ(H) ≅ Hⁱ(Vₕ)` ([AFW2010], Thm 3.4, Thm 3.5).

The cochain projections enter twice: the total projection `Πₕ` (`ConstrainedFEEC.piProj`)
commutes with `𝐝` and turns the approximation property in `W` into the graph-norm approximation
behind items 3 and 4 (`ConstrainedFEEC.dense_graph`), and they give the uniform discrete Poincaré
inequality `constrainedFEEC_discretePoincare` ([AFW2010], Thm 3.6).

Further: the data of the non-vacuity witness `constrainedFEEC_nonvacuous` (on `𝕜 --id--> 𝕜 → 0`
with `Vₕ = W` and `πₕ = id`, both branches of item 4 occur: `K = W` reduces `L`, and
`K = 𝕜 × 0 × 0` does not, so some datum of `D(L) ∩ K` has discrete residuals with a positive
limit; it also gives a rate class).

## Hypotheses

The density of `D(L) ∩ K` in `K` in the converse of item 4 with data in `D(L)` cannot be
dropped: if `D(L) ∩ K = 0`, no datum of `D(L) ∩ K` leaves `K`. Without a grading the converse is
stated for `K` or `Kᗮ` forward in time, or for `K` in both time directions. Forward invariance
of a closed subspace under an isometric group does not make it reducing. On the de Rham complex
over `ℝ`, where the wave equation reads `u' = ∂ₓv`, `v' = ∂ₓu`, the subspace
`K = {(f, -f) : f ∈ L²(0, ∞)}` is invariant in one time direction only (`u - v` is translated
and `u + v = 0` is preserved). Forward invariance of both `K` and `Kᗮ`
does make `K` reducing (`DissipFEEC.Verdict.isReducing_iff`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (approximation property, bounded cochain projections, Thm 3.4, Thm 3.6), §3.4 (Thm 3.9)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 5 (Thm 5.3)
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (approximation of Hilbert complexes by subcomplexes with bounded cochain projections)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4 (Thms 4.6, 4.7), §4.6 ((4.10), (4.11), Prop. 4.13, Thm 4.14), §4.10 (Prop. 4.17)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

namespace Feec.HilbertComplex

open _root_.Feec.HodgeWave

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

/-- **Degreewise approximation gives the approximation property of the total space**: the total
spaces `∏ Vₕⁱ` of a conforming family of a finite complex approximate every point of
`W = ⊕ Wⁱ`. -/
theorem ConformingFamily.dense {κ : Type*} {H : HilbertComplex 𝕜 c W} (F : ConformingFamily H κ) :
    ∀ x : PiLp 2 W, ∀ δ > 0, ∀ᶠ h in F.l, ∃ w ∈ totalSub (F.V h).V, ‖x - w‖ < δ := by
  intro x δ hδ
  set m : ℝ := (Fintype.card ι : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  set ε := δ / (m + 1)
  have hε : 0 < ε := div_pos hδ (by positivity)
  filter_upwards [Filter.eventually_all.2 fun i => F.eventually_exists_lt i (x i) hε] with h hh
  choose v hv hlt using hh
  refine ⟨WithLp.toLp 2 fun i => v i, fun i => hv i, ?_⟩
  refine (PiLp.norm_le_sum_norm _).trans_lt ?_
  have e : m * ε < δ := by
    have : m * ε = m / (m + 1) * δ := by simp only [ε]; field_simp
    rw [this]
    have h1 : m / (m + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  calc ∑ i, ‖(x - WithLp.toLp 2 fun i => v i) i‖ ≤ ∑ _i : ι, ε :=
        Finset.sum_le_sum fun i _ => by simpa using (hlt i).le
    _ = m * ε := by simp [m]
    _ < δ := e

/-- A **constrained FEEC discretization** of the Hodge wave equation of the Hilbert complex `H`
(on a finite index type): a conforming family (finite-dimensional subcomplexes `Vₕ`, `h : κ`
along the filter `l`, with commuting cochain projections `πₕ` uniformly bounded in `W` and the
approximation property) and a closed constraint subspace `K` of the total space. See [AFW2010],
§3.3, [Arnold2018], Ch. 5 and [QuennevilleBelair2015], §4.6, §4.7. -/
structure ConstrainedFEEC (H : HilbertComplex 𝕜 c W) (κ : Type*) extends ConformingFamily H κ where
  /-- the constraint subspace -/
  K : Submodule 𝕜 (PiLp 2 W)
  isClosed_K : IsClosed (K : Set (PiLp 2 W))

/-- **A conforming family with a closed constraint** is a constrained FEEC discretization. -/
def ConformingFamily.withConstraint {κ : Type*} {H : HilbertComplex 𝕜 c W}
    (F : ConformingFamily H κ) (K : Submodule 𝕜 (PiLp 2 W)) (hK : IsClosed (K : Set (PiLp 2 W))) :
    ConstrainedFEEC H κ :=
  { F with K := K, isClosed_K := hK }

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

/-! ### The total cochain projection -/

/-- The **total cochain projection** `Πₕ x = (πₕⁱ xⁱ)ᵢ` on `W = ⊕ Wⁱ`. -/
def piProj (h : κ) : PiLp 2 W →ₗ[𝕜] PiLp 2 W :=
  (WithLp.linearEquiv 2 𝕜 (∀ i, W i)).symm.toLinearMap ∘ₗ
    LinearMap.pi fun i => (F.π h).π i ∘ₗ PiLp.projₗ 2 W i

omit [Fintype ι] in
@[simp] theorem piProj_apply (h : κ) (x : PiLp 2 W) (i : ι) :
    F.piProj h x i = (F.π h).π i (x i) := rfl

omit [Fintype ι] in
theorem piProj_mem (h : κ) (x : PiLp 2 W) : F.piProj h x ∈ totalSub (F.V h).V :=
  fun i => (F.π h).mem i _

omit [Fintype ι] in
theorem piProj_of_mem (h : κ) {x : PiLp 2 W} (hx : x ∈ totalSub (F.V h).V) :
    F.piProj h x = x :=
  PiLp.ext fun i => (F.π h).proj i _ (hx i)

/-- A nonnegative uniform bound of the cochain projections. -/
def projConst : ℝ := max F.bound_π.choose 0

omit [Fintype ι] in
theorem projConst_nonneg : 0 ≤ F.projConst := le_max_right _ _

omit [Fintype ι] in
theorem norm_π_le (h : κ) (i : ι) (y : W i) : ‖(F.π h).π i y‖ ≤ F.projConst * ‖y‖ :=
  (F.bound_π.choose_spec h i y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- `‖Πₕ x‖ ≤ C ‖x‖`, uniformly in `h`. -/
theorem norm_piProj_le (h : κ) (x : PiLp 2 W) : ‖F.piProj h x‖ ≤ F.projConst * ‖x‖ := by
  have h0 := F.projConst_nonneg
  have hsq : ‖F.piProj h x‖ ^ 2 ≤ (F.projConst * ‖x‖) ^ 2 := by
    rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [piProj_apply, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (F.norm_π_le h i _) 2
  have := norm_nonneg (F.piProj h x)
  nlinarith [mul_nonneg h0 (norm_nonneg x)]

/-- **Quasi-optimality of the cochain projection** in `W`: `‖y - Πₕ y‖ ≤ (1 + C) ‖y - w‖` for
every `w ∈ Vₕ`. [AFW2010], §3.3 -/
theorem norm_sub_piProj_le (h : κ) (y : PiLp 2 W) {w : PiLp 2 W}
    (hw : w ∈ totalSub (F.V h).V) : ‖y - F.piProj h y‖ ≤ (1 + F.projConst) * ‖y - w‖ := by
  have e : y - F.piProj h y = (y - w) - F.piProj h (y - w) := by
    rw [_root_.map_sub, F.piProj_of_mem h hw]; abel
  rw [e]
  have := F.norm_piProj_le h (y - w)
  calc _ ≤ ‖y - w‖ + ‖F.piProj h (y - w)‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

theorem piProj_mem_domain (h : κ) (x : PiLp 2 W) : F.piProj h x ∈ H.totalD.domain :=
  fun i j => (F.V h).le_domain i j ((F.π h).mem i _)

/-- **The total cochain projection commutes with `𝐝`**: `𝐝 Πₕ x = Πₕ 𝐝 x`. -/
theorem totalD_piProj (h : κ) (x : H.totalD.domain) :
    H.totalD ⟨F.piProj h x, F.piProj_mem_domain h x⟩ = F.piProj h (H.totalD x) := by
  refine PiLp.ext fun j => ?_
  rw [totalD_apply, piProj_apply, totalD_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => (F.π h).comm i j ⟨(x : PiLp 2 W) i, x.2 i j⟩

/-- **The approximation property in the graph norm**, from the approximation property in `W` and
the uniformly bounded commuting cochain projections: `Πₕ ζ` approximates `ζ ∈ Γ(𝐝)` since
`‖x - Πₕ x‖ ≤ (1 + C) ‖x - w₁‖` and `‖𝐝 x - 𝐝 Πₕ x‖ = ‖(1 - Πₕ) 𝐝 x‖ ≤ (1 + C) ‖𝐝 x - w₂‖`.
[AFW2010], §3.3 -/
theorem dense_graph (ζ : H.totalD.GraphSpace) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ h in F.l, ∃ w ∈ (F.V h).graphSub, ‖ζ - w‖ < δ := by
  obtain ⟨x, rfl, -, -⟩ := H.totalD.exists_toGraphSpace_eq ζ
  have hC := F.projConst_nonneg
  set ε := δ / (2 * (1 + F.projConst)) with hε
  have hε0 : 0 < ε := by positivity
  filter_upwards [F.dense (x : PiLp 2 W) ε hε0, F.dense (H.totalD x) ε hε0] with h hw₁ hw₂
  obtain ⟨w₁, hw₁, h₁⟩ := hw₁
  obtain ⟨w₂, hw₂, h₂⟩ := hw₂
  set y : H.totalD.domain := ⟨F.piProj h x, F.piProj_mem_domain h x⟩
  refine ⟨H.totalD.toGraphSpace y, fun i => F.piProj_mem h x i, ?_⟩
  have e1 : H.totalD.graphFst (H.totalD.toGraphSpace x - H.totalD.toGraphSpace y) =
      (x : PiLp 2 W) - F.piProj h x := by
    rw [H.totalD.graphFst.map_sub]; rfl
  have e2 : H.totalD.graphSnd (H.totalD.toGraphSpace x - H.totalD.toGraphSpace y) =
      H.totalD x - F.piProj h (H.totalD x) := by
    rw [H.totalD.graphSnd.map_sub, graphSnd_toGraphSpace, graphSnd_toGraphSpace, F.totalD_piProj]
  have hsq := norm_sq_graphSpace (H.totalD.toGraphSpace x - H.totalD.toGraphSpace y)
  rw [e1, e2] at hsq
  have a1 := F.norm_sub_piProj_le h (x : PiLp 2 W) hw₁
  have a2 := F.norm_sub_piProj_le h (H.totalD x) hw₂
  have b1 : (1 + F.projConst) * ‖(x : PiLp 2 W) - w₁‖ < (1 + F.projConst) * ε :=
    mul_lt_mul_of_pos_left h₁ (by linarith)
  have b2 : (1 + F.projConst) * ‖H.totalD x - w₂‖ < (1 + F.projConst) * ε :=
    mul_lt_mul_of_pos_left h₂ (by linarith)
  have hδε : 2 * ((1 + F.projConst) * ε) = δ := by
    rw [hε]; field_simp
  have c1 := a1.trans_lt b1
  have c2 := a2.trans_lt b2
  have n1 := norm_nonneg ((x : PiLp 2 W) - F.piProj h x)
  have n2 := norm_nonneg (H.totalD x - F.piProj h (H.totalD x))
  have n3 := norm_nonneg (H.totalD.toGraphSpace x - H.totalD.toGraphSpace y)
  have hm : 0 < (1 + F.projConst) * ε := by positivity
  have hlt : ‖H.totalD.toGraphSpace x - H.totalD.toGraphSpace y‖ ^ 2 < δ ^ 2 := by
    rw [hsq, ← hδε]; nlinarith
  nlinarith

/-- A constrained FEEC discretization is approximating (uniformly bounded elliptic projections,
[QuennevilleBelair2015], Prop. 4.13, and the approximation property in the graph norm,
`dense_graph`). -/
theorem isApproximating : IsApproximating F.l F.Kh :=
  Subcomplex.isApproximating F.dense_graph

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

/-- A **rate class** of a constrained FEEC discretization on the time horizon `[0, T]`: data
`x ∈ D(L²)` (the class `Data`, with a class norm `‖x‖_class`) whose orbit `ξ(t) = e^{tL} x` and its
derivative `ξ'(t) = e^{tL} L x`, read in the graph space `Γ(𝐝)`, are approximated by `Vₕ` to order
`C hᵅ ‖x‖_class` for `t ∈ [0, T]`. The constant `C` and the class norm may depend on `T` (e.g.
`‖x‖_class = ‖x‖_{D(L³)} + (1 + T) Λ` for regularity known only along the trajectory on
`[0, T]`). Instances supply it from regularity (`D(L³)`, Sobolev classes) and approximation
estimates; the constrained FEEC theorem turns it into the error bound `constrainedFEEC_rate`.
[QuennevilleBelair2015], Thm 4.14, Thm 4.15; [AFW2010], §3.3 -/
structure ConstrainedFEEC.RateClass (F : ConstrainedFEEC H κ) (T : ℝ) where
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
  approx : ∀ x ∈ Data, ∀ h, ∀ t ∈ Icc 0 T, ∀ v : H.totalD.GraphSpace,
    H.totalD.graphFst v = H.waveGroup.S t x →
      ∃ w ∈ F.Kh h, ‖v - w‖ ≤ C * meshSize h ^ α * classNorm x
  approx_deriv : ∀ x (hx : x ∈ H.wave.domain), x ∈ Data → ∀ h, ∀ t ∈ Icc 0 T,
    ∀ v : H.totalD.GraphSpace, H.totalD.graphFst v = H.waveGroup.S t (H.wave ⟨x, hx⟩) →
      ∃ w ∈ F.Kh h, ‖v - w‖ ≤ C * meshSize h ^ α * classNorm x

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- The approximation estimate behind `RateClass.ofDegreewise`: a graph-space point whose
components are all `Reg`-regular is within `(m + m²) Σᵢ Bᵢ Λ r_h` of `Kₕ`. -/
theorem ConstrainedFEEC.RateClass.exists_mem_Kh_le_of_degreewise (F : ConstrainedFEEC H κ)
    {Reg : ∀ i, W i → Prop} {B : ι → ℝ} {r : κ → ℝ} {Λ : ℝ}
    (happ : ∀ h i (x : W i), Reg i x → ∃ v, ∃ hv : v ∈ (F.V h).V i,
      ‖x - v‖ ≤ B i * Λ * r h ∧ ∀ j (hxj : x ∈ (H.d i j).domain),
        ‖H.d i j ⟨x - v, Submodule.sub_mem _ hxj ((F.V h).le_domain i j hv)⟩‖ ≤ B i * Λ * r h)
    (hB : ∀ i, 0 ≤ B i) (hΛ : 0 ≤ Λ) (hr : ∀ h, 0 ≤ r h) (h : κ) {z : PiLp 2 W}
    (hz : ∀ i, Reg i (z i)) (v : H.totalD.GraphSpace) (hv : H.totalD.graphFst v = z) :
    ∃ w ∈ F.Kh h, ‖v - w‖ ≤ ((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)) *
      (∑ i, B i) * r h ^ (1 : ℝ) * Λ := by
  obtain ⟨y, rfl, -, -⟩ := H.totalD.exists_toGraphSpace_eq v
  obtain ⟨w, hw, hle⟩ := Subcomplex.exists_mem_graphSub_le (F.V h) y
    (ε := (∑ i, B i) * Λ * r h) fun i => by
      rw [show (y : PiLp 2 W) = z from hv]
      obtain ⟨u, hu, h1, h2⟩ := happ h _ _ (hz i)
      have hle : B i * Λ * r h ≤ (∑ i, B i) * Λ * r h :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := B) (fun _ _ => hB _) (Finset.mem_univ i)) hΛ) (hr h)
      exact ⟨u, hu, h1.trans hle, fun j hxj => (h2 j hxj).trans hle⟩
  refine ⟨w, hw, hle.trans_eq ?_⟩
  rw [Real.rpow_one]; ring

/-! ### 3. The constraint residual -/

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- **The constraint residual is bounded by the error**: if `ξ(t) ∈ K`, then
`dist(ξₕ(t), K) ≤ ‖ξ(t) - ξₕ(t)‖`. -/
theorem ConstrainedFEEC.infDist_le_norm_sub {y z : PiLp 2 W} (hy : y ∈ F.K) :
    infDist z (F.K : Set (PiLp 2 W)) ≤ ‖y - z‖ := by
  rw [norm_sub_rev, ← dist_eq_norm]; exact infDist_le_dist_of_mem hy

/-! ### The discrete Poincaré inequality -/

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] [Fintype ι] in
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

/-! ### The verdict -/

/-- **The conclusions of the constrained FEEC theorem** (`constrainedFEEC`) for a constrained FEEC
discretization `F` of the Hodge wave equation `ξ' = L ξ`, with `ξₕ` the semi-discrete solutions
(4.10) from the elliptic projections `Pₕ ξ₀` (`ConstrainedFEEC.discrete`). [QuennevilleBelair2015],
Thms 4.6, 4.7, 4.14, Prop. 4.17; [AFW2010], §3.3, Thm 3.4 -/
structure ConstrainedFEEC.Verdict (F : ConstrainedFEEC H κ) : Prop where
  /-- (**well-posedness**, Stone) for `ξ₀ ∈ D(L)`, `t ↦ e^{tL} ξ₀` is a classical solution on
  `[0, T]`, the only strong and the only weak solution, and it conserves energy -/
  wellPosed {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (T : ℝ) :
    Evolution.IsClassicalSolution H.wave (Icc 0 T) 0 (fun t => H.waveGroup.S t x) ∧
    (∀ U, U 0 = x → Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U →
      EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
    (∀ U, U 0 = x → HodgeWave.IsWeakSolution H (Icc 0 T) 0 U →
      EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
    ∀ t, ‖H.waveGroup.S t x‖ = ‖x‖
  /-- (**propagation**) `K` reduces `L` iff `e^{tL} K ⊆ K` for all `t ∈ ℝ` -/
  propagates_iff : H.wave.IsReducing F.K ↔ ∀ t, ∀ x ∈ F.K, H.waveGroup.S t x ∈ F.K
  /-- (**convergence**) for `ξ₀ ∈ D(L)`, `ξₕ → e^{tL} ξ₀` uniformly on `[0, T]` -/
  converges (x : H.wave.domain) (T : ℝ) :
    TendstoUniformlyOn (fun h t => H.totalD.graphFst (F.discrete h (waveLift H x) t))
      (fun t => H.waveGroup.S t x) F.l (Icc 0 T)
  /-- for `ξ₀ ∈ W`, every family of semi-discrete solutions with `ξₕ(0) → ξ₀` converges to
  `e^{tL} ξ₀` uniformly on `[0, T]` -/
  converges_of_tendsto (x : PiLp 2 W) {T : ℝ} (ξh ξh' : κ → ℝ → H.totalD.GraphSpace)
    (hξh : ∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h))
    (h0 : Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x)) :
    TendstoUniformlyOn (fun h t => H.totalD.graphFst (ξh h t)) (fun t => H.waveGroup.S t x) F.l
      (Icc 0 T)
  /-- and such families exist -/
  exists_tendsto (x : PiLp 2 W) (T : ℝ) :
    ∃ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
      (∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) ∧
      Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x)
  /-- (**rate**) for data in a rate class on `[0, T]`,
  `‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + t)² C hᵅ ‖ξ₀‖_class` -/
  rate {T : ℝ} (R : F.RateClass T) {x : PiLp 2 W} (hxR : x ∈ R.Data) (h : κ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖H.waveGroup.S t x -
        H.totalD.graphFst (F.discrete h (waveLift H ⟨x, R.mem_domain x hxR⟩) t)‖ ≤
      (1 + ellipticConst H) * (1 + t) ^ 2 * (R.C * R.meshSize h ^ R.α * R.classNorm x)
  /-- (**constraint residual**) if `K` reduces `L` and `ξ₀ ∈ D(L) ∩ K`, the residual is bounded
  by the error -/
  residual_le (hK : H.wave.IsReducing F.K) (x : H.wave.domain) (hxK : (x : PiLp 2 W) ∈ F.K)
    (h : κ) (t : ℝ) :
    infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t)) (F.K : Set (PiLp 2 W)) ≤
      ‖H.waveGroup.S t x - H.totalD.graphFst (F.discrete h (waveLift H x) t)‖
  /-- and tends to `0` uniformly on `[0, T]` -/
  residual_tendsto (hK : H.wave.IsReducing F.K) (x : H.wave.domain) (hxK : (x : PiLp 2 W) ∈ F.K)
    (T : ℝ) :
    TendstoUniformlyOn
      (fun h t => infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t))
        (F.K : Set (PiLp 2 W))) (fun _ => 0) F.l (Icc 0 T)
  /-- (**departure**) if `K` does not reduce `L`, then for every `T > 0` some datum of `Q = K` or
  of `Q = Kᗮ` leaves `Q` at some `t ∈ [0, T]`, and the residuals `dist(ξₕ(t), Q)` of every
  convergent discretization tend to `dist(e^{tL} ξ₀, Q) > 0` -/
  leaves (hK : ¬ H.wave.IsReducing F.K) {T : ℝ} (hT : 0 < T) :
    ∃ Q : Submodule 𝕜 (PiLp 2 W), (Q = F.K ∨ Q = F.Kᗮ) ∧ ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
      H.waveGroup.S t x ∉ Q ∧ 0 < infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)) ∧
      ∀ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
        (∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
        Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x) →
        Tendsto (fun h => infDist (H.totalD.graphFst (ξh h t)) (Q : Set (PiLp 2 W))) F.l
          (𝓝 (infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W))))
  /-- if `K` does not reduce `L` and `D(L) ∩ K` is dense in `K`, some `ξ₀ ∈ D(L) ∩ K` leaves `K`
  at some `t ∈ [-T, T]`, for every `T > 0` -/
  leaves_symm (hK : ¬ H.wave.IsReducing F.K)
    (hD : ∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) {T : ℝ} (hT : 0 < T) :
    ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc (-T) T,
      H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W))
  /-- on a graded complex, for an `R`-invariant `K` with `D(L) ∩ K` dense in `K` that does not
  reduce `L`, some `ξ₀ ∈ D(L) ∩ K` leaves `K` at some `t ∈ [0, T]`, and the residuals of the
  discrete solutions from `Pₕ ξ₀` tend to `dist(e^{tL} ξ₀, K) > 0` -/
  leaves_graded {p : ι → Bool} (hp : ∀ i j, c.Rel i j → p j ≠ p i)
    (hRK : ∀ x ∈ F.K, reversal 𝕜 p x ∈ F.K)
    (hD : ∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K))
    (hK : ¬ H.wave.IsReducing F.K) {T : ℝ} (hT : 0 < T) :
    ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc 0 T,
      H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) ∧
      Tendsto (fun h => infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t))
        (F.K : Set (PiLp 2 W))) F.l (𝓝 (infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)))) ∧
      ∀ᶠ h in F.l, infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) / 2 <
        infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t)) (F.K : Set (PiLp 2 W))
  /-- (**discrete cohomology**) if `H` has closed range at `i` and `ℌⁱ` is finite-dimensional,
  the projections `πₕ` eventually induce isomorphisms `Hⁱ(H) ≅ Hⁱ(Vₕ)`, `[z] ↦ [πₕ z]` -/
  cohomology {i : ι} [FiniteDimensional 𝕜 (H.harmonic i)] (hi : H.ClosedRangeAt i) :
    ∀ᶠ h in F.l, Function.Bijective ((F.π h).cohomologyMap i)

variable {F} in
/-- (**constraint residual rate**) if `K` reduces `L`, the residual of data in `K` and in a rate
class is at most the rate of the error, `dist(ξₕ(t), K) ≤ (1 + C_P)(1 + t)² C hᵅ ‖ξ₀‖_class`
(`propagates_iff`, `ConstrainedFEEC.infDist_le_norm_sub`, `rate`). -/
theorem ConstrainedFEEC.Verdict.residual_rate (V : F.Verdict) (hK : H.wave.IsReducing F.K)
    {T : ℝ} (R : F.RateClass T) {x : PiLp 2 W} (hxR : x ∈ R.Data) (hxK : x ∈ F.K) (h : κ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    infDist (H.totalD.graphFst (F.discrete h (waveLift H ⟨x, R.mem_domain x hxR⟩) t))
        (F.K : Set (PiLp 2 W)) ≤
      (1 + ellipticConst H) * (1 + t) ^ 2 * (R.C * R.meshSize h ^ R.α * R.classNorm x) :=
  (F.infDist_le_norm_sub (V.propagates_iff.1 hK t x hxK)).trans (V.rate R hxR h ht)

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
  approx i w := by
    rw [infDist_zero_of_mem (show w ∈ ((topSub 𝕜).V i : Set _) from Submodule.mem_top)]
    exact tendsto_const_nhds

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
def idRate (T : ℝ) : (idFEEC 𝕜 (firstSub 𝕜) isClosed_totalSub).RateClass T where
  Data := univ
  classNorm := norm
  meshSize N := 1 / ((N : ℝ) + 1)
  α := 1
  C := 1
  mem_domain x _ := mem_idComplex_wave_domain x
  mem_domain_sq _ _ _ := mem_idComplex_wave_domain _
  approx x _ N _ _ v _ := ⟨v, fun _ => Submodule.mem_top, idRate_bound N x⟩
  approx_deriv x _ _ N _ _ v _ := ⟨v, fun _ => Submodule.mem_top, idRate_bound N x⟩

end ConstrainedFEEC

end Feec.HilbertComplex
