module

public import Feec.Semigroup.DissipativeInvariance
public import Feec.Evolution.WellPosed
public import Feec.Evolution.Energy
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The dissipative FEEC theorem

Boundary conditions that absorb energy (radiation conditions, impedance conditions, damping) give
generators that are only **m-dissipative**: `re ⟪A x, x⟫ ≤ 0` and `μ - A` onto, i.e.
(Lumer–Phillips, `LinearPMap.isMDissipative_iff_exists_contraction`) generators of contraction
semigroups `S(t)`, `t ≥ 0`. This file states the FEEC theorem for them. It is the base of a tower:
the skew-adjoint case (`Feec.HilbertComplex.SkewFEEC`, a unitary group) extends the structure
defined here, and the Hodge wave case (`Feec.HilbertComplex.ApproxFEEC`) is the skew-adjoint case
for the wave operator `L = 𝐝 - 𝐝†` of a Hilbert complex.

A **dissipative FEEC discretization** (`Feec.HilbertComplex.DissipFEEC`) of `ξ' = A ξ` for an
m-dissipative `A` on a Hilbert space `E` consists of a closed constraint subspace `K`, Hilbert
spaces `Xₕ` with their own inner products (not subspaces of `E`, not necessarily
finite-dimensional), bounded **dissipative** discrete generators `Lₕ` (`re ⟪Lₕ v, v⟫ ≤ 0`, so
`e^{tLₕ}` is a contraction for `t ≥ 0`: uniform stability), and uniformly bounded reading maps
`ιₕ : Xₕ → E` with uniformly bounded left inverses `πₕ` (`πₕ ιₕ = 1`). Neither `ιₕ` nor `πₕ` is
assumed isometric, a cochain map, or to commute with anything; `ιₕ πₕ → 1` is not assumed
either: it is derived (`DissipFEEC.tendsto_incl_proj`). The exact flow is the Lumer–Phillips
semigroup `DissipFEEC.S` of `A`, the discrete solution is `ιₕ e^{tLₕ} v` (`DissipFEEC.sol`).

**Consistency** is tested along exact orbits, never in operator norm. A **comparison**
(`DissipFEEC.Comparison`) assigns to each datum `x` discrete trajectories `pₕ(t)` with derivatives
`pₕ'(t)`; its **consistency defect** is `pₕ' - Lₕ pₕ`. A **core** (`DissipFEEC.Core`) is a subspace
of data whose comparisons approximate the orbit (`ιₕ pₕ(t) → S(t) x`) with defects tending to `0`,
both uniformly on `[0, T]` (the orbit form of the consistency hypothesis of the Trotter–Kato
theorem); a **rate class** (`DissipFEEC.RateClass`) has comparisons with rates. The energy
estimate `norm_sub_le_of_defect_of_dissipative`, which needs only `re ⟪Lₕ e, e⟫ ≤ 0`, reads

`‖S(t) x - ιₕ e^{tLₕ} pₕ(0)‖ ≤ ‖S(t) x - ιₕ pₕ(t)‖ + ‖ιₕ‖ ∫₀ᵗ ‖pₕ' - Lₕ pₕ‖`,

**best approximation plus consistency**, a semi-discrete (evolution) analogue of the elliptic
estimates of [HolstStern2012], Thm 3.9, Thm 3.10: inner-product and commutation crimes both enter
through the orbit defect `pₕ' - Lₕ pₕ`.

## Main results

The **dissipative FEEC theorem** `dissipFEEC` (statement `DissipFEEC.Verdict`, a structure whose
fields are the conclusions) bundles the following results; `dissipFEEC_converges_core` and
`dissipFEEC_leaves_of_not_isReducing` are not fields, being the cases `vₕ = pₕ(0)` of
`converges` and `Q ∈ {K, Kᗮ}` of `leaves`, nor is `DissipFEEC.Verdict.detects` (a departure
from a closed set has residuals of positive limit, eventually above half of it), a corollary of
`tendsto_infDist`:

1. well-posedness (Lumer–Phillips, `dissipFEEC_wellPosed`): for `ξ₀ ∈ D(A)`, `t ↦ S(t) ξ₀` is a
   classical solution and the only strong one, with the energy identity
   `‖S(t) ξ₀‖² = ‖ξ₀‖² + ∫₀ᵗ 2 re ⟪S(s) A ξ₀, S(s) ξ₀⟫ ds`; the energy of every datum is
   nonincreasing;
2. constraint propagation (`dissipFEEC_propagates_iff`): `S(t) K ⊆ K` for all `t ≥ 0`
   (`DissipFEEC.Keeps`) iff the resolvents `(μ - A)⁻¹` map `K` into `K`, iff for one `μ > 0` the
   stationary problem `μ u - A u = f` is solvable in `D(A) ∩ K` for all `f ∈ K`; `K` reduces `A`
   iff both `K` and `Kᗮ` are invariant;
3. convergence: on the core (`dissipFEEC_converges_core`), on its closure for every family `vₕ`
   with `ιₕ vₕ → ξ₀` (`dissipFEEC_converges`; `ιₕ πₕ ξ₀ → ξ₀` gives one), with rates for a rate
   class (`dissipFEEC_rate`:
   `‖S(t) ξ₀ - ιₕ e^{tLₕ} v‖ ≤ (C + ‖ιₕ‖ C' t) hᵅ ‖ξ₀‖_c + ‖ιₕ‖ ‖pₕ(0) - v‖`);
4. the constraint residual `dist(ιₕ e^{tLₕ} vₕ, K)`: for invariant `K` it is bounded by the error
   and tends to `0` (`dissipFEEC_residual_le`, `dissipFEEC_residual`); for every set `Q` the
   distances `dist(ιₕ e^{tLₕ} vₕ, Q)` tend to `dist(S(t) ξ₀, Q)`, which is positive when the
   solution has left a closed `Q` (`dissipFEEC_tendsto_infDist`); a set that is not kept is left by
   one of its data before any time `T > 0` (`dissipFEEC_leaves`; a non-reducing `K` is left by a
   datum of `K` or of `Kᗮ`, `dissipFEEC_leaves_of_not_isReducing`), by a datum of `D(A) ∩ Q` when
   `Q` is closed and `D(A) ∩ Q` is dense in it (`DissipFEEC.SmoothDense`,
   `dissipFEEC_leaves_smooth`).

The **Trotter–Kato bridge** `DissipFEEC.Core.ofOperator` builds a core `D(A)` from bounded
`Rₕ : E → Xₕ` with `ιₕ Rₕ → 1` strongly and a defect identity `Rₕ A - Lₕ Rₕ = Δₕ A + Δₕ'` on `D(A)`
with uniformly bounded defects tending to `0` strongly (uniformity on `[0, T]` from compactness of
the orbits); `Core.ofOperator_data_closure`: that core is dense, so convergence holds for every
datum.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.4 (Thm 4.3 Lumer–Phillips), §3.4 (Trotter–Kato approximation theorems), §4.1 (classical and
  strong solutions)
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

/-- **Pointwise convergence of uniformly bounded operators is uniform along a curve with compact
image**: `Pₕ ζ → P₀ ζ` for every `ζ` and `‖Pₕ‖ ≤ C` give `Pₕ (f t) → P₀ (f t)` uniformly on `S`
when `f(S)` is compact. -/
theorem tendstoUniformlyOn_apply_of_tendsto {𝕜 κ F G : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    {l : Filter κ} {P : κ → F →L[𝕜] G} {P₀ : F →L[𝕜] G} (hP : ∃ C, ∀ h, ‖P h‖ ≤ C)
    (hlim : ∀ ζ, Tendsto (fun h => P h ζ) l (𝓝 (P₀ ζ))) {f : ℝ → F} {S : Set ℝ}
    (hf : IsCompact (f '' S)) :
    TendstoUniformlyOn (fun h t => P h (f t)) (fun t => P₀ (f t)) l S := by
  obtain ⟨C, hC⟩ := hP
  have hB : ∀ h ζ, ‖(P₀ - P h) ζ‖ ≤ (‖P₀‖ + C) * ‖ζ‖ := fun h ζ =>
    ((P₀ - P h).le_opNorm ζ).trans (mul_le_mul_of_nonneg_right
      ((norm_sub_le _ _).trans (add_le_add_right (hC h) _)) (norm_nonneg _))
  have hB0 : ∀ ζ, Tendsto (fun h => ‖(P₀ - P h) ζ‖) l (𝓝 0) := fun ζ =>
    (tendsto_iff_norm_sub_tendsto_zero.1 (hlim ζ)).congr fun h => norm_sub_rev _ _
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_forall_norm_lt_of_tendsto hB hB0 hf hε] with h hh t ht
  simpa [dist_eq_norm] using hh _ (mem_image_of_mem _ ht)

/-- **Defects dominated by uniformly bounded operators tending to `0` pointwise tend to `0`
uniformly along compact orbits**: `‖dₕ(t)‖ ≤ ‖Δₕ (f t)‖ + ‖Δₕ' (g t)‖` on `S`, with `f(S)` and
`g(S)` compact, give `‖dₕ‖ → 0` uniformly on `S`. -/
theorem tendstoUniformlyOn_norm_of_le {𝕜 κ F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 F] {G D : κ → Type*} [∀ h, SeminormedAddCommGroup (G h)]
    [∀ h, NormedSpace 𝕜 (G h)] [∀ h, SeminormedAddCommGroup (D h)] {l : Filter κ}
    {Δ Δ' : ∀ h, F →L[𝕜] G h} (hΔ : ∃ C, ∀ h, ‖Δ h‖ ≤ C ∧ ‖Δ' h‖ ≤ C)
    (hΔ0 : ∀ ζ, Tendsto (fun h => ‖Δ h ζ‖) l (𝓝 0))
    (hΔ'0 : ∀ ζ, Tendsto (fun h => ‖Δ' h ζ‖) l (𝓝 0)) {f g : ℝ → F} {S : Set ℝ}
    (hf : IsCompact (f '' S)) (hg : IsCompact (g '' S)) {d : ∀ h, ℝ → D h}
    (hd : ∀ h, ∀ t ∈ S, ‖d h t‖ ≤ ‖Δ h (f t)‖ + ‖Δ' h (g t)‖) :
    TendstoUniformlyOn (fun h t => ‖d h t‖) (fun _ => 0) l S := by
  obtain ⟨C, hC⟩ := hΔ
  have hb : ∀ B : ∀ h, F →L[𝕜] G h, (∀ h, ‖B h‖ ≤ C) → ∀ h ζ, ‖B h ζ‖ ≤ C * ‖ζ‖ :=
    fun B hB h ζ => ((B h).le_opNorm ζ).trans (mul_le_mul_of_nonneg_right (hB h) (norm_nonneg _))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_forall_norm_lt_of_tendsto (hb Δ fun h => (hC h).1) hΔ0 hf
      (half_pos hε),
    eventually_forall_norm_lt_of_tendsto (hb Δ' fun h => (hC h).2) hΔ'0 hg (half_pos hε)]
    with h h1 h2 t ht
  rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg (norm_nonneg _)]
  linarith [hd h t ht, h1 _ (mem_image_of_mem _ ht), h2 _ (mem_image_of_mem _ ht)]

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
`ιₕ : Xₕ → E`, `πₕ : E → Xₕ` with `πₕ ιₕ = 1`. `ιₕ` need not be an inclusion, an isometry or a
cochain map, and `ιₕ πₕ → 1` is not assumed (it is derived on the closure of a core,
`tendsto_incl_proj`). The m-dissipativity of `A` is a field, not a parameter, so that a projection
`F.X h` carries `A` once. [HolstStern2012], §3; [Pazy1983], §3.4 -/
structure DissipFEEC (A : E →ₗ.[𝕜] E) (κ : Type*) where
  /-- the generator is m-dissipative -/
  isMDissipative : A.IsMDissipative
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

variable {A : E →ₗ.[𝕜] E} {κ : Type*} (F : DissipFEEC.{u} A κ)

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

/-- `ιₕ Rₕ` is uniformly bounded when `Rₕ` is. -/
theorem bound_incl_comp {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    {R : ∀ h, G →L[𝕜] F.X h} (hR : ∃ C, ∀ h, ‖R h‖ ≤ C) : ∃ C, ∀ h, ‖F.incl h ∘L R h‖ ≤ C :=
  let ⟨C, hC⟩ := hR
  ⟨F.boundConst * C, fun h => (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (F.norm_incl_le h) (hC h) (norm_nonneg _) F.boundConst_nonneg)⟩

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

/-- `v` converges to `x` through the reading maps, `ιₕ vₕ → x`. -/
abbrev Converges (v : ∀ h, F.X h) (x : E) : Prop := Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x)

/-- **Comparison trajectories** on `[0, T]`: for each datum `x` of `Data`, discrete trajectories
`pₕ(t)` with right derivatives `pₕ'(t)`. Consistency is tested along them (orbit form), never in
operator norm: for the BGG scheme of [QuennevilleBelair2015], (6.5), the static strong consistency
bound of Prop. 5.9(2) fails (ratio `√(2/3)`, per the unformalized audit recorded in
`Feec.HilbertComplex.BGG.WeakConsistency`). -/
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

variable {F} in
/-- Restriction of a comparison to a subset of its data. -/
def Comparison.restrict {T : ℝ} (P : F.Comparison T) (D : Set E) (hD : D ⊆ P.Data) :
    F.Comparison T where
  Data := D
  p := P.p
  p' := P.p'
  continuousOn x hx := P.continuousOn x (hD hx)
  continuousOn' x hx := P.continuousOn' x (hD hx)
  hasDerivWithinAt x hx := P.hasDerivWithinAt x (hD hx)

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

omit [CompleteSpace E] in
/-- The discrete solution is differentiable: `(d/dt) ιₕ e^{tLₕ} v = ιₕ Lₕ e^{tLₕ} v`. -/
theorem hasDerivAt_sol (h : κ) (v : F.X h) (t : ℝ) :
    HasDerivAt (F.sol h v) (F.incl h (F.L h ((F.group h).S t v))) t :=
  ((F.incl h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (C0Group.hasDerivAt_exp_ofReal_smul_apply (F.L h) v t)

/-- The **exact flow** `S(t)` of `F`: the Lumer–Phillips contraction semigroup of `A` (only
`t ≥ 0` matters). -/
def S (t : ℝ) : E →L[𝕜] E := F.isMDissipative.semigroup.S t

theorem S_def (t : ℝ) : F.S t = F.isMDissipative.semigroup.S t := rfl

/-- The orbits of the exact flow are continuous on `[0, T]`. -/
theorem continuousOn_S (x : E) (T : ℝ) : ContinuousOn (fun t => F.S t x) (Icc 0 T) :=
  (F.isMDissipative.semigroup.strongCont x).mono Icc_subset_Ici_self

/-- **Inexactness criterion**: if the discrete initial velocity `ιₕ Lₕ v` differs from `A x`,
the discrete solution from `v` differs from `S(t) x` at some time `t ≥ 0`. -/
theorem exists_sol_ne {x : E} (hx : x ∈ A.domain) (h : κ) (v : F.X h)
    (hne : F.incl h (F.L h v) ≠ A ⟨x, hx⟩) : ∃ t, 0 ≤ t ∧ F.sol h v t ≠ F.S t x := by
  by_contra hc
  push Not at hc
  have h1 : HasDerivWithinAt (fun s => F.S s x) (F.incl h (F.L h ((F.group h).S 0 v))) (Ici 0)
      0 := ((F.hasDerivAt_sol h v 0).hasDerivWithinAt).congr (fun s hs => (hc s hs).symm)
    (hc 0 le_rfl).symm
  have h2 := F.isMDissipative.hasDerivWithinAt_semigroup ⟨x, hx⟩ (le_refl 0)
  have e := (uniqueDiffWithinAt_Ici 0).eq_deriv _ h1 h2
  rw [C0Group.S_zero_apply, C0Semigroup.S_zero_apply] at e
  exact hne e

/-- `F` keeps `Q`: `S(t) Q ⊆ Q` for every `t ≥ 0`. -/
abbrev Keeps (Q : Set E) : Prop := ∀ t, 0 ≤ t → ∀ x ∈ Q, F.S t x ∈ Q

/-- `x` leaves `Q` by time `T`: `S(t) x ∉ Q` for some `t ∈ [0, T]`. -/
abbrev Leaves (x : E) (Q : Set E) (T : ℝ) : Prop := ∃ t ∈ Icc 0 T, F.S t x ∉ Q

/-- `Q` has a dense smooth part: `D(A) ∩ Q` is dense in `Q`. -/
abbrev SmoothDense (_ : DissipFEEC.{u} A κ) (Q : Set E) : Prop :=
  ∀ k ∈ Q, k ∈ closure ((A.domain : Set E) ∩ Q)

/-- A **rate class** on `[0, T]`: comparison trajectories with best approximation
`‖S(t) x - ιₕ pₕ(t)‖ ≤ C hᵅ ‖x‖_c` and consistency `‖pₕ' - Lₕ pₕ‖ ≤ C' hᵅ ‖x‖_c`.
Cf. [HolstStern2012], Thm 3.10 (elliptic analogue) -/
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
    ‖F.S t x - F.incl h (p x h t)‖ ≤ C * meshSize h ^ α * classNorm x
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
    (fun h t => F.incl h ((cmp T).p x h t)) (fun t => F.S t x) F.l (Icc 0 T)
  tendsto_defect : ∀ T, ∀ x ∈ Data, TendstoUniformlyOn
    (fun h t => ‖(cmp T).defect x h t‖) (fun _ => 0) F.l (Icc 0 T)

/-- **Best approximation plus consistency**: the error of the discrete solution from the
comparison initial value is at most the approximation error plus `‖ιₕ‖` times the integrated
consistency defect. Cf. [HolstStern2012], Thm 3.9 (elliptic analogue) -/
theorem norm_sub_sol_le {T : ℝ} (P : F.Comparison T) {x : E} (hx : x ∈ P.Data) (h : κ) :
    ∀ t ∈ Icc 0 T, ‖F.S t x - F.sol h (P.p x h 0) t‖ ≤
      ‖F.S t x - F.incl h (P.p x h t)‖ + ‖F.incl h‖ * ∫ s in (0 : ℝ)..t, ‖P.defect x h s‖ :=
  norm_sub_le_of_defect_of_dissipative (F.L h) (F.dissipative h) (F.incl h)
    (P.continuousOn x hx h) (P.continuousOn' x hx h) (P.hasDerivWithinAt x hx h)

variable {F} in
/-- The comparison initial values of a core read in `E` converge to the datum. -/
theorem Core.tendsto_incl_p (Z : F.Core) {T : ℝ} (hT : 0 ≤ T) {x : E} (hx : x ∈ Z.Data) :
    F.Converges (fun h => (Z.cmp T).p x h 0) x := by
  have h0 := (Z.tendsto_approx T x hx).tendsto_at (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)
  rwa [S_def, C0Semigroup.S_zero_apply] at h0

/-- **The approximation property, derived**: `ιₕ πₕ x → x` on the closure of a core (`πₕ ιₕ = 1`
and the uniform bounds give `‖ιₕ πₕ y - y‖ ≤ (1 + C²) ‖y - ιₕ v‖`). -/
theorem tendsto_incl_proj (Z : F.Core) {x : E} (hx : x ∈ Z.Data.topologicalClosure) :
    F.Converges (fun h => F.proj h x) x := by
  unfold Converges
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
  p x h t := R h (F.S t x)
  p' x h t := R h (F.S t (genExt A x))
  continuousOn x _ h := (R h).continuous.comp_continuousOn (F.continuousOn_S x T)
  continuousOn' x _ h := (R h).continuous.comp_continuousOn (F.continuousOn_S (genExt A x) T)
  hasDerivWithinAt x hx h t ht := by
    have hd := F.isMDissipative.hasDerivWithinAt_semigroup ⟨x, hx⟩ ht.1
    rw [← genExt_of_mem hx] at hd
    exact ((R h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hd

/-- **The Trotter–Kato bridge**: uniformly bounded `Rₕ : E → Xₕ` with `ιₕ Rₕ y → y`, and a defect
identity `Rₕ (A y) - Lₕ (Rₕ y) = Δₕ (A y) + Δₕ' y` on `D(A)` with uniformly bounded `Δₕ`, `Δₕ'`
tending to `0` pointwise, give the core `D(A)`; uniformity on `[0, T]` comes from the
compactness of the orbits `S([0, T]) x`, `S([0, T]) A x`. [Pazy1983], §3.4 -/
def Core.ofOperator (R : ∀ h, E →L[𝕜] F.X h) (hR : ∃ C, ∀ h, ‖R h‖ ≤ C)
    (happrox : ∀ y, Tendsto (fun h => F.incl h (R h y)) F.l (𝓝 y))
    (Δ Δ' : ∀ h, E →L[𝕜] F.X h) (hΔ : ∃ C, ∀ h, ‖Δ h‖ ≤ C ∧ ‖Δ' h‖ ≤ C)
    (hdef : ∀ h (y : A.domain), R h (A y) - F.L h (R h y) = Δ h (A y) + Δ' h y)
    (hΔ0 : ∀ y, Tendsto (fun h => ‖Δ h y‖) F.l (𝓝 0))
    (hΔ'0 : ∀ y, Tendsto (fun h => ‖Δ' h y‖) F.l (𝓝 0)) : F.Core where
  Data := A.domain
  cmp T := Comparison.ofOperator F R T
  data_eq _ := rfl
  tendsto_approx T x _ := tendstoUniformlyOn_apply_of_tendsto (P₀ := ContinuousLinearMap.id 𝕜 E)
    (F.bound_incl_comp hR) happrox (isCompact_Icc.image_of_continuousOn (F.continuousOn_S x T))
  tendsto_defect T x hx := tendstoUniformlyOn_norm_of_le hΔ hΔ0 hΔ'0
    (isCompact_Icc.image_of_continuousOn (F.continuousOn_S (genExt A x) T))
    (isCompact_Icc.image_of_continuousOn (F.continuousOn_S x T))
    fun h t ht => by
      have e := hdef h ⟨_, F.isMDissipative.semigroup_mem_domain ⟨x, hx⟩ ht.1⟩
      rw [F.isMDissipative.apply_semigroup ⟨x, hx⟩ ht.1] at e
      change ‖R h (F.isMDissipative.semigroup.S t (genExt A x)) -
        F.L h (R h (F.isMDissipative.semigroup.S t x))‖ ≤ _
      rw [genExt_of_mem hx, e]
      exact norm_add_le _ _

/-- **The Trotter–Kato core is dense**: its data `D(A)` are dense (an m-dissipative operator is
densely defined), so `dissipFEEC_converges` applies to every datum. -/
theorem Core.ofOperator_data_closure (R : ∀ h, E →L[𝕜] F.X h) (hR : ∃ C, ∀ h, ‖R h‖ ≤ C)
    (happrox : ∀ y, Tendsto (fun h => F.incl h (R h y)) F.l (𝓝 y))
    (Δ Δ' : ∀ h, E →L[𝕜] F.X h) (hΔ : ∃ C, ∀ h, ‖Δ h‖ ≤ C ∧ ‖Δ' h‖ ≤ C)
    (hdef : ∀ h (y : A.domain), R h (A y) - F.L h (R h y) = Δ h (A y) + Δ' h y)
    (hΔ0 : ∀ y, Tendsto (fun h => ‖Δ h y‖) F.l (𝓝 0))
    (hΔ'0 : ∀ y, Tendsto (fun h => ‖Δ' h y‖) F.l (𝓝 0)) :
    (Core.ofOperator F R hR happrox Δ Δ' hΔ hdef hΔ0 hΔ'0).Data.topologicalClosure = ⊤ := by
  exact Submodule.dense_iff_topologicalClosure_eq_top.1 F.isMDissipative.dense_domain

end DissipFEEC

/-! ### The dissipative FEEC theorem -/

section Main

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
variable {A : E →ₗ.[𝕜] E} {κ : Type*} (F : DissipFEEC.{u} A κ)

open DissipFEEC

/-- **1. Well-posedness and energy** (Lumer–Phillips): for `x ∈ D(A)`, `t ↦ S(t) x` is a
classical solution on `[0, T]`, the only strong solution, with the energy identity
`‖S(t) x‖² = ‖x‖² + ∫₀ᵗ 2 re ⟪S(s) A x, S(s) x⟫ ds`; for every datum the energy is
nonincreasing. -/
theorem dissipFEEC_wellPosed (x : A.domain) (T : ℝ) :
    Evolution.IsClassicalSolution A (Icc 0 T) 0 (fun t => F.S t x) ∧
    (∀ U, U 0 = (x : E) → Evolution.IsStrongSolution A (Icc 0 T) 0 U →
      EqOn U (fun t => F.S t x) (Icc 0 T)) ∧
    ∀ t, 0 ≤ t → ‖F.S t x‖ ^ 2 = ‖(x : E)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, 2 * RCLike.re ⟪F.S s (A x), F.S s x⟫_𝕜 := by
  have hcl : Evolution.IsClassicalSolution A (Icc 0 T) 0 (fun t => F.S t x) := by
    have h := F.isMDissipative.semigroup.isClassicalSolution_orbit
      (F.isMDissipative.mem_semigroup_generator_domain x) 0 T
    rw [F.isMDissipative.generator_semigroup] at h
    simpa [S_def] using h
  refine ⟨hcl, fun U hU0 hU => ?_, fun t ht => F.isMDissipative.norm_sq_semigroup_apply x ht⟩
  exact hU.unique F.isMDissipative.dissipative hcl.toIsStrongSolution (by rw [hU0, S_def]; simp)

/-- **1. The energy is nonincreasing**, `‖S(t) x‖ ≤ ‖S(s) x‖` for `0 ≤ s ≤ t`, for every datum. -/
theorem dissipFEEC_antitone (x : E) : AntitoneOn (fun t => ‖F.S t x‖) (Ici 0) := by
  intro s (hs : 0 ≤ s) t _ hst
  have e : F.S t x = F.S (t - s) (F.S s x) := by
    simp only [S_def]
    rw [← C0Semigroup.S_add_apply _ (by linarith) hs, sub_add_cancel]
  change ‖F.S t x‖ ≤ ‖F.S s x‖
  rw [e]
  exact ((F.S (t - s)).le_opNorm _).trans (by
    simpa [S_def] using mul_le_mul_of_nonneg_right
      (F.isMDissipative.isContraction_semigroup _ (by linarith)) (norm_nonneg (F.S s x)))

/-- **2. Constraint propagation**: `S(t) K ⊆ K` for all `t ≥ 0` iff the resolvents map `K` into
`K`, iff the stationary problem is solvable within `K`; `K` reduces `A` iff `K` and `Kᗮ` are both
invariant. -/
theorem dissipFEEC_propagates_iff :
    (F.Keeps F.K ↔ ∀ μ : ℝ, 0 < μ → ∀ y ∈ F.K, Operator.resolvent A (μ : 𝕜) y ∈ F.K) ∧
    (F.Keeps F.K ↔
      ∃ μ : ℝ, 0 < μ ∧ ∀ y ∈ F.K, ∃ u : A.domain, (u : E) ∈ F.K ∧ (μ : 𝕜) • (u : E) - A u = y) ∧
    (A.IsReducing F.K ↔ F.Keeps F.K ∧ F.Keeps F.Kᗮ) :=
  ⟨F.isMDissipative.invariant_iff_resolvent F.isClosed_K,
    F.isMDissipative.invariant_iff_exists_solve F.isClosed_K, F.isMDissipative.isReducing_iff⟩

/-- **3a. Convergence on the core**, from the comparison initial values, uniformly on `[0, T]`. -/
theorem dissipFEEC_converges_core (Z : F.Core) (T : ℝ) {x : E} (hx : x ∈ Z.Data) :
    TendstoUniformlyOn (fun h t => F.sol h ((Z.cmp T).p x h 0) t) (fun t => F.S t x) F.l
      (Icc 0 T) := by
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
    {v : ∀ h, F.X h} (hv : F.Converges v x) :
    TendstoUniformlyOn (fun h t => F.sol h (v h) t) (fun t => F.S t x) F.l (Icc 0 T) := by
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
  have a1 : ‖F.S t x - F.S t y‖ ≤ ‖x - y‖ := by
    rw [← _root_.map_sub]
    exact ((F.S t).le_opNorm _).trans (by
      simpa [S_def] using mul_le_mul_of_nonneg_right
        (F.isMDissipative.isContraction_semigroup t ht.1) (norm_nonneg (x - y)))
  have a2 : ‖F.S t y - F.sol h w t‖ < ε / 4 := by
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
  have e : F.S t x - F.sol h (v h) t =
      (F.S t x - F.S t y) + (F.S t y - F.sol h w t) + (F.sol h w t - F.sol h (v h) t) := by abel
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

/-- **3c. The rate: best approximation plus consistency** (plus the initial mismatch), for data in
a rate class and every discrete initial value `v`:
`‖S(t) x - ιₕ e^{tLₕ} v‖ ≤ (C + ‖ιₕ‖ C' t) hᵅ ‖x‖_c + ‖ιₕ‖ ‖pₕ(0) - v‖`.
Cf. [HolstStern2012], Thm 3.10 (elliptic analogue) -/
theorem dissipFEEC_rate {T : ℝ} (R : F.RateClass T) {x : E} (hx : x ∈ R.Data) (h : κ)
    (v : F.X h) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖F.S t x - F.sol h v t‖ ≤
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
  have e : F.S t x - F.sol h v t =
      (F.S t x - F.sol h (R.p x h 0) t) + (F.sol h (R.p x h 0) t - F.sol h v t) := by
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
theorem dissipFEEC_residual_le (hK : F.Keeps F.K) {x : E} (hxK : x ∈ F.K) (h : κ) (v : F.X h)
    {t : ℝ} (ht : 0 ≤ t) : infDist (F.sol h v t) F.K ≤ ‖F.S t x - F.sol h v t‖ := by
  rw [norm_sub_rev, ← dist_eq_norm]
  exact infDist_le_dist_of_mem (hK t ht x hxK)

/-- **4a. Residual of an invariant constraint**: for `x ∈ K` in the closure of the core and
every convergent family of discrete initial values, the residual tends to `0` uniformly on
`[0, T]`. -/
theorem dissipFEEC_residual (hK : F.Keeps F.K) (Z : F.Core) (T : ℝ) {x : E}
    (hx : x ∈ Z.Data.topologicalClosure) (hxK : x ∈ F.K) {v : ∀ h, F.X h}
    (hv : F.Converges v x) :
    TendstoUniformlyOn (fun h t => infDist (F.sol h (v h) t) F.K) (fun _ => 0) F.l (Icc 0 T) := by
  have hc := Metric.tendstoUniformlyOn_iff.1 (dissipFEEC_converges F Z T hx hv)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hc ε hε] with h hh t ht
  have := hh t ht
  rw [dist_eq_norm] at this
  rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg infDist_nonneg]
  exact (dissipFEEC_residual_le F hK hxK h (v h) ht.1).trans_lt this

/-- **4b. The residuals detect departures**: for every set `Q`, datum `x` in the closure of the
core, convergent family `vₕ` and `t ≥ 0`, `dist(ιₕ e^{tLₕ} vₕ, Q) → dist(S(t) x, Q)`; the limit is
positive when `Q` is closed and `S(t) x ∉ Q`. -/
theorem dissipFEEC_tendsto_infDist (Z : F.Core) (Q : Set E) {x : E}
    (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h} (hv : F.Converges v x) {t : ℝ}
    (ht : 0 ≤ t) :
    Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l (𝓝 (infDist (F.S t x) Q)) :=
  ((continuous_infDist_pt Q).tendsto _).comp
    ((dissipFEEC_converges F Z t hx hv).tendsto_at ⟨ht, le_rfl⟩)

/-- **4c. A set that is not kept is left arbitrarily soon**: if `S(t) Q ⊄ Q` for some `t ≥ 0`,
then for every `T > 0` some datum of `Q` leaves `Q` by time `T` (`S(t) = S(t - T) S(T)`). -/
theorem dissipFEEC_leaves {Q : Set E} (hQ : ¬ F.Keeps Q) {T : ℝ} (hT : 0 < T) :
    ∃ x ∈ Q, F.Leaves x Q T := by
  by_contra hc
  refine hQ fun t ht x hx =>
    F.isMDissipative.semigroup.forall_nonneg_of_forall_Icc hT (fun y hy s hs => ?_) x hx t ht
  by_contra hout
  exact hc ⟨y, hy, s, hs, hout⟩

/-- **4c. A non-reducing constraint is left** by a datum of `K` or of `Kᗮ` before any time
`T > 0` (`K` reduces `A` iff both are kept). -/
theorem dissipFEEC_leaves_of_not_isReducing (hK : ¬ A.IsReducing F.K) {T : ℝ} (hT : 0 < T) :
    ∃ Q : Submodule 𝕜 E, (Q = F.K ∨ Q = F.Kᗮ) ∧ ∃ x ∈ Q, F.Leaves x Q T := by
  by_cases hk : F.Keeps F.K
  · exact ⟨F.Kᗮ, Or.inr rfl, dissipFEEC_leaves F
      (fun h => hK ((dissipFEEC_propagates_iff F).2.2.2 ⟨hk, h⟩)) hT⟩
  · exact ⟨F.K, Or.inl rfl, dissipFEEC_leaves F hk hT⟩

/-- **4c. A closed set that is not kept is left by a smooth datum**: if `D(A) ∩ Q` is dense in
the closed `Q`, some datum of `D(A) ∩ Q` leaves `Q` by any time `T > 0`. -/
theorem dissipFEEC_leaves_smooth {Q : Set E} (hQc : IsClosed Q) (hQ : ¬ F.Keeps Q)
    (hD : F.SmoothDense Q) {T : ℝ} (hT : 0 < T) :
    ∃ x ∈ (A.domain : Set E) ∩ Q, F.Leaves x Q T := by
  by_contra hc
  refine hQ fun t ht => ?_
  have hP : ∀ y ∈ (A.domain : Set E) ∩ Q, ∀ s, 0 ≤ s → F.S s y ∈ (A.domain : Set E) ∩ Q :=
    F.isMDissipative.semigroup.forall_nonneg_of_forall_Icc hT fun y hy s hs =>
      ⟨F.isMDissipative.semigroup_mem_domain ⟨y, hy.1⟩ hs.1,
        by_contra fun hout => hc ⟨y, hy, s, hs, hout⟩⟩
  exact F.isMDissipative.semigroup.mem_of_dense hQc hD fun y hy => (hP y hy t ht).2

/-- The conclusions of the dissipative FEEC theorem (`dissipFEEC`) for `F` and the core `Z`. -/
structure DissipFEEC.Verdict (Z : F.Core) : Prop where
  /-- for `x ∈ D(A)`, the orbit `t ↦ S(t) x` is a classical solution of `u' = A u` on `[0, T]` -/
  isClassicalSolution (x : A.domain) (T : ℝ) :
    Evolution.IsClassicalSolution A (Icc 0 T) 0 (fun t => F.S t x)
  /-- and the only strong one -/
  unique (x : A.domain) (T : ℝ) (U : ℝ → E) (hU0 : U 0 = (x : E))
    (hU : Evolution.IsStrongSolution A (Icc 0 T) 0 U) : EqOn U (fun t => F.S t x) (Icc 0 T)
  /-- the energy identity `‖S(t) x‖² = ‖x‖² + ∫₀ᵗ 2 re ⟪S(s) A x, S(s) x⟫ ds` on `D(A)` -/
  energy (x : A.domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖F.S t x‖ ^ 2 = ‖(x : E)‖ ^ 2 + ∫ s in (0 : ℝ)..t, 2 * RCLike.re ⟪F.S s (A x), F.S s x⟫_𝕜
  /-- the energy `‖S(t) x‖` of every datum is nonincreasing -/
  antitone (x : E) : AntitoneOn (fun t => ‖F.S t x‖) (Ici 0)
  /-- `K` is kept iff the resolvents `(μ - A)⁻¹`, `μ > 0`, map `K` into `K` -/
  keeps_iff_resolvent :
    F.Keeps F.K ↔ ∀ μ : ℝ, 0 < μ → ∀ y ∈ F.K, Operator.resolvent A (μ : 𝕜) y ∈ F.K
  /-- `K` is kept iff for one `μ > 0` the stationary problem `μ u - A u = f` is solvable in
  `D(A) ∩ K` for all `f ∈ K` -/
  keeps_iff_solvable : F.Keeps F.K ↔
    ∃ μ : ℝ, 0 < μ ∧ ∀ y ∈ F.K, ∃ u : A.domain, (u : E) ∈ F.K ∧ (μ : 𝕜) • (u : E) - A u = y
  /-- `K` reduces `A` iff `K` and `Kᗮ` are kept -/
  isReducing_iff : A.IsReducing F.K ↔ F.Keeps F.K ∧ F.Keeps F.Kᗮ
  /-- on the closure of the core, the discrete states `πₕ x` converge to `x` -/
  tendsto_incl_proj {x : E} (hx : x ∈ Z.Data.topologicalClosure) :
    F.Converges (fun h => F.proj h x) x
  /-- on the closure of the core, from every family `ιₕ vₕ → x`, the discrete solutions converge
  to `S(t) x` uniformly on `[0, T]` -/
  converges {x : E} (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h} (hv : F.Converges v x)
    (T : ℝ) : TendstoUniformlyOn (fun h t => F.sol h (v h) t) (fun t => F.S t x) F.l (Icc 0 T)
  /-- the rate: best approximation plus consistency plus initial mismatch -/
  rate {T : ℝ} (R : F.RateClass T) {x : E} (hx : x ∈ R.Data) (h : κ) (v : F.X h) {t : ℝ}
    (ht : t ∈ Icc 0 T) : ‖F.S t x - F.sol h v t‖ ≤
      (R.C + ‖F.incl h‖ * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖F.incl h‖ * ‖R.p x h 0 - v‖
  /-- for a kept `K`, the residual `dist(ιₕ e^{tLₕ} v, K)` is at most the error from `x ∈ K` -/
  residual_le (hK : F.Keeps F.K) {x : E} (hxK : x ∈ F.K) (h : κ) (v : F.X h) {t : ℝ}
    (ht : 0 ≤ t) : infDist (F.sol h v t) F.K ≤ ‖F.S t x - F.sol h v t‖
  /-- for a kept `K` and `x ∈ K` in the closure of the core, the residuals of every convergent
  family tend to `0` uniformly on `[0, T]` -/
  residual_tendsto (hK : F.Keeps F.K) {x : E} (hxK : x ∈ F.K)
    (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h} (hv : F.Converges v x) (T : ℝ) :
    TendstoUniformlyOn (fun h t => infDist (F.sol h (v h) t) F.K) (fun _ => 0) F.l (Icc 0 T)
  /-- on the closure of the core, the distances of the discrete solutions to any set `Q` tend
  to that of the exact one (positive once it has left a closed `Q`) -/
  tendsto_infDist (Q : Set E) {x : E} (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h}
    (hv : F.Converges v x) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l (𝓝 (infDist (F.S t x) Q))
  /-- a set that is not kept is left by one of its data before any time `T > 0` -/
  leaves {Q : Set E} (hQ : ¬ F.Keeps Q) {T : ℝ} (hT : 0 < T) : ∃ x ∈ Q, F.Leaves x Q T
  /-- a closed set that is not kept, with a dense part in `D(A)`, is left by a datum of that
  part before any time `T > 0` -/
  leaves_smooth {Q : Set E} (hQc : IsClosed Q) (hQ : ¬ F.Keeps Q) (hD : F.SmoothDense Q) {T : ℝ}
    (hT : 0 < T) : ∃ x ∈ (A.domain : Set E) ∩ Q, F.Leaves x Q T

/-- **The dissipative FEEC theorem.** For a dissipative FEEC discretization `F` of `ξ' = A ξ`
with `A` m-dissipative (discrete Hilbert spaces with their own inner products, bounded
dissipative generators, uniformly bounded reading maps with uniformly bounded left inverses;
variational crimes allowed) and an orbit-consistent core `Z`:

1. (**well-posedness**, Lumer–Phillips) for `ξ₀ ∈ D(A)`, `t ↦ S(t) ξ₀` is a classical solution
   and the only strong one, with the energy identity; the energy of every datum is nonincreasing;
2. (**propagation**) `S(t) K ⊆ K` for `t ≥ 0` iff `(μ - A)⁻¹ K ⊆ K` for `μ > 0`, iff the
   stationary problem is solvable in `D(A) ∩ K`; `K` reduces `A` iff `K` and `Kᗮ` are invariant;
3. (**convergence**) on the closure of the core, for every family with `ιₕ vₕ → ξ₀` (and
   `vₕ = πₕ ξ₀` is one), uniformly on `[0, T]`, and the rate
   `(C + ‖ιₕ‖ C' t) hᵅ ‖ξ₀‖_c + ‖ιₕ‖ ‖pₕ(0) - v‖`;
4. (**constraint residual**) for invariant `K`: bounded by the error, tends to `0`; the
   distances of the discrete solutions to any set tend to that of the exact solution; a set that
   is not kept is left by one of its data before any `T > 0`, by a smooth datum when it is closed
   with a dense smooth part.

Cf. [Pazy1983], §1.4 (Thm 4.3), §3.4; [HolstStern2012], Thm 3.9, Thm 3.10 (elliptic analogues) -/
theorem dissipFEEC (Z : F.Core) : F.Verdict Z where
  isClassicalSolution x T := (dissipFEEC_wellPosed F x T).1
  unique x T U hU0 hU := (dissipFEEC_wellPosed F x T).2.1 U hU0 hU
  energy := fun x {_} ht => (dissipFEEC_wellPosed F x 0).2.2 _ ht
  antitone := dissipFEEC_antitone F
  keeps_iff_resolvent := (dissipFEEC_propagates_iff F).1
  keeps_iff_solvable := (dissipFEEC_propagates_iff F).2.1
  isReducing_iff := (dissipFEEC_propagates_iff F).2.2
  tendsto_incl_proj := fun {_} hx => tendsto_incl_proj F Z hx
  converges := fun {_} hx {_} hv T => dissipFEEC_converges F Z T hx hv
  rate := fun {_} R {_} hx h v {_} ht => dissipFEEC_rate F R hx h v ht
  residual_le := fun hK {_} hxK h v {_} ht => dissipFEEC_residual_le F hK hxK h v ht
  residual_tendsto := fun hK {_} hxK hx {_} hv T => dissipFEEC_residual F hK Z T hx hxK hv
  tendsto_infDist := fun Q {_} hx {_} hv {_} ht => dissipFEEC_tendsto_infDist F Z Q hx hv ht
  leaves := fun {_} hQ {_} hT => dissipFEEC_leaves F hQ hT
  leaves_smooth := fun {_} hQc hQ hD {_} hT => dissipFEEC_leaves_smooth F hQc hQ hD hT

variable {F} in
/-- **A departure is detected by the residuals** (a corollary of the verdict, not a field): if
`S(t) x ∉ Q` (`t ≥ 0`) for a closed nonempty `Q`, then `dist(S(t) x, Q) > 0`, and when `x` is in
the closure of the core, the residuals `dist(ιₕ e^{tLₕ} vₕ, Q)` of every family `ιₕ vₕ → x` tend to
it (`tendsto_infDist`), so they eventually exceed half of it. -/
theorem DissipFEEC.Verdict.detects {Z : F.Core} (V : F.Verdict Z) {Q : Set E} (hQc : IsClosed Q)
    (hQ : Q.Nonempty) {x : E} {t : ℝ} (ht : 0 ≤ t) (hout : F.S t x ∉ Q) :
    0 < infDist (F.S t x) Q ∧ (x ∈ Z.Data.topologicalClosure → ∀ v : ∀ h, F.X h,
      F.Converges v x → Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l
        (𝓝 (infDist (F.S t x) Q)) ∧
      ∀ᶠ h in F.l, infDist (F.S t x) Q / 2 < infDist (F.sol h (v h) t) Q) := by
  have hpos := (hQc.notMem_iff_infDist_pos hQ).1 hout
  refine ⟨hpos, fun hx v hv => ?_⟩
  have hlim := V.tendsto_infDist Q hx hv ht
  exact ⟨hlim, (tendsto_order.1 hlim).1 _ (half_lt_self hpos)⟩

end Main

end Feec.HilbertComplex
