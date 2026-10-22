module

public import Feec.HilbertComplex.Approximation.ConstrainedFEEC
public import Feec.Semigroup.DomainSq

/-!
# The approximating FEEC theorem

An **approximating FEEC discretization** (`Feec.HilbertComplex.ApproxFEEC`) of the Hodge wave
equation `ξ' = L ξ` (`L = 𝐝 - 𝐝†`) of a Hilbert complex `H` allows variational crimes: its discrete
spaces `Xₕ` are Hilbert spaces of their own (not subspaces of `W`, with their own inner products,
not necessarily finite-dimensional), its discrete generators `Lₕ` are bounded and skew in the
discrete inner product (so `e^{tLₕ}` is unitary: uniform stability), and it is read in `W`
through uniformly bounded maps `ιₕ : Xₕ → W` with uniformly bounded left inverses `πₕ`
(`πₕ ιₕ = 1`). Neither `ιₕ` nor `πₕ` is assumed isometric, a cochain map, or to commute with
anything; `ιₕ πₕ → 1` is not assumed either: it is derived (`ApproxFEEC.tendsto_incl_proj`).
The discrete solution is `ιₕ e^{tLₕ} v` (`ApproxFEEC.sol`).

**Consistency** is tested along exact orbits, never in operator norm (for the BGG scheme of
[QuennevilleBelair2015], (6.5), the static strong consistency bound of Prop. 5.9(2) for
`S₁ - S₁,ₕ` fails, with ratio `√(2/3)`, per an unformalized symbolic audit recorded in
`Feec.HilbertComplex.BGG.WeakConsistency`). A **comparison** (`ApproxFEEC.Comparison`) assigns to
each datum `x` discrete trajectories `pₕ(t)` with derivatives `pₕ'(t)`; its **consistency defect**
is `pₕ' - Lₕ pₕ`. A **core** (`ApproxFEEC.Core`) is a subspace of data whose comparisons
approximate the orbit in `W` (`ιₕ pₕ(t) → e^{tL} x`) with defects tending to `0`, both uniformly on
`[0, T]` (the orbit form of the Trotter–Kato consistency hypothesis). The abstract estimate
`norm_sub_le_of_defect` (energy method) reads

`‖e^{tL} x - ιₕ e^{tLₕ} pₕ(0)‖ ≤ ‖e^{tL} x - ιₕ pₕ(t)‖ + ‖ιₕ‖ ∫₀ᵗ ‖pₕ' - Lₕ pₕ‖`,

**best approximation plus consistency**, a semi-discrete (evolution) analogue of the elliptic
estimates of [HolstStern2012], Thm 3.9, Thm 3.10. The Holst–Stern terms `‖I - Jₕ‖` and
`‖(I - iₕπₕ)u‖` do not appear as such: inner-product and commutation crimes both enter through
the orbit defect `pₕ' - Lₕ pₕ`.

`ApproxFEEC` is a **semigroup-form** abstraction: it carries no discrete differential `𝐝ₕ` and
no cochain condition on `ιₕ`; the complex structure of the discrete spaces is not a hypothesis.
Consequently it cannot express discrete constraints such as `𝐝ₕ`-closedness being preserved; the
constraint residual is measured in `W`, through `ιₕ`. The complex-level front end
`ApproxFEEC.ofComplex` (`Feec.HilbertComplex.Approximation.ApproxComplex`) builds an `ApproxFEEC`
from a family of discrete Hilbert complexes with cochain maps `iₕ` ([HolstStern2012], §3), derives
its core from the inner-product defect and the graph-norm approximation property, and states the
discrete constraints (`approxFEEC_ofComplex`).

## Main results

The **approximating FEEC theorem** `approxFEEC` (statement `ApproxFEEC.Verdict`) bundles:

1. well-posedness of the continuous problem (`constrainedFEEC_wellPosed`);
2. `approxFEEC_propagates_iff`: constraints propagate iff `K` reduces `L`;
3. convergence: `approxFEEC_converges_core` (from the comparison initial values, on the core),
   `approxFEEC_converges` (on the closure of the core, for every family `vₕ` with `ιₕ vₕ → x`;
   `ιₕ πₕ x → x` gives one, `ApproxFEEC.tendsto_incl_proj`), `approxFEEC_rate` (for a rate class:
   `‖e^{tL} x - ιₕ e^{tLₕ} v‖ ≤ (C + ‖ιₕ‖ C' t) hᵅ ‖x‖_c + ‖ιₕ‖ ‖pₕ(0) - v‖`);
4. the constraint residual `dist(ιₕ e^{tLₕ} vₕ, K)`, measured through `ιₕ`:
   `approxFEEC_residual_le`, `approxFEEC_residual` (reducing `K`: bounded by the error, tends to
   `0` uniformly), `approxFEEC_residual_not_mem` (per datum: a solution leaving a closed nonempty
   `Q` has residuals tending to `dist(e^{tL} x, Q) > 0`), `approxFEEC_exists_not_mem`
   (a non-reducing `K` is left by data of `K` or `Kᗮ`), `approxFEEC_residual_not_isReducing_symm`
   (with `D(L) ∩ K` dense in `K`: a datum of `D(L) ∩ K` leaves `K` for some `t ∈ [-T, T]`),
   `approxFEEC_residual_not_isReducing_of_grading` (graded complex, `R`-invariant `K`: a datum of
   `D(L) ∩ K` leaves `K` forward in time, with residuals tending to a positive limit).

Constructions of cores: `ApproxFEEC.Core.ofOperator` (the Trotter–Kato bridge: an operator
`Rₕ : Γ(𝐝) → Xₕ` with `ιₕ Rₕ → graphFst` pointwise and a defect identity on `D(L²)` with uniformly
bounded defect operators tending to `0` pointwise; uniformity on `[0, T]` comes from the
compactness of the orbits), and `ApproxFEEC.complexify` runs a real scheme on real and imaginary
parts.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (Thm 3.9, Thm 3.10)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §3.4 (Trotter–Kato approximation theorems)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4 (Thms 4.6, 4.7), §4.10 (Prop. 4.17), §6.3 ((6.5))

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

/-! ### The abstract consistency estimate -/

section Core

variable {𝕜 : Type*} [RCLike 𝕜] {X E : Type*}
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X] [NormedSpace ℝ X]
  [IsScalarTower ℝ 𝕜 X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **The abstract consistency estimate** (energy method): for a skew bounded `L` on `X`, a
bounded `ι : X → E`, a target `u` and a comparison trajectory `p` with right derivative `p'` on
`[0, T]`, `‖u(t) - ι e^{tL} p(0)‖ ≤ ‖u(t) - ι p(t)‖ + ‖ι‖ ∫₀ᵗ ‖p' - L p‖`. -/
theorem norm_sub_le_of_defect (L : X →L[𝕜] X) (hL : ∀ x y, ⟪L x, y⟫_𝕜 = -⟪x, L y⟫_𝕜)
    (ι : X →L[𝕜] E) {u : ℝ → E} {p p' : ℝ → X} {T : ℝ}
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
    have hskew : RCLike.re ⟪L (e t), e t⟫_𝕜 = 0 := by
      have h := hL (e t) (e t)
      have : RCLike.re ⟪L (e t), e t⟫_𝕜 = - RCLike.re ⟪L (e t), e t⟫_𝕜 := by
        conv_rhs => rw [h, _root_.map_neg, ← inner_conj_symm, RCLike.conj_re]
        simp
      linarith
    rw [hsplit, inner_add_left, _root_.map_add, hskew, add_zero]
    exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
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

/-- **Uniqueness for skew bounded generators**: a differentiable `u` with `u' = L u` is the
orbit `e^{tL} u(0)`, for all times (forward by the energy estimate, backward by time reversal). -/
theorem eq_ofBounded_of_hasDerivAt (L : X →L[𝕜] X) (hL : ∀ x y, ⟪L x, y⟫_𝕜 = -⟪x, L y⟫_𝕜)
    {u : ℝ → X} (hu : ∀ t, HasDerivAt u (L (u t)) t) (t : ℝ) :
    u t = (C0Group.ofBounded L).S t (u 0) := by
  have fwd : ∀ (L : X →L[𝕜] X), (∀ x y, ⟪L x, y⟫_𝕜 = -⟪x, L y⟫_𝕜) → ∀ u : ℝ → X,
      (∀ t, HasDerivAt u (L (u t)) t) → ∀ t, 0 ≤ t → u t = (C0Group.ofBounded L).S t (u 0) := by
    intro L hL u hu t ht
    have hc : Continuous u := continuous_iff_continuousAt.2 fun s => (hu s).continuousAt
    have h := norm_sub_le_of_defect L hL (ContinuousLinearMap.id 𝕜 X) (u := u) (p := u)
      (p' := fun s => L (u s)) (T := t) hc.continuousOn
      (L.continuous.comp hc).continuousOn (fun s _ => (hu s).hasDerivWithinAt) t ⟨ht, le_rfl⟩
    simp only [ContinuousLinearMap.id_apply, sub_self, norm_zero, intervalIntegral.integral_zero,
      mul_zero, add_zero, norm_le_zero_iff] at h
    exact (sub_eq_zero.1 h)
  rcases le_total 0 t with ht | ht
  · exact fwd L hL u hu t ht
  · have hL' : ∀ x y, ⟪(-L) x, y⟫_𝕜 = -⟪x, (-L) y⟫_𝕜 := fun x y => by
      simp only [_root_.neg_apply, inner_neg_left, inner_neg_right, hL]
    have hv : ∀ s, HasDerivAt (fun s => u (-s)) ((-L) (u (-s))) s := fun s => by
      have := (hu (-s)).scomp s (hasDerivAt_neg s)
      simpa [Function.comp_def] using this
    have h := fwd (-L) hL' (fun s => u (-s)) hv (-t) (by linarith)
    simp only [neg_neg, neg_zero] at h
    rw [h, C0Group.ofBounded_S, C0Group.ofBounded_S]
    congr 2
    rw [RCLike.ofReal_neg, smul_neg, neg_smul, neg_neg]

end Core

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

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

/-! ### Orbits of `D(L²)` in the graph space -/

section Orbit

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- `L e^{tL} x = e^{tL} L x` on `D(L)`. -/
theorem wave_waveGroup {H : HilbertComplex 𝕜 c W} {x : PiLp 2 W} (hx : x ∈ H.wave.domain)
    (t : ℝ) :
    H.wave ⟨H.waveGroup.S t x, waveGroup_mem_domain H hx t⟩ =
      H.waveGroup.S t (H.wave ⟨x, hx⟩) := by
  have hg := H.generator_waveGroup
  have hx' : x ∈ H.waveGroup.generator.domain := by rw [hg]; exact hx
  have h := H.waveGroup.generator_apply_S ⟨x, hx'⟩ t
  rwa [LinearPMap.apply_eq_of_eq hg _ ⟨H.waveGroup.S t x, waveGroup_mem_domain H hx t⟩ rfl,
    LinearPMap.apply_eq_of_eq hg _ ⟨x, hx⟩ rfl] at h

variable (H : HilbertComplex 𝕜 c W)

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
open scoped Classical in
/-- `L` on `D(L)`, extended by `0`. -/
def waveExt (x : PiLp 2 W) : PiLp 2 W :=
  if hx : x ∈ H.wave.domain then H.wave ⟨x, hx⟩ else 0

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
variable {H} in
theorem waveExt_of_mem {x : PiLp 2 W} (hx : x ∈ H.wave.domain) :
    H.waveExt x = H.wave ⟨x, hx⟩ := by
  unfold waveExt; simp [hx]

open scoped Classical in
/-- The graph-space orbit `t ↦ (e^{tL} x, 𝐝 e^{tL} x)` of `x ∈ D(L)` (`0` off `D(L)`). -/
def waveOrbit (x : PiLp 2 W) (t : ℝ) : H.totalD.GraphSpace :=
  if hx : x ∈ H.wave.domain then waveLift H ⟨H.waveGroup.S t x, waveGroup_mem_domain H hx t⟩
  else 0

theorem waveOrbit_of_mem {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (t : ℝ) :
    waveOrbit H x t = waveLift H ⟨H.waveGroup.S t x, waveGroup_mem_domain H hx t⟩ := by
  unfold waveOrbit; simp [hx]

theorem graphFst_waveOrbit {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (t : ℝ) :
    H.totalD.graphFst (waveOrbit H x t) = H.waveGroup.S t x := by
  rw [waveOrbit_of_mem H hx]; rfl

/-- The orbit of `L x` is the lift of `L e^{tL} x`. -/
theorem waveOrbit_waveExt {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq) (t : ℝ) :
    waveOrbit H (waveExt H x) t = waveLift H ⟨H.wave ⟨H.waveGroup.S t x,
      waveGroup_mem_domain H (domainSq_le_domain hx) t⟩, by
        rw [wave_waveGroup (domainSq_le_domain hx) t]
        exact waveGroup_mem_domain H (mem_domainSq.1 hx).2 t⟩ := by
  have hx1 := domainSq_le_domain hx
  have hx2 : waveExt H x ∈ H.wave.domain := by
    rw [waveExt_of_mem hx1]; exact (mem_domainSq.1 hx).2
  rw [waveOrbit_of_mem H hx2]
  congr 2
  rw [wave_waveGroup hx1 t, waveExt_of_mem hx1]

/-- **The graph-space orbit of `x ∈ D(L²)` is `C¹`**, with derivative the orbit of `L x`. -/
theorem waveOrbit_isC1 {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq) {b : ℝ} (hb : 0 < b) :
    ContinuousOn (waveOrbit H x) (Icc 0 b) ∧
      ContinuousOn (waveOrbit H (waveExt H x)) (Icc 0 b) ∧
      ∀ t ∈ Icc 0 b, HasDerivWithinAt (waveOrbit H x) (waveOrbit H (waveExt H x) t)
        (Icc 0 b) t := by
  have hx1 := domainSq_le_domain hx
  have hLx : H.wave ⟨x, hx1⟩ ∈ H.wave.domain := (mem_domainSq.1 hx).2
  have hx2 : waveExt H x ∈ H.wave.domain := by rw [waveExt_of_mem hx1]; exact hLx
  obtain ⟨ξ, ξ', hξ, hξS, hξ'S⟩ := exists_isGraphSolution_waveGroup H hx1 hLx hb
  have e1 : ξ = waveOrbit H x := funext fun t => H.totalD.graphFst_injective (by
    rw [hξS, graphFst_waveOrbit H hx1])
  have e2 : EqOn ξ' (waveOrbit H (waveExt H x)) (Icc 0 b) := fun t ht =>
    H.totalD.graphFst_injective (by
      rw [hξ'S t ht, graphFst_waveOrbit H hx2, waveExt_of_mem hx1])
  subst e1
  refine ⟨hξ.continuousOn, hξ.continuousOn_deriv.congr fun t ht => (e2 ht).symm,
    fun t ht => ?_⟩
  rw [← e2 ht]
  exact hξ.deriv t ht

/-- The `C¹` facts of `waveOrbit_isC1` on `[0, T]`, with right derivatives. -/
theorem waveOrbit_isC1' {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq) (T : ℝ) :
    ContinuousOn (waveOrbit H x) (Icc 0 T) ∧
      ContinuousOn (waveOrbit H (waveExt H x)) (Icc 0 T) ∧
      ∀ t ∈ Ico 0 T, HasDerivWithinAt (waveOrbit H x) (waveOrbit H (waveExt H x) t)
        (Ici t) t := by
  have hb : (0 : ℝ) < max T 0 + 1 := by positivity
  have hsub : Icc 0 T ⊆ Icc 0 (max T 0 + 1) :=
    Icc_subset_Icc le_rfl (by linarith [le_max_left T 0])
  obtain ⟨h1, h2, h3⟩ := waveOrbit_isC1 H hx hb
  refine ⟨h1.mono hsub, h2.mono hsub, fun t ht => ?_⟩
  have ht' : t ∈ Ico 0 (max T 0 + 1) := ⟨ht.1, by linarith [ht.2, le_max_left T 0]⟩
  exact (h3 t (Ico_subset_Icc_self ht')).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht')

/-- The orbits of `x ∈ D(L²)` and of `L x` on `[0, T]` are compact in the graph space. -/
theorem isCompact_waveOrbit {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq) (T : ℝ) :
    IsCompact (waveOrbit H x '' Icc 0 T) ∧ IsCompact (waveOrbit H (waveExt H x) '' Icc 0 T) :=
  ⟨isCompact_Icc.image_of_continuousOn (waveOrbit_isC1' H hx T).1,
    isCompact_Icc.image_of_continuousOn (waveOrbit_isC1' H hx T).2.1⟩

end Orbit

/-! ### Approximating FEEC discretizations -/

/-- An **approximating FEEC discretization** (semigroup form) of the Hodge wave equation of `H`:
a closed constraint `K`; Hilbert spaces `Xₕ` with their own inner products (not subspaces of
`W`, not necessarily finite-dimensional) and skew bounded generators `Lₕ` (so `e^{tLₕ}` is
unitary: uniform stability); uniformly bounded `ιₕ : Xₕ → W`, `πₕ : W → Xₕ` with `πₕ ιₕ = 1`.
`ιₕ πₕ → 1` is NOT assumed: it is derived on the closure of a core (`tendsto_incl_proj`).
[HolstStern2012], §3 -/
structure ApproxFEEC (H : HilbertComplex 𝕜 c W) (κ : Type*) where
  /-- the constraint subspace -/
  K : Submodule 𝕜 (PiLp 2 W)
  isClosed_K : IsClosed (K : Set (PiLp 2 W))
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
  skew : ∀ h x y, ⟪L h x, y⟫_𝕜 = -⟪x, L h y⟫_𝕜
  /-- the maps reading discrete states in `W` -/
  incl : ∀ h, X h →L[𝕜] PiLp 2 W
  /-- their left inverses -/
  proj : ∀ h, PiLp 2 W →L[𝕜] X h
  proj_incl : ∀ h x, proj h (incl h x) = x
  bound : ∃ C, ∀ h, ‖incl h‖ ≤ C ∧ ‖proj h‖ ≤ C

attribute [instance] ApproxFEEC.normedAddCommGroup ApproxFEEC.innerProductSpace
  ApproxFEEC.completeSpace ApproxFEEC.normedSpaceReal ApproxFEEC.isScalarTower

namespace ApproxFEEC

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxFEEC.{u} H κ)

instance : CompleteSpace F.K := F.isClosed_K.completeSpace_coe

instance : F.K.HasOrthogonalProjection := .ofCompleteSpace _

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

theorem norm_incl_proj_le (h : κ) (y : PiLp 2 W) :
    ‖F.incl h (F.proj h y)‖ ≤ F.boundConst ^ 2 * ‖y‖ := by
  have h1 := F.norm_incl_apply_le h (F.proj h y)
  have h2 := ((F.proj h).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right (F.norm_proj_le h) (norm_nonneg _))
  have h0 := F.boundConst_nonneg
  calc _ ≤ F.boundConst * ‖F.proj h y‖ := h1
    _ ≤ F.boundConst * (F.boundConst * ‖y‖) := mul_le_mul_of_nonneg_left h2 h0
    _ = _ := by ring

/-- The discrete group `e^{t Lₕ}`. -/
def group (h : κ) : C0Group 𝕜 (F.X h) := C0Group.ofBounded (F.L h)

theorem norm_group_apply (h : κ) (t : ℝ) (v : F.X h) : ‖(F.group h).S t v‖ = ‖v‖ :=
  C0Group.isIsometric_ofBounded (F.skew h) t v

/-- The discrete solution `ιₕ e^{t Lₕ} v`. -/
def sol (h : κ) (v : F.X h) (t : ℝ) : PiLp 2 W := F.incl h ((F.group h).S t v)

@[simp] theorem sol_zero (h : κ) (v : F.X h) : F.sol h v 0 = F.incl h v := by
  simp [sol, group]

theorem norm_sol_sub_sol_le (h : κ) (v w : F.X h) (t : ℝ) :
    ‖F.sol h v t - F.sol h w t‖ ≤ ‖F.incl h‖ * ‖v - w‖ := by
  rw [sol, sol, ← _root_.map_sub, ← _root_.map_sub]
  refine ((F.incl h).le_opNorm _).trans ?_
  rw [norm_group_apply]

/-- **Comparison trajectories** on `[0, T]`: for each datum `x` of `Data`, discrete trajectories
`pₕ(t)` with right derivatives `pₕ'(t)`. Consistency is tested along them (orbit form), never in
operator norm: for (6.5) the static strong consistency bound Prop. 5.9(2) fails (ratio `√(2/3)`,
per the unformalized audit recorded in `Feec.HilbertComplex.BGG.WeakConsistency`). -/
structure Comparison (T : ℝ) where
  /-- the data -/
  Data : Set (PiLp 2 W)
  /-- the comparison trajectories -/
  p : PiLp 2 W → ∀ h, ℝ → F.X h
  /-- their derivatives -/
  p' : PiLp 2 W → ∀ h, ℝ → F.X h
  continuousOn : ∀ x ∈ Data, ∀ h, ContinuousOn (p x h) (Icc 0 T)
  continuousOn' : ∀ x ∈ Data, ∀ h, ContinuousOn (p' x h) (Icc 0 T)
  hasDerivWithinAt : ∀ x ∈ Data, ∀ h, ∀ t ∈ Ico 0 T,
    HasDerivWithinAt (p x h) (p' x h t) (Ici t) t

variable {F} in
/-- The **consistency defect** `pₕ' - Lₕ pₕ`. -/
def Comparison.defect {T : ℝ} (P : F.Comparison T) (x : PiLp 2 W) (h : κ) (t : ℝ) : F.X h :=
  P.p' x h t - F.L h (P.p x h t)

variable {F} in
/-- Restriction of a comparison to a subset of its data. -/
def Comparison.restrict {T : ℝ} (P : F.Comparison T) (S : Set (PiLp 2 W)) (hS : S ⊆ P.Data) :
    F.Comparison T where
  Data := S
  p := P.p
  p' := P.p'
  continuousOn x hx := P.continuousOn x (hS hx)
  continuousOn' x hx := P.continuousOn' x (hS hx)
  hasDerivWithinAt x hx := P.hasDerivWithinAt x (hS hx)

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- A **rate class** on `[0, T]`: comparison trajectories with best approximation
`‖e^{tL} x - ιₕ pₕ(t)‖ ≤ C hᵅ ‖x‖_c` and consistency `‖pₕ' - Lₕ pₕ‖ ≤ C' hᵅ ‖x‖_c`.
Cf. [HolstStern2012], Thm 3.10 (elliptic analogue) -/
structure RateClass (T : ℝ) extends F.Comparison T where
  /-- the norm of the class -/
  classNorm : PiLp 2 W → ℝ
  /-- the mesh size -/
  meshSize : κ → ℝ
  /-- the order -/
  α : ℝ
  /-- the approximation constant -/
  C : ℝ
  /-- the consistency constant -/
  C' : ℝ
  approx : ∀ x ∈ Data, ∀ h, ∀ t ∈ Icc 0 T,
    ‖H.waveGroup.S t x - F.incl h (p x h t)‖ ≤ C * meshSize h ^ α * classNorm x
  consistency : ∀ x ∈ Data, ∀ h, ∀ t ∈ Icc 0 T,
    ‖toComparison.defect x h t‖ ≤ C' * meshSize h ^ α * classNorm x

/-- An **orbit-consistent core** (the orbit form of the Trotter–Kato consistency hypothesis): a
subspace of data with comparisons on every horizon `[0, T]` that approximate the exact orbit
through `ιₕ` and whose consistency defects tend to `0`, both uniformly on `[0, T]`.
[Pazy1983], §3.4 -/
structure Core where
  /-- the core -/
  Data : Submodule 𝕜 (PiLp 2 W)
  /-- the comparisons -/
  cmp : ∀ T : ℝ, F.Comparison T
  data_eq : ∀ T, (cmp T).Data = Data
  tendsto_approx : ∀ T, ∀ x ∈ Data, TendstoUniformlyOn
    (fun h t => F.incl h ((cmp T).p x h t)) (fun t => H.waveGroup.S t x) F.l (Icc 0 T)
  tendsto_defect : ∀ T, ∀ x ∈ Data, TendstoUniformlyOn
    (fun h t => ‖(cmp T).defect x h t‖) (fun _ => 0) F.l (Icc 0 T)

/-- **Best approximation plus consistency**: the error of the discrete solution from the
comparison initial value is at most the approximation error plus `‖ιₕ‖` times the integrated
consistency defect. Cf. [HolstStern2012], Thm 3.9 (elliptic analogue) -/
theorem norm_sub_sol_le {T : ℝ} (P : F.Comparison T) {x : PiLp 2 W} (hx : x ∈ P.Data) (h : κ) :
    ∀ t ∈ Icc 0 T, ‖H.waveGroup.S t x - F.sol h (P.p x h 0) t‖ ≤
      ‖H.waveGroup.S t x - F.incl h (P.p x h t)‖ +
        ‖F.incl h‖ * ∫ s in (0 : ℝ)..t, ‖P.defect x h s‖ :=
  norm_sub_le_of_defect (F.L h) (F.skew h) (F.incl h) (P.continuousOn x hx h)
    (P.continuousOn' x hx h) (P.hasDerivWithinAt x hx h)

variable {F} in
/-- The comparison initial values of a core read in `W` converge to the datum. -/
theorem Core.tendsto_incl_p (Z : F.Core) {T : ℝ} (hT : 0 ≤ T) {x : PiLp 2 W}
    (hx : x ∈ Z.Data) : Tendsto (fun h => F.incl h ((Z.cmp T).p x h 0)) F.l (𝓝 x) := by
  have h0 := (Z.tendsto_approx T x hx).tendsto_at (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)
  rwa [C0Group.S_zero_apply] at h0

/-- **The approximation property, derived**: `ιₕ πₕ x → x` on the closure of a core (`πₕ ιₕ = 1`
and the uniform bounds give `‖ιₕ πₕ y - y‖ ≤ (1 + C²) ‖y - ιₕ v‖`). -/
theorem tendsto_incl_proj (Z : F.Core) {x : PiLp 2 W} (hx : x ∈ Z.Data.topologicalClosure) :
    Tendsto (fun h => F.incl h (F.proj h x)) F.l (𝓝 x) := by
  set B := F.boundConst ^ 2 + 1
  have hB : 0 < B := by positivity
  have key : ∀ (h : κ) (y : PiLp 2 W) (v : F.X h),
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

/-- Comparison trajectories `pₕ(t) = Rₕ (e^{tL} x, 𝐝 e^{tL} x)` of an operator
`Rₕ : Γ(𝐝) → Xₕ`, on `D(L²)`, with derivatives `pₕ'(t) = Rₕ (L e^{tL} x, 𝐝 L e^{tL} x)`. -/
def Comparison.ofOperator (R : ∀ h, H.totalD.GraphSpace →L[𝕜] F.X h) (T : ℝ) :
    F.Comparison T where
  Data := H.wave.domainSq
  p x h t := R h (waveOrbit H x t)
  p' x h t := R h (waveOrbit H (waveExt H x) t)
  continuousOn _ hx h := (R h).continuous.comp_continuousOn (waveOrbit_isC1' H hx T).1
  continuousOn' _ hx h := (R h).continuous.comp_continuousOn (waveOrbit_isC1' H hx T).2.1
  hasDerivWithinAt _ hx h t ht :=
    ((R h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      ((waveOrbit_isC1' H hx T).2.2 t ht)

/-- Uniform approximation along the orbits, from pointwise approximation by uniformly bounded
`ιₕ Rₕ` (compactness of the orbit). -/
theorem tendstoUniformlyOn_ofOperator (R : ∀ h, H.totalD.GraphSpace →L[𝕜] F.X h)
    (hR : ∃ C, ∀ h, ‖R h‖ ≤ C)
    (happrox : ∀ ζ, Tendsto (fun h => F.incl h (R h ζ)) F.l (𝓝 (H.totalD.graphFst ζ)))
    (T : ℝ) {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq) :
    TendstoUniformlyOn (fun h t => F.incl h (R h (waveOrbit H x t)))
      (fun t => H.waveGroup.S t x) F.l (Icc 0 T) := by
  obtain ⟨C, hC⟩ := hR
  set A : ∀ _ : κ, H.totalD.GraphSpace →L[𝕜] PiLp 2 W := fun h =>
    H.totalD.graphFst - F.incl h ∘L R h
  have hA : ∀ h ζ, ‖A h ζ‖ ≤ (1 + F.boundConst * max C 0) * ‖ζ‖ := fun h ζ => by
    have h1 := HodgeWave.norm_graphFst_le (T := H.totalD) ζ
    have h2 : ‖F.incl h (R h ζ)‖ ≤ F.boundConst * (max C 0 * ‖ζ‖) :=
      (F.norm_incl_apply_le h _).trans (mul_le_mul_of_nonneg_left
        (((R h).le_opNorm ζ).trans (mul_le_mul_of_nonneg_right
          ((hC h).trans (le_max_left _ _)) (norm_nonneg _))) F.boundConst_nonneg)
    calc ‖A h ζ‖ ≤ ‖H.totalD.graphFst ζ‖ + ‖F.incl h (R h ζ)‖ := norm_sub_le _ _
      _ ≤ _ := by nlinarith
  have hlim : ∀ ζ, Tendsto (fun h => ‖A h ζ‖) F.l (𝓝 0) := fun ζ => by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 (happrox ζ))
    refine this.congr fun h => ?_
    rw [norm_sub_rev]; rfl
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_forall_norm_lt_of_tendsto hA hlim (isCompact_waveOrbit H hx T).1
    hε] with h hh t ht
  have := hh _ (mem_image_of_mem _ ht)
  rw [dist_eq_norm]
  convert this using 2
  simp only [A, _root_.sub_apply, ContinuousLinearMap.comp_apply,
    graphFst_waveOrbit H (domainSq_le_domain hx)]

/-- **The Trotter–Kato bridge**: an operator `Rₕ : Γ(𝐝) → Xₕ`, uniformly bounded, with
`ιₕ Rₕ ζ → graphFst ζ`, and a defect identity on `D(L²)`,
`Rₕ (L y) - Lₕ Rₕ y = Δₕ (L y) + Δₕ' y` (lifted to `Γ(𝐝)`), with uniformly bounded `Δₕ`, `Δₕ'`
tending to `0` pointwise, give a core `D(L²)`; uniformity on `[0, T]` comes from the compactness
of the orbits. [Pazy1983], §3.4 -/
def Core.ofOperator (R : ∀ h, H.totalD.GraphSpace →L[𝕜] F.X h)
    (hR : ∃ C, ∀ h, ‖R h‖ ≤ C)
    (happrox : ∀ ζ, Tendsto (fun h => F.incl h (R h ζ)) F.l (𝓝 (H.totalD.graphFst ζ)))
    (Δ Δ' : ∀ h, H.totalD.GraphSpace →L[𝕜] F.X h) (hΔ : ∃ C, ∀ h, ‖Δ h‖ ≤ C ∧ ‖Δ' h‖ ≤ C)
    (hdef : ∀ h (y : H.wave.domain) (hLy : H.wave y ∈ H.wave.domain),
      R h (waveLift H ⟨_, hLy⟩) - F.L h (R h (waveLift H y)) =
        Δ h (waveLift H ⟨_, hLy⟩) + Δ' h (waveLift H y))
    (hΔ0 : ∀ ζ, Tendsto (fun h => ‖Δ h ζ‖) F.l (𝓝 0))
    (hΔ'0 : ∀ ζ, Tendsto (fun h => ‖Δ' h ζ‖) F.l (𝓝 0)) : F.Core where
  Data := H.wave.domainSq
  cmp T := Comparison.ofOperator F R T
  data_eq _ := rfl
  tendsto_approx T _ hx := F.tendstoUniformlyOn_ofOperator R hR happrox T hx
  tendsto_defect T x hx := by
    obtain ⟨C, hC⟩ := hΔ
    have hb1 : ∀ h ζ, ‖Δ h ζ‖ ≤ C * ‖ζ‖ := fun h ζ => ((Δ h).le_opNorm ζ).trans
      (mul_le_mul_of_nonneg_right (hC h).1 (norm_nonneg _))
    have hb2 : ∀ h ζ, ‖Δ' h ζ‖ ≤ C * ‖ζ‖ := fun h ζ => ((Δ' h).le_opNorm ζ).trans
      (mul_le_mul_of_nonneg_right (hC h).2 (norm_nonneg _))
    have hx1 := domainSq_le_domain hx
    have hdefect : ∀ h t, ‖(Comparison.ofOperator F R T).defect x h t‖ ≤
        ‖Δ h (waveOrbit H (waveExt H x) t)‖ + ‖Δ' h (waveOrbit H x t)‖ := fun h t => by
      have e := hdef h ⟨H.waveGroup.S t x, waveGroup_mem_domain H hx1 t⟩ (by
        rw [wave_waveGroup hx1 t]; exact waveGroup_mem_domain H (mem_domainSq.1 hx).2 t)
      change ‖R h (waveOrbit H (waveExt H x) t) - F.L h (R h (waveOrbit H x t))‖ ≤ _
      rw [waveOrbit_waveExt H (SetLike.mem_coe.1 hx), waveOrbit_of_mem H hx1, e]
      exact norm_add_le _ _
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [eventually_forall_norm_lt_of_tendsto hb1 hΔ0
      (isCompact_waveOrbit H hx T).2 (half_pos hε),
      eventually_forall_norm_lt_of_tendsto hb2 hΔ'0 (isCompact_waveOrbit H hx T).1
        (half_pos hε)] with h h1 h2 t ht
    rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg (norm_nonneg _)]
    have := hdefect h t
    linarith [h1 _ (mem_image_of_mem _ ht), h2 _ (mem_image_of_mem _ ht)]

/-! ### Complexification (real schemes for complex data: real and imaginary parts) -/

section Complexify

variable {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace ℝ (W' i)]
  [∀ i, CompleteSpace (W' i)] {H' : HilbertComplex ℝ c W'} {κ' : Type*}

/-- Over `ℝ`, the field `normedSpaceReal` need not be the normed space structure of the inner
product: the constructions below use the latter, the one of `Lₕ`, `ιₕ`, `πₕ`. -/
local instance (priority := high) instNormedSpaceRealOfInner (F : ApproxFEEC.{u} H' κ')
    (h : κ') : NormedSpace ℝ (F.X h) :=
  (F.innerProductSpace h).toNormedSpace

/-- The discrete generator `Lₕ ⊕ Lₕ` on `Xₕ ⊕₂ Xₕ`. -/
def complexifyL (F : ApproxFEEC.{u} H' κ') (h : κ') :
    WithLp 2 (F.X h × F.X h) →L[ℝ] WithLp 2 (F.X h × F.X h) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (F.X h) (F.X h)).symm.toContinuousLinearMap ∘L
    ((F.L h ∘L WithLp.fstL 2 ℝ (F.X h) (F.X h)).prod (F.L h ∘L WithLp.sndL 2 ℝ (F.X h) (F.X h)))

@[simp] theorem complexifyL_apply (F : ApproxFEEC.{u} H' κ') (h : κ') (a b : F.X h) :
    complexifyL F h (WithLp.toLp 2 (a, b)) = WithLp.toLp 2 (F.L h a, F.L h b) := rfl

/-- Run a real scheme on the real and imaginary parts: `X' = Xₕ ⊕₂ Xₕ`, `L' = Lₕ ⊕ Lₕ`,
`ι'(a, b) = ιₕ a + J ιₕ b`, `π' y = (πₕ y, -πₕ (J y))`, for an isometric complex structure `J`
(multiplication by `i`) with `πₕ J ιₕ = 0` and `ιₕ Xₕ ⊥ J ιₕ Xₕ` (real states and imaginary states
are orthogonal and not confused by `πₕ`). -/
def complexify (F : ApproxFEEC.{u} H' κ') (J : PiLp 2 W' →L[ℝ] PiLp 2 W')
    (hJJ : ∀ x, J (J x) = -x) (hJ : ∀ x, ‖J x‖ = ‖x‖)
    (hπJ : ∀ h b, F.proj h (J (F.incl h b)) = 0)
    (hJι : ∀ h a b, ⟪F.incl h a, J (F.incl h b)⟫_ℝ = 0) : ApproxFEEC.{u} H' κ' where
  K := F.K
  isClosed_K := F.isClosed_K
  l := F.l
  X h := WithLp 2 (F.X h × F.X h)
  normedAddCommGroup _ := inferInstance
  innerProductSpace _ := inferInstance
  completeSpace _ := inferInstance
  normedSpaceReal _ := inferInstance
  isScalarTower _ := IsScalarTower.left _
  L := complexifyL F
  skew h x y := by
    obtain ⟨⟨a, b⟩⟩ := x
    obtain ⟨⟨a', b'⟩⟩ := y
    simp only [complexifyL_apply, WithLp.prod_inner_apply, F.skew h]
    ring
  incl h := F.incl h ∘L WithLp.fstL 2 ℝ (F.X h) (F.X h) +
    J ∘L F.incl h ∘L WithLp.sndL 2 ℝ (F.X h) (F.X h)
  proj h := (WithLp.prodContinuousLinearEquiv 2 ℝ (F.X h) (F.X h)).symm.toContinuousLinearMap ∘L
    ((F.proj h).prod (-(F.proj h ∘L J)))
  proj_incl h x := by
    obtain ⟨⟨a, b⟩⟩ := x
    change WithLp.toLp 2 (F.proj h (F.incl h a + J (F.incl h b)),
      -F.proj h (J (F.incl h a + J (F.incl h b)))) = WithLp.toLp 2 (a, b)
    rw [_root_.map_add, _root_.map_add, _root_.map_add, F.proj_incl, hπJ, hJJ, _root_.map_neg,
      F.proj_incl, add_zero, hπJ, zero_add, neg_neg]
  bound := by
    refine ⟨2 * F.boundConst, fun h => ⟨?_, ?_⟩⟩
    · refine ContinuousLinearMap.opNorm_le_bound _ (by have := F.boundConst_nonneg; positivity)
        fun x => ?_
      obtain ⟨⟨a, b⟩⟩ := x
      simp only [ContinuousLinearMap.comp_apply, _root_.add_apply, WithLp.fstL_apply,
        WithLp.sndL_apply]
      have hn := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (a, b))
      have h1 := F.norm_incl_apply_le h a
      have h2 := F.norm_incl_apply_le h b
      have h0 := F.boundConst_nonneg
      have hsq : ‖F.incl h a + J (F.incl h b)‖ ^ 2 ≤
          (F.boundConst * ‖WithLp.toLp 2 (a, b)‖) ^ 2 := by
        rw [norm_add_sq_real, hJι, hJ, mul_pow, hn]
        simp only [WithLp.fst, WithLp.snd, mul_zero, add_zero]
        have := pow_le_pow_left₀ (norm_nonneg _) h1 2
        have := pow_le_pow_left₀ (norm_nonneg _) h2 2
        nlinarith
      change ‖F.incl h a + J (F.incl h b)‖ ≤ 2 * F.boundConst * ‖WithLp.toLp 2 (a, b)‖
      have hle := (pow_le_pow_iff_left₀ (norm_nonneg _)
        (mul_nonneg h0 (norm_nonneg (WithLp.toLp 2 (a, b)))) two_ne_zero).1 hsq
      have := mul_nonneg h0 (norm_nonneg (WithLp.toLp 2 (a, b)))
      linarith
    · refine ContinuousLinearMap.opNorm_le_bound _ (by have := F.boundConst_nonneg; positivity)
        fun y => ?_
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        _root_.neg_apply, ContinuousLinearEquiv.coe_coe,
        WithLp.prodContinuousLinearEquiv_symm_apply]
      have hn := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (F.proj h y, -F.proj h (J y)))
      simp only [WithLp.fst, WithLp.snd, norm_neg] at hn
      have h1 : ‖F.proj h y‖ ≤ F.boundConst * ‖y‖ := ((F.proj h).le_opNorm y).trans
        (mul_le_mul_of_nonneg_right (F.norm_proj_le h) (norm_nonneg _))
      have h2 : ‖F.proj h (J y)‖ ≤ F.boundConst * ‖y‖ := ((F.proj h).le_opNorm _).trans
        (by rw [hJ]; exact mul_le_mul_of_nonneg_right (F.norm_proj_le h) (norm_nonneg _))
      have h0 := F.boundConst_nonneg
      have := norm_nonneg (WithLp.toLp 2 (F.proj h y, -F.proj h (J y)))
      have := norm_nonneg (F.proj h y)
      have := norm_nonneg (F.proj h (J y))
      have := norm_nonneg y
      nlinarith

theorem complexify_incl (F : ApproxFEEC.{u} H' κ') (J : PiLp 2 W' →L[ℝ] PiLp 2 W') hJJ hJ hπJ
    hJι (h : κ') (a b : F.X h) :
    (F.complexify J hJJ hJ hπJ hJι).incl h (WithLp.toLp 2 (a, b)) =
      F.incl h a + J (F.incl h b) := rfl

/-- The complexified discrete solution is the real solution of the real part plus `J` times the
real solution of the imaginary part. -/
theorem complexify_sol (F : ApproxFEEC.{u} H' κ') (J : PiLp 2 W' →L[ℝ] PiLp 2 W') hJJ hJ hπJ
    hJι (h : κ') (a b : F.X h) (t : ℝ) :
    (F.complexify J hJJ hJ hπJ hJι).sol h (WithLp.toLp 2 (a, b)) t =
      F.sol h a t + J (F.sol h b t) := by
  set F' := F.complexify J hJJ hJ hπJ hJι
  set u : ℝ → F'.X h := fun s => WithLp.toLp 2 ((F.group h).S s a, (F.group h).S s b)
  have hu : ∀ s, HasDerivAt u (F'.L h (u s)) s := fun s => by
    have ha := C0Group.hasDerivAt_exp_ofReal_smul_apply (F.L h) a s
    have hb := C0Group.hasDerivAt_exp_ofReal_smul_apply (F.L h) b s
    have hp := ha.prodMk hb
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ (F.X h) (F.X h)).symm.hasFDerivAt.comp_hasDerivAt
      s hp
  have e := eq_ofBounded_of_hasDerivAt (F'.L h) (F'.skew h) hu t
  have e0 : u 0 = WithLp.toLp 2 (a, b) := by
    change WithLp.toLp 2 ((F.group h).S 0 a, (F.group h).S 0 b) = _
    rw [C0Group.S_zero_apply, C0Group.S_zero_apply]
  rw [e0] at e
  change F'.incl h ((C0Group.ofBounded (F'.L h)).S t (WithLp.toLp 2 (a, b))) = _
  rw [← e]
  rfl

end Complexify

end ApproxFEEC

/-! ### The approximating FEEC theorem -/

section Main

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxFEEC.{u} H κ)

open ApproxFEEC

/-- **2. Constraints propagate iff `K` is reducing**: `K` reduces `L` iff `e^{tL} K ⊆ K` for all
`t`. [QuennevilleBelair2015], Prop. 4.17, with necessity. -/
theorem approxFEEC_propagates_iff :
    H.wave.IsReducing F.K ↔ ∀ t, ∀ x ∈ F.K, H.waveGroup.S t x ∈ F.K :=
  (H.isReducing_iff_waveGroup_invariant F.K).trans C0Group.map_le_iff_forall

/-- **3a. Convergence on the core**, from the comparison initial values, uniformly on `[0, T]`. -/
theorem approxFEEC_converges_core (Z : F.Core) (T : ℝ) {x : PiLp 2 W} (hx : x ∈ Z.Data) :
    TendstoUniformlyOn (fun h t => F.sol h ((Z.cmp T).p x h 0) t)
      (fun t => H.waveGroup.S t x) F.l (Icc 0 T) := by
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

/-- **3b. Convergence on the closure of the core**: for `x` in the closure of the core, every
family of discrete initial values with `ιₕ vₕ → x` gives discrete solutions converging to
`e^{tL} x` uniformly on `[0, T]` (stability `‖v‖ ≤ C ‖ιₕ v‖`, unitarity, and density). -/
theorem approxFEEC_converges (Z : F.Core) (T : ℝ) {x : PiLp 2 W}
    (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h}
    (hv : Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x)) :
    TendstoUniformlyOn (fun h t => F.sol h (v h) t) (fun t => H.waveGroup.S t x) F.l
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
  have hc := Metric.tendstoUniformlyOn_iff.1 (approxFEEC_converges_core F Z T hy') _
    (show 0 < ε / 4 by positivity)
  filter_upwards [hc, (Metric.tendsto_nhds.1 (Z.tendsto_incl_p hT hy')) _ hε',
    Metric.tendsto_nhds.1 hv _ hε'] with h h1 h2 h3 t ht
  set w := (Z.cmp T).p y h 0
  rw [dist_eq_norm] at h2 h3 ⊢
  have a1 : ‖H.waveGroup.S t x - H.waveGroup.S t y‖ = ‖x - y‖ := by
    rw [← _root_.map_sub]; exact H.isIsometric_waveGroup t _
  have a2 : ‖H.waveGroup.S t y - F.sol h w t‖ < ε / 4 := by
    have := h1 t ht; rwa [dist_eq_norm] at this
  have a3 : ‖F.sol h w t - F.sol h (v h) t‖ ≤ C * ‖w - v h‖ :=
    (F.norm_sol_sub_sol_le h _ _ t).trans
      (mul_le_mul_of_nonneg_right (F.norm_incl_le h) (norm_nonneg _))
  have a4 : ‖w - v h‖ ≤ C * (‖F.incl h w - y‖ + ‖y - x‖ + ‖x - F.incl h (v h)‖) := by
    refine (F.norm_le_norm_incl h _).trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [_root_.map_sub]
    calc ‖F.incl h w - F.incl h (v h)‖ =
        ‖(F.incl h w - y) + (y - x) + (x - F.incl h (v h))‖ := by abel_nf
      _ ≤ _ := norm_add₃_le
  have e : H.waveGroup.S t x - F.sol h (v h) t = (H.waveGroup.S t x - H.waveGroup.S t y) +
      (H.waveGroup.S t y - F.sol h w t) + (F.sol h w t - F.sol h (v h) t) := by abel
  rw [e]
  refine norm_add₃_le.trans_lt ?_
  rw [a1]
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
  linarith [a3.trans (mul_le_mul_of_nonneg_left a4 hC), hxy]

/-- **3c. The rate: best approximation plus consistency** (plus the initial mismatch), for data in
a rate class and every discrete initial value `v`:
`‖e^{tL} x - ιₕ e^{tLₕ} v‖ ≤ (C + ‖ιₕ‖ C' t) hᵅ ‖x‖_c + ‖ιₕ‖ ‖pₕ(0) - v‖`.
Cf. [HolstStern2012], Thm 3.10 (elliptic analogue) -/
theorem approxFEEC_rate {T : ℝ} (R : F.RateClass T) {x : PiLp 2 W} (hx : x ∈ R.Data) (h : κ)
    (v : F.X h) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖H.waveGroup.S t x - F.sol h v t‖ ≤
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
  have h3 := F.norm_sol_sub_sol_le h (R.p x h 0) v t
  have e : H.waveGroup.S t x - F.sol h v t =
      (H.waveGroup.S t x - F.sol h (R.p x h 0) t) + (F.sol h (R.p x h 0) t - F.sol h v t) := by
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have : (R.C + ‖F.incl h‖ * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) =
      R.C * R.meshSize h ^ R.α * R.classNorm x +
        ‖F.incl h‖ * (R.C' * R.meshSize h ^ R.α * R.classNorm x * t) := by ring
  rw [this]
  linarith

/-- **4a. The constraint residual is bounded by the error** (reducing `K`, datum in `K`). -/
theorem approxFEEC_residual_le (hK : H.wave.IsReducing F.K) {x : PiLp 2 W} (hxK : x ∈ F.K)
    (h : κ) (v : F.X h) (t : ℝ) :
    infDist (F.sol h v t) (F.K : Set (PiLp 2 W)) ≤ ‖H.waveGroup.S t x - F.sol h v t‖ := by
  rw [norm_sub_rev, ← dist_eq_norm]
  exact infDist_le_dist_of_mem ((approxFEEC_propagates_iff F).1 hK t x hxK)

/-- **4a. Residual of a reducing constraint**: for `x ∈ K` in the closure of the core and every
convergent family of discrete initial values, the residual through `ιₕ` tends to `0` uniformly
on `[0, T]`. -/
theorem approxFEEC_residual (hK : H.wave.IsReducing F.K) (Z : F.Core) (T : ℝ) {x : PiLp 2 W}
    (hx : x ∈ Z.Data.topologicalClosure) (hxK : x ∈ F.K) {v : ∀ h, F.X h}
    (hv : Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x)) :
    TendstoUniformlyOn (fun h t => infDist (F.sol h (v h) t) (F.K : Set (PiLp 2 W)))
      (fun _ => 0) F.l (Icc 0 T) := by
  have hc := Metric.tendstoUniformlyOn_iff.1 (approxFEEC_converges F Z T hx hv)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hc ε hε] with h hh t ht
  have := hh t ht
  rw [dist_eq_norm] at this
  rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg infDist_nonneg]
  exact (approxFEEC_residual_le F hK hxK h (v h) t).trans_lt this

/-- **4b. Residual of a solution leaving a constraint** (per datum, any closed nonempty `Q`): if
`e^{tL} x ∉ Q`, the residuals `dist(ιₕ e^{tLₕ} vₕ, Q)` of every convergent family tend to
`dist(e^{tL} x, Q) > 0`. -/
theorem approxFEEC_residual_not_mem (Z : F.Core) {Q : Set (PiLp 2 W)} (hQ : IsClosed Q)
    (hQne : Q.Nonempty) {x : PiLp 2 W} (hx : x ∈ Z.Data.topologicalClosure) {v : ∀ h, F.X h}
    (hv : Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x)) {t : ℝ} (ht : 0 ≤ t)
    (hout : H.waveGroup.S t x ∉ Q) :
    0 < infDist (H.waveGroup.S t x) Q ∧
      Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l (𝓝 (infDist (H.waveGroup.S t x) Q)) :=
  ⟨(hQ.notMem_iff_infDist_pos hQne).1 hout, ((continuous_infDist_pt Q).tendsto _).comp
    ((approxFEEC_converges F Z t hx hv).tendsto_at ⟨ht, le_rfl⟩)⟩

/-- Forward invariance of `K` and `Kᗮ` makes `K` reducing (`e^{-tL} = (e^{tL})*`). -/
theorem approxFEEC_isReducing_of_forall_nonneg
    (h1 : ∀ x ∈ F.K, ∀ t, 0 ≤ t → H.waveGroup.S t x ∈ F.K)
    (h2 : ∀ x ∈ F.Kᗮ, ∀ t, 0 ≤ t → H.waveGroup.S t x ∈ F.Kᗮ) : H.wave.IsReducing F.K := by
  refine (approxFEEC_propagates_iff F).2 fun t x hx => ?_
  rcases le_total 0 t with ht | ht
  · exact h1 x hx t ht
  · rw [← Submodule.orthogonal_orthogonal F.K, Submodule.mem_orthogonal]
    intro u hu
    have hu' : H.waveGroup.S (-t) u ∈ F.Kᗮ := h2 u hu (-t) (by linarith)
    rw [← inner_conj_symm, H.isIsometric_waveGroup.inner_S_left,
      Submodule.inner_right_of_mem_orthogonal hx hu', _root_.map_zero]

/-- **4b. A non-reducing constraint is left** by a datum of `K` or of `Kᗮ`, at some
`t ∈ [0, T]`. -/
theorem approxFEEC_exists_not_mem (hK : ¬ H.wave.IsReducing F.K) {T : ℝ} (hT : 0 < T) :
    ∃ Q : Submodule 𝕜 (PiLp 2 W), (Q = F.K ∨ Q = F.Kᗮ) ∧ ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
      H.waveGroup.S t x ∉ Q := by
  by_contra hc
  push Not at hc
  exact hK (approxFEEC_isReducing_of_forall_nonneg F
    (forall_nonneg_of_forall_Icc H hT (P := F.K) (hc F.K (Or.inl rfl)))
    (forall_nonneg_of_forall_Icc H hT (P := F.Kᗮ) (hc F.Kᗮ (Or.inr rfl))))

/-- The discrete solution is differentiable: `(d/dt) ιₕ e^{tLₕ} v = ιₕ Lₕ e^{tLₕ} v`. -/
theorem ApproxFEEC.hasDerivAt_sol (h : κ) (v : F.X h) (t : ℝ) :
    HasDerivAt (F.sol h v) (F.incl h (F.L h ((F.group h).S t v))) t :=
  ((F.incl h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (C0Group.hasDerivAt_exp_ofReal_smul_apply (F.L h) v t)

/-- **Inexactness criterion**: if the discrete initial velocity `ιₕ Lₕ v` differs from `L x`, the
discrete solution from `v` differs from `e^{tL} x` at some time. -/
theorem ApproxFEEC.exists_sol_ne {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (h : κ) (v : F.X h)
    (hne : F.incl h (F.L h v) ≠ H.wave ⟨x, hx⟩) : ∃ t, F.sol h v t ≠ H.waveGroup.S t x := by
  by_contra hc
  push Not at hc
  have e : F.sol h v = fun s => H.waveGroup.S s x := funext hc
  have h1 := F.hasDerivAt_sol h v 0
  rw [e] at h1
  have h2 := h1.unique (hasDerivAt_waveGroup H hx 0)
  rw [C0Group.S_zero_apply, C0Group.S_zero_apply] at h2
  exact hne h2

/-- **4c. A non-reducing constraint is left by data of `D(L) ∩ K`, in one of the two time
directions**, when `D(L) ∩ K` is dense in `K` (continuous level; no grading, no hypothesis on
`Kᗮ`). -/
theorem approxFEEC_residual_not_isReducing_symm (hK : ¬ H.wave.IsReducing F.K)
    (hdense : ∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) {T : ℝ}
    (hT : 0 < T) :
    ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc (-T) T,
      H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) := by
  have hex : ∃ x ∈ H.wave.domain, x ∈ F.K ∧ ∃ t ∈ Icc (-T) T, H.waveGroup.S t x ∉ F.K := by
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    refine hK ((approxFEEC_propagates_iff F).2 fun t => waveGroup_mem_of_dense F.isClosed_K
      hdense fun x hx hxK => ?_)
    have hP := forall_of_forall_Icc_neg H hT (P := (H.wave.domain : Set (PiLp 2 W)) ∩ F.K)
      fun y hy s hs => ⟨waveGroup_mem_domain H hy.1 s, hc y hy.1 hy.2 s hs⟩
    exact (hP x ⟨hx, hxK⟩ t).2
  obtain ⟨x, hx, hxK, t, ht, hout⟩ := hex
  exact ⟨⟨x, hx⟩, hxK, t, ht, hout,
    (F.isClosed_K.notMem_iff_infDist_pos ⟨0, F.K.zero_mem⟩).1 hout⟩

/-- **4c. A non-reducing constraint on a graded complex is left by data of `D(L) ∩ K` forward in
time**: for a grading `p` and an `R`-invariant `K` with `D(L) ∩ K` dense in `K`, some
`ξ₀ ∈ D(L) ∩ K` leaves `K` at some `t ∈ [0, T]`, and (for `ξ₀` in the closure of the core) the
residuals through `ιₕ` of every convergent discretization tend to `dist(e^{tL} ξ₀, K) > 0`, so they
stay eventually above half of it. [QuennevilleBelair2015], Prop. 4.17 -/
theorem approxFEEC_residual_not_isReducing_of_grading (Z : F.Core) {p : ι → Bool}
    (hp : ∀ i j, c.Rel i j → p j ≠ p i) (hRK : ∀ x ∈ F.K, reversal 𝕜 p x ∈ F.K)
    (hdense : ∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K))
    (hK : ¬ H.wave.IsReducing F.K) {T : ℝ} (hT : 0 < T) :
    ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc 0 T,
      H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) ∧
      ((x : PiLp 2 W) ∈ Z.Data.topologicalClosure → ∀ v : ∀ h, F.X h,
        Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
        Tendsto (fun h => infDist (F.sol h (v h) t) (F.K : Set (PiLp 2 W))) F.l
          (𝓝 (infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)))) ∧
        ∀ᶠ h in F.l, infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) / 2 <
          infDist (F.sol h (v h) t) (F.K : Set (PiLp 2 W))) := by
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
  refine ⟨⟨x, hx⟩, hxK, t, ht, hout, hpos, fun hxc v hv => ?_⟩
  have hlim := (approxFEEC_residual_not_mem F Z F.isClosed_K ⟨0, F.K.zero_mem⟩ hxc hv ht.1
    hout).2
  exact ⟨hlim, (tendsto_order.1 hlim).1 _ (half_lt_self hpos)⟩

/-- The conclusion of the approximating FEEC theorem (instances state their headline as
`F.Verdict Z`, proved by `approxFEEC F Z`). -/
abbrev ApproxFEEC.Verdict (Z : F.Core) : Prop :=
    -- 1. well-posedness (`constrainedFEEC_wellPosed`)
    (∀ x ∈ H.wave.domain, ∀ T : ℝ,
      Evolution.IsClassicalSolution H.wave (Icc 0 T) 0 (fun t => H.waveGroup.S t x) ∧
      (∀ U, U 0 = x → Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U →
        EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
      (∀ U, U 0 = x → HodgeWave.IsWeakSolution H (Icc 0 T) 0 U →
        EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
      ∀ t, ‖H.waveGroup.S t x‖ = ‖x‖) ∧
    -- 2. propagation iff reducing
    (H.wave.IsReducing F.K ↔ ∀ t, ∀ x ∈ F.K, H.waveGroup.S t x ∈ F.K) ∧
    -- 3a. convergence on the core
    (∀ T : ℝ, ∀ x ∈ Z.Data, TendstoUniformlyOn
      (fun h t => F.sol h ((Z.cmp T).p x h 0) t) (fun t => H.waveGroup.S t x) F.l (Icc 0 T)) ∧
    -- 3b. convergence on the closure of the core, every convergent initial family; one exists
    (∀ T : ℝ, ∀ x ∈ Z.Data.topologicalClosure,
      Tendsto (fun h => F.incl h (F.proj h x)) F.l (𝓝 x) ∧
      ∀ v : ∀ h, F.X h, Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
        TendstoUniformlyOn (fun h t => F.sol h (v h) t) (fun t => H.waveGroup.S t x) F.l
          (Icc 0 T)) ∧
    -- 3c. rates: best approximation + consistency (+ initial mismatch)
    (∀ (T : ℝ) (R : F.RateClass T), ∀ x ∈ R.Data, ∀ h, ∀ v : F.X h, ∀ t ∈ Icc 0 T,
      ‖H.waveGroup.S t x - F.sol h v t‖ ≤
        (R.C + ‖F.incl h‖ * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) +
          ‖F.incl h‖ * ‖R.p x h 0 - v‖) ∧
    -- 4a. reducing constraint: residual through `ιₕ` bounded by the error, tends to `0`
    (H.wave.IsReducing F.K → ∀ x ∈ F.K,
      (∀ h (v : F.X h) t, infDist (F.sol h v t) (F.K : Set (PiLp 2 W)) ≤
        ‖H.waveGroup.S t x - F.sol h v t‖) ∧
      (x ∈ Z.Data.topologicalClosure → ∀ T : ℝ, ∀ v : ∀ h, F.X h,
        Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
        TendstoUniformlyOn (fun h t => infDist (F.sol h (v h) t) (F.K : Set (PiLp 2 W)))
          (fun _ => 0) F.l (Icc 0 T))) ∧
    -- 4b. per datum: a solution leaving `Q` has residual tending to `dist(e^{tL}x, Q) > 0`
    (∀ Q : Set (PiLp 2 W), IsClosed Q → Q.Nonempty → ∀ x ∈ Z.Data.topologicalClosure,
      ∀ v : ∀ h, F.X h, Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) → ∀ t, 0 ≤ t →
      H.waveGroup.S t x ∉ Q → 0 < infDist (H.waveGroup.S t x) Q ∧
        Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l
          (𝓝 (infDist (H.waveGroup.S t x) Q))) ∧
    -- 4b. a non-reducing constraint is left by data of `K` or `Kᗮ`; with a dense core, the
    -- residuals of every convergent discretization of that datum have a positive limit
    (¬ H.wave.IsReducing F.K → ∀ T : ℝ, 0 < T →
      ∃ Q : Submodule 𝕜 (PiLp 2 W), (Q = F.K ∨ Q = F.Kᗮ) ∧ ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
        H.waveGroup.S t x ∉ Q ∧ 0 < infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)) ∧
        (Dense (Z.Data : Set (PiLp 2 W)) → ∀ v : ∀ h, F.X h,
          Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
          Tendsto (fun h => infDist (F.sol h (v h) t) (Q : Set (PiLp 2 W))) F.l
            (𝓝 (infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)))))) ∧
    -- 4c. with `D(L) ∩ K` dense in `K`: a datum of `D(L) ∩ K` leaves `K` for some `t ∈ [-T, T]`
    (¬ H.wave.IsReducing F.K →
      (∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) → ∀ T : ℝ, 0 < T →
      ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc (-T) T,
        H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W))) ∧
    -- 4c. graded complex, `R`-invariant `K`, `D(L) ∩ K` dense in `K`: a datum of `D(L) ∩ K`
    -- leaves `K` forward in time, with residuals tending to a positive limit
    (∀ p : ι → Bool, (∀ i j, c.Rel i j → p j ≠ p i) → (∀ x ∈ F.K, reversal 𝕜 p x ∈ F.K) →
      (∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) →
      ¬ H.wave.IsReducing F.K → ∀ T : ℝ, 0 < T →
      ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc 0 T,
        H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) ∧
        ((x : PiLp 2 W) ∈ Z.Data.topologicalClosure → ∀ v : ∀ h, F.X h,
          Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
          Tendsto (fun h => infDist (F.sol h (v h) t) (F.K : Set (PiLp 2 W))) F.l
            (𝓝 (infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)))) ∧
          ∀ᶠ h in F.l, infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) / 2 <
            infDist (F.sol h (v h) t) (F.K : Set (PiLp 2 W))))

/-- **The approximating FEEC theorem.** For an approximating FEEC discretization `F` (discrete
Hilbert spaces with their own inner products, skew bounded generators, uniformly bounded reading
maps `ιₕ` with uniformly bounded left inverses `πₕ`; variational crimes allowed) and an
orbit-consistent core `Z`:

1. (**well-posedness**, Stone) for `ξ₀ ∈ D(L)`, `t ↦ e^{tL} ξ₀` is a classical solution, the only
   strong and the only weak solution, and conserves energy;
2. (**propagation**) `K` reduces `L` iff `e^{tL} K ⊆ K` for all `t`;
3. (**convergence**) on the core, from the comparison initial values; on its closure, for every
   family `vₕ` with `ιₕ vₕ → ξ₀` (and `vₕ = πₕ ξ₀` is one), uniformly on `[0, T]`; for data in a
   rate class, `‖e^{tL} ξ₀ - ιₕ e^{tLₕ} v‖ ≤ (C + ‖ιₕ‖ C' t) hᵅ ‖ξ₀‖_c + ‖ιₕ‖ ‖pₕ(0) - v‖`
   (best approximation plus consistency);
4. (**constraint residual**, measured through `ιₕ`) if `K` reduces `L`, it is bounded by the error
   and tends to `0`; a solution leaving a closed nonempty `Q` has residuals with the positive limit
   `dist(e^{tL} ξ₀, Q)`; a non-reducing `K` is left by data of `K` or `Kᗮ`, and with a dense core
   the residuals of every convergent discretization of that datum have a positive limit; if
   `D(L) ∩ K` is dense in `K`, a datum of `D(L) ∩ K` leaves `K` for some `t ∈ [-T, T]`; on a graded
   complex with `R`-invariant `K`, a datum of `D(L) ∩ K` leaves `K` forward in time and its
   residuals tend to a positive limit.

Cf. [HolstStern2012], Thm 3.9, Thm 3.10 (elliptic analogues); [QuennevilleBelair2015], Thms 4.6,
4.7, Prop. 4.17 -/
theorem approxFEEC (Z : F.Core) : F.Verdict Z := by
  refine ⟨fun _ hx T => constrainedFEEC_wellPosed hx T, approxFEEC_propagates_iff F,
    fun T _ hx => approxFEEC_converges_core F Z T hx,
    fun T _ hx => ⟨tendsto_incl_proj F Z hx, fun _ hv => approxFEEC_converges F Z T hx hv⟩,
    fun _ R _ hx h v _ ht => approxFEEC_rate F R hx h v ht,
    fun hK _ hxK => ⟨fun h v t => approxFEEC_residual_le F hK hxK h v t,
      fun hx T _ hv => approxFEEC_residual F hK Z T hx hxK hv⟩,
    fun _ hQ hQne _ hx _ hv _ ht hout => approxFEEC_residual_not_mem F Z hQ hQne hx hv ht hout,
    fun hK T hT => ?_,
    fun hK hdense _ hT => approxFEEC_residual_not_isReducing_symm F hK hdense hT,
    fun _ hp hRK hdense hK _ hT =>
      approxFEEC_residual_not_isReducing_of_grading F Z hp hRK hdense hK hT⟩
  obtain ⟨Q, hQK, x, hx, t, ht, hout⟩ := approxFEEC_exists_not_mem F hK hT
  have hQc : IsClosed (Q : Set (PiLp 2 W)) := by
    rcases hQK with rfl | rfl
    exacts [F.isClosed_K, Submodule.isClosed_orthogonal _]
  refine ⟨Q, hQK, x, hx, t, ht, hout, (hQc.notMem_iff_infDist_pos ⟨0, Q.zero_mem⟩).1 hout,
    fun hd _ hv => ?_⟩
  have hxc : x ∈ Z.Data.topologicalClosure := by
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, hd.closure_eq]; trivial
  exact (approxFEEC_residual_not_mem F Z hQc ⟨0, Q.zero_mem⟩ hxc hv ht.1 hout).2

end Main

end Feec.HilbertComplex
