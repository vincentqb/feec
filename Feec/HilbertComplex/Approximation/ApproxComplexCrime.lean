module

public import Feec.HilbertComplex.Approximation.ApproxComplex
public import Feec.HilbertComplex.Approximation.ApproxOrthogonal
public import Feec.HilbertComplex.Approximation.RitzResolvent

/-!
# Approximating families of discrete differential spaces with a cochain defect

The complex-level front end `Feec.HilbertComplex.ApproxFEEC.ofComplex` requires the reading maps
`iₕ : Vₕ → W` to be exact cochain maps (`𝐝 iₕ = iₕ 𝐝ₕ`). This file removes that hypothesis: the
discrete differential `𝐝ₕ` is independent of `𝐝`, and its failure to commute with the reading map
enters, weakly, as a **cochain defect**, next to the inner-product defect of [HolstStern2012],
§3. The result is again an approximating FEEC discretization (`Feec.HilbertComplex.ApproxFEEC`):
the hypotheses of the Trotter–Kato bridge are derived from the inner-product defect and from
pointwise convergence `iₕ Rₕ y → y` of the modified elliptic projection on the admissible states,
which is what the field `consistent` amounts to (`consistent_iff_tendsto_incl_load`).

## Setting

An **approximating family of discrete differential spaces** (`ApproxComplexCrime.Family`) has,
for each `h`, a finite-dimensional inner product space `Xₕ` (its own inner product), a
**differential** `𝐝ₕ : Xₕ → Xₕ` with `𝐝ₕ 𝐝ₕ = 0` (a total discrete complex: no grading is needed
for the convergence theory), uniformly bounded reading maps `iₕ : Xₕ → W` and left inverses `πₕ`.
Nothing relates `𝐝ₕ` to `𝐝`, and `iₕ Xₕ` need not lie in `D(𝐝)`. The discrete generator is the
Hodge wave operator `Lₕ = 𝐝ₕ - 𝐝ₕ*` (`ApproxComplexCrime.Family.L`), `Jₕ = iₕ* iₕ`.

The **cochain defect** of `y ∈ D(L)` is `κₕ(y) = 𝐝ₕ* iₕ* y - iₕ* 𝐝* y ∈ Xₕ`
(`ApproxComplexCrime.Family.cochainDefect`): `⟪κₕ(y), v⟫ = ⟪y, iₕ 𝐝ₕ v⟫ - ⟪𝐝* y, iₕ v⟫`, the
pairing of `y` with `(iₕ 𝐝ₕ - 𝐝 iₕ) v` when `iₕ v ∈ D(𝐝)` (`inner_cochainDefect_of_mem`). It
vanishes for cochain maps (`cochainDefect_eq_zero`) and is measured in the dual discrete graph
norm, `|⟪κₕ(y), v⟫| ≤ δ (‖v‖ + ‖𝐝ₕ v‖)`.

The comparison is the **exact-load modified elliptic projection** `Rₕ y = (1 - Lₕ)⁻¹ iₕ* (1 - L) y`
of `y ∈ D(L)` (`load` applied to `y - L y`). It needs `L y`, not only `(y, 𝐝 y)`: with a cochain
defect the load of `ApproxComplex.Family.ellProj` (defined on `Γ(𝐝)`) differs from `iₕ*(1 - L)`
on `D(L)` by `κₕ`, which is not a bounded function of `(y, 𝐝 y)`. So the comparison is the
**load Ritz projection** `ApproxFEEC.loadRitz` (a `DissipFEEC.Ritz` of the resolvent lift
`ℓ = 1 - L`, `DissipFEEC.Lift.resolvent`, with `Δₕ = Bₕ - iₕ* (1 - L)⁻¹`, `Δₕ' = -Δₕ`), restricted
to the core (`ApproxFEEC.crimeCmp`, `ApproxFEEC.ofComplexCrimeCore`), and the hypotheses of the
core (approximation, vanishing defects, uniformly on `[0, T]`) are derived on the admissible
states.

**The approximating family** (`ApproxComplexCrime`) adds a constraint `K`, a filter, a set
`A ⊆ D(L)` of admissible states and a core `Z ≤ D(L²)` whose forward orbits (and those of `L Z`)
stay in `A`, and two hypotheses: the inner-product defect in the graph norm of `𝐝ₕ` tends to `0`
(`ApproxComplexCrime.Family.graphDefect`, the norm of `1 - Jₕ` on the graph space of `𝐝ₕ`, at most
`‖1 - Jₕ‖`; with the family, the constraint and the filter, the data
`ApproxComplexCrime.HeatFamily` of the heat theorem with crimes, which it extends), and **consistent
approximation** on `A` (`ApproxComplexCrime.consistent`): approximants `wₕ` with
`‖y - iₕ wₕ‖ → 0` whose discrete residual `⟪(1 - Lₕ) wₕ, v⟫ - ⟪(1 - L) y, iₕ v⟫` tends to `0` in
the dual discrete graph norm (a "best approximation plus consistency" condition in the spirit of
[HolstStern2012], §3.3). Since `Rₕ y` is itself an approximant with residual `0`, this is
equivalent to `iₕ Rₕ y → y` (`ApproxComplexCrime.consistent_iff_tendsto_incl_load`): the field
is the convergence hypothesis on the projection, and the content is in the ways to check it.
The residual splits exactly (`inner_residual_eq`) into the inner-product defect, the
graph-norm approximation error `‖y - iₕ w‖ + ‖𝐝 y - iₕ 𝐝ₕ w‖` and the cochain defect, so graph-norm
approximation, a cochain defect tending to `0` and `‖1 - Jₕ‖_{Vₕ} → 0` give it
(`consistent_of_cochainDefect`, `ApproxComplexCrime.ofCochainDefect`). It also holds with a
Galerkin projection as approximant (residual `0`): `ApproxComplexCrime.ofGalerkinCore` re-reads a
discretization whose generator is `𝐝ₕ - 𝐝ₕ*`, with `‖1 - Jₕ‖_{Vₕ} → 0` (orthogonal reading maps
are the case `Jₕ = 1`), and a core whose comparison satisfies the Galerkin identity
`(1 - Lₕ) pₕ(t) = iₕ* (1 - L) e^{tL} x` as a complex-level family; the cochain defect is then
absorbed by the Galerkin identity and not computed. This bridge takes the existing core (its
convergence is not re-proved) and adds the complex-level structure.

## Main results

* `ApproxComplexCrime.Family.norm_sub_load_add_le`, `norm_sub_incl_load_le`: **the Strang lemma**,
  `‖w - Rₕ y‖ + ‖𝐝ₕ (w - Rₕ y)‖ ≤ 8 ε` and `‖y - iₕ Rₕ y‖ ≤ ‖y - iₕ w‖ + 8 C ε` for an approximant
  `w` of residual `≤ ε`.
* `ApproxComplexCrime.Family.inner_residual_eq`, `norm_residual_le`: the residual is at most
  `‖(1 - Jₕ) w‖ + ‖(1 - Jₕ) 𝐝ₕ w‖ + C (‖y - iₕ w‖ + ‖𝐝 y - iₕ 𝐝ₕ w‖) + δ`, `δ` the cochain
  defect, and `‖(1 - Jₕ) w‖ + ‖(1 - Jₕ) 𝐝ₕ w‖` is at most `‖1 - Jₕ‖ (‖w‖ + ‖𝐝ₕ w‖)` and at most
  `‖1 - Jₕ‖_{Vₕ} (‖w‖ + 2 ‖𝐝ₕ w‖)` (`norm_one_sub_J_add_le_opNorm`, `norm_one_sub_J_add_le`).
* `ApproxComplexCrime.Family.graphDefect`: **the inner-product defect in the graph norm**
  `‖1 - Jₕ‖_{Vₕ}`, the norm of `1 - Jₕ` from the graph space `Vₕ` of `𝐝ₕ` to `Xₕ`
  (`ContinuousLinearMap.graphOpNorm`, as for the discrete complexes of `ofComplex`,
  `ApproxComplex.Family.graphDefect`), so
  `‖(1 - Jₕ) v‖ ≤ ‖1 - Jₕ‖_{Vₕ} (‖v‖ + ‖𝐝ₕ v‖)` (`norm_one_sub_J_apply_le`); at most `‖1 - Jₕ‖`
  (`graphDefect_le`), and at most `√2 δ` if `‖(1 - Jₕ) v‖ ≤ δ (‖v‖ + ‖𝐝ₕ v‖)` for every `v`
  (`graphDefect_le_of_forall`). It is the defect hypothesis of the heat and wave families
  (`HeatFamily`, `ApproxComplexCrime`): `Bₕ` is bounded in the graph norm,
  `‖Bₕ z‖ + ‖𝐝ₕ Bₕ z‖ ≤ 8 C ‖z‖` (`norm_load_add_le`).
* `ApproxComplexCrime.Family.load_defect`, `norm_load_sub_adjoint_le`: **the defect identity**
  `Rₕ (L y) - Lₕ Rₕ y = Δₕ (L y) - Δₕ y`, `Δₕ z = Rₕ z - iₕ* z`, and
  `‖Δₕ z‖ ≤ ‖(1 - Jₕ) Rₕ z‖ + C ‖z - iₕ Rₕ z‖`.
* `ApproxFEEC.ofComplexCrime`, `ApproxFEEC.ofComplexCrimeCore`, `approxFEEC_ofComplexCrime`: the
  approximating FEEC discretization (`Xₕ`, `Lₕ = 𝐝ₕ - 𝐝ₕ*`, `iₕ`, `πₕ`) with the core `Z`
  (comparison `Rₕ e^{tL} x`), the four conclusions of `approxFEEC`, the Strang and defect bounds,
  and discrete constraints (an `Lₕ`-invariant subspace of `Xₕ` is preserved exactly,
  `mem_of_invariant`; if it is read inside `K` the residual is `0`).
* **The cochain special case**: `ApproxComplex.toCrime` (zero cochain defect,
  `ApproxComplex.Family.cochainDefect_toCrimeFamily`) has `ofComplexCrime F.toCrime = ofComplex F`
  (`ApproxFEEC.ofComplexCrime_toCrime`, by `rfl`) and the same comparison on `D(L²)`
  (`ApproxFEEC.ofComplexCrimeCore_toCrime_p`); in particular a conforming discretization is the
  case of zero defects (`ConstrainedFEEC.toCrime`, `toCrime_J`, `toCrime_cochainDefect`,
  `toCrime_sol`), the embedding through which the crown contains the FEEC theorem for these
  families (`ApproxComplexCrime.feec`, `Feec.HilbertComplex.Approximation.Crown`).
* **Galerkin cores** (`ApproxComplexCrime.ofGalerkinCore`): the discrete solutions are those of
  the given discretization (`ofComplexCrime_ofGalerkinCore_sol`), the comparison is the given one
  (`galerkin_p_eq`, `galerkin_p'_eq` for the derivative), and `iₕ iₕ* → 1` on the closure of the
  core (`tendsto_incl_adjoint_galerkin`, from the defect in the graph norm and the uniform bound,
  `ContinuousLinearMap.tendsto_apply_of_mem_closure`). Complexification of a
  differential and of Galerkin identities: `ApproxFEEC.complexifyD`,
  `ApproxFEEC.complexify_L_eq_diffWave`, `ApproxFEEC.complexify_galerkin`.
* **Rates from complex-level estimates** (`ApproxComplexCrime.rateClass`, the rate class of the
  load Ritz projection, `DissipFEEC.Ritz.orbitRateClass`): approximants along the
  trajectory with approximation, inner-product defect `‖(1 - Jₕ) w‖` and residual `O(m(h)ᵅ)` give
  a `DissipFEEC.RateClass` with `C = (1 + 8 C_ι) Cₐ`,
  `C' = 2 (1 + 8 (1 + C_ι²) + C_ι (1 + 8 C_ι)) Cₐ`, hence
  `‖e^{tL} x - iₕ e^{tLₕ} Rₕ x‖ ≤ (C + C_ι C' t) m(h)ᵅ ‖x‖_c` (`error_le_of_rateClass`);
  `ApproxComplexCrime.rateClass_of_split` gives a rate class at order `min(α, β, γ)` from
  graph-norm best approximation `O(mᵅ)`, inner-product defect `O(m^β)` at the approximants
  (`‖(1 - Jₕ) w‖ + ‖(1 - Jₕ) 𝐝ₕ w‖`) and cochain defect `O(m^γ)` (`0 ≤ m ≤ 1`), with
  `Cₐ' = (1 + C_ι) Cₐ + C_β + C_γ` in place of `Cₐ` (through `Family.rateData_of_split` and
  `add_rpow_le_rpow_min`), and `error_le_of_split`; `galerkinRateClass` for Galerkin cores
  (approximation and inner-product defect along the comparison; `galerkinRateClass_of_isOrthogonal`
  for orthogonal reading maps);
  `ConstrainedFEEC.RateClass.toCrimeRate`: the conforming rate classes give rate classes of
  `ofComplex` (factor `C + C_ι C' t`, `ConstrainedFEEC.RateClass.norm_sub_ofComplex_le`).

The static and heat FEEC theorems for these families (the mixed Hodge Laplacian with the load
`iₕ* f`, and the heat equation with the heat Ritz projection) are in
`Feec.HilbertComplex.Approximation.StaticCrime` and `Feec.HilbertComplex.Approximation.HeatCrime`.

Non-vacuity, with a nonzero cochain defect and a non-cochain isometric reading map:
`Feec.HilbertComplex.ApproxComplexCrime.shifted_nonvacuous`
(`Feec.HilbertComplex.Approximation.ApproxComplexCrimeWitness`); with distinct orders in
`rateClass_of_split` (inner-product defect `O(h)`, cochain defect and graph-norm error `O(h²)`,
rate class of order `1`): `Feec.HilbertComplex.ApproxComplexCrime.mixed_nonvacuous`. Instances: the
scheme (6.5) of [QuennevilleBelair2015] with both boundary conditions
(`Feec.Instances.EinsteinBianchiFEMComplex`) and the Maxwell discretizations
(`Feec.Instances.Maxwell.cubePMC_ofComplex`).

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (§3.3, Thm 3.10)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.6 ((4.11)), §6.2 ((6.4))
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §3.4 (Trotter–Kato)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

open _root_.Feec.HodgeWave

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Uniform convergence on compact sets, from pointwise convergence on the set -/

/-- **Pointwise convergence to `0` on a compact set is uniform there** for a family of functions
with a uniform Lipschitz-type bound (the centres of a finite cover by small balls lie in the
set). -/
theorem eventually_forall_lt_of_tendsto_on {κ F : Type*} [SeminormedAddCommGroup F]
    {l : Filter κ} {f : κ → F → ℝ} {M : ℝ} (hf : ∀ h ζ ζ', f h ζ ≤ f h ζ' + M * ‖ζ - ζ'‖)
    {S : Set F} (hlim : ∀ ζ ∈ S, Tendsto (fun h => f h ζ) l (𝓝 0)) (hS : IsCompact S) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ h in l, ∀ ζ ∈ S, f h ζ < ε := by
  set M' := max M 0
  have hM' : 0 ≤ M' := le_max_right _ _
  set δ := ε / (2 * (M' + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨t, hts, htf, hcov⟩ := hS.finite_cover_balls hδ
  have hev : ∀ᶠ h in l, ∀ z ∈ t, f h z < ε / 2 :=
    (htf.eventually_all).2 fun z hz => (tendsto_order.1 (hlim z (hts hz))).2 _ (half_pos hε)
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

/-! ### Differential spaces -/

section DiffSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
  (D : X →L[𝕜] X)

/-- The **Hodge wave operator** `D - D*` of an operator `D` (a differential when `D D = 0`). -/
def diffWave : X →L[𝕜] X := D - D.adjoint

theorem diffWave_apply (v : X) : diffWave D v = D v - D.adjoint v := rfl

theorem inner_diffWave (v w : X) : ⟪diffWave D v, w⟫_𝕜 = ⟪D v, w⟫_𝕜 - ⟪v, D w⟫_𝕜 := by
  rw [diffWave_apply, inner_sub_left, ContinuousLinearMap.adjoint_inner_left]

theorem diffWave_skew (v w : X) : ⟪diffWave D v, w⟫_𝕜 = -⟪v, diffWave D w⟫_𝕜 := by
  rw [inner_diffWave, diffWave_apply, inner_sub_right, ContinuousLinearMap.adjoint_inner_right]
  ring

theorem re_inner_sub_diffWave_self (v : X) :
    RCLike.re ⟪v - diffWave D v, v⟫_𝕜 = ‖v‖ ^ 2 := by
  have hs : RCLike.re ⟪diffWave D v, v⟫_𝕜 = 0 := by
    have h := diffWave_skew D v v
    have : RCLike.re ⟪diffWave D v, v⟫_𝕜 = - RCLike.re ⟪diffWave D v, v⟫_𝕜 := by
      conv_rhs => rw [h, _root_.map_neg, ← inner_conj_symm, RCLike.conj_re]
      simp
    linarith
  rw [inner_sub_left, _root_.map_sub, hs, sub_zero, inner_self_eq_norm_sq]

/-- `‖v‖ ≤ ‖v - (D - D*) v‖` (skewness). -/
theorem norm_le_norm_sub_diffWave (v : X) : ‖v‖ ≤ ‖v - diffWave D v‖ := by
  have h := re_inner_sub_diffWave_self D v
  have h1 : RCLike.re ⟪v - diffWave D v, v⟫_𝕜 ≤ ‖v - diffWave D v‖ * ‖v‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  rw [h] at h1
  rcases (norm_nonneg v).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

theorem injective_one_sub_diffWave :
    Function.Injective ((1 - diffWave D : X →L[𝕜] X) : X →ₗ[𝕜] X) := fun a b hab => by
  have h0 : (a - b) - diffWave D (a - b) = 0 := by
    have : ((1 - diffWave D : X →L[𝕜] X)) (a - b) = 0 := by
      rw [_root_.map_sub]; exact sub_eq_zero.2 hab
    simpa using this
  have h1 := norm_le_norm_sub_diffWave D (a - b)
  rw [h0, norm_zero] at h1
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)

variable [FiniteDimensional 𝕜 X]

/-- `1 - (D - D*)` as an isomorphism (finite dimension: it is injective). -/
def diffResolvent : X ≃L[𝕜] X :=
  (LinearEquiv.ofInjectiveEndo _ (injective_one_sub_diffWave D)).toContinuousLinearEquiv

theorem diffResolvent_apply (v : X) : diffResolvent D v = v - diffWave D v := rfl

/-- `‖(1 - (D - D*))⁻¹ v‖ ≤ ‖v‖`. -/
theorem norm_diffResolvent_symm_apply_le (v : X) : ‖(diffResolvent D).symm v‖ ≤ ‖v‖ := by
  have h := norm_le_norm_sub_diffWave D ((diffResolvent D).symm v)
  rwa [← diffResolvent_apply, ContinuousLinearEquiv.apply_symm_apply] at h

omit [FiniteDimensional 𝕜 X] in
/-- **Coercivity of `1 - (D - D*)` in the discrete graph norm** of a differential (`D D = 0`): if
`|⟪r - L r, v⟫| ≤ M (‖v‖ + ‖D v‖)` for every `v`, then `‖r‖ + ‖D r‖ ≤ 8 M` (test with
`v = r - D r`). -/
theorem norm_add_norm_le_of_inner_diff (hDD : ∀ v, D (D v) = 0) (r : X) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ v, ‖⟪r - diffWave D r, v⟫_𝕜‖ ≤ M * (‖v‖ + ‖D v‖)) :
    ‖r‖ + ‖D r‖ ≤ 8 * M := by
  have hDv : D (r - D r) = D r := by rw [_root_.map_sub, hDD, sub_zero]
  have hv := h (r - D r)
  rw [hDv] at hv
  have e1 : r - diffWave D r = (r - D r) + D.adjoint r := by rw [diffWave_apply]; abel
  have e2 : ⟪D.adjoint r, r - D r⟫_𝕜 = ⟪r, D r⟫_𝕜 := by
    rw [ContinuousLinearMap.adjoint_inner_left, hDv]
  have hre : RCLike.re ⟪r - diffWave D r, r - D r⟫_𝕜 =
      ‖r‖ ^ 2 + ‖D r‖ ^ 2 - RCLike.re ⟪r, D r⟫_𝕜 := by
    rw [e1, inner_add_left, _root_.map_add, e2, inner_self_eq_norm_sq, @norm_sub_sq 𝕜]
    ring
  have hle : RCLike.re ⟪r - diffWave D r, r - D r⟫_𝕜 ≤ ‖⟪r - diffWave D r, r - D r⟫_𝕜‖ :=
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

/-- **Invariant subspaces of a skew generator are preserved by its group**: if `L` is skew on a
finite-dimensional `X` and `L K ⊆ K`, then `e^{tL} K ⊆ K` for all `t` (the orbit of the
restriction solves `u' = L u`, and the solution is unique). -/
theorem mem_of_invariant [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] (L : X →L[𝕜] X)
    (hL : ∀ x y, ⟪L x, y⟫_𝕜 = -⟪x, L y⟫_𝕜) (K : Submodule 𝕜 X) (hK : ∀ v ∈ K, L v ∈ K)
    {v : X} (hv : v ∈ K) (t : ℝ) : (C0Group.ofBounded L).S t v ∈ K := by
  have : CompleteSpace K := FiniteDimensional.complete 𝕜 K
  set LK : K →L[𝕜] K := LinearMap.toContinuousLinearMap (L.toLinearMap.restrict hK)
  set u : ℝ → X := fun s => (K.subtypeL ((C0Group.ofBounded LK).S s ⟨v, hv⟩))
  have hu : ∀ s, HasDerivAt u (L (u s)) s := fun s => by
    have hd := ContinuousLinearMap.hasDerivAt_exp_ofReal_smul_apply LK ⟨v, hv⟩ s
    exact (K.subtypeL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hd
  have e := eq_ofBounded_of_hasDerivAt L hL hu t
  have e0 : u 0 = v := by simp only [u, C0Group.S_zero_apply]; rfl
  rw [e0] at e
  rw [← e]
  exact ((C0Group.ofBounded LK).S t ⟨v, hv⟩).2

end DiffSpace

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι}
  {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
  [∀ i, CompleteSpace (W i)]

/-! ### `D(L)`: the two halves of the wave operator -/

section WaveDomain

variable (H : HilbertComplex 𝕜 c W)

/-- `L y = 𝐝 y - 𝐝* y` on `D(L)`. -/
theorem wave_eq_sub (y : H.wave.domain) :
    H.wave y = H.totalD ⟨y, y.2.1⟩ - H.dual.totalD ⟨y, y.2.2⟩ := rfl

/-- `‖L y‖² = ‖𝐝 y‖² + ‖𝐝* y‖²` on `D(L)` (`𝐝 𝐝 = 0`). -/
theorem norm_wave_sq' (y : H.wave.domain) :
    ‖H.wave y‖ ^ 2 = ‖H.totalD ⟨y, y.2.1⟩‖ ^ 2 + ‖H.dual.totalD ⟨y, y.2.2⟩‖ ^ 2 := by
  have h0 : ⟪H.totalD ⟨y, y.2.1⟩, H.dual.totalD ⟨y, y.2.2⟩⟫_𝕜 = 0 := by
    rw [← H.inner_totalD_dual ⟨_, H.totalD_mapsTo ⟨y, y.2.1⟩⟩ ⟨y, y.2.2⟩,
      H.totalD_comp_totalD, inner_zero_left]
  rw [wave_eq_sub, @norm_sub_sq 𝕜, h0, _root_.map_zero, mul_zero, sub_zero]

/-- `‖𝐝 y‖ ≤ ‖L y‖` on `D(L)`. -/
theorem norm_totalD_le_norm_wave (y : H.wave.domain) : ‖H.totalD ⟨y, y.2.1⟩‖ ≤ ‖H.wave y‖ := by
  have h := norm_wave_sq' H y
  nlinarith [norm_nonneg (H.totalD ⟨y, y.2.1⟩), norm_nonneg (H.wave y),
    norm_nonneg (H.dual.totalD ⟨y, y.2.2⟩)]

end WaveDomain

/-! ### Approximating families of discrete differential spaces -/

/-- A **family of discrete differential spaces with reading maps** for the Hilbert complex `H`:
for each `h`, a finite-dimensional inner product space `Xₕ` with its own inner product, a
differential `𝐝ₕ` (`𝐝ₕ 𝐝ₕ = 0`), bounded reading maps `iₕ : Xₕ → W` with left inverses `πₕ`
(`πₕ iₕ = 1`), uniformly bounded. `𝐝ₕ` is not related to `𝐝`: `iₕ` need not be a cochain map,
nor isometric, nor map into `D(𝐝)`. -/
structure ApproxComplexCrime.Family (H : HilbertComplex 𝕜 c W) (κ : Type*) where
  /-- the discrete spaces -/
  X : κ → Type u
  [normedAddCommGroup : ∀ h, NormedAddCommGroup (X h)]
  [innerProductSpace : ∀ h, InnerProductSpace 𝕜 (X h)]
  [completeSpace : ∀ h, CompleteSpace (X h)]
  [finiteDimensional : ∀ h, FiniteDimensional 𝕜 (X h)]
  [normedSpaceReal : ∀ h, NormedSpace ℝ (X h)]
  [isScalarTower : ∀ h, IsScalarTower ℝ 𝕜 (X h)]
  /-- the discrete differentials -/
  D : ∀ h, X h →L[𝕜] X h
  D_D : ∀ h v, D h (D h v) = 0
  /-- the reading maps `iₕ` -/
  incl : ∀ h, X h →L[𝕜] PiLp 2 W
  /-- the left inverses `πₕ` -/
  proj : ∀ h, PiLp 2 W →L[𝕜] X h
  proj_incl : ∀ h v, proj h (incl h v) = v
  bound : ∃ C, ∀ h, ‖incl h‖ ≤ C ∧ ‖proj h‖ ≤ C

attribute [instance] ApproxComplexCrime.Family.normedAddCommGroup
  ApproxComplexCrime.Family.innerProductSpace ApproxComplexCrime.Family.completeSpace
  ApproxComplexCrime.Family.finiteDimensional ApproxComplexCrime.Family.normedSpaceReal
  ApproxComplexCrime.Family.isScalarTower

namespace ApproxComplexCrime.Family

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (S : ApproxComplexCrime.Family.{u} H κ)

/-- A nonnegative uniform bound of `‖iₕ‖`, `‖πₕ‖`. -/
def boundConst : ℝ := max S.bound.choose 0

theorem boundConst_nonneg : 0 ≤ S.boundConst := le_max_right _ _

theorem norm_incl_le (h : κ) : ‖S.incl h‖ ≤ S.boundConst :=
  (S.bound.choose_spec h).1.trans (le_max_left _ _)

theorem norm_proj_le (h : κ) : ‖S.proj h‖ ≤ S.boundConst :=
  (S.bound.choose_spec h).2.trans (le_max_left _ _)

theorem norm_incl_apply_le (h : κ) (v : S.X h) : ‖S.incl h v‖ ≤ S.boundConst * ‖v‖ :=
  ((S.incl h).le_opNorm v).trans (mul_le_mul_of_nonneg_right (S.norm_incl_le h) (norm_nonneg _))

theorem norm_adjoint_incl_apply_le (h : κ) (z : PiLp 2 W) :
    ‖(S.incl h).adjoint z‖ ≤ S.boundConst * ‖z‖ :=
  ((S.incl h).adjoint.le_opNorm z).trans (mul_le_mul_of_nonneg_right
    ((ContinuousLinearMap.adjoint.norm_map (S.incl h)).trans_le (S.norm_incl_le h))
    (norm_nonneg _))

/-- **Stability of the reading map**: `‖v‖ ≤ C ‖iₕ v‖` (from `πₕ iₕ = 1`). -/
theorem norm_le_norm_incl (h : κ) (v : S.X h) : ‖v‖ ≤ S.boundConst * ‖S.incl h v‖ :=
  calc ‖v‖ = ‖S.proj h (S.incl h v)‖ := by rw [S.proj_incl]
    _ ≤ ‖S.proj h‖ * ‖S.incl h v‖ := (S.proj h).le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_right (S.norm_proj_le h) (norm_nonneg _)

/-- The discrete Hodge wave operator `Lₕ = 𝐝ₕ - 𝐝ₕ*` (adjoint in the inner product of `Xₕ`). -/
abbrev L (h : κ) : S.X h →L[𝕜] S.X h := diffWave (S.D h)

/-- The **inner-product operator** `Jₕ = iₕ* iₕ` (`⟪Jₕ v, w⟫ = ⟪iₕ v, iₕ w⟫`). -/
def J (h : κ) : S.X h →L[𝕜] S.X h := (S.incl h).adjoint ∘L S.incl h

theorem inner_J (h : κ) (v w : S.X h) : ⟪S.J h v, w⟫_𝕜 = ⟪S.incl h v, S.incl h w⟫_𝕜 := by
  rw [J, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]

theorem norm_one_sub_J_le (h : κ) : ‖1 - S.J h‖ ≤ 1 + S.boundConst ^ 2 := by
  refine (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le ?_)
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map, pow_two]
  exact mul_le_mul (S.norm_incl_le h) (S.norm_incl_le h) (norm_nonneg _) S.boundConst_nonneg

/-- **The inner-product defect in the graph norm** `‖1 - Jₕ‖_{Vₕ}`: the norm of `1 - Jₕ` from the
graph space `Vₕ` of `𝐝ₕ` (`‖v‖²_{Vₕ} = ‖v‖² + ‖𝐝ₕ v‖²`) to `Xₕ`
(`ContinuousLinearMap.graphOpNorm`), the least `δ` with `‖(1 - Jₕ) v‖ ≤ δ ‖v‖_{Vₕ}`. It is at most
`‖1 - Jₕ‖` (`graphDefect_le`), and it is the defect that the static, heat and wave theories with
crimes use: they apply `1 - Jₕ` only to discrete forms whose graph norm they control
(`norm_one_sub_J_apply_le`, `norm_one_sub_J_apply_le_of_D_eq_zero`). -/
def graphDefect (h : κ) : ℝ := (S.D h).graphOpNorm (1 - S.J h)

theorem graphDefect_nonneg (h : κ) : 0 ≤ S.graphDefect h := (S.D h).graphOpNorm_nonneg _

/-- `‖1 - Jₕ‖_{Vₕ} ≤ ‖1 - Jₕ‖`. -/
theorem graphDefect_le (h : κ) : S.graphDefect h ≤ ‖1 - S.J h‖ := (S.D h).graphOpNorm_le _

/-- `‖1 - Jₕ‖_{Vₕ} = 0` iff `Jₕ = 1` (the inclusion of the graph space is onto). -/
theorem graphDefect_eq_zero_iff (h : κ) : S.graphDefect h = 0 ↔ S.J h = 1 :=
  ((S.D h).graphOpNorm_eq_zero_iff _).trans (sub_eq_zero.trans eq_comm)

/-- `‖(1 - Jₕ) v‖ ≤ ‖1 - Jₕ‖_{Vₕ} ‖v‖_{Vₕ}` on the graph space `Vₕ` of `𝐝ₕ`. -/
theorem norm_one_sub_J_graphFst_le (h : κ)
    (v : ((S.D h : S.X h →ₗ[𝕜] S.X h).toPMap ⊤).GraphSpace) :
    ‖(1 - S.J h) (((S.D h : S.X h →ₗ[𝕜] S.X h).toPMap ⊤).graphFst v)‖ ≤ S.graphDefect h * ‖v‖ :=
  (S.D h).norm_graphFst_le_graphOpNorm _ v

/-- `‖(1 - Jₕ) v‖ ≤ ‖1 - Jₕ‖_{Vₕ} (‖v‖ + ‖𝐝ₕ v‖)`. -/
theorem norm_one_sub_J_apply_le (h : κ) (v : S.X h) :
    ‖(1 - S.J h) v‖ ≤ S.graphDefect h * (‖v‖ + ‖S.D h v‖) :=
  (S.D h).norm_apply_le_graphOpNorm _ v

/-- `‖(1 - Jₕ) v‖ ≤ ‖1 - Jₕ‖_{Vₕ} ‖v‖` on the discrete cycles (`𝐝ₕ v = 0`). -/
theorem norm_one_sub_J_apply_le_of_D_eq_zero (h : κ) {v : S.X h} (hv : S.D h v = 0) :
    ‖(1 - S.J h) v‖ ≤ S.graphDefect h * ‖v‖ :=
  (S.D h).norm_apply_le_graphOpNorm_of_eq_zero _ hv

/-- **The inner-product defect of a discrete form and of its differential**, the form in which the
residual bound uses it (`norm_residual_le`):
`‖(1 - Jₕ) w‖ + ‖(1 - Jₕ) 𝐝ₕ w‖ ≤ ‖1 - Jₕ‖_{Vₕ} (‖w‖ + 2 ‖𝐝ₕ w‖)`, since `𝐝ₕ 𝐝ₕ w = 0`. -/
theorem norm_one_sub_J_add_le (h : κ) (w : S.X h) :
    ‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖ ≤ S.graphDefect h * (‖w‖ + 2 * ‖S.D h w‖) :=
  (add_le_add (S.norm_one_sub_J_apply_le h w)
    (S.norm_one_sub_J_apply_le_of_D_eq_zero h (S.D_D h w))).trans_eq (by ring)

/-- `‖(1 - Jₕ) w‖ + ‖(1 - Jₕ) 𝐝ₕ w‖ ≤ ‖1 - Jₕ‖ (‖w‖ + ‖𝐝ₕ w‖)`. -/
theorem norm_one_sub_J_add_le_opNorm (h : κ) (w : S.X h) :
    ‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖ ≤ ‖1 - S.J h‖ * (‖w‖ + ‖S.D h w‖) :=
  (add_le_add ((1 - S.J h).le_opNorm w) ((1 - S.J h).le_opNorm _)).trans_eq (by ring)

/-- **The defect from a bound in the graph norm**: if `‖(1 - Jₕ) v‖ ≤ δ (‖v‖ + ‖𝐝ₕ v‖)` for every
`v`, then `‖1 - Jₕ‖_{Vₕ} ≤ √2 δ` (`‖v‖ + ‖𝐝ₕ v‖ ≤ √2 ‖v‖_{Vₕ}`). -/
theorem graphDefect_le_of_forall (h : κ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ v, ‖(1 - S.J h) v‖ ≤ δ * (‖v‖ + ‖S.D h v‖)) : S.graphDefect h ≤ √2 * δ :=
  (S.D h).graphOpNorm_le_of_forall _ hδ hb

/-- `‖1 - Jₕ‖ → 0` implies `‖1 - Jₕ‖_{Vₕ} → 0`. -/
theorem tendsto_graphDefect_of_tendsto {l : Filter κ}
    (hJ : Tendsto (fun h => ‖1 - S.J h‖) l (𝓝 0)) : Tendsto S.graphDefect l (𝓝 0) :=
  squeeze_zero S.graphDefect_nonneg S.graphDefect_le hJ

/-! #### The exact-load elliptic projection -/

/-- The **load map** `Bₕ = (1 - Lₕ)⁻¹ iₕ* : W → Xₕ`; the exact-load modified elliptic projection
of `y ∈ D(L)` is `Rₕ y = Bₕ (y - L y)`, the solution of `⟪(1 - Lₕ) Rₕ y, v⟫ = ⟪(1 - L) y, iₕ v⟫`
(the elliptic projection (4.11) of [QuennevilleBelair2015] with `iₕ*` in place of the orthogonal
projection; cf. the thesis' (6.4)). -/
def load (h : κ) : PiLp 2 W →L[𝕜] S.X h :=
  ((diffResolvent (S.D h)).symm : S.X h →L[𝕜] S.X h) ∘L (S.incl h).adjoint

theorem load_sub (h : κ) (z : PiLp 2 W) :
    S.load h z - S.L h (S.load h z) = (S.incl h).adjoint z :=
  (diffResolvent (S.D h)).apply_symm_apply ((S.incl h).adjoint z)

theorem inner_load_sub (h : κ) (z : PiLp 2 W) (v : S.X h) :
    ⟪S.load h z - S.L h (S.load h z), v⟫_𝕜 = ⟪z, S.incl h v⟫_𝕜 := by
  rw [S.load_sub, ContinuousLinearMap.adjoint_inner_left]

/-- `Bₕ` is characterized by `(1 - Lₕ) Bₕ z = iₕ* z`. -/
theorem eq_load (h : κ) {z : PiLp 2 W} {r : S.X h} (hr : r - S.L h r = (S.incl h).adjoint z) :
    r = S.load h z :=
  (diffResolvent (S.D h)).injective (by
    rw [diffResolvent_apply, diffResolvent_apply, hr, S.load_sub])

theorem norm_load_apply_le (h : κ) (z : PiLp 2 W) : ‖S.load h z‖ ≤ S.boundConst * ‖z‖ :=
  (norm_diffResolvent_symm_apply_le (S.D h) _).trans (S.norm_adjoint_incl_apply_le h z)

/-- **`Bₕ` is bounded in the discrete graph norm**: `‖Bₕ z‖ + ‖𝐝ₕ Bₕ z‖ ≤ 8 C ‖z‖`, since
`⟪(1 - Lₕ) Bₕ z, v⟫ = ⟪z, iₕ v⟫` (`norm_add_norm_le_of_inner_diff`). -/
theorem norm_load_add_le (h : κ) (z : PiLp 2 W) :
    ‖S.load h z‖ + ‖S.D h (S.load h z)‖ ≤ 8 * S.boundConst * ‖z‖ := by
  have hC := S.boundConst_nonneg
  refine (norm_add_norm_le_of_inner_diff (S.D h) (S.D_D h) (S.load h z)
    (M := S.boundConst * ‖z‖) (by positivity) fun v => ?_).trans_eq (by ring)
  rw [S.inner_load_sub h z v]
  calc ‖⟪z, S.incl h v⟫_𝕜‖ ≤ ‖z‖ * (S.boundConst * ‖v‖) :=
        (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (S.norm_incl_apply_le h v) (norm_nonneg _))
    _ = S.boundConst * ‖z‖ * ‖v‖ := by ring
    _ ≤ S.boundConst * ‖z‖ * (‖v‖ + ‖S.D h v‖) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) (by positivity)

/-- **The inner-product defect at the load**: `‖(1 - Jₕ) Bₕ z‖ ≤ 8 C ‖1 - Jₕ‖_{Vₕ} ‖z‖` (`Bₕ` is
bounded in the discrete graph norm, `norm_load_add_le`). -/
theorem norm_one_sub_J_load_le (h : κ) (z : PiLp 2 W) :
    ‖(1 - S.J h) (S.load h z)‖ ≤ S.graphDefect h * (8 * S.boundConst * ‖z‖) :=
  (S.norm_one_sub_J_apply_le h _).trans
    (mul_le_mul_of_nonneg_left (S.norm_load_add_le h z) (S.graphDefect_nonneg h))

/-! #### The Strang lemma -/

/-- **The Strang lemma, discrete form**: if the discrete residual of `w` against the load `z`,
`⟪(1 - Lₕ) w, v⟫ - ⟪z, iₕ v⟫`, is at most `ε (‖v‖ + ‖𝐝ₕ v‖)`, then
`‖w - Bₕ z‖ + ‖𝐝ₕ (w - Bₕ z)‖ ≤ 8 ε`. -/
theorem norm_sub_load_add_le (h : κ) (z : PiLp 2 W) (w : S.X h) {ε : ℝ} (hε : 0 ≤ ε)
    (hres : ∀ v, ‖⟪w - S.L h w, v⟫_𝕜 - ⟪z, S.incl h v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖S.D h v‖)) :
    ‖w - S.load h z‖ + ‖S.D h (w - S.load h z)‖ ≤ 8 * ε := by
  refine norm_add_norm_le_of_inner_diff (S.D h) (S.D_D h) _ hε fun v => ?_
  have e : ⟪(w - S.load h z) - S.L h (w - S.load h z), v⟫_𝕜 =
      ⟪w - S.L h w, v⟫_𝕜 - ⟪z, S.incl h v⟫_𝕜 := by
    rw [← S.inner_load_sub h z v, ← inner_sub_left, _root_.map_sub]
    congr 1; abel
  rw [e]; exact hres v

/-- **The Strang lemma**: `‖y - iₕ Bₕ z‖ ≤ ‖y - iₕ w‖ + 8 C ε` for an approximant `w` whose
residual against `z` is at most `ε`. -/
theorem norm_sub_incl_load_le (h : κ) (y z : PiLp 2 W) (w : S.X h) {ε : ℝ} (hε : 0 ≤ ε)
    (hres : ∀ v, ‖⟪w - S.L h w, v⟫_𝕜 - ⟪z, S.incl h v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖S.D h v‖)) :
    ‖y - S.incl h (S.load h z)‖ ≤ ‖y - S.incl h w‖ + 8 * S.boundConst * ε := by
  have h1 := S.norm_sub_load_add_le h z w hε hres
  have h2 : ‖w - S.load h z‖ ≤ 8 * ε := by linarith [norm_nonneg (S.D h (w - S.load h z))]
  have e : y - S.incl h (S.load h z) = (y - S.incl h w) + S.incl h (w - S.load h z) := by
    rw [_root_.map_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (S.norm_incl_apply_le h _).trans ?_
  have := S.boundConst_nonneg
  nlinarith

/-! #### The consistency defect -/

/-- **The defect bound**: `Δₕ = Bₕ z - iₕ* y` satisfies
`‖Δₕ‖ ≤ ‖(1 - Jₕ) Bₕ z‖ + C ‖y - iₕ Bₕ z‖`; the first term is at most `‖1 - Jₕ‖ ‖Bₕ z‖` and at most
`8 C ‖1 - Jₕ‖_{Vₕ} ‖z‖` (`norm_one_sub_J_load_le`). -/
theorem norm_load_sub_adjoint_le (h : κ) (y z : PiLp 2 W) :
    ‖S.load h z - (S.incl h).adjoint y‖ ≤
      ‖(1 - S.J h) (S.load h z)‖ + S.boundConst * ‖y - S.incl h (S.load h z)‖ := by
  have e : S.load h z - (S.incl h).adjoint y =
      (1 - S.J h) (S.load h z) - (S.incl h).adjoint (y - S.incl h (S.load h z)) := by
    simp only [J, _root_.sub_apply, one_apply_eq_self,
      ContinuousLinearMap.comp_apply, _root_.map_sub]
    abel
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (S.norm_adjoint_incl_apply_le h _))

/-- **The defect identity** (algebraic): for states `a`, `b`, `b'`,
`Bₕ (b - b') - Lₕ Bₕ (a - b) = (Bₕ (b - b') - iₕ* b) - (Bₕ (a - b) - iₕ* a)`; along a trajectory
(`b = L a`, `b' = L b`) this is `Rₕ (L y) - Lₕ Rₕ y = Δₕ (L y) - Δₕ y`. -/
theorem load_defect (h : κ) (a b b' : PiLp 2 W) :
    S.load h (b - b') - S.L h (S.load h (a - b)) =
      (S.load h (b - b') - (S.incl h).adjoint b) - (S.load h (a - b) - (S.incl h).adjoint a) := by
  have e := S.load_sub h (a - b)
  have e' : S.L h (S.load h (a - b)) = S.load h (a - b) - (S.incl h).adjoint (a - b) := by
    rw [← e]; abel
  rw [e']
  simp only [_root_.map_sub]
  abel

/-! #### The cochain defect and the splitting of the residual -/

/-- The **cochain defect** `κₕ(y) = 𝐝ₕ* iₕ* y - iₕ* 𝐝* y` of `y ∈ D(L)`:
`⟪κₕ(y), v⟫ = ⟪y, iₕ 𝐝ₕ v⟫ - ⟪𝐝* y, iₕ v⟫` (`inner_cochainDefect`). -/
def cochainDefect (h : κ) (y : H.wave.domain) : S.X h :=
  (S.D h).adjoint ((S.incl h).adjoint y) - (S.incl h).adjoint (H.dual.totalD ⟨y, y.2.2⟩)

theorem inner_cochainDefect (h : κ) (y : H.wave.domain) (v : S.X h) :
    ⟪S.cochainDefect h y, v⟫_𝕜 =
      ⟪(y : PiLp 2 W), S.incl h (S.D h v)⟫_𝕜 - ⟪H.dual.totalD ⟨y, y.2.2⟩, S.incl h v⟫_𝕜 := by
  rw [cochainDefect, inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]

/-- When `iₕ v ∈ D(𝐝)`, the cochain defect pairs `y` with the strong cochain defect:
`⟪κₕ(y), v⟫ = ⟪y, iₕ 𝐝ₕ v - 𝐝 iₕ v⟫`. -/
theorem inner_cochainDefect_of_mem (h : κ) (y : H.wave.domain) (v : S.X h)
    (hv : S.incl h v ∈ H.totalD.domain) :
    ⟪S.cochainDefect h y, v⟫_𝕜 =
      ⟪(y : PiLp 2 W), S.incl h (S.D h v) - H.totalD ⟨_, hv⟩⟫_𝕜 := by
  rw [inner_cochainDefect, inner_sub_right]
  congr 1
  rw [← inner_conj_symm, ← H.inner_totalD_dual ⟨_, hv⟩ ⟨y, y.2.2⟩, inner_conj_symm]

/-- **The cochain defect vanishes for cochain maps**: if `iₕ Xₕ ⊆ D(𝐝)` and `𝐝 iₕ = iₕ 𝐝ₕ`,
then `κₕ = 0`. -/
theorem cochainDefect_eq_zero (h : κ) (hmem : ∀ v, S.incl h v ∈ H.totalD.domain)
    (hcomm : ∀ v, H.totalD ⟨_, hmem v⟩ = S.incl h (S.D h v)) (y : H.wave.domain) :
    S.cochainDefect h y = 0 :=
  ext_inner_right 𝕜 fun v => by
    rw [S.inner_cochainDefect_of_mem h y v (hmem v), hcomm, sub_self, inner_zero_right,
      inner_zero_left]

/-- **The residual splits** into the inner-product defect, the graph-norm approximation error and
the cochain defect: for `y ∈ D(L)` and every approximant `w`,
`⟪(1 - Lₕ) w, v⟫ - ⟪(1 - L) y, iₕ v⟫ = ⟪(1 - Jₕ) w, v⟫ - ⟪(1 - Jₕ) 𝐝ₕ w, v⟫ + ⟪(1 - Jₕ) w, 𝐝ₕ v⟫
+ ⟪iₕ w - y, iₕ v⟫ - ⟪iₕ 𝐝ₕ w - 𝐝 y, iₕ v⟫ + ⟪iₕ w - y, iₕ 𝐝ₕ v⟫ + ⟪κₕ(y), v⟫`. -/
theorem inner_residual_eq (h : κ) (y : H.wave.domain) (w v : S.X h) :
    ⟪w - S.L h w, v⟫_𝕜 - ⟪(y : PiLp 2 W) - H.wave y, S.incl h v⟫_𝕜 =
      ⟪(1 - S.J h) w, v⟫_𝕜 - ⟪(1 - S.J h) (S.D h w), v⟫_𝕜 + ⟪(1 - S.J h) w, S.D h v⟫_𝕜 +
        ⟪S.incl h w - y, S.incl h v⟫_𝕜 -
        ⟪S.incl h (S.D h w) - H.totalD ⟨y, y.2.1⟩, S.incl h v⟫_𝕜 +
        ⟪S.incl h w - y, S.incl h (S.D h v)⟫_𝕜 + ⟪S.cochainDefect h y, v⟫_𝕜 := by
  rw [S.inner_cochainDefect, wave_eq_sub]
  simp only [_root_.sub_apply, one_apply_eq_self, inner_sub_left, inner_diffWave, S.inner_J]
  ring

/-- **The residual bound**: if the cochain defect is at most `δ` in the dual discrete graph norm,
the residual of `w` is at most
`(‖(1 - Jₕ) w‖ + ‖(1 - Jₕ) 𝐝ₕ w‖ + C (‖y - iₕ w‖ + ‖𝐝 y - iₕ 𝐝ₕ w‖) + δ) (‖v‖ + ‖𝐝ₕ v‖)`. The
inner-product defect enters only at `w` and `𝐝ₕ w`: at most `‖1 - Jₕ‖ (‖w‖ + ‖𝐝ₕ w‖)`
(`norm_one_sub_J_add_le_opNorm`) and at most `‖1 - Jₕ‖_{Vₕ} (‖w‖ + 2 ‖𝐝ₕ w‖)`
(`norm_one_sub_J_add_le`). -/
theorem norm_residual_le (h : κ) (y : H.wave.domain) (w : S.X h) {δ : ℝ}
    (hδ : ∀ v, ‖⟪S.cochainDefect h y, v⟫_𝕜‖ ≤ δ * (‖v‖ + ‖S.D h v‖)) (v : S.X h) :
    ‖⟪w - S.L h w, v⟫_𝕜 - ⟪(y : PiLp 2 W) - H.wave y, S.incl h v⟫_𝕜‖ ≤
      (‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖ + S.boundConst *
        (‖(y : PiLp 2 W) - S.incl h w‖ + ‖H.totalD ⟨y, y.2.1⟩ - S.incl h (S.D h w)‖) + δ) *
        (‖v‖ + ‖S.D h v‖) := by
  rw [S.inner_residual_eq]
  set C := S.boundConst
  set p := ‖(1 - S.J h) w‖
  set q := ‖(1 - S.J h) (S.D h w)‖
  set a := ‖(y : PiLp 2 W) - S.incl h w‖
  set b := ‖H.totalD ⟨y, y.2.1⟩ - S.incl h (S.D h w)‖
  have hC := S.boundConst_nonneg
  have hp : 0 ≤ p := norm_nonneg _
  have hq : 0 ≤ q := norm_nonneg _
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hv := norm_nonneg v
  have hDv := norm_nonneg (S.D h v)
  have b1 : ‖⟪(1 - S.J h) w, v⟫_𝕜‖ ≤ p * ‖v‖ := norm_inner_le_norm _ _
  have b2 : ‖⟪(1 - S.J h) (S.D h w), v⟫_𝕜‖ ≤ q * ‖v‖ := norm_inner_le_norm _ _
  have b3 : ‖⟪(1 - S.J h) w, S.D h v⟫_𝕜‖ ≤ p * ‖S.D h v‖ := norm_inner_le_norm _ _
  have b4 : ‖⟪S.incl h w - y, S.incl h v⟫_𝕜‖ ≤ a * (C * ‖v‖) := by
    refine (norm_inner_le_norm _ _).trans (mul_le_mul (le_of_eq ?_) (S.norm_incl_apply_le h v)
      (norm_nonneg _) ha)
    rw [norm_sub_rev]
  have b5 : ‖⟪S.incl h (S.D h w) - H.totalD ⟨y, y.2.1⟩, S.incl h v⟫_𝕜‖ ≤ b * (C * ‖v‖) := by
    refine (norm_inner_le_norm _ _).trans (mul_le_mul (le_of_eq ?_) (S.norm_incl_apply_le h v)
      (norm_nonneg _) hb)
    rw [norm_sub_rev]
  have b6 : ‖⟪S.incl h w - y, S.incl h (S.D h v)⟫_𝕜‖ ≤ a * (C * ‖S.D h v‖) := by
    refine (norm_inner_le_norm _ _).trans (mul_le_mul (le_of_eq ?_) (S.norm_incl_apply_le h _)
      (norm_nonneg _) ha)
    rw [norm_sub_rev]
  have b7 := hδ v
  calc _ ≤ ‖⟪(1 - S.J h) w, v⟫_𝕜‖ + ‖⟪(1 - S.J h) (S.D h w), v⟫_𝕜‖ +
        ‖⟪(1 - S.J h) w, S.D h v⟫_𝕜‖ + ‖⟪S.incl h w - y, S.incl h v⟫_𝕜‖ +
        ‖⟪S.incl h (S.D h w) - H.totalD ⟨y, y.2.1⟩, S.incl h v⟫_𝕜‖ +
        ‖⟪S.incl h w - y, S.incl h (S.D h v)⟫_𝕜‖ + ‖⟪S.cochainDefect h y, v⟫_𝕜‖ := by
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        exact norm_sub_le _ _
    _ ≤ _ := by nlinarith [mul_nonneg hq hDv, mul_nonneg (mul_nonneg hC hb) hDv]

/-- The reading error `‖a - iₕ Bₕ (a - b)‖` is Lipschitz in the pair `(a, b)`. -/
theorem reading_le (h : κ)
    (ζ ζ' : PiLp 2 W × PiLp 2 W) :
    ‖ζ.1 - S.incl h (S.load h (ζ.1 - ζ.2))‖ ≤ ‖ζ'.1 - S.incl h (S.load h (ζ'.1 - ζ'.2))‖ +
      (1 + 2 * S.boundConst ^ 2) * ‖ζ - ζ'‖ := by
  set C := S.boundConst
  have hC := S.boundConst_nonneg
  have e : ζ.1 - S.incl h (S.load h (ζ.1 - ζ.2)) =
      (ζ'.1 - S.incl h (S.load h (ζ'.1 - ζ'.2))) +
        ((ζ - ζ').1 - S.incl h (S.load h ((ζ - ζ').1 - (ζ - ζ').2))) := by
    simp only [Prod.fst_sub, Prod.snd_sub, _root_.map_sub]; abel
  have h1 := norm_fst_le (ζ - ζ')
  have h2 := norm_snd_le (ζ - ζ')
  have h3 : ‖S.incl h (S.load h ((ζ - ζ').1 - (ζ - ζ').2))‖ ≤
      C * (C * (‖(ζ - ζ').1‖ + ‖(ζ - ζ').2‖)) :=
    (S.norm_incl_apply_le h _).trans (mul_le_mul_of_nonneg_left
      ((S.norm_load_apply_le h _).trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hC)) hC)
  have h4 : C * (C * (‖(ζ - ζ').1‖ + ‖(ζ - ζ').2‖)) ≤ 2 * C ^ 2 * ‖ζ - ζ'‖ := by
    have : ‖(ζ - ζ').1‖ + ‖(ζ - ζ').2‖ ≤ 2 * ‖ζ - ζ'‖ := by linarith
    have := mul_le_mul_of_nonneg_left this (mul_nonneg hC hC)
    nlinarith
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sub_le _ _).trans ?_))
  nlinarith

/-- The defect `‖Bₕ (a - b) - iₕ* a‖` is Lipschitz in the pair `(a, b)`. -/
theorem defect_le (h : κ)
    (ζ ζ' : PiLp 2 W × PiLp 2 W) :
    ‖S.load h (ζ.1 - ζ.2) - (S.incl h).adjoint ζ.1‖ ≤
      ‖S.load h (ζ'.1 - ζ'.2) - (S.incl h).adjoint ζ'.1‖ + (3 * S.boundConst) * ‖ζ - ζ'‖ := by
  set C := S.boundConst
  have hC := S.boundConst_nonneg
  have e : S.load h (ζ.1 - ζ.2) - (S.incl h).adjoint ζ.1 =
      (S.load h (ζ'.1 - ζ'.2) - (S.incl h).adjoint ζ'.1) +
        (S.load h ((ζ - ζ').1 - (ζ - ζ').2) - (S.incl h).adjoint (ζ - ζ').1) := by
    simp only [Prod.fst_sub, Prod.snd_sub, _root_.map_sub]; abel
  have h1 := norm_fst_le (ζ - ζ')
  have h2 := norm_snd_le (ζ - ζ')
  have h3 : ‖S.load h ((ζ - ζ').1 - (ζ - ζ').2)‖ ≤ C * (‖(ζ - ζ').1‖ + ‖(ζ - ζ').2‖) :=
    (S.norm_load_apply_le h _).trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hC)
  have h4 := S.norm_adjoint_incl_apply_le h (ζ - ζ').1
  have h5 : C * (‖(ζ - ζ').1‖ + ‖(ζ - ζ').2‖) + C * ‖(ζ - ζ').1‖ ≤ 3 * C * ‖ζ - ζ'‖ := by
    have a := mul_le_mul_of_nonneg_left h1 hC
    have b := mul_le_mul_of_nonneg_left h2 hC
    nlinarith
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sub_le _ _).trans ?_))
  linarith

end ApproxComplexCrime.Family

/-! ### Approximating families -/

section Families

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- A **family of discrete differential spaces for the heat equation** for `H`: a family
(`ApproxComplexCrime.Family`) of discrete differential spaces `(Xₕ, 𝐝ₕ)` with reading maps that
need not be cochain maps, a closed constraint `K`, a filter `l`, and the **inner-product defect in
the graph norm** `‖1 - Jₕ‖_{Vₕ} → 0` (`Family.graphDefect`; implied by `‖1 - iₕ* iₕ‖ → 0`,
`Family.tendsto_graphDefect_of_tendsto`): the data of the heat FEEC theorem with crimes
(`Feec.HilbertComplex.Approximation.HeatCrime`). An approximating family (`ApproxComplexCrime`)
adds the admissible states, the core and consistent approximation of the wave equation. -/
structure ApproxComplexCrime.HeatFamily (H : HilbertComplex 𝕜 c W) (κ : Type*) where
  /-- the discrete differential spaces and reading maps -/
  toFamily : ApproxComplexCrime.Family.{u} H κ
  /-- the constraint subspace -/
  K : Submodule 𝕜 (PiLp 2 W)
  isClosed_K : IsClosed (K : Set (PiLp 2 W))
  /-- the filter along which the discretization is refined -/
  l : Filter κ
  tendsto_graphDefect : Tendsto toFamily.graphDefect l (𝓝 0)

/-- An **approximating family of discrete differential spaces** for `H`: a family
(`ApproxComplexCrime.Family`) of discrete differential spaces `(Xₕ, 𝐝ₕ)` with reading maps that
need not be cochain maps, a closed constraint `K`, a filter `l`, a set `A ⊆ D(L)` of admissible
states, a core `Z ≤ D(L²)` whose forward orbits and those of `L Z` stay in `A`, and hypotheses
of Holst–Stern type:

* the **inner-product defect in the graph norm** `‖1 - Jₕ‖_{Vₕ} → 0` (`Family.graphDefect`);
* **consistent approximation** on `A`: approximants `wₕ` with `‖y - iₕ wₕ‖ → 0` whose discrete
  residual `⟪(1 - Lₕ) wₕ, v⟫ - ⟪(1 - L) y, iₕ v⟫` tends to `0` in the dual discrete graph norm.
  By `ApproxComplexCrime.Family.inner_residual_eq` the residual is the sum of the inner-product
  defect, the graph-norm approximation error and the cochain defect, so it follows from graph-norm
  approximation, a cochain defect tending to `0` and `‖1 - Jₕ‖_{Vₕ} → 0`
  (`ApproxComplexCrime.ofCochainDefect`); it can also be checked directly with a Galerkin
  projection as approximant (residual `0`).

The field `consistent` is equivalent to `iₕ Rₕ y → y` on `A`
(`consistent_iff_tendsto_incl_load`); from it and the inner-product defect, the uniform
approximation of the comparison trajectories `Rₕ e^{tL} x` and their consistency defects are
derived (`ApproxFEEC.ofComplexCrimeCore`). The family, the constraint, the filter and the
inner-product defect form the data of the heat equation (`ApproxComplexCrime.HeatFamily`). -/
structure ApproxComplexCrime (H : HilbertComplex 𝕜 c W) (κ : Type*) extends
    ApproxComplexCrime.HeatFamily.{u} H κ where
  /-- the admissible states -/
  A : Set (PiLp 2 W)
  A_sub : A ⊆ H.wave.domain
  /-- the core -/
  Z : Submodule 𝕜 (PiLp 2 W)
  Z_le : Z ≤ H.wave.domainSq
  orbit_mem : ∀ x ∈ Z, ∀ t : ℝ, 0 ≤ t →
    H.waveGroup.S t x ∈ A ∧ H.waveGroup.S t (waveExt H x) ∈ A
  consistent : ∀ y ∈ A, ∀ ε > 0, ∀ᶠ h in l, ∃ w : toFamily.X h,
    ‖y - toFamily.incl h w‖ ≤ ε ∧ ∀ v, ‖⟪w - toFamily.L h w, v⟫_𝕜 -
      ⟪y - waveExt H y, toFamily.incl h v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖toFamily.D h v‖)

namespace ApproxComplexCrime

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplexCrime.{u} H κ)

/-- **Consistent approximation at `y` is pointwise convergence of the exact-load projection**:
the approximants of `ApproxComplexCrime.consistent` exist at `y` iff `iₕ Rₕ y → y`,
`Rₕ y = Bₕ (y - L y)`. Forward: the Strang lemma. Backward: `Rₕ y` itself is an approximant with
residual `0` (`Family.inner_load_sub`). So the field `consistent` is exactly the hypothesis
`iₕ Rₕ y → y` on `A`; the splittings `consistent_of_cochainDefect` and `ofGalerkinCore` are the
ways it is checked. -/
theorem consistent_iff_tendsto_incl_load (y : PiLp 2 W) :
    (∀ ε > 0, ∀ᶠ h in F.l, ∃ w : F.toFamily.X h,
      ‖y - F.toFamily.incl h w‖ ≤ ε ∧ ∀ v, ‖⟪w - F.toFamily.L h w, v⟫_𝕜 -
        ⟪y - waveExt H y, F.toFamily.incl h v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖F.toFamily.D h v‖)) ↔
      Tendsto (fun h => ‖y - F.toFamily.incl h (F.toFamily.load h (y - waveExt H y))‖) F.l
        (𝓝 0) := by
  set S := F.toFamily
  constructor
  · intro hc
    rw [Metric.tendsto_nhds]
    intro ε hε
    set B := 1 + 8 * S.boundConst
    have hB : 0 < B := by have := S.boundConst_nonneg; positivity
    filter_upwards [hc (ε / (2 * B)) (by positivity)] with h ⟨w, hw, hres⟩
    rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg (norm_nonneg _)]
    have h1 := S.norm_sub_incl_load_le h y _ w (by positivity) hres
    have : ‖y - S.incl h w‖ + 8 * S.boundConst * (ε / (2 * B)) ≤ ε / 2 := by
      have e : ε / (2 * B) + 8 * S.boundConst * (ε / (2 * B)) = ε / 2 := by
        have e1 : ε / (2 * B) + 8 * S.boundConst * (ε / (2 * B)) = ε / (2 * B) * B := by
          simp only [B]; ring
        rw [e1]; field_simp
      linarith
    linarith
  · intro ht ε hε
    have hev := (Metric.tendsto_nhds.1 ht) ε hε
    filter_upwards [hev] with h hh
    rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg (norm_nonneg _)] at hh
    refine ⟨S.load h (y - waveExt H y), hh.le, fun v => ?_⟩
    rw [S.inner_load_sub, sub_self, norm_zero]
    exact mul_nonneg hε.le (by positivity)

/-- **Convergence of the exact-load elliptic projection** at an admissible state:
`iₕ Rₕ y → y`, `Rₕ y = Bₕ (y - L y)` (the Strang lemma and consistent approximation). -/
theorem tendsto_incl_load {y : PiLp 2 W} (hy : y ∈ F.A) :
    Tendsto (fun h => ‖y - F.toFamily.incl h (F.toFamily.load h (y - waveExt H y))‖) F.l
      (𝓝 0) :=
  (F.consistent_iff_tendsto_incl_load y).1 (F.consistent y hy)

/-- **The derived consistency**: the defect `Δₕ y = Rₕ y - iₕ* y` tends to `0` at admissible
states. -/
theorem tendsto_defect {y : PiLp 2 W} (hy : y ∈ F.A) :
    Tendsto (fun h => ‖F.toFamily.load h (y - waveExt H y) - (F.toFamily.incl h).adjoint y‖)
      F.l (𝓝 0) := by
  set S := F.toFamily
  have h1 := F.tendsto_graphDefect
  have h2 := F.tendsto_incl_load hy
  have hb : Tendsto (fun h => S.graphDefect h * (8 * S.boundConst * ‖y - waveExt H y‖) +
      S.boundConst * ‖y - S.incl h (S.load h (y - waveExt H y))‖) F.l (𝓝 0) := by
    have := (h1.mul_const (8 * S.boundConst * ‖y - waveExt H y‖)).add (h2.const_mul S.boundConst)
    simpa using this
  exact squeeze_zero (fun _ => norm_nonneg _) (fun h => (S.norm_load_sub_adjoint_le h y _).trans
    (add_le_add (S.norm_one_sub_J_load_le h _) le_rfl)) hb

end ApproxComplexCrime

/-! ### The approximating FEEC discretization -/

section OfComplexCrime

namespace ApproxFEEC

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplexCrime.{u} H κ)

/-- **The approximating FEEC discretization of an approximating family of discrete differential
spaces**: `Xₕ` with its own inner product, `Lₕ = 𝐝ₕ - 𝐝ₕ*` (the Hodge wave operator of
`(Xₕ, 𝐝ₕ)`), `ιₕ = iₕ`, `πₕ` the left inverses. -/
def ofComplexCrime : ApproxFEEC H κ where
  K := F.K
  isClosed_K := F.isClosed_K
  l := F.l
  X := F.toFamily.X
  L h := F.toFamily.L h
  isSkewAdjoint := H.isSkewAdjoint_wave
  skew h := diffWave_skew (F.toFamily.D h)
  incl := F.toFamily.incl
  proj := F.toFamily.proj
  proj_incl := F.toFamily.proj_incl
  bound := F.toFamily.bound

theorem ofComplexCrime_L (h : κ) :
    (ofComplexCrime F).L h = F.toFamily.D h - (F.toFamily.D h).adjoint :=
  rfl

/-- The defect `Δₕ = Bₕ - iₕ* (1 - L)⁻¹` of the exact-load elliptic projection on lifted states:
`Δₕ (y - L y) = Bₕ (y - L y) - iₕ* y` (`loadDefect_apply`). -/
def loadDefect (h : κ) : PiLp 2 W →L[𝕜] F.toFamily.X h :=
  F.toFamily.load h - (F.toFamily.incl h).adjoint ∘L Operator.resolvent H.wave 1

theorem loadDefect_apply (h : κ) {y : PiLp 2 W} (hy : y ∈ H.wave.domain) :
    loadDefect F h (y - waveExt H y) =
      F.toFamily.load h (y - waveExt H y) - (F.toFamily.incl h).adjoint y := by
  have e : Operator.resolvent H.wave (1 : 𝕜) (y - waveExt H y) = y := by
    rw [waveExt_of_mem hy]
    exact resolvent_one_apply_sub (ofComplexCrime F).isMDissipative ⟨y, hy⟩
  change F.toFamily.load h _ - (F.toFamily.incl h).adjoint
    (Operator.resolvent H.wave (1 : 𝕜) (y - waveExt H y)) = _
  rw [e]

/-- **The load Ritz projection**: the exact-load modified elliptic projection `Rₕ = Bₕ` on the
resolvent lift `ℓ = 1 - L` (`DissipFEEC.Lift.resolvent`, data `D(L²)`), with `Δₕ = loadDefect`,
`Δₕ' = -Δₕ` (the defect identity `Family.load_defect`). -/
def loadRitz : DissipFEEC.Ritz (DissipFEEC.Lift.resolvent (ofComplexCrime F).toDissipFEEC) where
  R := F.toFamily.load
  Δ := loadDefect F
  Δ' h := -loadDefect F h
  defect_eq h y hy := by
    have hA := (ofComplexCrime F).isMDissipative
    have hy1 := DissipFEEC.mem_domain_of_mem_resData hA hy
    have hy2 := DissipFEEC.genExt_mem_domain_of_mem_resData hy hA
    change F.toFamily.load h (DissipFEEC.genExt H.wave y -
        DissipFEEC.genExt H.wave (DissipFEEC.genExt H.wave y)) -
      F.toFamily.L h (F.toFamily.load h (y - DissipFEEC.genExt H.wave y)) =
      loadDefect F h (DissipFEEC.genExt H.wave y -
        DissipFEEC.genExt H.wave (DissipFEEC.genExt H.wave y)) +
      -loadDefect F h (y - DissipFEEC.genExt H.wave y)
    rw [← waveExt_eq_genExt] at hy2 ⊢
    rw [loadDefect_apply F h hy1, loadDefect_apply F h hy2, F.toFamily.load_defect]
    abel
  bound := by
    set C := F.toFamily.boundConst
    have hC := F.toFamily.boundConst_nonneg
    have hD : ∀ h, ‖loadDefect F h‖ ≤ 2 * C := fun h =>
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => by
        have h1 := F.toFamily.norm_load_apply_le h y
        have h2 := F.toFamily.norm_adjoint_incl_apply_le h (Operator.resolvent H.wave (1 : 𝕜) y)
        have h3 : ‖Operator.resolvent H.wave (1 : 𝕜) y‖ ≤ ‖y‖ := by
          simpa using (ofComplexCrime F).isMDissipative.norm_resolvent_apply_le one_pos y
        have e : loadDefect F h y = F.toFamily.load h y -
            (F.toFamily.incl h).adjoint (Operator.resolvent H.wave (1 : 𝕜) y) := rfl
        rw [e]
        refine (norm_sub_le _ _).trans ?_
        nlinarith [mul_le_mul_of_nonneg_left h3 hC]
    exact ⟨2 * C, fun h => ⟨(ContinuousLinearMap.opNorm_le_bound _ hC
      (F.toFamily.norm_load_apply_le h)).trans (by linarith), hD h,
      (norm_neg (loadDefect F h)).trans_le (hD h)⟩⟩

/-- **The comparison of `ofComplexCrime`** on `[0, T]`: the comparison of the load Ritz projection
on the core `Z`, `pₕ(t) = Bₕ (e^{tL} x - e^{tL} L x) = Rₕ (e^{tL} x)` (`crimeCmp_p`: the
exact-load modified elliptic projection of the exact orbit), with derivative `Rₕ (e^{tL} L x)`. -/
def crimeCmp (T : ℝ) : (ofComplexCrime F).Comparison T :=
  ((loadRitz F).cmp T).restrict F.Z fun _ hx =>
    DissipFEEC.domainSq_le_resData (ofComplexCrime F).isMDissipative (F.Z_le hx)

/-- The comparison trajectories of the load Ritz projection:
`pₕ(t) = Bₕ (e^{tL} x - e^{tL} L x)` for `t ≥ 0`. -/
theorem loadRitz_cmp_p (T : ℝ) {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (h : κ) {t : ℝ}
    (ht : 0 ≤ t) :
    ((loadRitz F).cmp T).p x h t =
      F.toFamily.load h (H.waveGroup.S t x - H.waveGroup.S t (waveExt H x)) := by
  change F.toFamily.load h ((ofComplexCrime F).S t x -
    DissipFEEC.genExt H.wave ((ofComplexCrime F).S t x)) = _
  rw [(ofComplexCrime F).S_eq_waveGroup ht, ← waveExt_eq_genExt, waveExt_waveGroup H hx]

theorem crimeCmp_p (T : ℝ) {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (h : κ) {t : ℝ}
    (ht : 0 ≤ t) :
    (crimeCmp F T).p x h t =
      F.toFamily.load h (H.waveGroup.S t x - H.waveGroup.S t (waveExt H x)) :=
  loadRitz_cmp_p F T hx h ht

/-- On the core, the comparison is the exact-load elliptic projection of the exact state:
`pₕ(t) = Bₕ (y - L y)`, `y = e^{tL} x`. -/
theorem crimeCmp_p_eq (T : ℝ) {x : PiLp 2 W} (hx : x ∈ F.Z) (h : κ) {t : ℝ} (ht : 0 ≤ t) :
    (crimeCmp F T).p x h t = F.toFamily.load h (H.waveGroup.S t x -
      waveExt H (H.waveGroup.S t x)) := by
  rw [crimeCmp_p F T (domainSq_le_domain (F.Z_le hx)) h ht,
    waveExt_waveGroup H (domainSq_le_domain (F.Z_le hx))]

/-- The consistency defect of the comparison is `Δₕ (L y) - Δₕ y` along the orbit
(`DissipFEEC.Ritz.cmp_defect`). -/
theorem crimeCmp_defect (T : ℝ) {x : PiLp 2 W} (hx : x ∈ F.Z) (h : κ) {t : ℝ} (ht : 0 ≤ t) :
    (crimeCmp F T).defect x h t =
      (F.toFamily.load h (H.waveGroup.S t (waveExt H x) -
          H.waveGroup.S t (waveExt H (waveExt H x))) -
        (F.toFamily.incl h).adjoint (H.waveGroup.S t (waveExt H x))) -
      (F.toFamily.load h (H.waveGroup.S t x - H.waveGroup.S t (waveExt H x)) -
        (F.toFamily.incl h).adjoint (H.waveGroup.S t x)) := by
  have hx2 := F.Z_le hx
  have hx1 := domainSq_le_domain hx2
  have hLx := waveExt_mem_domain H hx2
  change ((loadRitz F).cmp T).defect x h t = _
  rw [(loadRitz F).cmp_defect T
    (DissipFEEC.domainSq_le_resData (ofComplexCrime F).isMDissipative hx2) h ht]
  change loadDefect F h ((ofComplexCrime F).S t (DissipFEEC.genExt H.wave x) -
      DissipFEEC.genExt H.wave ((ofComplexCrime F).S t (DissipFEEC.genExt H.wave x))) +
    -loadDefect F h ((ofComplexCrime F).S t x -
      DissipFEEC.genExt H.wave ((ofComplexCrime F).S t x)) = _
  rw [(ofComplexCrime F).S_eq_waveGroup ht, ← waveExt_eq_genExt,
    loadDefect_apply F h (waveGroup_mem_domain H hLx t),
    loadDefect_apply F h (waveGroup_mem_domain H hx1 t), waveExt_waveGroup H hLx,
    waveExt_waveGroup H hx1]
  abel

/-- The orbit pairs `(e^{tL} x, e^{tL} L x)`, `t ∈ [0, T]`, form a compact set. -/
theorem isCompact_orbitPair (x : PiLp 2 W) (T : ℝ) :
    IsCompact ((fun t => (H.waveGroup.S t x, H.waveGroup.S t (waveExt H x))) '' Icc 0 T) :=
  isCompact_Icc.image ((H.waveGroup.strongCont _).prodMk (H.waveGroup.strongCont _))

/-- **Uniform approximation of the orbit by the comparison** (from the Strang lemma at the
admissible states, by compactness). -/
theorem crimeCmp_tendsto_approx (T : ℝ) {x : PiLp 2 W} (hx : x ∈ F.Z) :
    TendstoUniformlyOn (fun h t => F.toFamily.incl h
      (F.toFamily.load h (H.waveGroup.S t x - H.waveGroup.S t (waveExt H x))))
      (fun t => H.waveGroup.S t x) F.l (Icc 0 T) := by
  have hx1 := domainSq_le_domain (F.Z_le hx)
  set f : κ → PiLp 2 W × PiLp 2 W → ℝ := fun h ζ =>
    ‖ζ.1 - F.toFamily.incl h (F.toFamily.load h (ζ.1 - ζ.2))‖ with hf
  set P : Set (PiLp 2 W × PiLp 2 W) :=
    (fun t => (H.waveGroup.S t x, H.waveGroup.S t (waveExt H x))) '' Icc 0 T
  have hlim : ∀ ζ ∈ P, Tendsto (fun h => f h ζ) F.l (𝓝 0) := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 := F.tendsto_incl_load (F.orbit_mem x hx t ht.1).1
    rw [waveExt_waveGroup H hx1] at h1
    exact h1
  have hev : ∀ ε > 0, ∀ᶠ h in F.l, ∀ ζ ∈ P, f h ζ < ε := fun ε hε =>
    eventually_forall_lt_of_tendsto_on (f := f) (M := 1 + 2 * F.toFamily.boundConst ^ 2)
      (fun h ζ ζ' => F.toFamily.reading_le h ζ ζ') hlim (isCompact_orbitPair x T) hε
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hev ε hε] with h hh t ht
  rw [dist_eq_norm]
  exact hh (H.waveGroup.S t x, H.waveGroup.S t (waveExt H x)) ⟨t, ht, rfl⟩

/-- **The consistency defect of the comparison tends to `0` uniformly** (from the defect
identity and the defect bound at the admissible states, by compactness). -/
theorem crimeCmp_tendsto_defect (T : ℝ) {x : PiLp 2 W} (hx : x ∈ F.Z) :
    TendstoUniformlyOn (fun h t => ‖(crimeCmp F T).defect x h t‖) (fun _ => 0) F.l
      (Icc 0 T) := by
  have hx2 := F.Z_le hx
  have hx1 := domainSq_le_domain hx2
  have hLx := waveExt_mem_domain H hx2
  set g : κ → PiLp 2 W × PiLp 2 W → ℝ := fun h ζ =>
    ‖F.toFamily.load h (ζ.1 - ζ.2) - (F.toFamily.incl h).adjoint ζ.1‖ with hg
  set P1 : Set (PiLp 2 W × PiLp 2 W) :=
    (fun t => (H.waveGroup.S t x, H.waveGroup.S t (waveExt H x))) '' Icc 0 T
  set P2 : Set (PiLp 2 W × PiLp 2 W) :=
    (fun t => (H.waveGroup.S t (waveExt H x), H.waveGroup.S t (waveExt H (waveExt H x)))) ''
      Icc 0 T
  have hlim1 : ∀ ζ ∈ P1, Tendsto (fun h => g h ζ) F.l (𝓝 0) := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 := F.tendsto_defect (F.orbit_mem x hx t ht.1).1
    rw [waveExt_waveGroup H hx1] at h1
    exact h1
  have hlim2 : ∀ ζ ∈ P2, Tendsto (fun h => g h ζ) F.l (𝓝 0) := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 := F.tendsto_defect (F.orbit_mem x hx t ht.1).2
    rw [waveExt_waveGroup H hLx] at h1
    exact h1
  have hev1 : ∀ ε > 0, ∀ᶠ h in F.l, ∀ ζ ∈ P1, g h ζ < ε := fun ε hε =>
    eventually_forall_lt_of_tendsto_on (f := g) (M := 3 * F.toFamily.boundConst)
      (fun h ζ ζ' => F.toFamily.defect_le h ζ ζ') hlim1 (isCompact_orbitPair x T) hε
  have hev2 : ∀ ε > 0, ∀ᶠ h in F.l, ∀ ζ ∈ P2, g h ζ < ε := fun ε hε =>
    eventually_forall_lt_of_tendsto_on (f := g) (M := 3 * F.toFamily.boundConst)
      (fun h ζ ζ' => F.toFamily.defect_le h ζ ζ') hlim2 (isCompact_orbitPair (waveExt H x) T) hε
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hev1 _ (half_pos hε), hev2 _ (half_pos hε)] with h h1 h2 t ht
  rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg (norm_nonneg _),
    crimeCmp_defect F T hx h ht.1]
  refine (norm_sub_le _ _).trans_lt ?_
  have a1 : ‖F.toFamily.load h (H.waveGroup.S t x - H.waveGroup.S t (waveExt H x)) -
      (F.toFamily.incl h).adjoint (H.waveGroup.S t x)‖ < ε / 2 :=
    h1 (H.waveGroup.S t x, H.waveGroup.S t (waveExt H x)) ⟨t, ht, rfl⟩
  have a2 : ‖F.toFamily.load h (H.waveGroup.S t (waveExt H x) -
      H.waveGroup.S t (waveExt H (waveExt H x))) -
      (F.toFamily.incl h).adjoint (H.waveGroup.S t (waveExt H x))‖ < ε / 2 :=
    h2 (H.waveGroup.S t (waveExt H x), H.waveGroup.S t (waveExt H (waveExt H x))) ⟨t, ht, rfl⟩
  exact lt_of_lt_of_eq (add_lt_add a2 a1) (add_halves ε)

/-- **The core of `ofComplexCrime`**: data `Z`, comparison `crimeCmp` (the load Ritz projection
on `Z`). Its two hypotheses (uniform approximation of the orbit, uniform vanishing of the
consistency defect) are derived from the Strang lemma and the defect identity at the admissible
states only, by compactness of the orbits (`crimeCmp_tendsto_approx`, `crimeCmp_tendsto_defect`):
the pointwise hypotheses of `DissipFEEC.Ritz.toCore` on all states are not available. -/
def ofComplexCrimeCore : (ofComplexCrime F).Core where
  Data := F.Z
  cmp T := crimeCmp F T
  data_eq _ := rfl
  tendsto_approx T _ hx := ((crimeCmp_tendsto_approx F T hx).congr
    (Eventually.of_forall fun h _ ht => congrArg (F.toFamily.incl h)
      (crimeCmp_p F T (domainSq_le_domain (F.Z_le hx)) h ht.1).symm)).congr_right
    fun _ ht => (DFunLike.congr_fun ((ofComplexCrime F).S_eq_waveGroup ht.1) _).symm
  tendsto_defect T _ hx := crimeCmp_tendsto_defect F T hx

theorem ofComplexCrimeCore_cmp (T : ℝ) : (ofComplexCrimeCore F).cmp T = crimeCmp F T := rfl

end ApproxFEEC

open ApproxFEEC in
/-- **The approximating FEEC theorem for approximating families of discrete differential spaces**
(reading maps that need not be cochain maps). For an approximating family `F`
(`ApproxComplexCrime`: inner-product defect `‖1 - Jₕ‖_{Vₕ} → 0` in the graph norm and consistent
approximation on the admissible states), the discretization `ofComplexCrime F` (generator the Hodge wave operator
`𝐝ₕ - 𝐝ₕ*` of `Xₕ`) with the core `ofComplexCrimeCore F` (comparison: the exact-load modified
elliptic projection of the exact orbit) satisfies:

1. the four conclusions of `approxFEEC` (`ApproxFEEC.Verdict`), on the core `Z` and its closure;
2. the discrete generator is `𝐝ₕ - 𝐝ₕ*`;
3. **discrete constraints**: a subspace `Kₕ ⊆ Xₕ` invariant under `Lₕ` is preserved exactly by
   `e^{tLₕ}` for all `t`, and if `iₕ Kₕ ⊆ K` the residual `dist(ξₕ(t), K)` of the discrete
   solutions from `Kₕ` is exactly `0`;
4. the **Strang estimate** `‖y - iₕ Rₕ y‖ ≤ ‖y - iₕ w‖ + 8 C ε` for every approximant `w` of
   residual `≤ ε`, with the **splitting** of the residual into the inner-product defect at `w` and
   `𝐝ₕ w`, the graph-norm approximation error and the cochain defect, and the **defect bound**
   `‖Δₕ y‖ ≤ ‖(1 - Jₕ) Rₕ y‖ + C ‖y - iₕ Rₕ y‖`; both tend to `0` at admissible states. The
   inner-product defect enters applied to `w`, `𝐝ₕ w` and `Rₕ y` only: at most `‖1 - Jₕ‖` times
   their norms, and at most `‖1 - Jₕ‖_{Vₕ}` times their discrete graph norms
   (`Family.norm_one_sub_J_add_le`, `Family.norm_one_sub_J_apply_le`).

Cf. [HolstStern2012], §3.3, Thm 3.10 (elliptic analogues) -/
theorem approxFEEC_ofComplexCrime {H : HilbertComplex 𝕜 c W} {κ : Type*}
    (F : ApproxComplexCrime.{u} H κ) :
    (ofComplexCrime F).Verdict (ofComplexCrimeCore F) ∧
    -- 2. the discrete generator
    (∀ h, (ofComplexCrime F).L h = F.toFamily.D h - (F.toFamily.D h).adjoint) ∧
    -- 3. discrete constraints
    (∀ h (Kh : Submodule 𝕜 (F.toFamily.X h)), (∀ v ∈ Kh, F.toFamily.L h v ∈ Kh) →
      ∀ v ∈ Kh, ∀ t, ((ofComplexCrime F).group h).S t v ∈ Kh) ∧
    (∀ h (Kh : Submodule 𝕜 (F.toFamily.X h)), (∀ v ∈ Kh, F.toFamily.L h v ∈ Kh) →
      Kh.map (F.toFamily.incl h : F.toFamily.X h →ₗ[𝕜] PiLp 2 W) ≤ F.K →
      ∀ v ∈ Kh, ∀ t, infDist ((ofComplexCrime F).sol h v t) (F.K : Set (PiLp 2 W)) = 0) ∧
    -- 4. the Strang estimate, the residual splitting, the defect bound, and their limits
    (∀ h (y z : PiLp 2 W) (w : F.toFamily.X h) (ε : ℝ), 0 ≤ ε →
      (∀ v, ‖⟪w - F.toFamily.L h w, v⟫_𝕜 - ⟪z, F.toFamily.incl h v⟫_𝕜‖ ≤
        ε * (‖v‖ + ‖F.toFamily.D h v‖)) →
      ‖y - F.toFamily.incl h (F.toFamily.load h z)‖ ≤
        ‖y - F.toFamily.incl h w‖ + 8 * F.toFamily.boundConst * ε) ∧
    (∀ h (y : H.wave.domain) (w : F.toFamily.X h) (δ : ℝ),
      (∀ v, ‖⟪F.toFamily.cochainDefect h y, v⟫_𝕜‖ ≤ δ * (‖v‖ + ‖F.toFamily.D h v‖)) → ∀ v,
      ‖⟪w - F.toFamily.L h w, v⟫_𝕜 - ⟪(y : PiLp 2 W) - H.wave y, F.toFamily.incl h v⟫_𝕜‖ ≤
        (‖(1 - F.toFamily.J h) w‖ + ‖(1 - F.toFamily.J h) (F.toFamily.D h w)‖ +
          F.toFamily.boundConst * (‖(y : PiLp 2 W) - F.toFamily.incl h w‖ +
            ‖H.totalD ⟨y, y.2.1⟩ - F.toFamily.incl h (F.toFamily.D h w)‖) + δ) *
          (‖v‖ + ‖F.toFamily.D h v‖)) ∧
    (∀ h (y z : PiLp 2 W), ‖F.toFamily.load h z - (F.toFamily.incl h).adjoint y‖ ≤
      ‖(1 - F.toFamily.J h) (F.toFamily.load h z)‖ +
        F.toFamily.boundConst * ‖y - F.toFamily.incl h (F.toFamily.load h z)‖) ∧
    (∀ y ∈ F.A, Tendsto (fun h => ‖y - F.toFamily.incl h
      (F.toFamily.load h (y - waveExt H y))‖) F.l (𝓝 0)) ∧
    (∀ y ∈ F.A, Tendsto (fun h => ‖F.toFamily.load h (y - waveExt H y) -
      (F.toFamily.incl h).adjoint y‖) F.l (𝓝 0)) := by
  set S := F.toFamily
  have hinv : ∀ h (Kh : Submodule 𝕜 (S.X h)), (∀ v ∈ Kh, S.L h v ∈ Kh) →
      ∀ v ∈ Kh, ∀ t, ((ofComplexCrime F).group h).S t v ∈ Kh := fun h Kh hK v hv t =>
    mem_of_invariant (S.L h) (diffWave_skew (S.D h)) Kh hK hv t
  refine ⟨approxFEEC _ _, ofComplexCrime_L F, hinv, fun h Kh hK hKK v hv t => ?_,
    fun h y z w ε hε hres => S.norm_sub_incl_load_le h y z w hε hres,
    fun h y w δ hδ v => S.norm_residual_le h y w hδ v, S.norm_load_sub_adjoint_le,
    fun y hy => F.tendsto_incl_load hy, fun y hy => F.tendsto_defect hy⟩
  exact Metric.infDist_zero_of_mem (hKK ⟨_, hinv h Kh hK v hv t, rfl⟩)

end OfComplexCrime

end Families

/-! ### From the split hypotheses: graph-norm approximation and the cochain defect -/

section Split

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

namespace ApproxComplexCrime.Family

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (S : ApproxComplexCrime.Family.{u} H κ)

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- **Consistent approximation from the Holst–Stern hypotheses with a cochain defect**: at
`y ∈ D(L)`, graph-norm approximation (`‖y - iₕ w‖ + ‖𝐝 y - iₕ 𝐝ₕ w‖ → 0`), the inner-product
defect in the graph norm `‖1 - Jₕ‖_{Vₕ} → 0` (implied by `‖1 - Jₕ‖ → 0`,
`tendsto_graphDefect_of_tendsto`) and the cochain defect `κₕ(y) → 0` in the dual discrete graph
norm give approximants whose residual tends to `0` (`norm_residual_le`: the approximants are
bounded in the discrete graph norm, and `1 - Jₕ` enters only at `w` and `𝐝ₕ w`). -/
theorem consistent_of_cochainDefect {l : Filter κ} {y : PiLp 2 W} (hy : y ∈ H.wave.domain)
    (hJ : Tendsto S.graphDefect l (𝓝 0))
    (hgraph : ∀ ε > 0, ∀ᶠ h in l, ∃ w : S.X h,
      ‖y - S.incl h w‖ + ‖H.totalD ⟨y, hy.1⟩ - S.incl h (S.D h w)‖ < ε)
    (hcd : ∀ ε > 0, ∀ᶠ h in l, ∀ v : S.X h,
      ‖⟪S.cochainDefect h ⟨y, hy⟩, v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖S.D h v‖)) :
    ∀ ε > 0, ∀ᶠ h in l, ∃ w : S.X h, ‖y - S.incl h w‖ ≤ ε ∧ ∀ v,
      ‖⟪w - S.L h w, v⟫_𝕜 - ⟪y - waveExt H y, S.incl h v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖S.D h v‖) := by
  intro ε hε
  set C := S.boundConst
  have hC := S.boundConst_nonneg
  set dy := H.totalD ⟨y, hy.1⟩
  set M0 := C * (‖y‖ + ‖dy‖ + 2)
  have hM0 : 0 ≤ M0 := by positivity
  set η := min 1 (ε / (3 * (C + 1)))
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / (3 * (C + 1)) := min_le_right _ _
  set θ := ε / (3 * (2 * M0 + 1))
  have hθ : 0 < θ := by positivity
  filter_upwards [hgraph η hη, Metric.tendsto_nhds.1 hJ θ hθ, hcd (ε / 3) (by positivity)]
    with h ⟨w, hw⟩ hJh hcdh
  rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg (S.graphDefect_nonneg h)] at hJh
  have ha := norm_nonneg (y - S.incl h w)
  have hb := norm_nonneg (dy - S.incl h (S.D h w))
  have hCη : C * η ≤ ε / 3 := by
    have h1 : C * η ≤ C * (ε / (3 * (C + 1))) := mul_le_mul_of_nonneg_left hηε hC
    have h2 : C * (ε / (3 * (C + 1))) ≤ ε / 3 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hεη : η ≤ ε := by
    have : ε / (3 * (C + 1)) ≤ ε := div_le_self hε.le (by nlinarith)
    linarith
  refine ⟨w, by linarith, fun v => ?_⟩
  have hres := S.norm_residual_le h ⟨y, hy⟩ w hcdh v
  rw [waveExt_of_mem hy]
  refine hres.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  -- the three terms
  have hwn : ‖w‖ ≤ C * (‖y‖ + η) := by
    refine (S.norm_le_norm_incl h w).trans (mul_le_mul_of_nonneg_left ?_ hC)
    have := norm_sub_norm_le (S.incl h w) y
    rw [norm_sub_rev] at this
    linarith
  have hDwn : ‖S.D h w‖ ≤ C * (‖dy‖ + η) := by
    refine (S.norm_le_norm_incl h _).trans (mul_le_mul_of_nonneg_left ?_ hC)
    have := norm_sub_norm_le (S.incl h (S.D h w)) dy
    rw [norm_sub_rev] at this
    linarith
  have t1 : ‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖ ≤ ε / 3 := by
    have e1 : ‖w‖ + 2 * ‖S.D h w‖ ≤ 2 * M0 := by
      have : C * (‖y‖ + η) + 2 * (C * (‖dy‖ + η)) ≤ 2 * M0 := by
        have h1 : C * η ≤ C * 1 := mul_le_mul_of_nonneg_left hη1 hC
        have h2 : 0 ≤ C * ‖y‖ := mul_nonneg hC (norm_nonneg _)
        simp only [M0]; nlinarith
      linarith
    have e2 : S.graphDefect h * (‖w‖ + 2 * ‖S.D h w‖) ≤ θ * (2 * M0) :=
      mul_le_mul hJh.le e1 (by positivity) hθ.le
    have e3 : θ * (2 * M0) ≤ ε / 3 := by
      simp only [θ]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith [S.norm_one_sub_J_add_le h w]
  have t2 : C * (‖(⟨y, hy⟩ : H.wave.domain).1 - S.incl h w‖ +
      ‖H.totalD ⟨(⟨y, hy⟩ : H.wave.domain), (⟨y, hy⟩ : H.wave.domain).2.1⟩ -
        S.incl h (S.D h w)‖) ≤ ε / 3 := by
    have : C * (‖y - S.incl h w‖ + ‖dy - S.incl h (S.D h w)‖) ≤ C * η :=
      mul_le_mul_of_nonneg_left hw.le hC
    exact this.trans hCη
  linarith

end ApproxComplexCrime.Family

/-- **An approximating family from the split hypotheses** of Holst–Stern type with a cochain
defect: graph-norm approximation and a cochain defect tending to `0` (dual discrete graph norm)
at the admissible states, and the inner-product defect in the graph norm `‖1 - Jₕ‖_{Vₕ} → 0`
(implied by `‖1 - Jₕ‖ → 0`, `Family.tendsto_graphDefect_of_tendsto`). -/
def ApproxComplexCrime.ofCochainDefect {H : HilbertComplex 𝕜 c W} {κ : Type*}
    (S : ApproxComplexCrime.Family.{u} H κ) (K : Submodule 𝕜 (PiLp 2 W))
    (hK : IsClosed (K : Set (PiLp 2 W))) (l : Filter κ) (A : Set (PiLp 2 W))
    (hA : A ⊆ H.wave.domain) (Z : Submodule 𝕜 (PiLp 2 W)) (hZ : Z ≤ H.wave.domainSq)
    (horbit : ∀ x ∈ Z, ∀ t : ℝ, 0 ≤ t →
      H.waveGroup.S t x ∈ A ∧ H.waveGroup.S t (waveExt H x) ∈ A)
    (hJ : Tendsto S.graphDefect l (𝓝 0))
    (hgraph : ∀ y (hy : y ∈ A), ∀ ε > 0, ∀ᶠ h in l, ∃ w : S.X h,
      ‖y - S.incl h w‖ + ‖H.totalD ⟨y, (hA hy).1⟩ - S.incl h (S.D h w)‖ < ε)
    (hcd : ∀ y (hy : y ∈ A), ∀ ε > 0, ∀ᶠ h in l, ∀ v : S.X h,
      ‖⟪S.cochainDefect h ⟨y, hA hy⟩, v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖S.D h v‖)) :
    ApproxComplexCrime.{u} H κ where
  toFamily := S
  K := K
  isClosed_K := hK
  l := l
  A := A
  A_sub := hA
  Z := Z
  Z_le := hZ
  orbit_mem := horbit
  tendsto_graphDefect := hJ
  consistent y hy := S.consistent_of_cochainDefect (hA hy) hJ (hgraph y hy) (hcd y hy)

end Split

/-! ### The cochain special case: `ofComplex` -/

section Cochain

namespace ApproxComplex.Family

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (S : ApproxComplex.Family.{u} H κ)

/-- **A family of discrete complexes with cochain reading maps is a family of discrete
differential spaces**: `Xₕ = Vₕ` (total space), `𝐝ₕ` its total differential. -/
def toCrimeFamily : ApproxComplexCrime.Family H κ where
  X h := PiLp 2 (S.V h)
  D h := S.D h
  D_D h v := (S.cpx h).totalDL_totalDL v
  incl := S.inclL
  proj := S.projL
  proj_incl := S.projL_inclL
  bound := ⟨S.boundConst, fun h => ⟨S.norm_inclL_le h, S.norm_projL_le h⟩⟩

/-- The inner-product defect in the graph norm is that of the discrete complexes. -/
theorem graphDefect_toCrimeFamily (h : κ) : S.toCrimeFamily.graphDefect h = S.graphDefect h :=
  rfl

/-- **The cochain defect of cochain reading maps vanishes.** -/
theorem cochainDefect_toCrimeFamily (h : κ) (y : H.wave.domain) :
    S.toCrimeFamily.cochainDefect h y = 0 :=
  S.toCrimeFamily.cochainDefect_eq_zero h (S.inclL_mem h) (fun v => (S.inclL_D h v).symm) y

/-- On `D(L)` the modified elliptic projection of `ofComplex` is the exact-load projection:
`Rₕ (y, 𝐝 y) = Bₕ (y - L y)` (`ApproxComplex.Family.G_waveLift`). -/
theorem ellProj_waveLift_eq_load (h : κ) (y : H.wave.domain) :
    S.ellProj h (waveLift H y) = S.toCrimeFamily.load h ((y : PiLp 2 W) - H.wave y) :=
  S.toCrimeFamily.eq_load h ((S.ellProj_sub h _).trans (S.G_waveLift h y))

end ApproxComplex.Family

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

namespace ApproxComplex

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplex.{u} H κ)

/-- **An approximating family of discrete complexes with cochain reading maps is an approximating
family of discrete differential spaces** with zero cochain defect
(`Family.cochainDefect_toCrimeFamily`): admissible states `D(L)`, core `D(L²)`, consistent
approximation from the graph-norm approximation property and the inner-product defect in the graph
norm (that of the discrete complexes, `Family.graphDefect_toCrimeFamily`). -/
def toCrime : ApproxComplexCrime H κ :=
  ApproxComplexCrime.ofCochainDefect F.toFamily.toCrimeFamily F.K F.isClosed_K F.l
    H.wave.domain (fun _ hy => hy) H.wave.domainSq le_rfl
    (fun x hx t _ => ⟨waveGroup_mem_domain H (domainSq_le_domain hx) t,
      waveGroup_mem_domain H (waveExt_mem_domain H hx) t⟩)
    F.tendsto_graphDefect
    (fun y hy ε hε => (F.graphApprox (waveLift H ⟨y, hy⟩) (ε / 2) (half_pos hε)).mono
      fun h ⟨w, hw⟩ => ⟨w, by
        have e1 : y - F.toFamily.inclL h w =
            H.totalD.graphFst (waveLift H ⟨y, hy⟩ - F.toFamily.graphIncl h w) := by
          rw [H.totalD.graphFst.map_sub, F.toFamily.graphFst_graphIncl]; rfl
        have e2 : H.totalD ⟨y, hy.1⟩ - F.toFamily.inclL h (F.toFamily.D h w) =
            H.totalD.graphSnd (waveLift H ⟨y, hy⟩ - F.toFamily.graphIncl h w) := by
          rw [H.totalD.graphSnd.map_sub, F.toFamily.graphSnd_graphIncl]; rfl
        have h1 := norm_graphFst_le (waveLift H ⟨y, hy⟩ - F.toFamily.graphIncl h w)
        have h2 := norm_graphSnd_le (waveLift H ⟨y, hy⟩ - F.toFamily.graphIncl h w)
        change ‖y - F.toFamily.inclL h w‖ +
          ‖H.totalD ⟨y, hy.1⟩ - F.toFamily.inclL h (F.toFamily.D h w)‖ < ε
        rw [e1, e2]
        linarith⟩)
    (fun y hy ε hε => Eventually.of_forall fun h v => by
      rw [F.toFamily.cochainDefect_toCrimeFamily, inner_zero_left, norm_zero]
      positivity)

end ApproxComplex

namespace ApproxFEEC

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplex.{u} H κ)

/-- **`ofComplex` is the cochain special case of `ofComplexCrime`**: the same spaces, generators,
reading maps and left inverses. -/
theorem ofComplexCrime_toCrime : ofComplexCrime F.toCrime = ofComplex F := rfl

/-- **The comparisons agree on `D(L²)`**: the trajectory of `ofComplexCrimeCore F.toCrime` is the
modified elliptic projection `Rₕ (e^{tL} x, 𝐝 e^{tL} x)` of `ofComplexCore F`. -/
theorem ofComplexCrimeCore_toCrime_p (T : ℝ) {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq)
    (h : κ) {t : ℝ} (ht : 0 ≤ t) :
    ((ofComplexCrimeCore F.toCrime).cmp T).p x h t = ((ofComplexCore F).cmp T).p x h t := by
  have hx1 := domainSq_le_domain hx
  rw [ofComplexCrimeCore_cmp, crimeCmp_p_eq F.toCrime T hx h ht, ofComplexCore_cmp_p F T hx1 h ht,
    waveOrbit_of_mem H hx1, F.toFamily.ellProj_waveLift_eq_load,
    waveExt_of_mem (waveGroup_mem_domain H hx1 t)]
  rfl

end ApproxFEEC

namespace ConstrainedFEEC

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ConstrainedFEEC H κ)

/-- **The conforming case of an approximating family of discrete differential spaces**: a
constrained FEEC discretization (subcomplexes `Vₕ ⊆ W` with commuting cochain projections),
read as `F.toComplex.toCrime`. Both Holst–Stern defects vanish (`toCrime_J`,
`toCrime_cochainDefect`), and its discrete solutions are those of the subcomplex scheme
(`toCrime_sol`). [HolstStern2012], §3 -/
abbrev toCrime : ApproxComplexCrime H κ := F.toComplex.toCrime

/-- **Zero inner-product defect**: the reading maps are the inclusions, `Jₕ = iₕ* iₕ = 1`. -/
theorem toCrime_J (h : κ) : F.toCrime.toFamily.J h = 1 := F.toFamily_J h

/-- **Zero cochain defect**: the inclusions are cochain maps. -/
theorem toCrime_cochainDefect (h : κ) (y : H.wave.domain) :
    F.toCrime.toFamily.cochainDefect h y = 0 :=
  F.toFamily.cochainDefect_toCrimeFamily h y

/-- **The discrete solutions are those of the subcomplex scheme** (4.10) of
[QuennevilleBelair2015], through `Vₕ ≅ Xₕ` (`ConstrainedFEEC.toComplex_sol`). -/
theorem toCrime_sol (h : κ) (v : PiLp 2 (F.toFamily.V h)) (t : ℝ) :
    (ApproxFEEC.ofComplexCrime F.toCrime).sol h v t = F.toApprox.sol h (F.toXh h v) t :=
  F.toComplex_sol h v t

end ConstrainedFEEC

end Cochain

/-! ### Rates from complex-level estimates -/

section Rate

namespace ApproxComplexCrime.Family

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (S : ApproxComplexCrime.Family.{u} H κ)

/-- The approximation constant `1 + 8 C` of the Strang lemma. -/
def rateConstA : ℝ := 1 + 8 * S.boundConst

/-- The consistency constant `1 + 8 (1 + C²) + C (1 + 8 C)` of the defect bound. -/
def rateConstD : ℝ := 1 + 8 * (1 + S.boundConst ^ 2) + S.boundConst * (1 + 8 * S.boundConst)

/-- **The Strang lemma with rates**: an approximant `w` of `y` with `‖y - iₕ w‖ ≤ ε` and residual
`≤ ε` gives `‖y - iₕ Bₕ z‖ ≤ (1 + 8 C) ε`. -/
theorem norm_sub_incl_load_le_of_rate (h : κ) (y z : PiLp 2 W) (w : S.X h) {ε : ℝ}
    (hw : ‖y - S.incl h w‖ ≤ ε)
    (hres : ∀ v, ‖⟪w - S.L h w, v⟫_𝕜 - ⟪z, S.incl h v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖S.D h v‖)) :
    ‖y - S.incl h (S.load h z)‖ ≤ S.rateConstA * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hw
  have := S.norm_sub_incl_load_le h y z w hε hres
  unfold rateConstA; nlinarith

/-- **The defect bound with rates**: if moreover `‖(1 - Jₕ) w‖ ≤ ε`, then
`‖Bₕ z - iₕ* y‖ ≤ (1 + 8 (1 + C²) + C (1 + 8 C)) ε`. -/
theorem norm_load_sub_adjoint_le_of_rate (h : κ) (y z : PiLp 2 W) (w : S.X h) {ε : ℝ}
    (hw : ‖y - S.incl h w‖ ≤ ε) (hJw : ‖(1 - S.J h) w‖ ≤ ε)
    (hres : ∀ v, ‖⟪w - S.L h w, v⟫_𝕜 - ⟪z, S.incl h v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖S.D h v‖)) :
    ‖S.load h z - (S.incl h).adjoint y‖ ≤ S.rateConstD * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hw
  set C := S.boundConst
  have hC := S.boundConst_nonneg
  have h1 := S.norm_sub_load_add_le h z w hε hres
  have h2 : ‖w - S.load h z‖ ≤ 8 * ε := by linarith [norm_nonneg (S.D h (w - S.load h z))]
  have h3 := S.norm_sub_incl_load_le_of_rate h y z w hw hres
  have h4 : ‖(1 - S.J h) (S.load h z)‖ ≤ ε + (1 + C ^ 2) * (8 * ε) := by
    have e : (1 - S.J h) (S.load h z) = (1 - S.J h) w - (1 - S.J h) (w - S.load h z) := by
      rw [_root_.map_sub]; abel
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add hJw ?_)
    exact ((1 - S.J h).le_opNorm _).trans (mul_le_mul (S.norm_one_sub_J_le h) h2
      (norm_nonneg _) (by positivity))
  refine (S.norm_load_sub_adjoint_le h y z).trans ?_
  have h5 := mul_le_mul_of_nonneg_left h3 hC
  unfold rateConstD
  unfold rateConstA at h5
  nlinarith

/-- **Rate data from the split estimates**: at `y ∈ D(L)`, an approximant `w` with graph-norm
error `‖y - iₕ w‖ + ‖𝐝 y - iₕ 𝐝ₕ w‖ ≤ Eₐ`, inner-product defect
`‖(1 - Jₕ) w‖ + ‖(1 - Jₕ) 𝐝ₕ w‖ ≤ E_β` and a cochain defect `≤ E_γ` in the dual discrete graph
norm satisfies `‖y - iₕ w‖ ≤ Eₐ`, `‖(1 - Jₕ) w‖ ≤ E_β` and has residual `≤ E_β + C Eₐ + E_γ`
(`norm_residual_le`). For an approximant of size `‖w‖ + ‖𝐝ₕ w‖ ≤ E_w`, one can take
`E_β = ‖1 - Jₕ‖ E_w` (`norm_one_sub_J_add_le_opNorm`) or `E_β = 2 ‖1 - Jₕ‖_{Vₕ} E_w`
(`norm_one_sub_J_add_le`). -/
theorem rateData_of_split (h : κ) (y : H.wave.domain) (w : S.X h) {Ea Eb Eg : ℝ}
    (ha : ‖(y : PiLp 2 W) - S.incl h w‖ + ‖H.totalD ⟨y, y.2.1⟩ - S.incl h (S.D h w)‖ ≤ Ea)
    (hb : ‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖ ≤ Eb)
    (hcd : ∀ v, ‖⟪S.cochainDefect h y, v⟫_𝕜‖ ≤ Eg * (‖v‖ + ‖S.D h v‖)) :
    ‖(y : PiLp 2 W) - S.incl h w‖ ≤ Ea ∧ ‖(1 - S.J h) w‖ ≤ Eb ∧
      ∀ v, ‖⟪w - S.L h w, v⟫_𝕜 - ⟪(y : PiLp 2 W) - H.wave y, S.incl h v⟫_𝕜‖ ≤
        (Eb + S.boundConst * Ea + Eg) * (‖v‖ + ‖S.D h v‖) := by
  have hd := norm_nonneg (H.totalD ⟨y, y.2.1⟩ - S.incl h (S.D h w))
  refine ⟨by linarith, by linarith [norm_nonneg ((1 - S.J h) (S.D h w))], fun v => ?_⟩
  refine (S.norm_residual_le h y w hcd v).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have e := mul_le_mul_of_nonneg_left ha S.boundConst_nonneg
  linarith

end ApproxComplexCrime.Family

/-- **Combining the orders**: for `0 ≤ m ≤ 1` and orders `α, β, γ ≥ 0`,
`A mᵅ + B m^β + G m^γ ≤ (A + B + G) m^{min(α, β, γ)}` (`A, B, G ≥ 0`). -/
theorem add_rpow_le_rpow_min {m α β γ A B G : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G) :
    A * m ^ α + B * m ^ β + G * m ^ γ ≤ (A + B + G) * m ^ min α (min β γ) := by
  have hμ : 0 ≤ min α (min β γ) := le_min hα (le_min hβ hγ)
  have h1 : m ^ α ≤ m ^ min α (min β γ) :=
    Real.rpow_le_rpow_of_exponent_ge' hm0 hm1 hμ (min_le_left _ _)
  have h2 : m ^ β ≤ m ^ min α (min β γ) :=
    Real.rpow_le_rpow_of_exponent_ge' hm0 hm1 hμ ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : m ^ γ ≤ m ^ min α (min β γ) :=
    Real.rpow_le_rpow_of_exponent_ge' hm0 hm1 hμ ((min_le_right _ _).trans (min_le_right _ _))
  nlinarith [mul_le_mul_of_nonneg_left h1 hA, mul_le_mul_of_nonneg_left h2 hB,
    mul_le_mul_of_nonneg_left h3 hG]

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

namespace ApproxComplexCrime

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplexCrime.{u} H κ)

open ApproxFEEC in
/-- **A rate class from complex-level rate data**. Data `Dc ⊆ Z` with a class norm `‖·‖_c`, a mesh
size `m` and an order `α`: if along the exact trajectory, for `y = e^{tL} x` and `y = e^{tL} L x`,
`t ∈ [0, T]`, there are approximants `w` with `‖y - iₕ w‖`, `‖(1 - Jₕ) w‖` and the residual (dual
discrete graph norm) all `≤ Cₐ m(h)ᵅ ‖x‖_c`, then the load Ritz projection on `Dc` gives a rate
class (`DissipFEEC.Ritz.orbitRateClass`, with the Strang lemma and the defect bound along the
orbit) with `C = (1 + 8 C_ι) Cₐ` and
`C' = 2 (1 + 8 (1 + C_ι²) + C_ι (1 + 8 C_ι)) Cₐ`. The data can be assembled from graph-norm best
approximation `O(mᵅ)`, inner-product defect `O(m^β)` and cochain defect `O(m^γ)`, at order
`min(α, β, γ)`, by `rateClass_of_split` (through `rateData_of_split` and `add_rpow_le_rpow_min`). -/
def rateClass (T : ℝ) (Dc : Set (PiLp 2 W)) (hDc : Dc ⊆ (F.Z : Set (PiLp 2 W)))
    (cn : PiLp 2 W → ℝ) (m : κ → ℝ) (α Ca : ℝ)
    (hrate : ∀ x ∈ Dc, ∀ h, ∀ t ∈ Icc 0 T, ∀ y ∈ ({H.waveGroup.S t x,
      H.waveGroup.S t (waveExt H x)} : Set (PiLp 2 W)), ∃ w : F.toFamily.X h,
      ‖y - F.toFamily.incl h w‖ ≤ Ca * m h ^ α * cn x ∧
      ‖(1 - F.toFamily.J h) w‖ ≤ Ca * m h ^ α * cn x ∧
      ∀ v, ‖⟪w - F.toFamily.L h w, v⟫_𝕜 - ⟪y - waveExt H y, F.toFamily.incl h v⟫_𝕜‖ ≤
        Ca * m h ^ α * cn x * (‖v‖ + ‖F.toFamily.D h v‖)) :
    (ofComplexCrime F).RateClass T :=
  (loadRitz F).orbitRateClass Dc (fun _ hx =>
      DissipFEEC.domainSq_le_resData (ofComplexCrime F).isMDissipative (F.Z_le (hDc hx)))
    cn m α (F.toFamily.rateConstA * Ca) (2 * F.toFamily.rateConstD * Ca)
    (fun x hx h t ht => by
      obtain ⟨w, hw, -, hres⟩ := hrate x hx h t ht _ (Set.mem_insert _ _)
      change ‖(ofComplexCrime F).S t x - F.toFamily.incl h (F.toFamily.load h
        ((ofComplexCrime F).S t x - DissipFEEC.genExt H.wave ((ofComplexCrime F).S t x)))‖ ≤ _
      rw [(ofComplexCrime F).S_eq_waveGroup ht.1, ← waveExt_eq_genExt]
      calc _ ≤ _ := F.toFamily.norm_sub_incl_load_le_of_rate h _ _ w hw hres
        _ = _ := by ring)
    (fun x hx h t ht => by
      have hx2 := F.Z_le (hDc hx)
      have hx1 := domainSq_le_domain hx2
      have hLx := waveExt_mem_domain H hx2
      obtain ⟨w, hw, hJw, hres⟩ := hrate x hx h t ht _ (Set.mem_insert _ _)
      obtain ⟨w', hw', hJw', hres'⟩ := hrate x hx h t ht _
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have d1 := F.toFamily.norm_load_sub_adjoint_le_of_rate h _ _ w hw hJw hres
      have d2 := F.toFamily.norm_load_sub_adjoint_le_of_rate h _ _ w' hw' hJw' hres'
      change ‖loadDefect F h ((ofComplexCrime F).S t (DissipFEEC.genExt H.wave x) -
          DissipFEEC.genExt H.wave ((ofComplexCrime F).S t (DissipFEEC.genExt H.wave x)))‖ +
        ‖-loadDefect F h ((ofComplexCrime F).S t x -
          DissipFEEC.genExt H.wave ((ofComplexCrime F).S t x))‖ ≤ _
      rw [(ofComplexCrime F).S_eq_waveGroup ht.1, ← waveExt_eq_genExt, norm_neg,
        loadDefect_apply F h (waveGroup_mem_domain H hLx t),
        loadDefect_apply F h (waveGroup_mem_domain H hx1 t)]
      calc _ ≤ F.toFamily.rateConstD * (Ca * m h ^ α * cn x) +
            F.toFamily.rateConstD * (Ca * m h ^ α * cn x) := add_le_add d2 d1
        _ = _ := by ring)

/-- **The error bound of a rate class of `ofComplexCrime`** (the rate clause of the verdict,
`dissipFEEC_rate`, from the comparison initial value): `‖e^{tL} x - iₕ e^{tLₕ} pₕ(0)‖ ≤
(C + C_ι C' t) m(h)ᵅ ‖x‖_c` on `[0, T]`, with `C_ι` the uniform bound of the reading maps. -/
theorem error_le_of_rateClass {T : ℝ} (R : (ApproxFEEC.ofComplexCrime F).RateClass T)
    {x : PiLp 2 W} (hx : x ∈ R.Data) (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖H.waveGroup.S t x - (ApproxFEEC.ofComplexCrime F).sol h (R.p x h 0) t‖ ≤
      (R.C + F.toFamily.boundConst * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) := by
  have hr := dissipFEEC_rate _ R hx h (R.p x h 0) ht
  rw [ApproxFEEC.S_eq_waveGroup _ ht.1, sub_self, norm_zero, mul_zero, add_zero] at hr
  refine hr.trans ?_
  have h0 : 0 ≤ R.C' * (R.meshSize h ^ R.α * R.classNorm x) := by
    have := (norm_nonneg _).trans (R.consistency x hx h t ht)
    linarith [show R.C' * R.meshSize h ^ R.α * R.classNorm x =
      R.C' * (R.meshSize h ^ R.α * R.classNorm x) by ring]
  have hI : ‖(ApproxFEEC.ofComplexCrime F).incl h‖ ≤ F.toFamily.boundConst :=
    F.toFamily.norm_incl_le h
  have hpos : 0 ≤ t * (R.C' * (R.meshSize h ^ R.α * R.classNorm x)) := mul_nonneg ht.1 h0
  have e1 : (R.C + ‖(ApproxFEEC.ofComplexCrime F).incl h‖ * R.C' * t) *
      (R.meshSize h ^ R.α * R.classNorm x) = R.C * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖(ApproxFEEC.ofComplexCrime F).incl h‖ *
          (t * (R.C' * (R.meshSize h ^ R.α * R.classNorm x))) := by
    ring
  have e2 : (R.C + F.toFamily.boundConst * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) =
      R.C * (R.meshSize h ^ R.α * R.classNorm x) +
        F.toFamily.boundConst * (t * (R.C' * (R.meshSize h ^ R.α * R.classNorm x))) := by ring
  rw [e1, e2]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hI hpos)

end ApproxComplexCrime

/-! #### The conforming case: rates through `ofComplex` -/

namespace ConstrainedFEEC

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ConstrainedFEEC H κ)

/-- A point of the discrete graph space `Kₕ` is the lift of an element of the discrete complex. -/
theorem exists_graphIncl_eq {h : κ} {w : H.totalD.GraphSpace} (hw : w ∈ F.Kh h) :
    ∃ u : PiLp 2 (F.toFamily.V h), F.toFamily.graphIncl h u = w :=
  ⟨WithLp.toLp 2 fun i => ⟨H.totalD.graphFst w i, hw i⟩,
    H.totalD.graphFst_injective (PiLp.ext fun _ => rfl)⟩

/-- **The rate classes of a constrained FEEC discretization are rate classes of `ofComplex`**
(through `ofComplexCrime F.toComplex.toCrime = ofComplex F.toComplex`): graph-norm best
approximation `O(hᵅ)` along the trajectory, zero inner-product defect and zero cochain defect,
with `Cₐ = 2 (1 + C_ι) R.C`. Through `dissipFEEC_rate` the error has the factor
`C₁ + C₂ t`, not `(1 + C_P)(1 + t)²`. -/
def RateClass.toCrimeRate {T : ℝ} (R : F.RateClass T) :
    (ApproxFEEC.ofComplexCrime F.toComplex.toCrime).RateClass T :=
  F.toComplex.toCrime.rateClass T R.Data
    (fun x hx => mem_domainSq.2 ⟨R.mem_domain x hx, R.mem_domain_sq x _ hx⟩)
    R.classNorm R.meshSize R.α (2 * (1 + F.toFamily.toCrimeFamily.boundConst) * R.C)
    fun x hx h t ht y hy => by
      set S := F.toFamily
      have hx1 := R.mem_domain x hx
      have hC := S.toCrimeFamily.boundConst_nonneg
      have key : ∀ (y : H.wave.domain) (w : H.totalD.GraphSpace), w ∈ F.Kh h →
          ‖waveLift H y - w‖ ≤ R.C * R.meshSize h ^ R.α * R.classNorm x →
          ∃ u : F.toComplex.toCrime.toFamily.X h,
            ‖(y : PiLp 2 W) - F.toComplex.toCrime.toFamily.incl h u‖ ≤
              2 * (1 + S.toCrimeFamily.boundConst) * R.C * R.meshSize h ^ R.α * R.classNorm x ∧
            ‖(1 - F.toComplex.toCrime.toFamily.J h) u‖ ≤
              2 * (1 + S.toCrimeFamily.boundConst) * R.C * R.meshSize h ^ R.α * R.classNorm x ∧
            ∀ v, ‖⟪u - F.toComplex.toCrime.toFamily.L h u, v⟫_𝕜 -
              ⟪(y : PiLp 2 W) - waveExt H y, F.toComplex.toCrime.toFamily.incl h v⟫_𝕜‖ ≤
              2 * (1 + S.toCrimeFamily.boundConst) * R.C * R.meshSize h ^ R.α * R.classNorm x *
                (‖v‖ + ‖F.toComplex.toCrime.toFamily.D h v‖) := by
        intro y w hw hle
        obtain ⟨u, rfl⟩ := F.exists_graphIncl_eq hw
        set Rc := R.C * R.meshSize h ^ R.α * R.classNorm x
        have hRc : 0 ≤ Rc := (norm_nonneg _).trans hle
        have e1 : (y : PiLp 2 W) - S.inclL h u =
            H.totalD.graphFst (waveLift H y - S.graphIncl h u) := by
          rw [H.totalD.graphFst.map_sub, S.graphFst_graphIncl]; rfl
        have e2 : H.totalD ⟨y, y.2.1⟩ - S.inclL h (S.D h u) =
            H.totalD.graphSnd (waveLift H y - S.graphIncl h u) := by
          rw [H.totalD.graphSnd.map_sub, S.graphSnd_graphIncl]; rfl
        have ha : ‖(y : PiLp 2 W) - S.inclL h u‖ ≤ Rc := by
          rw [e1]; exact (norm_graphFst_le _).trans hle
        have hb : ‖H.totalD ⟨y, y.2.1⟩ - S.inclL h (S.D h u)‖ ≤ Rc := by
          rw [e2]; exact (norm_graphSnd_le _).trans hle
        have hJ : S.toCrimeFamily.J h = 1 := F.toFamily_J h
        have hres := fun v => (S.toCrimeFamily.norm_residual_le h y u (δ := 0) (fun v => by
          rw [S.cochainDefect_toCrimeFamily, inner_zero_left, norm_zero, zero_mul]) v).trans
          (mul_le_mul_of_nonneg_right (add_le_add_left (add_le_add_left
            (S.toCrimeFamily.norm_one_sub_J_add_le_opNorm h u) _) _) (by positivity))
        refine ⟨u, ?_, ?_, fun v => ?_⟩
        · change ‖(y : PiLp 2 W) - S.inclL h u‖ ≤ _
          nlinarith
        · change ‖(1 - S.toCrimeFamily.J h) u‖ ≤ _
          refine ((1 - S.toCrimeFamily.J h).le_opNorm u).trans ?_
          rw [hJ, sub_self, norm_zero, zero_mul]
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (1 + S.toCrimeFamily.boundConst)) hRc]
        · have h1 := hres v
          rw [hJ, sub_self, norm_zero, zero_mul, zero_add, add_zero] at h1
          rw [waveExt_of_mem y.2]
          refine h1.trans (mul_le_mul_of_nonneg_right ?_
            (add_nonneg (norm_nonneg _) (norm_nonneg _)))
          change S.toCrimeFamily.boundConst * (‖(y : PiLp 2 W) - S.inclL h u‖ +
            ‖H.totalD ⟨y, y.2.1⟩ - S.inclL h (S.D h u)‖) ≤ _
          nlinarith
      rcases hy with rfl | hy
      · obtain ⟨w, hw, hle⟩ := R.approx x hx h t ht
          (waveLift H ⟨_, waveGroup_mem_domain H hx1 t⟩) rfl
        exact key ⟨_, waveGroup_mem_domain H hx1 t⟩ w hw hle
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        have hLx : waveExt H x ∈ H.wave.domain := by
          rw [waveExt_of_mem hx1]; exact R.mem_domain_sq x hx1 hx
        obtain ⟨w, hw, hle⟩ := R.approx_deriv x hx1 hx h t ht
          (waveLift H ⟨_, waveGroup_mem_domain H hLx t⟩) (by
            change H.waveGroup.S t (waveExt H x) = _
            rw [waveExt_of_mem hx1])
        exact key ⟨_, waveGroup_mem_domain H hLx t⟩ w hw hle

variable {F} in
/-- **The rate of a constrained FEEC discretization through the discrete complex**: for data in a
rate class `R` on `[0, T]`, the discrete solution of `ofComplex F.toComplex` from the modified
elliptic projection `Rₕ (x, 𝐝 x)` of the datum (the comparison of `ofComplexCore`) satisfies
`‖e^{tL} x - iₕ e^{tLₕ} Rₕ x‖ ≤ (C + C_ι C' t) hᵅ ‖x‖_class`, with the constants of
`RateClass.toCrimeRate` (`error_le_of_rateClass`, `ofComplexCrimeCore_toCrime_p`). -/
theorem RateClass.norm_sub_ofComplex_le {T : ℝ} (R : F.RateClass T) {x : PiLp 2 W}
    (hx : x ∈ R.Data) (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖H.waveGroup.S t x - (ApproxFEEC.ofComplex F.toComplex).sol h
        (((ApproxFEEC.ofComplexCore F.toComplex).cmp T).p x h 0) t‖ ≤
      (R.toCrimeRate.C + F.toComplex.toCrime.toFamily.boundConst * R.toCrimeRate.C' * t) *
        (R.meshSize h ^ R.α * R.classNorm x) := by
  rw [← ApproxFEEC.ofComplexCrimeCore_toCrime_p F.toComplex T
    (mem_domainSq.2 ⟨R.mem_domain x hx, R.mem_domain_sq x _ hx⟩) h le_rfl]
  exact F.toComplex.toCrime.error_le_of_rateClass R.toCrimeRate hx h ht

end ConstrainedFEEC

end Rate

/-! ### From a Galerkin core: discretizations whose comparison is a Galerkin projection -/

section Galerkin

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*}

/-- **The discrete differential spaces of an approximating FEEC discretization** with a
differential `𝐝ₕ` on its spaces: the same spaces, reading maps and left inverses. When
`Lₕ = 𝐝ₕ - 𝐝ₕ*` the discretization is `ofComplexCrime` of it (`ofComplexCrime_ofGalerkinCore_sol`).
-/
def ApproxComplexCrime.Family.ofApproxFEEC (F : ApproxFEEC.{u} H κ)
    [hfd : ∀ h, FiniteDimensional 𝕜 (F.X h)] (D : ∀ h, F.X h →L[𝕜] F.X h)
    (hDD : ∀ h v, D h (D h v) = 0) : ApproxComplexCrime.Family.{u} H κ where
  X := F.X
  normedAddCommGroup := F.normedAddCommGroup
  innerProductSpace := F.innerProductSpace
  completeSpace := F.completeSpace
  finiteDimensional := hfd
  normedSpaceReal := F.normedSpaceReal
  isScalarTower := F.isScalarTower
  D := D
  D_D := hDD
  incl := F.incl
  proj := F.proj
  proj_incl := F.proj_incl
  bound := F.bound

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- Orthogonal reading maps have no inner-product defect: `Jₕ = 1`. -/
theorem ApproxComplexCrime.Family.ofApproxFEEC_J (F : ApproxFEEC.{u} H κ)
    [hfd : ∀ h, FiniteDimensional 𝕜 (F.X h)] (D : ∀ h, F.X h →L[𝕜] F.X h)
    (hDD : ∀ h v, D h (D h v) = 0) (hF : F.IsOrthogonal) (h : κ) :
    (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).J h = 1 :=
  ContinuousLinearMap.ext fun v => ext_inner_right 𝕜 fun w => by
    rw [ApproxComplexCrime.Family.inner_J, one_apply_eq_self]
    exact hF.inner_incl h v w

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- Orthogonal reading maps have no inner-product defect in the graph norm either. -/
theorem ApproxComplexCrime.Family.tendsto_graphDefect_ofApproxFEEC (F : ApproxFEEC.{u} H κ)
    [hfd : ∀ h, FiniteDimensional 𝕜 (F.X h)] (D : ∀ h, F.X h →L[𝕜] F.X h)
    (hDD : ∀ h v, D h (D h v) = 0) (hF : F.IsOrthogonal) :
    Tendsto (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).graphDefect F.l (𝓝 0) :=
  tendsto_const_nhds.congr fun h =>
    (((ApproxComplexCrime.Family.ofApproxFEEC F D hDD).graphDefect_eq_zero_iff h).2
      (ApproxComplexCrime.Family.ofApproxFEEC_J F D hDD hF h)).symm

variable (H) in
/-- The **orbit states** of a set `Z ⊆ D(L²)`: `e^{tL} x` and `e^{tL} L x`, `x ∈ Z`, `t ≥ 0`. -/
def orbitStates (Z : Set (PiLp 2 W)) : Set (PiLp 2 W) :=
  {y | ∃ x ∈ Z, ∃ t : ℝ, 0 ≤ t ∧ (y = H.waveGroup.S t x ∨ y = H.waveGroup.S t (waveExt H x))}

theorem orbitStates_sub {Z : Set (PiLp 2 W)} (hZ : Z ⊆ H.wave.domainSq) :
    orbitStates H Z ⊆ H.wave.domain := by
  rintro y ⟨x, hx, t, -, rfl | rfl⟩
  · exact waveGroup_mem_domain H (domainSq_le_domain (hZ hx)) t
  · exact waveGroup_mem_domain H (waveExt_mem_domain H (hZ hx)) t

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- Orthogonal reading maps: `ιₕ* = πₕ`. -/
theorem ApproxFEEC.IsOrthogonal.adjoint_incl {F : ApproxFEEC.{u} H κ} (hF : F.IsOrthogonal)
    (h : κ) : (F.incl h).adjoint = F.proj h :=
  ContinuousLinearMap.ext fun y => ext_inner_right 𝕜 fun a => by
    rw [ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm, hF.inner_incl_left,
      inner_conj_symm]

section Bridge

variable (F : ApproxFEEC.{u} H κ) [hfd : ∀ h, FiniteDimensional 𝕜 (F.X h)] (hF : F.IsOrthogonal)
  (D : ∀ h, F.X h →L[𝕜] F.X h) (hDD : ∀ h v, D h (D h v) = 0)
  (hJ : Tendsto (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).graphDefect F.l (𝓝 0))
  (hL : ∀ h, F.L h = diffWave (D h)) (Z0 : F.Core) (hZ : Z0.Data ≤ H.wave.domainSq)
  (hgal : ∀ T, ∀ x ∈ Z0.Data, ∀ h, ∀ t ∈ Ico 0 T,
    (Z0.cmp T).p x h t - F.L h ((Z0.cmp T).p x h t) =
      (F.incl h).adjoint (H.waveGroup.S t x - H.waveGroup.S t (waveExt H x)))
  (hcl : ∀ x ∈ Z0.Data, ∀ t : ℝ, 0 ≤ t →
    H.waveGroup.S t (waveExt H x) ∈ Z0.Data.topologicalClosure)

include hL hgal in
/-- **The Galerkin comparison is the exact-load elliptic projection**: on `[0, T)`,
`pₕ(t) = Bₕ (e^{tL} x - e^{tL} L x)`. -/
theorem galerkin_p_eq {T : ℝ} {x : PiLp 2 W} (hx : x ∈ Z0.Data) (h : κ) {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    (Z0.cmp T).p x h t = (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).load h
      (H.waveGroup.S t x - H.waveGroup.S t (waveExt H x)) :=
  (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).eq_load h (by
    have e := hgal T x hx h t ht
    rw [hL] at e
    exact e)

include hL hgal hZ in
/-- **The derivative of the Galerkin comparison is the exact-load elliptic projection of the
derivative** (uniqueness of one-sided derivatives): `pₕ'(t) = Bₕ (e^{tL} L x - e^{tL} L² x)`. -/
theorem galerkin_p'_eq {T : ℝ} {x : PiLp 2 W} (hx : x ∈ Z0.Data) (h : κ) {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    (Z0.cmp T).p' x h t = (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).load h
      (H.waveGroup.S t (waveExt H x) - H.waveGroup.S t (waveExt H (waveExt H x))) := by
  set S := ApproxComplexCrime.Family.ofApproxFEEC F D hDD
  have hx2 := hZ hx
  have hx' : x ∈ (Z0.cmp T).Data := by rw [Z0.data_eq]; exact hx
  have hp := (Z0.cmp T).hasDerivWithinAt x hx' h t ht
  have hq : HasDerivAt (fun s => S.load h (H.waveGroup.S s x - H.waveGroup.S s (waveExt H x)))
      (S.load h (H.waveGroup.S t (waveExt H x) - H.waveGroup.S t (waveExt H (waveExt H x)))) t :=
    ((S.load h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_waveGroup_waveExt H (domainSq_le_domain hx2) t).sub
        (hasDerivAt_waveGroup_waveExt H (waveExt_mem_domain H hx2) t))
  have heq : (Z0.cmp T).p x h =ᶠ[𝓝[Ici t] t]
      fun s => S.load h (H.waveGroup.S s x - H.waveGroup.S s (waveExt H x)) := by
    filter_upwards [Ico_mem_nhdsGE ht.2] with s hs
    exact galerkin_p_eq F D hDD hL Z0 hgal hx h ⟨ht.1.trans hs.1, hs.2⟩
  have hq' := hq.hasDerivWithinAt.congr_of_eventuallyEq heq
    (galerkin_p_eq F D hDD hL Z0 hgal hx h ht)
  exact (uniqueDiffWithinAt_Ici t).eq_deriv _ hp hq'

include hJ hL hgal in
/-- **`iₕ iₕ* → 1` on the closure of a Galerkin core** (for orthogonal reading maps `iₕ* = πₕ`,
`DissipFEEC.tendsto_incl_proj`). At a point `x` of the core the comparison `pₕ(0) = Bₕ (x - L x)`
approximates `x` and is bounded in the discrete graph norm, so with `‖1 - Jₕ‖_{Vₕ} → 0`,
`iₕ iₕ* x - x = iₕ iₕ* (x - iₕ pₕ(0)) - iₕ (1 - Jₕ) pₕ(0) + (iₕ pₕ(0) - x) → 0`
(`Family.norm_one_sub_J_load_le`); the uniform bound `‖iₕ iₕ*‖ ≤ C²` carries it to the closure
(`ContinuousLinearMap.tendsto_apply_of_mem_closure`). -/
theorem tendsto_incl_adjoint_galerkin {z : PiLp 2 W} (hz : z ∈ Z0.Data.topologicalClosure) :
    Tendsto (fun h => F.incl h ((F.incl h).adjoint z)) F.l (𝓝 z) := by
  set S := ApproxComplexCrime.Family.ofApproxFEEC F D hDD
  have hC := S.boundConst_nonneg
  refine ContinuousLinearMap.tendsto_apply_of_mem_closure
    (T := fun h => S.incl h ∘L (S.incl h).adjoint) (M := S.boundConst ^ 2) (fun h => ?_)
    continuous_id' (s := Z0.Data) (fun x hx => ?_) (by rwa [← Submodule.topologicalClosure_coe])
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [ContinuousLinearMap.adjoint.norm_map, pow_two]
    exact mul_le_mul (S.norm_incl_le h) (S.norm_incl_le h) (norm_nonneg _) hC
  · have hx1 : x ∈ Z0.Data := hx
    have hv : ∀ h, (Z0.cmp 1).p x h 0 = S.load h (x - waveExt H x) := fun h => by
      simpa only [C0Group.S_zero_apply] using
        galerkin_p_eq F D hDD hL Z0 hgal hx1 h (T := 1) ⟨le_rfl, one_pos⟩
    have h1 := tendsto_iff_norm_sub_tendsto_zero.1 (Z0.tendsto_incl_p zero_le_one hx1)
    have h2 : Tendsto (fun h => (S.boundConst ^ 2 + 1) * ‖F.incl h ((Z0.cmp 1).p x h 0) - x‖ +
        S.boundConst * (S.graphDefect h * (8 * S.boundConst * ‖x - waveExt H x‖))) F.l
        (𝓝 0) := by
      simpa using (h1.const_mul (S.boundConst ^ 2 + 1)).add
        ((hJ.mul_const (8 * S.boundConst * ‖x - waveExt H x‖)).const_mul S.boundConst)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun h => ?_) h2
    set v := (Z0.cmp 1).p x h 0
    have e : F.incl h ((F.incl h).adjoint x) - x =
        F.incl h ((F.incl h).adjoint (x - F.incl h v)) -
          F.incl h (v - (F.incl h).adjoint (F.incl h v)) + (F.incl h v - x) := by
      simp only [_root_.map_sub]
      abel
    have b1 : ‖F.incl h ((F.incl h).adjoint (x - F.incl h v))‖ ≤
        S.boundConst ^ 2 * ‖F.incl h v - x‖ := by
      refine (S.norm_incl_apply_le h _).trans ?_
      rw [pow_two, mul_assoc, norm_sub_rev (F.incl h v)]
      exact mul_le_mul_of_nonneg_left (S.norm_adjoint_incl_apply_le h _) hC
    have b2 : ‖F.incl h (v - (F.incl h).adjoint (F.incl h v))‖ ≤
        S.boundConst * (S.graphDefect h * (8 * S.boundConst * ‖x - waveExt H x‖)) := by
      refine (S.norm_incl_apply_le h _).trans (mul_le_mul_of_nonneg_left ?_ hC)
      have hv' : v = S.load h (x - waveExt H x) := hv h
      calc _ = ‖(1 - S.J h) v‖ := rfl
        _ ≤ _ := by rw [hv']; exact S.norm_one_sub_J_load_le h _
    have b3 := norm_sub_le (F.incl h ((F.incl h).adjoint (x - F.incl h v)))
      (F.incl h (v - (F.incl h).adjoint (F.incl h v)))
    have b4 := norm_add_le (F.incl h ((F.incl h).adjoint (x - F.incl h v)) -
      F.incl h (v - (F.incl h).adjoint (F.incl h v))) (F.incl h v - x)
    change ‖F.incl h ((F.incl h).adjoint x) - x‖ ≤ (S.boundConst ^ 2 + 1) * ‖F.incl h v - x‖ +
      S.boundConst * (S.graphDefect h * (8 * S.boundConst * ‖x - waveExt H x‖))
    rw [e]
    nlinarith

include hJ hL hgal hZ hcl in
/-- **Convergence of the exact-load elliptic projection at the orbit states of a Galerkin core**:
`iₕ Rₕ y → y` for `y = e^{tL} x` (the approximation of the core) and for `y = e^{tL} L x` (the
consistency of the core, the Galerkin identity
`iₕ* y' - pₕ' = -(pₕ' - Lₕ pₕ) + iₕ* (y - iₕ pₕ) - (1 - Jₕ) pₕ`, `y' = e^{tL} L x`, the
inner-product defect at the comparison `pₕ = Bₕ (y - y')`, which is bounded in the discrete graph
norm, and `iₕ iₕ* → 1` on the closure of the core, `tendsto_incl_adjoint_galerkin`). -/
theorem tendsto_reading_galerkin {y : PiLp 2 W} (hy : y ∈ orbitStates H Z0.Data) :
    Tendsto (fun h => ‖y - (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).incl h
      ((ApproxComplexCrime.Family.ofApproxFEEC F D hDD).load h (y - waveExt H y))‖) F.l
      (𝓝 0) := by
  set S := ApproxComplexCrime.Family.ofApproxFEEC F D hDD
  obtain ⟨x, hx, t, ht0, rfl | rfl⟩ := hy
  · have hx2 := hZ hx
    have ht : t ∈ Ico 0 (t + 1) := ⟨ht0, by linarith⟩
    have h1 := (Z0.tendsto_approx (t + 1) x hx).tendsto_at (Ico_subset_Icc_self ht)
    rw [F.S_eq_waveGroup ht0] at h1
    have h2 := tendsto_iff_norm_sub_tendsto_zero.1 h1
    refine h2.congr fun h => ?_
    rw [norm_sub_rev, waveExt_waveGroup H (domainSq_le_domain hx2),
      galerkin_p_eq F D hDD hL Z0 hgal hx h ht]
    rfl
  · have hx2 := hZ hx
    have hLx := waveExt_mem_domain H hx2
    have ht : t ∈ Ico 0 (t + 1) := ⟨ht0, by linarith⟩
    set T := t + 1
    set p := fun h => (Z0.cmp T).p x h t
    set p' := fun h => (Z0.cmp T).p' x h t
    set y := H.waveGroup.S t x
    set y' := H.waveGroup.S t (waveExt H x)
    have hda : Tendsto (fun h => ‖F.incl h (p h) - y‖) F.l (𝓝 0) := by
      have := tendsto_iff_norm_sub_tendsto_zero.1
        ((Z0.tendsto_approx T x hx).tendsto_at (Ico_subset_Icc_self ht))
      rw [F.S_eq_waveGroup ht0] at this
      exact this
    have hdd : Tendsto (fun h => ‖p' h - F.L h (p h)‖) F.l (𝓝 0) := by
      have := (Z0.tendsto_defect T x hx).tendsto_at (Ico_subset_Icc_self ht)
      exact this
    have hii := tendsto_iff_norm_sub_tendsto_zero.1
      (tendsto_incl_adjoint_galerkin F D hDD hJ hL Z0 hgal (hcl x hx t ht0))
    have hC := S.boundConst_nonneg
    have key : ∀ h, ‖y' - F.incl h (p' h)‖ ≤ ‖F.incl h ((F.incl h).adjoint y') - y'‖ +
        S.boundConst * (‖p' h - F.L h (p h)‖ + S.boundConst * ‖F.incl h (p h) - y‖ +
          ‖(1 - S.J h) (p h)‖) := fun h => by
      have hg := hgal T x hx h t ht
      have e1 : (F.incl h).adjoint y' - p' h = -(p' h - F.L h (p h)) +
          ((F.incl h).adjoint (y - F.incl h (p h)) -
            (p h - (F.incl h).adjoint (F.incl h (p h)))) := by
        have hLp : F.L h (p h) = p h - (F.incl h).adjoint (y - y') := by rw [← hg]; abel
        rw [hLp]
        simp only [_root_.map_sub]
        abel
      have e2 : y' - F.incl h (p' h) = (y' - F.incl h ((F.incl h).adjoint y')) +
          F.incl h ((F.incl h).adjoint y' - p' h) := by rw [_root_.map_sub]; abel
      have b1 : ‖F.incl h ((F.incl h).adjoint y' - p' h)‖ ≤
          S.boundConst * ‖(F.incl h).adjoint y' - p' h‖ :=
        S.norm_incl_apply_le h _
      have b2 : ‖(F.incl h).adjoint (y - F.incl h (p h))‖ ≤
          S.boundConst * ‖F.incl h (p h) - y‖ := by
        rw [norm_sub_rev (F.incl h (p h))]
        exact S.norm_adjoint_incl_apply_le h _
      have b3 : ‖(F.incl h).adjoint y' - p' h‖ ≤ ‖p' h - F.L h (p h)‖ +
          (S.boundConst * ‖F.incl h (p h) - y‖ + ‖(1 - S.J h) (p h)‖) := by
        rw [e1]
        refine (norm_add_le _ _).trans (add_le_add (norm_neg _).le ?_)
        exact (norm_sub_le _ _).trans (add_le_add b2 (le_of_eq rfl))
      rw [e2]
      refine (norm_add_le _ _).trans (add_le_add (by rw [norm_sub_rev]) ?_)
      refine b1.trans (mul_le_mul_of_nonneg_left (b3.trans_eq (by ring)) hC)
    have hb : Tendsto (fun h => ‖F.incl h ((F.incl h).adjoint y') - y'‖ +
        S.boundConst * (‖p' h - F.L h (p h)‖ + S.boundConst * ‖F.incl h (p h) - y‖ +
          S.graphDefect h * (8 * S.boundConst * ‖y - y'‖))) F.l (𝓝 0) := by
      have := hii.add (((hdd.add (hda.const_mul S.boundConst)).add
        (hJ.mul_const (8 * S.boundConst * ‖y - y'‖))).const_mul S.boundConst)
      simpa using this
    refine squeeze_zero (fun _ => norm_nonneg _) (fun h => ?_) hb
    rw [waveExt_waveGroup H hLx, ← galerkin_p'_eq F D hDD hL Z0 hZ hgal hx h ht]
    refine (key h).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl ?_) hC))
    rw [show p h = S.load h (y - y') from galerkin_p_eq F D hDD hL Z0 hgal hx h ht]
    exact S.norm_one_sub_J_load_le h _

include hJ hL hgal hZ hcl in
/-- **An approximating family of discrete differential spaces from a Galerkin core**: an
approximating FEEC discretization `F` whose generator is the Hodge wave operator `𝐝ₕ - 𝐝ₕ*` of a
differential `𝐝ₕ`, with inner-product defect `‖1 - Jₕ‖_{Vₕ} → 0` in the graph norm of `𝐝ₕ`
(`0` for orthogonal reading maps, `Family.tendsto_graphDefect_ofApproxFEEC`), and a core
`Z0 ≤ D(L²)` whose comparison trajectories satisfy the **Galerkin identity**
`⟪(1 - Lₕ) pₕ(t), v⟫ = ⟪(1 - L) e^{tL} x, iₕ v⟫` (an elliptic projection of the exact orbit, with
the continuous forms on the exact state), with `e^{tL} L x` in the closure of the core. The
admissible states are the orbit states of the core; consistent approximation holds with the
elliptic projection as approximant (residual `0`, approximation from the core,
`tendsto_reading_galerkin`). The cochain defect is not required to be computed: it is absorbed by
the Galerkin identity.

This is a **bridge, not a new convergence proof**: it takes an existing `DissipFEEC.Core` `Z0`
of `F` (whose approximation and consistency hypotheses were established for `F` elsewhere) and
re-reads it as a complex-level family. What it adds is the complex-level structure on the same
discrete solutions (`ofComplexCrime_ofGalerkinCore_sol`): the generator `𝐝ₕ - 𝐝ₕ*`, the
preserved `Lₕ`-invariant subspaces, the Strang and defect bounds, and rates
(`galerkinRateClass`). -/
def ApproxComplexCrime.ofGalerkinCore : ApproxComplexCrime.{u} H κ where
  toFamily := ApproxComplexCrime.Family.ofApproxFEEC F D hDD
  K := F.K
  isClosed_K := F.isClosed_K
  l := F.l
  A := orbitStates H Z0.Data
  A_sub := orbitStates_sub hZ
  Z := Z0.Data
  Z_le := hZ
  orbit_mem x hx t ht := ⟨⟨x, hx, t, ht, Or.inl rfl⟩, ⟨x, hx, t, ht, Or.inr rfl⟩⟩
  tendsto_graphDefect := hJ
  consistent y hy ε hε := by
    set S := ApproxComplexCrime.Family.ofApproxFEEC F D hDD
    filter_upwards [(tendsto_order.1 (tendsto_reading_galerkin F D hDD hJ hL Z0 hZ hgal hcl
      hy)).2 ε hε] with h hh
    refine ⟨S.load h (y - waveExt H y), hh.le, fun v => ?_⟩
    rw [S.inner_load_sub, sub_self, norm_zero]
    positivity

include hL in
/-- **The discrete solutions are those of `F`**: `ofComplexCrime` of the Galerkin family has the
spaces, reading maps and (by `Lₕ = 𝐝ₕ - 𝐝ₕ*`) the generators of `F`. -/
theorem ofComplexCrime_ofGalerkinCore_sol (h : κ) (v : F.X h) (t : ℝ) :
    (ApproxFEEC.ofComplexCrime (ApproxComplexCrime.ofGalerkinCore F D hDD hJ hL Z0 hZ hgal
      hcl)).sol h v t = F.sol h v t := by
  change F.incl h ((C0Group.ofBounded (diffWave (D h))).S t v) =
    F.incl h ((C0Group.ofBounded (F.L h)).S t v)
  rw [hL]

include hJ hL hgal hZ hcl in
/-- **Rates of a Galerkin family**: approximation estimates of the Galerkin comparison and of its
derivative along the trajectory, `‖e^{tL} x - iₕ pₕ(t)‖`,
`‖e^{tL} L x - iₕ pₕ'(t)‖ ≤ Cₐ m(h)ᵅ ‖x‖_c` on `[0, T]` (horizon `T + 1` of the core), and the
inner-product defect at them, `‖(1 - Jₕ) pₕ(t)‖, ‖(1 - Jₕ) pₕ'(t)‖ ≤ Cₐ m(h)ᵅ ‖x‖_c`, give the
complex-level rate data with the elliptic projection as approximant (residual `0`), hence a rate
class of `ofComplexCrime` (`ApproxComplexCrime.rateClass`). The defect along the comparison
vanishes for orthogonal reading maps (`galerkinRateClass_of_isOrthogonal`), and it is at most
`8 C ‖1 - Jₕ‖_{Vₕ} ‖y - L y‖` at `y = e^{tL} x` and `y = e^{tL} L x`
(`pₕ = Bₕ (y - L y)`, `Family.norm_one_sub_J_load_le`). The estimates `happ` are rates of the given
core; this transports them to the complex-level constants, it does not derive them. -/
def galerkinRateClass (T : ℝ) (Dc : Set (PiLp 2 W)) (hDc : Dc ⊆ (Z0.Data : Set (PiLp 2 W)))
    (cn : PiLp 2 W → ℝ) (m : κ → ℝ) (α Ca : ℝ)
    (happ : ∀ x ∈ Dc, ∀ h, ∀ t ∈ Icc 0 T,
      ‖H.waveGroup.S t x - F.incl h ((Z0.cmp (T + 1)).p x h t)‖ ≤ Ca * m h ^ α * cn x ∧
      ‖H.waveGroup.S t (waveExt H x) - F.incl h ((Z0.cmp (T + 1)).p' x h t)‖ ≤
        Ca * m h ^ α * cn x)
    (hdef : ∀ x ∈ Dc, ∀ h, ∀ t ∈ Icc 0 T,
      ‖(1 - (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).J h) ((Z0.cmp (T + 1)).p x h t)‖ ≤
        Ca * m h ^ α * cn x ∧
      ‖(1 - (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).J h) ((Z0.cmp (T + 1)).p' x h t)‖ ≤
        Ca * m h ^ α * cn x) :
    (ApproxFEEC.ofComplexCrime
      (ApproxComplexCrime.ofGalerkinCore F D hDD hJ hL Z0 hZ hgal hcl)).RateClass T :=
  (ApproxComplexCrime.ofGalerkinCore F D hDD hJ hL Z0 hZ hgal hcl).rateClass T Dc hDc cn m α Ca
    fun x hx h t ht y hy => by
      set S := ApproxComplexCrime.Family.ofApproxFEEC F D hDD
      have hx2 := hZ (hDc hx)
      have hT1 : t ∈ Ico 0 (T + 1) := ⟨ht.1, by linarith [ht.2]⟩
      obtain ⟨ha, ha'⟩ := happ x hx h t ht
      obtain ⟨hd, hd'⟩ := hdef x hx h t ht
      have hε : 0 ≤ Ca * m h ^ α * cn x := (norm_nonneg _).trans ha
      refine ⟨S.load h (y - waveExt H y), ?_, ?_, fun v => ?_⟩
      · rcases hy with rfl | hy
        · rw [waveExt_waveGroup H (domainSq_le_domain hx2),
            ← galerkin_p_eq F D hDD hL Z0 hgal (hDc hx) h hT1]
          exact ha
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          rw [waveExt_waveGroup H (waveExt_mem_domain H hx2),
            ← galerkin_p'_eq F D hDD hL Z0 hZ hgal (hDc hx) h hT1]
          exact ha'
      · rcases hy with rfl | hy
        · rw [waveExt_waveGroup H (domainSq_le_domain hx2),
            ← galerkin_p_eq F D hDD hL Z0 hgal (hDc hx) h hT1]
          exact hd
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          rw [waveExt_waveGroup H (waveExt_mem_domain H hx2),
            ← galerkin_p'_eq F D hDD hL Z0 hZ hgal (hDc hx) h hT1]
          exact hd'
      · refine (le_of_eq ?_).trans (mul_nonneg hε (add_nonneg (norm_nonneg _) (norm_nonneg _)))
        exact (congrArg norm (sub_eq_zero.2 (S.inner_load_sub h (y - waveExt H y) v))).trans
          norm_zero

theorem galerkinRateClass_p (T : ℝ) (Dc : Set (PiLp 2 W)) (hDc) (cn) (m) (α Ca) (happ) (hdef)
    {x : PiLp 2 W} (hx : x ∈ Dc) (h : κ) {t : ℝ} (ht : t ∈ Ico 0 (T + 1)) :
    (galerkinRateClass F D hDD hJ hL Z0 hZ hgal hcl T Dc hDc cn m α Ca happ hdef).p x h t =
      (Z0.cmp (T + 1)).p x h t :=
  (ApproxFEEC.loadRitz_cmp_p _ T (domainSq_le_domain (hZ (hDc hx))) h ht.1).trans
    (galerkin_p_eq F D hDD hL Z0 hgal (hDc hx) h ht).symm

include hF hL hgal hZ hcl in
/-- **Rates of a Galerkin family with orthogonal reading maps**: there the inner-product defect
vanishes (`Family.ofApproxFEEC_J`), and the approximation estimates of the comparison and of its
derivative give the rate class (`galerkinRateClass`, with the same constants). -/
def galerkinRateClass_of_isOrthogonal (T : ℝ) (Dc : Set (PiLp 2 W))
    (hDc : Dc ⊆ (Z0.Data : Set (PiLp 2 W))) (cn : PiLp 2 W → ℝ) (m : κ → ℝ) (α Ca : ℝ)
    (happ : ∀ x ∈ Dc, ∀ h, ∀ t ∈ Icc 0 T,
      ‖H.waveGroup.S t x - F.incl h ((Z0.cmp (T + 1)).p x h t)‖ ≤ Ca * m h ^ α * cn x ∧
      ‖H.waveGroup.S t (waveExt H x) - F.incl h ((Z0.cmp (T + 1)).p' x h t)‖ ≤
        Ca * m h ^ α * cn x) :
    (ApproxFEEC.ofComplexCrime (ApproxComplexCrime.ofGalerkinCore F D hDD
      (ApproxComplexCrime.Family.tendsto_graphDefect_ofApproxFEEC F D hDD hF) hL Z0 hZ hgal
        hcl)).RateClass T :=
  galerkinRateClass F D hDD (ApproxComplexCrime.Family.tendsto_graphDefect_ofApproxFEEC F D hDD hF)
    hL Z0 hZ hgal hcl T Dc hDc cn m α Ca happ fun x hx h t ht => by
    have hε : 0 ≤ Ca * m h ^ α * cn x := (norm_nonneg _).trans (happ x hx h t ht).1
    have h0 : ‖1 - (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).J h‖ = 0 := by
      rw [ApproxComplexCrime.Family.ofApproxFEEC_J F D hDD hF h, sub_self, norm_zero]
    exact ⟨(ContinuousLinearMap.le_opNorm _ _).trans (by rw [h0, zero_mul]; exact hε),
      (ContinuousLinearMap.le_opNorm _ _).trans (by rw [h0, zero_mul]; exact hε)⟩

theorem galerkinRateClass_of_isOrthogonal_p (T : ℝ) (Dc : Set (PiLp 2 W)) (hDc) (cn) (m) (α Ca)
    (happ) {x : PiLp 2 W} (hx : x ∈ Dc) (h : κ) {t : ℝ} (ht : t ∈ Ico 0 (T + 1)) :
    (galerkinRateClass_of_isOrthogonal F hF D hDD hL Z0 hZ hgal hcl T Dc hDc cn m α Ca happ).p x h
        t = (Z0.cmp (T + 1)).p x h t :=
  galerkinRateClass_p F D hDD _ hL Z0 hZ hgal hcl T Dc hDc cn m α Ca happ _ hx h ht

end Bridge

end Galerkin

/-! ### Complexification of a differential (real schemes for complex data) -/

section Complexify

variable {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace ℝ (W' i)]
  [∀ i, CompleteSpace (W' i)] {H' : HilbertComplex ℝ c W'} {κ' : Type*}

-- over `ℝ`, the normed space structure of the inner product (as in `ApproxFEEC.complexify`)
attribute [local instance high] ApproxFEEC.instNormedSpaceRealOfInner

namespace ApproxFEEC

variable (F : ApproxFEEC.{u} H' κ') (J : PiLp 2 W' →L[ℝ] PiLp 2 W')
  (hJJ : ∀ x, J (J x) = -x) (hJ : ∀ x, ‖J x‖ = ‖x‖)
  (hπJ : ∀ h b, F.proj h (J (F.incl h b)) = 0)
  (hJι : ∀ h a b, ⟪F.incl h a, J (F.incl h b)⟫_ℝ = 0)

/-- **The differential of the complexification**: `𝐝ₕ ⊕ 𝐝ₕ` on real and imaginary parts. -/
def complexifyD (D : ∀ h, F.X h →L[ℝ] F.X h) (h : κ') :
    (F.complexify J hJJ hJ hπJ hJι).X h →L[ℝ] (F.complexify J hJJ hJ hπJ hJι).X h :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (F.X h) (F.X h)).symm.toContinuousLinearMap ∘L
    ((D h ∘L WithLp.fstL 2 ℝ (F.X h) (F.X h)).prod (D h ∘L WithLp.sndL 2 ℝ (F.X h) (F.X h)))

@[simp] theorem complexifyD_apply (D : ∀ h, F.X h →L[ℝ] F.X h) (h : κ') (a b : F.X h) :
    F.complexifyD J hJJ hJ hπJ hJι D h (WithLp.toLp 2 (a, b)) = WithLp.toLp 2 (D h a, D h b) :=
  rfl

theorem complexifyD_D (D : ∀ h, F.X h →L[ℝ] F.X h) (hDD : ∀ h v, D h (D h v) = 0) (h : κ')
    (v : (F.complexify J hJJ hJ hπJ hJι).X h) :
    F.complexifyD J hJJ hJ hπJ hJι D h (F.complexifyD J hJJ hJ hπJ hJι D h v) = 0 := by
  obtain ⟨⟨a, b⟩⟩ := v
  rw [complexifyD_apply, complexifyD_apply, hDD, hDD]; rfl

/-- **The complexified generator is the Hodge wave operator of the complexified differential**:
if `Lₕ = 𝐝ₕ - 𝐝ₕ*`, then `Lₕ ⊕ Lₕ = (𝐝ₕ ⊕ 𝐝ₕ) - (𝐝ₕ ⊕ 𝐝ₕ)*`. -/
theorem complexify_L_eq_diffWave (D : ∀ h, F.X h →L[ℝ] F.X h)
    (hL : ∀ h, F.L h = diffWave (D h)) (h : κ') :
    (F.complexify J hJJ hJ hπJ hJι).L h = diffWave (F.complexifyD J hJJ hJ hπJ hJι D h) := by
  refine ContinuousLinearMap.ext fun v => ext_inner_right ℝ fun w => ?_
  obtain ⟨⟨a, b⟩⟩ := v
  obtain ⟨⟨a', b'⟩⟩ := w
  refine Eq.trans ?_ (inner_diffWave (F.complexifyD J hJJ hJ hπJ hJι D h) _ _).symm
  change ⟪WithLp.toLp 2 (F.L h a, F.L h b), WithLp.toLp 2 (a', b')⟫_ℝ =
    ⟪WithLp.toLp 2 (D h a, D h b), WithLp.toLp 2 (a', b')⟫_ℝ -
      ⟪WithLp.toLp 2 (a, b), WithLp.toLp 2 (D h a', D h b')⟫_ℝ
  simp only [WithLp.prod_inner_apply, hL, inner_diffWave]
  ring

/-- The complexified discrete spaces are finite-dimensional. -/
theorem complexify_finiteDimensional [hfd : ∀ h, FiniteDimensional ℝ (F.X h)] (h : κ') :
    FiniteDimensional ℝ ((F.complexify J hJJ hJ hπJ hJι).X h) :=
  inferInstanceAs (FiniteDimensional ℝ (WithLp 2 (F.X h × F.X h)))

/-- A pair `(a, b)` of real states as a state of the complexification. -/
def complexifyPair (h : κ') (a b : F.X h) : (F.complexify J hJJ hJ hπJ hJι).X h :=
  WithLp.toLp 2 (a, b)

/-- **Galerkin identities pass to the complexification**: if real and imaginary parts satisfy
`(1 - Lₕ) a = πₕ z` and `(1 - Lₕ) b = -πₕ (J z)`, the pair satisfies `(1 - Lₕ') (a, b) = ι'* z`
(orthogonal reading maps). -/
theorem complexify_galerkin (hF : F.IsOrthogonal) (h : κ') (a b : F.X h) (z : PiLp 2 W')
    (h1 : a - F.L h a = F.proj h z) (h2 : b - F.L h b = -F.proj h (J z)) :
    F.complexifyPair J hJJ hJ hπJ hJι h a b -
        (F.complexify J hJJ hJ hπJ hJι).L h (F.complexifyPair J hJJ hJ hπJ hJι h a b) =
      ((F.complexify J hJJ hJ hπJ hJι).incl h).adjoint z := by
  rw [(hF.complexify J hJJ hJ hπJ hJι).adjoint_incl]
  change WithLp.toLp 2 (a - F.L h a, b - F.L h b) = WithLp.toLp 2 (F.proj h z, -F.proj h (J z))
  rw [h1, h2]

end ApproxFEEC

end Complexify


/-! ### Rates at order `min(α, β, γ)` from the split estimates -/

section RateSplit

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

namespace ApproxComplexCrime

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplexCrime.{u} H κ)

/-- The constant `(1 + C_ι) Cₐ + C_β + C_γ` of `rateClass_of_split`. -/
def splitConst (Ca Cb Cg : ℝ) : ℝ := (1 + F.toFamily.boundConst) * Ca + Cb + Cg

open ApproxFEEC in
/-- **A rate class at order `min(α, β, γ)` from the split estimates** (Holst–Stern type, with a
cochain defect). For a mesh size `0 ≤ m(h) ≤ 1`, orders `α, β, γ ≥ 0` and constants
`Cₐ, C_β, C_γ ≥ 0`: if along the exact trajectory (`y = e^{tL} x` and `y = e^{tL} L x`,
`t ∈ [0, T]`, `x ∈ Dc`) there are approximants `w` with graph-norm error
`‖y - iₕ w‖ + ‖𝐝 y - iₕ 𝐝ₕ w‖ ≤ Cₐ m(h)ᵅ ‖x‖_c` and inner-product defect
`‖(1 - Jₕ) w‖ + ‖(1 - Jₕ) 𝐝ₕ w‖ ≤ C_β m(h)^β ‖x‖_c`, and the cochain defect of `y` is
`≤ C_γ m(h)^γ ‖x‖_c` in the dual discrete graph norm, then the comparison of `ofComplexCrimeCore`
on `Dc` is a rate class of order `min(α, β, γ)` (`rateClass` with `Cₐ' = (1 + C_ι) Cₐ + C_β + C_γ`,
`splitConst`): its constants are `C = (1 + 8 C_ι) Cₐ'` and
`C' = 2 (1 + 8 (1 + C_ι²) + C_ι (1 + 8 C_ι)) Cₐ'` (`rateClass_of_split_C`,
`rateClass_of_split_C'`). For approximants of size `‖w‖ + ‖𝐝ₕ w‖ ≤ C_w ‖x‖_c`, the inner-product
defect at them is `O(m^β)` with `C_β = c C_w` when `‖1 - Jₕ‖ ≤ c m(h)^β`
(`Family.norm_one_sub_J_add_le_opNorm`; the former hypotheses of this constructor, with the same
constants) and with `C_β = 2 c C_w` when only the defect in the graph norm is,
`‖1 - Jₕ‖_{Vₕ} ≤ c m(h)^β` (`Family.norm_one_sub_J_add_le`). The three estimates enter
through `Family.rateData_of_split` and are combined by `add_rpow_le_rpow_min`. -/
def rateClass_of_split (T : ℝ) (Dc : Set (PiLp 2 W)) (hDc : Dc ⊆ (F.Z : Set (PiLp 2 W)))
    (cn : PiLp 2 W → ℝ) (m : κ → ℝ) (α β γ Ca Cb Cg : ℝ)
    (hm0 : ∀ h, 0 ≤ m h) (hm1 : ∀ h, m h ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCg : 0 ≤ Cg) (hcn : ∀ x ∈ Dc, 0 ≤ cn x)
    (hsplit : ∀ x ∈ Dc, ∀ h, ∀ t ∈ Icc 0 T, ∀ y ∈ ({H.waveGroup.S t x,
      H.waveGroup.S t (waveExt H x)} : Set (PiLp 2 W)), ∀ hy : y ∈ H.wave.domain,
      ∃ w : F.toFamily.X h,
        ‖y - F.toFamily.incl h w‖ + ‖H.totalD ⟨y, hy.1⟩ - F.toFamily.incl h (F.toFamily.D h w)‖ ≤
          Ca * m h ^ α * cn x ∧
        ‖(1 - F.toFamily.J h) w‖ + ‖(1 - F.toFamily.J h) (F.toFamily.D h w)‖ ≤
          Cb * m h ^ β * cn x ∧
        ∀ v, ‖⟪F.toFamily.cochainDefect h ⟨y, hy⟩, v⟫_𝕜‖ ≤
          Cg * m h ^ γ * cn x * (‖v‖ + ‖F.toFamily.D h v‖)) :
    (ofComplexCrime F).RateClass T :=
  F.rateClass T Dc hDc cn m (min α (min β γ)) (F.splitConst Ca Cb Cg)
    fun x hx h t ht y hy => by
      set S := F.toFamily
      have hx2 := F.Z_le (hDc hx)
      have hx1 := domainSq_le_domain hx2
      have hyD : y ∈ H.wave.domain := by
        rcases hy with rfl | hy
        · exact waveGroup_mem_domain H hx1 t
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          exact waveGroup_mem_domain H (waveExt_mem_domain H hx2) t
      obtain ⟨w, ha, hb, hcd⟩ := hsplit x hx h t ht y hy hyD
      obtain ⟨h1, h2, h3⟩ := S.rateData_of_split h ⟨y, hyD⟩ w ha hb hcd
      have hC := S.boundConst_nonneg
      have hc := hcn x hx
      have hmh0 := hm0 h
      have hmh1 := hm1 h
      have pa : m h ^ α ≤ m h ^ min α (min β γ) :=
        Real.rpow_le_rpow_of_exponent_ge' hmh0 hmh1 (le_min hα (le_min hβ hγ)) (min_le_left _ _)
      have pb : m h ^ β ≤ m h ^ min α (min β γ) :=
        Real.rpow_le_rpow_of_exponent_ge' hmh0 hmh1 (le_min hα (le_min hβ hγ))
          ((min_le_right _ _).trans (min_le_left _ _))
      have hpa := Real.rpow_nonneg hmh0 α
      have hpb := Real.rpow_nonneg hmh0 β
      have hpμ := Real.rpow_nonneg hmh0 (min α (min β γ))
      -- the combined bound `E_β + C_ι Eₐ + E_γ ≤ Cₐ' m^μ ‖x‖_c`
      have hsum := add_rpow_le_rpow_min hmh0 hmh1 hα hβ hγ
        (mul_nonneg (mul_nonneg hC hCa) hc) (mul_nonneg hCb hc) (mul_nonneg hCg hc)
      have hres : Cb * m h ^ β * cn x + S.boundConst * (Ca * m h ^ α * cn x) +
          Cg * m h ^ γ * cn x ≤ F.splitConst Ca Cb Cg * m h ^ min α (min β γ) * cn x := by
        have e : F.splitConst Ca Cb Cg * m h ^ min α (min β γ) * cn x =
            (S.boundConst * Ca * cn x + Cb * cn x + Cg * cn x) * m h ^ min α (min β γ) +
              Ca * cn x * m h ^ min α (min β γ) := by
          unfold splitConst; ring
        rw [e]
        have : 0 ≤ Ca * cn x * m h ^ min α (min β γ) := by positivity
        have e2 : Cb * m h ^ β * cn x + S.boundConst * (Ca * m h ^ α * cn x) +
            Cg * m h ^ γ * cn x =
            S.boundConst * Ca * cn x * m h ^ α + Cb * cn x * m h ^ β + Cg * cn x * m h ^ γ := by
          ring
        linarith
      refine ⟨w, ?_, ?_, fun v => ?_⟩
      · refine h1.trans ?_
        have e : F.splitConst Ca Cb Cg * m h ^ min α (min β γ) * cn x =
            Ca * cn x * m h ^ min α (min β γ) +
              (S.boundConst * Ca + Cb + Cg) * cn x * m h ^ min α (min β γ) := by
          unfold splitConst; ring
        rw [e]
        have := mul_le_mul_of_nonneg_left pa (mul_nonneg hCa hc)
        have : 0 ≤ (S.boundConst * Ca + Cb + Cg) * cn x * m h ^ min α (min β γ) := by
          positivity
        linarith [show Ca * m h ^ α * cn x = Ca * cn x * m h ^ α by ring]
      · refine h2.trans ?_
        have e : F.splitConst Ca Cb Cg * m h ^ min α (min β γ) * cn x =
            Cb * cn x * m h ^ min α (min β γ) +
              ((1 + S.boundConst) * Ca + Cg) * cn x * m h ^ min α (min β γ) := by
          unfold splitConst; ring
        rw [e]
        have := mul_le_mul_of_nonneg_left pb (mul_nonneg hCb hc)
        have : 0 ≤ ((1 + S.boundConst) * Ca + Cg) * cn x * m h ^ min α (min β γ) := by
          positivity
        linarith [show Cb * m h ^ β * cn x = Cb * cn x * m h ^ β by ring]
      · rw [waveExt_of_mem hyD]
        exact (h3 v).trans (mul_le_mul_of_nonneg_right hres
          (add_nonneg (norm_nonneg _) (norm_nonneg _)))

variable (T : ℝ) (Dc : Set (PiLp 2 W)) (hDc : Dc ⊆ (F.Z : Set (PiLp 2 W)))
  (cn : PiLp 2 W → ℝ) (m : κ → ℝ) (α β γ Ca Cb Cg : ℝ)
  (hm0 : ∀ h, 0 ≤ m h) (hm1 : ∀ h, m h ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
  (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCg : 0 ≤ Cg) (hcn : ∀ x ∈ Dc, 0 ≤ cn x) (hsplit)

/-- The order of `rateClass_of_split` is `min(α, β, γ)`. -/
theorem rateClass_of_split_α :
    (F.rateClass_of_split T Dc hDc cn m α β γ Ca Cb Cg hm0 hm1 hα hβ hγ hCa hCb hCg hcn
      hsplit).α = min α (min β γ) := rfl

/-- The approximation constant of `rateClass_of_split`:
`C = (1 + 8 C_ι) ((1 + C_ι) Cₐ + C_β + C_γ)`. -/
theorem rateClass_of_split_C :
    (F.rateClass_of_split T Dc hDc cn m α β γ Ca Cb Cg hm0 hm1 hα hβ hγ hCa hCb hCg hcn
      hsplit).C = (1 + 8 * F.toFamily.boundConst) *
        ((1 + F.toFamily.boundConst) * Ca + Cb + Cg) := rfl

/-- The consistency constant of `rateClass_of_split`:
`C' = 2 (1 + 8 (1 + C_ι²) + C_ι (1 + 8 C_ι)) ((1 + C_ι) Cₐ + C_β + C_γ)`. -/
theorem rateClass_of_split_C' :
    (F.rateClass_of_split T Dc hDc cn m α β γ Ca Cb Cg hm0 hm1 hα hβ hγ hCa hCb hCg hcn
      hsplit).C' = 2 * (1 + 8 * (1 + F.toFamily.boundConst ^ 2) +
        F.toFamily.boundConst * (1 + 8 * F.toFamily.boundConst)) *
        ((1 + F.toFamily.boundConst) * Ca + Cb + Cg) := rfl

/-- **The error at order `min(α, β, γ)`**: under the split estimates of `rateClass_of_split`,
from the comparison initial value `Rₕ x`,
`‖e^{tL} x - iₕ e^{tLₕ} Rₕ x‖ ≤ (C + C_ι C' t) m(h)^{min(α, β, γ)} ‖x‖_c` on `[0, T]`. -/
theorem error_le_of_split {x : PiLp 2 W} (hx : x ∈ Dc) (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖H.waveGroup.S t x - (ApproxFEEC.ofComplexCrime F).sol h
        ((F.rateClass_of_split T Dc hDc cn m α β γ Ca Cb Cg hm0 hm1 hα hβ hγ hCa hCb hCg
          hcn hsplit).p x h 0) t‖ ≤
      ((F.rateClass_of_split T Dc hDc cn m α β γ Ca Cb Cg hm0 hm1 hα hβ hγ hCa hCb hCg
          hcn hsplit).C + F.toFamily.boundConst *
        (F.rateClass_of_split T Dc hDc cn m α β γ Ca Cb Cg hm0 hm1 hα hβ hγ hCa hCb hCg
          hcn hsplit).C' * t) * (m h ^ min α (min β γ) * cn x) :=
  F.error_le_of_rateClass _ hx h ht

end ApproxComplexCrime

end RateSplit

end Feec.HilbertComplex
