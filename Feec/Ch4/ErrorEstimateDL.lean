module

public import Feec.Ch4.Unconditional
public import Feec.Ch4.HodgeW
public import Mathlib.Analysis.PSeries

/-!
# Semi-discrete convergence for data in `D(L)` and in `W` (Thm 4.14 and the remark after it)

The convergence results of `Feec.Ch4.ErrorEstimate` (`Complex3.convergence`) and
`Feec.Ch4.Unconditional` (`HilbertComplex2.convergence_unconditional`) need the exact solution in
`C¹([0,T]; V)`, which Stone's theorem supplies for `ξ₀ ∈ D(L²)`. The thesis's remark after
Thm 4.14 (l.2449–2451) claims convergence of (4.10) with `ξₕ(0) = Πₕ ξ(0)` for its weak solutions,
whose data lie in `D(L)` (Thm 4.6). This module settles the question for every Hilbert complex of
length 2 and every family of finite-dimensional subcomplexes satisfying the density hypothesis.

* **The claim is true, and more.** `HilbertComplex2.convergence_domL`: for every `ξ₀ ∈ D(L)` and
  `ξₕ(0) = Πₕ ξ₀`, `ξₕ → e^{-tL} ξ₀` in `W`, uniformly on `[0,T]` (in `L∞(0,T; W)`).
  `HilbertComplex2.eqOn_waveGroup_of_isWeakSolution` identifies every weak solution of
  (4.7)–(4.8) (`HilbertComplex2.IsWeakSolution`) with `ξ₀ ∈ D(L)` with `e^{-tL} ξ₀` on `[0,T]`, so
  `convergence_domL_weakSolution` states the remark literally: `ξₕ → ξ` for the thesis's weak
  solution `ξ`; `convergence_domL_classicalWeak_exists` adds existence of `ξ` in
  `C⁰([0,T]; V) ∩ C¹([0,T]; W)` and of the discrete solutions.
  `HilbertComplex2.convergence_W`: for every `ξ₀ ∈ W` (the limit is then the mild solution
  `e^{-tL} ξ₀` of the Stone group) and every choice of discrete data with `ξₕ(0) → ξ₀` in `W`,
  the same uniform convergence holds; `HilbertComplex2.exists_init_W` constructs such data
  (the `W`-orthogonal projection onto `Vₕ`), and `convergence_W_exists` packages both.
  The proof is a stability-plus-density argument: approximate `ξ₀` in `W` by `ζ₀ ∈ D(L²)`
  (`IsSkewAdjoint.exists_mem_domain_sq_near`, via the resolvent `c (c - A)⁻¹`), apply the
  `D(L²)` result to `ζ₀`, and control the rest by `‖e^{-tL}‖ = 1` and the `W`-stability of the
  semi-discrete flow (`Complex3.discrete_stability`, uniform in `h`).
* **A comparison-datum error bound** (`HilbertComplex2.error_bound_W`, `error_bound_W'`): for
  every `ζ₀ ∈ D(L²)`, with `ζ` its exact solution and `e = Πₕζ − ζ`,
  `‖e^{-tL}ξ₀ − ξₕ(t)‖_W ≤ 2‖ξ₀ − ζ₀‖_W + ‖ξ₀ − ξₕ(0)‖_W + ‖e(t)‖_W + (1 + t)(‖e(0)‖_W +
  ∫₀ᵗ ‖ė‖_W)`. This is only a K-functional-type bound: the projection errors of `ζ` are not
  bounded here by a norm of `ζ₀` in `D(L²)` times a function of `h`, so no genuine K-functional
  `inf_{ζ₀} (‖ξ₀ − ζ₀‖_W + s ‖ζ₀‖_{D(L²)})` and no rate for `ξ₀ ∈ D(L)` or `W` is derived.
* **Thm 4.14 itself does not cover `D(L)` data.** `HilbertComplex2.embW_deriv_zero_of_isWeakSol`:
  a weak solution in `C¹([0,T]; V)` (`T > 0`) has `ξ̇(0) = −L ξ₀`, so `L ξ₀ ∈ V` is necessary
  (`not_isWeakSol_of_not_mem`). `FredholmCE.cxK1_exists_not_isWeakSol`: for the complex
  `0 → ℓ² --diag(n+1)--> ℓ²` there is `ξ₀ ∈ D(L) \ D(L²)` for which no weak solution in
  `C¹([0,T]; V)` exists for any `T > 0` (the obstruction is at `t = 0`: `ξ̇(0) ∉ V`); so the
  right side of Thm 4.14, which involves `Πₕ ξ̇`, is not available. On the same complex, the
  coordinate truncations `V¹ₕ = V²ₕ = span{e_0, …, e_{N-1}}` (`FredholmCE.cxK1Sub`) satisfy the
  density hypothesis (`FredholmCE.cxK1Sub_densityHyp`), and `FredholmCE.cxK1_convergence_without_C1`
  shows the discrete solutions for this `ξ₀` converge anyway: a concrete, infinite-dimensional
  case of convergence (without rate) outside the reach of Thm 4.14.

Thesis gap: the remark after Thm 4.14 does not say which data are allowed; Thm 4.14's bound
needs `ξ̇ ∈ V` (`ξ ∈ C¹([0,T]; V)` in the corrected form), which fails for some `D(L)` data
(`cxK1_exists_not_isWeakSol`). Convergence nevertheless holds for all `D(L)` data, and even for
all `W` data, but by a density argument, not from the bound of Thm 4.14.

Scope: in the general theorems the density hypothesis `Complex3.DensityHyp` is assumed as in the
thesis; the only infinite-dimensional family constructed here is `FredholmCE.cxK1Sub`. Whether
`ξ̇(t) ∉ V` for all `t` (not only `t = 0`) in the `cxK1` example is not formalized.

## References

* [QuennevilleBelair2015], §4.4 (Thm 4.6, weak solutions (4.7)–(4.8)), §4.6 (discretization
  (4.10), elliptic projection (4.11), Thm 4.14 and the convergence remark after it)
* [Pazy1983], §1.2 (density of `D(A²)`, regularity of orbits), §1.10 (Stone's theorem)
* [Kato1995] (resolvents of closed operators)
* [Baker1976], [Dupont1973], [Geveci1988] (energy error analysis of semi-discrete Galerkin
  methods for second-order hyperbolic problems)
* [AFW2010], [Arnold2018] (Hilbert complexes and their approximation by subcomplexes)
-/

open scoped RealInnerProductSpace LinearPMap Topology
open Set Filter

@[expose] public noncomputable section

namespace Feec

section DenseSq

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {A : E →ₗ.[ℝ] E}

/-- **`D(A²)` is dense** for a skew-adjoint `A`: every `y ∈ E` is within `δ` of some
`x ∈ D(A)` with `A x ∈ D(A)`. Take `w ∈ D(A)` near `y` and `x = c (c − A)⁻¹ w`; then
`A x = c (x − w) ∈ D(A)` and `x − w = (c − A)⁻¹ A w` has norm `≤ ‖A w‖ / c`.
Cf. [Pazy1983, §1.2]; resolvent bound from `Feec.norm_resolvent_apply_le`. -/
theorem IsSkewAdjoint.exists_mem_domain_sq_near (hA : IsSkewAdjoint A) (y : E) {δ : ℝ}
    (hδ : 0 < δ) : ∃ x : A.domain, A x ∈ A.domain ∧ ‖y - x‖ < δ := by
  obtain ⟨w, hw, hyw⟩ := hA.dense_domain.exists_dist_lt y (half_pos hδ)
  set w' : A.domain := ⟨w, hw⟩
  set c : ℝ := 2 * ‖A w'‖ / δ + 1 with hc
  have hc0 : 0 < c := by positivity
  have hcne : c ≠ 0 := hc0.ne'
  set x := resD hA hcne (c • w) with hx
  have hxv : (x : E) = resolvent hA c (c • w) := (resolvent_apply hA hcne _).symm
  have hAx : A x ∈ A.domain := by
    have h := apply_resD hA hcne (c • w)
    rw [← hx] at h
    rw [h, ← hxv]
    exact A.domain.sub_mem (A.domain.smul_mem c x.2) (A.domain.smul_mem c hw)
  refine ⟨x, hAx, ?_⟩
  have hxw : (x : E) - w = resolvent hA c (A w') := by
    rw [resolvent_apply_domain hA hcne w', hxv, map_smul]
  have hb : ‖(x : E) - w‖ < δ / 2 := by
    rw [hxw]
    refine (norm_resolvent_apply_le hA hcne _).trans_lt ?_
    rw [abs_of_pos hc0, inv_mul_lt_iff₀ hc0, hc]
    have := norm_nonneg (A w')
    field_simp
    nlinarith
  rw [dist_eq_norm] at hyw
  calc ‖y - x‖ = ‖(y - w) - ((x : E) - w)‖ := by congr 1; abel
    _ ≤ ‖y - w‖ + ‖(x : E) - w‖ := norm_sub_le _ _
    _ < δ / 2 + δ / 2 := add_lt_add hyw hb
    _ = δ := add_halves δ

end DenseSq

namespace Complex3

open HilbertComplex2 (Tot tot)

variable {X0 X1 X2 : Type*}
  [NormedAddCommGroup X0] [InnerProductSpace ℝ X0]
  [NormedAddCommGroup X1] [InnerProductSpace ℝ X1]
  [NormedAddCommGroup X2] [InnerProductSpace ℝ X2]
  {C : Complex3 X0 X1 X2}

/-- **Stability of the semi-discrete scheme (4.10)** in `W`, uniform in the subcomplex: for two
discrete solutions on the same `Vₕ`, `‖ξ₁(t) − ξ₂(t)‖_W ≤ ‖ξ₁(0) − ξ₂(0)‖_W` on `[0,T]`
(energy argument: `a(ψ, ψ) = 0`, then Lemma 4.12). The constant is `1`, independent of `h`.
See [QuennevilleBelair2015, §4.6]; this is `Complex3.IsDiscreteSol.norm_toW_sub_le`. -/
theorem discrete_stability (S : C.Sub) {T : ℝ} {ξ₁ ξ₁' ξ₂ ξ₂' : ℝ → C.VSp}
    (h₁ : C.IsDiscreteSol S T ξ₁ ξ₁') (h₂ : C.IsDiscreteSol S T ξ₂ ξ₂') :
    ∀ t ∈ Icc 0 T, ‖C.toW (ξ₁ t - ξ₂ t)‖ ≤ ‖C.toW (ξ₁ 0 - ξ₂ 0)‖ :=
  h₁.norm_toW_sub_le h₂

end Complex3

namespace HilbertComplex2

open Complex3

variable {W0 W1 W2 : Type*}
  [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
  (H : HilbertComplex2 W0 W1 W2)

/-- The inclusion `V = V⁰ × V¹ × W² → W = W⁰ × W¹ × W²` of the weak-form space into the
ambient space of the Hodge wave operator (`(σ, u, ρ) ↦ (σ, u, ρ)`), used to compare discrete
solutions with the orbits `e^{-tL} ξ₀ ∈ W` of the Stone group. -/
def embW : H.toComplex3.VSp →ₗ[ℝ] Tot W0 W1 W2 :=
  (tot W0 W1 W2).symm.toLinearMap ∘ₗ
    (LinearMap.prodMap H.d0.domain.subtype (LinearMap.prodMap H.d1.domain.subtype LinearMap.id))
    ∘ₗ H.toComplex3.vEquiv.toLinearMap

/-- `embW` on `mkV`. -/
theorem embW_mkV (σ : H.d0.domain) (u : H.d1.domain) (ρ : W2) :
    H.embW (H.toComplex3.mkV σ u ρ) = WithLp.toLp 2 ((σ : W0), WithLp.toLp 2 ((u : W1), ρ)) :=
  rfl

/-- `embW` is the `W`-norm reading `Complex3.toW`: `‖embW ξ‖ = ‖ξ‖_W`. -/
theorem norm_embW (ξ : H.toComplex3.VSp) : ‖H.embW ξ‖ = ‖H.toComplex3.toW ξ‖ := by
  induction ξ using VSp.induction with
  | h σ u ρ =>
  rw [embW_mkV, toW_mkV, WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, WithLp.prod_norm_eq_of_L2]
  rfl

/-- `embW ∘ toV` is the inclusion `D(L) → W`. -/
theorem embW_toV (x : H.domL) : H.embW (H.toV x) = (x : Tot W0 W1 W2) := rfl

/-- `D(L²)` is dense in `W` for the Hodge wave operator `L` of any Hilbert complex
(`IsSkewAdjoint.exists_mem_domain_sq_near` for `-L`). -/
theorem exists_domL2_near (ξ₀ : Tot W0 W1 W2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x : H.domL, (H.waveOp ⟨x.1, x.2⟩ : Tot W0 W1 W2) ∈ H.domL ∧ ‖ξ₀ - x‖ < δ := by
  obtain ⟨x, hx, hd⟩ := H.neg_waveOp_isSkewAdjoint.exists_mem_domain_sq_near ξ₀ hδ
  refine ⟨⟨x.1, x.2⟩, ?_, hd⟩
  have : (-(-H.waveOp) x : Tot W0 W1 W2) ∈ H.domL := H.domL.neg_mem hx
  simp only [LinearPMap.neg_apply, neg_neg] at this
  exact this

/-- `‖ξ‖_W ≤ ‖ξ‖_V`. -/
theorem norm_embW_le (ξ : H.toComplex3.VSp) : ‖H.embW ξ‖ ≤ ‖ξ‖ := by
  rw [norm_embW]; exact H.toComplex3.norm_toW_le ξ

/-- `embW` preserves the `W` inner product. -/
theorem inner_embW (ξ ψ : H.toComplex3.VSp) :
    ⟪H.embW ξ, H.embW ψ⟫ = ⟪H.toComplex3.toW ξ, H.toComplex3.toW ψ⟫ := by
  induction ξ using VSp.induction with
  | h σ u ρ =>
  induction ψ using VSp.induction with
  | h τ v μ =>
  rw [inner_toW_mkV, embW_mkV, embW_mkV, WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  rw [← add_assoc]; rfl

/-- `⟪w, (τ, v, μ)⟫_W` in coordinates. -/
theorem inner_embW_mkV (w : Tot W0 W1 W2) (τ : H.d0.domain) (v : H.d1.domain) (μ : W2) :
    ⟪w, H.embW (H.toComplex3.mkV τ v μ)⟫ =
      ⟪(tot W0 W1 W2 w).1, (τ : W0)⟫ + ⟪(tot W0 W1 W2 w).2.1, (v : W1)⟫
        + ⟪(tot W0 W1 W2 w).2.2, μ⟫ := by
  rw [embW_mkV, WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  rw [← add_assoc]; rfl

/-- For `z ∈ D(L)` and `ψ ∈ V`: `(−L z, ψ)_W + a(z, ψ) = 0` (the weak form (4.8) at one time,
without assuming `L z ∈ D(L)`; cf. `HilbertComplex2.weak_identity`).
See [QuennevilleBelair2015, (4.7)–(4.8), Thm 4.7]. -/
theorem weak_identity_neg (z : H.domL) (ψ : H.toComplex3.VSp) :
    ⟪-(H.waveOp ⟨z.1, z.2⟩ : Tot W0 W1 W2), H.embW ψ⟫ + H.toComplex3.aL (H.toV z) ψ = 0 := by
  induction ψ using VSp.induction with
  | h τ v μ =>
  rw [inner_embW_mkV]
  change _ + H.toComplex3.aL (H.toComplex3.mkV _ _ _) (H.toComplex3.mkV τ v μ) = 0
  rw [aL_mkV, toComplex3_a, _root_.map_neg, tot_waveOp]
  have e0 : H.pr0 ⟨z.1, z.2⟩ = H.pr0 z := rfl
  have e1 : H.prV1 ⟨z.1, z.2⟩ = H.prV1 z := rfl
  have e2 : H.prV1s ⟨z.1, z.2⟩ = H.prV1s z := rfl
  have e3 : H.prV2s ⟨z.1, z.2⟩ = H.prV2s z := rfl
  have a0 := LinearPMap.adjoint_isFormalAdjoint H.dense0 (H.prV1s z) τ
  have a1 := LinearPMap.adjoint_isFormalAdjoint H.dense1 (H.prV2s z) v
  simp only [coe_prV1s, coe_prV2s] at a0 a1
  simp only [e0, e1, e2, e3, Prod.neg_mk, inner_neg_left, inner_add_left, coe_prV1]
  linarith

/-- `V` is dense in `W`: an element of `W` orthogonal to `embW V` vanishes (density of
`V⁰ = D(d0)` in `W⁰` and of `V¹ = D(d1)` in `W¹`). -/
theorem eq_zero_of_inner_embW {y : Tot W0 W1 W2} (h : ∀ ψ, ⟪y, H.embW ψ⟫ = 0) : y = 0 := by
  have h0 : (tot W0 W1 W2 y).1 = 0 := H.dense0.eq_zero_of_inner_left ℝ fun τ hτ => by
    have := h (H.toComplex3.mkV ⟨τ, hτ⟩ 0 0)
    rw [inner_embW_mkV] at this
    simpa using this
  have h1 : (tot W0 W1 W2 y).2.1 = 0 := H.dense1.eq_zero_of_inner_left ℝ fun v hv => by
    have := h (H.toComplex3.mkV 0 ⟨v, hv⟩ 0)
    rw [inner_embW_mkV] at this
    simpa using this
  have h2 : (tot W0 W1 W2 y).2.2 = 0 := by
    have := h (H.toComplex3.mkV 0 0 (tot W0 W1 W2 y).2.2)
    rw [inner_embW_mkV] at this
    simpa using this
  apply (tot W0 W1 W2).injective
  rw [map_zero]
  ext <;> simp [h0, h1, h2]

/-- The `W¹` component of an element of `V` lies in `V¹ = D(d1)`. -/
theorem tot_embW_mem (ψ : H.toComplex3.VSp) : (tot W0 W1 W2 (H.embW ψ)).2.1 ∈ H.d1.domain := by
  induction ψ using VSp.induction with
  | h σ u ρ => exact u.2

/-- **Necessary condition for Thm 4.14's regularity.** If `T > 0` and `ξ` is a weak solution in
`C¹([0,T]; V)` (`Complex3.IsWeakSol`) with `ξ(0) = ξ₀ ∈ D(L)`, then `ξ̇(0) = −L ξ₀` in `W`; in
particular `L ξ₀ ∈ V` (`L ξ₀` lies in `embW V`).
See [QuennevilleBelair2015, Thm 4.14]. -/
theorem embW_deriv_zero_of_isWeakSol {T : ℝ} (hT : 0 < T) (x : H.domL)
    {ξ ξ' : ℝ → H.toComplex3.VSp} (hξ : H.toComplex3.IsWeakSol T ξ ξ') (h0 : ξ 0 = H.toV x) :
    H.embW (ξ' 0) = -(H.waveOp ⟨x.1, x.2⟩ : Tot W0 W1 W2) := by
  rw [← sub_eq_zero]
  refine H.eq_zero_of_inner_embW fun ψ => ?_
  have h1 := hξ.2.2.2 0 ⟨le_rfl, hT⟩ ψ
  have h2 := H.weak_identity_neg x ψ
  rw [h0, ← inner_embW] at h1
  rw [inner_sub_left]
  linarith

/-- If `L ξ₀ ∉ V`, no weak solution in `C¹([0,T]; V)` (`T > 0`) starts at `ξ₀ ∈ D(L)`, so
`Complex3.thm_4_14` does not apply to it. -/
theorem not_isWeakSol_of_not_mem {T : ℝ} (hT : 0 < T) (x : H.domL)
    (hx : ∀ ψ : H.toComplex3.VSp, H.embW ψ ≠ -(H.waveOp ⟨x.1, x.2⟩ : Tot W0 W1 W2)) :
    ¬ ∃ ξ ξ' : ℝ → H.toComplex3.VSp, ξ 0 = H.toV x ∧ H.toComplex3.IsWeakSol T ξ ξ' :=
  fun ⟨_, ξ', h0, hξ⟩ => hx (ξ' 0) (H.embW_deriv_zero_of_isWeakSol hT x hξ h0)

/-- **Error bound for `W` data via a `D(L²)` comparison datum.** Fix `ζ₀ = x ∈ D(L²)`; let `ζ`
be its exact solution in `C¹([0,T]; V)` (unique, `Complex3.isWeakSol_unique`), read in `W` as
`e^{-tL} x`. Then for every subcomplex `Vₕ`, every discrete solution `ξₕ` of (4.10), every
`ξ₀ ∈ W` and `t ∈ [0,T]`, with `e = Πₕζ − ζ` (`Complex3.projErr`):
`‖e^{-tL}ξ₀ − ξₕ(t)‖_W ≤ ‖ξ₀ − x‖_W + ‖Πₕx − ξₕ(0)‖_W + ‖e(t)‖_W + t ‖e(0)‖_W
+ (1 + t) ∫₀ᵗ ‖ė‖_W`.
Thm 4.14 (`Complex3.thm_4_14_pointwise`) for `ζ`, plus `‖e^{-tL}‖ = 1`.
See [QuennevilleBelair2015, Thm 4.14]. -/
theorem error_bound_W (T : ℝ) (x : H.domL) (hx : (H.waveOp ⟨x.1, x.2⟩ : Tot W0 W1 W2) ∈ H.domL) :
    ∃ ζ ζ' : ℝ → H.toComplex3.VSp, ζ 0 = H.toV x ∧ H.toComplex3.IsWeakSol T ζ ζ' ∧
      (∀ t, H.embW (ζ t) = H.waveGroup.S t x) ∧
      ∀ (S : H.toComplex3.Sub) [FiniteDimensional ℝ S.toV] (ξh ξh' : ℝ → H.toComplex3.VSp),
        H.toComplex3.IsDiscreteSol S T ξh ξh' → ∀ (ξ₀ : Tot W0 W1 W2), ∀ t ∈ Icc 0 T,
          ‖H.waveGroup.S t ξ₀ - H.embW (ξh t)‖ ≤ ‖ξ₀ - x‖
            + ‖H.toComplex3.toW (H.toComplex3.ellProj S (H.toV x) - ξh 0)‖
            + ‖H.toComplex3.projErr S (ζ t)‖ + t * ‖H.toComplex3.projErr S (ζ 0)‖
            + (1 + t) * ∫ s in (0:ℝ)..t, ‖H.toComplex3.projErr S (ζ' s)‖ := by
  obtain ⟨ζ, ζ', hζ0, hζ, hζS⟩ := H.exists_isWeakSol_unconditional T x hx
  have hS : ∀ t, H.embW (ζ t) = H.waveGroup.S t x := fun t => by rw [hζS t]; rfl
  refine ⟨ζ, ζ', hζ0, hζ, hS, fun S _ ξh ξh' hξh ξ₀ t ht => ?_⟩
  have h414 := H.toComplex3.thm_4_14_pointwise S hζ hξh t ht
  rw [hζ0] at h414
  have e1 : ‖H.waveGroup.S t ξ₀ - H.waveGroup.S t x‖ = ‖ξ₀ - x‖ := by
    rw [← map_sub, H.waveGroup.norm_map]
  have e2 : ‖H.waveGroup.S t x - H.embW (ξh t)‖ = ‖H.toComplex3.toW (ζ t - ξh t)‖ := by
    rw [← hS, ← map_sub, norm_embW]
  calc ‖H.waveGroup.S t ξ₀ - H.embW (ξh t)‖
      = ‖(H.waveGroup.S t ξ₀ - H.waveGroup.S t x) + (H.waveGroup.S t x - H.embW (ξh t))‖ := by
        congr 1; abel
    _ ≤ ‖H.waveGroup.S t ξ₀ - H.waveGroup.S t x‖ + ‖H.waveGroup.S t x - H.embW (ξh t)‖ :=
        norm_add_le _ _
    _ ≤ _ := by rw [e1, e2, hζ0]; linarith

/-- **Comparison-datum error bound** (a K-functional-type rearrangement of `error_bound_W`):
for every `x ∈ D(L²)` with exact solution `ζ` and `e = Πₕζ − ζ`,
`‖e^{-tL}ξ₀ − ξₕ(t)‖_W ≤ 2‖ξ₀ − x‖_W + ‖ξ₀ − ξₕ(0)‖_W + ‖e(t)‖_W + (1 + t) ‖e(0)‖_W
+ (1 + t) ∫₀ᵗ ‖ė‖_W`.
Only `W`-quantities of the data enter besides the elliptic-projection errors of the comparison
solution. The projection errors depend on `x` and are not bounded here by `‖x‖_{D(L²)}`, so
this is not a genuine K-functional bound and yields no rate by itself.
See [QuennevilleBelair2015, Thm 4.14]. -/
theorem error_bound_W' (T : ℝ) (x : H.domL)
    (hx : (H.waveOp ⟨x.1, x.2⟩ : Tot W0 W1 W2) ∈ H.domL) :
    ∃ ζ ζ' : ℝ → H.toComplex3.VSp, ζ 0 = H.toV x ∧ H.toComplex3.IsWeakSol T ζ ζ' ∧
      (∀ t, H.embW (ζ t) = H.waveGroup.S t x) ∧
      ∀ (S : H.toComplex3.Sub) [FiniteDimensional ℝ S.toV] (ξh ξh' : ℝ → H.toComplex3.VSp),
        H.toComplex3.IsDiscreteSol S T ξh ξh' → ∀ (ξ₀ : Tot W0 W1 W2), ∀ t ∈ Icc 0 T,
          ‖H.waveGroup.S t ξ₀ - H.embW (ξh t)‖ ≤ 2 * ‖ξ₀ - x‖ + ‖ξ₀ - H.embW (ξh 0)‖
            + ‖H.toComplex3.projErr S (ζ t)‖ + (1 + t) * ‖H.toComplex3.projErr S (ζ 0)‖
            + (1 + t) * ∫ s in (0:ℝ)..t, ‖H.toComplex3.projErr S (ζ' s)‖ := by
  obtain ⟨ζ, ζ', hζ0, hζ, hS, hb⟩ := H.error_bound_W T x hx
  refine ⟨ζ, ζ', hζ0, hζ, hS, fun S _ ξh ξh' hξh ξ₀ t ht => ?_⟩
  have h1 := hb S ξh ξh' hξh ξ₀ t ht
  have h2 : ‖H.toComplex3.toW (H.toComplex3.ellProj S (H.toV x) - ξh 0)‖
      ≤ ‖H.toComplex3.projErr S (ζ 0)‖ + ‖ξ₀ - x‖ + ‖ξ₀ - H.embW (ξh 0)‖ := by
    have e : H.toComplex3.toW (H.toComplex3.ellProj S (H.toV x) - ξh 0)
        = H.toComplex3.projErr S (ζ 0) + H.toComplex3.toW (ζ 0 - ξh 0) := by
      rw [projErr_apply, ← map_add, hζ0]; congr 1; abel
    have e' : ‖H.toComplex3.toW (ζ 0 - ξh 0)‖ ≤ ‖ξ₀ - x‖ + ‖ξ₀ - H.embW (ξh 0)‖ := by
      rw [← norm_embW, map_sub, hζ0, embW_toV]
      calc ‖(x : Tot W0 W1 W2) - H.embW (ξh 0)‖
          = ‖-(ξ₀ - x) + (ξ₀ - H.embW (ξh 0))‖ := by congr 1; abel
        _ ≤ ‖-(ξ₀ - x)‖ + ‖ξ₀ - H.embW (ξh 0)‖ := norm_add_le _ _
        _ = _ := by rw [norm_neg]
    rw [e]
    exact (norm_add_le _ _).trans (by linarith)
  have ht0 : 0 ≤ t := ht.1
  have hn := norm_nonneg (H.toComplex3.projErr S (ζ 0))
  nlinarith

/-- **Convergence of the semi-discrete method for arbitrary data `ξ₀ ∈ W`.** For every
Hilbert complex of length 2, every family of finite-dimensional subcomplexes `Vₕ` satisfying the
density hypothesis, and all discrete solutions `ξₕ` of (4.10) on `[0,T]` with `ξₕ(0) → ξ₀` in
`W`: `ξₕ(t) → e^{-tL} ξ₀` in `W`, uniformly for `t ∈ [0,T]`. For `ξ₀ ∈ D(L)`, `e^{-tL} ξ₀` is
the unique strong solution of `ξ' = −L ξ` (Thm 4.6); for `ξ₀ ∈ W` it is the mild solution.
No rate is claimed (see `error_bound_W'`).
See [QuennevilleBelair2015, §4.6, remark after Thm 4.14]. -/
theorem convergence_W {ι : Type*} {l : Filter ι} {S : ι → H.toComplex3.Sub}
    [∀ h, FiniteDimensional ℝ (S h).toV] (hd : H.toComplex3.DensityHyp l S) (T : ℝ)
    (ξ₀ : Tot W0 W1 W2) {ξh ξh' : ι → ℝ → H.toComplex3.VSp}
    (hξh : ∀ h, H.toComplex3.IsDiscreteSol (S h) T (ξh h) (ξh' h))
    (h0 : Tendsto (fun h => H.embW (ξh h 0)) l (𝓝 ξ₀)) :
    TendstoUniformlyOn (fun h t => H.embW (ξh h t)) (fun t => H.waveGroup.S t ξ₀) l
      (Icc 0 T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have hη8 : 0 < η / 8 := by positivity
  obtain ⟨x, hx, hξx⟩ := H.exists_domL2_near ξ₀ hη8
  obtain ⟨ζ, ζ', hζ0, hζ, hζS⟩ := H.exists_isWeakSol_unconditional T x hx
  have hS : ∀ t, H.embW (ζ t) = H.waveGroup.S t x := fun t => by rw [hζS t]; rfl
  choose ζh ζh' hinit hm hdv _ heq using fun h =>
    H.toComplex3.discrete_solution_exists (S h) (H.toComplex3.ellProj_mem (S h) (ζ 0))
  have hsol : ∀ h, H.toComplex3.IsDiscreteSol (S h) T (ζh h) (ζh' h) := fun h =>
    H.toComplex3.isDiscreteSol_of_global (S h) (hm h) (hdv h) (heq h)
  have hconv := Metric.tendstoUniformlyOn_iff.1
    (Complex3.convergence_of_initProj hd hζ hsol hinit) (η / 8) hη8
  have hP := hd.ellProj_tendsto (isCompact_singleton (x := ζ 0)) hη8
  have h0' := Metric.tendsto_nhds.1 h0 (η / 8) hη8
  filter_upwards [hconv, hP, h0'] with h hc hp hi t ht
  have e1 : ‖H.waveGroup.S t ξ₀ - H.waveGroup.S t x‖ = ‖ξ₀ - x‖ := by
    rw [← map_sub, H.waveGroup.norm_map]
  have e2 : ‖H.waveGroup.S t x - H.embW (ζh h t)‖ < η / 8 := by
    have := hc t ht
    rw [dist_eq_norm, ← map_sub, ← norm_embW, map_sub, hS] at this
    exact this
  have e3 : ‖H.embW (ζh h t) - H.embW (ξh h t)‖ ≤ ‖H.embW (ζh h 0) - H.embW (ξh h 0)‖ := by
    rw [← map_sub, ← map_sub, norm_embW, norm_embW]
    exact Complex3.discrete_stability (S h) (hsol h) (hξh h) t ht
  have e4 : ‖H.embW (ζh h 0) - x‖ ≤ η / 8 := by
    have hx0 : (x : Tot W0 W1 W2) = H.embW (ζ 0) := by rw [hζ0, embW_toV]
    rw [hinit, hx0, ← map_sub]
    refine (H.norm_embW_le _).trans ?_
    rw [norm_sub_rev]
    exact hp _ rfl
  have e5 : ‖H.embW (ζh h 0) - H.embW (ξh h 0)‖ < 3 * (η / 8) := by
    rw [dist_eq_norm] at hi
    calc ‖H.embW (ζh h 0) - H.embW (ξh h 0)‖
        = ‖(H.embW (ζh h 0) - x) + ((x : Tot W0 W1 W2) - ξ₀) + (ξ₀ - H.embW (ξh h 0))‖ := by
          congr 1; abel
      _ ≤ ‖H.embW (ζh h 0) - x‖ + ‖(x : Tot W0 W1 W2) - ξ₀‖ + ‖ξ₀ - H.embW (ξh h 0)‖ :=
          norm_add₃_le
      _ < 3 * (η / 8) := by
          rw [norm_sub_rev (x : Tot W0 W1 W2) ξ₀, norm_sub_rev ξ₀ (H.embW (ξh h 0))]; linarith
  rw [dist_eq_norm]
  calc ‖H.waveGroup.S t ξ₀ - H.embW (ξh h t)‖
      = ‖(H.waveGroup.S t ξ₀ - H.waveGroup.S t x) + (H.waveGroup.S t x - H.embW (ζh h t))
          + (H.embW (ζh h t) - H.embW (ξh h t))‖ := by congr 1; abel
    _ ≤ ‖H.waveGroup.S t ξ₀ - H.waveGroup.S t x‖ + ‖H.waveGroup.S t x - H.embW (ζh h t)‖
          + ‖H.embW (ζh h t) - H.embW (ξh h t)‖ := norm_add₃_le
    _ < η := by rw [e1]; linarith

/-- For `x ∈ D(L)`, the elliptic projections `Πₕ x` converge to `x` in `W` (indeed in `V`),
under the density hypothesis. -/
theorem tendsto_embW_ellProj {ι : Type*} {l : Filter ι} {S : ι → H.toComplex3.Sub}
    [∀ h, FiniteDimensional ℝ (S h).toV] (hd : H.toComplex3.DensityHyp l S) (x : H.domL) :
    Tendsto (fun h => H.embW (H.toComplex3.ellProj (S h) (H.toV x))) l
      (𝓝 (x : Tot W0 W1 W2)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hd.ellProj_tendsto (isCompact_singleton (x := H.toV x)) (half_pos hε)]
    with h hp
  rw [dist_eq_norm, ← H.embW_toV x, ← map_sub]
  refine ((H.norm_embW_le _).trans ?_).trans_lt (half_lt_self hε)
  rw [norm_sub_rev]
  exact hp _ rfl

/-- **The thesis's convergence claim for `D(L)` data** (remark after Thm 4.14): for
`ξ₀ ∈ D(L)` and discrete solutions with `ξₕ(0) = Πₕ ξ₀`, `ξₕ → e^{-tL} ξ₀` in `W`, uniformly
on `[0,T]`. No `D(L²)` assumption; compare `HilbertComplex2.convergence_unconditional`.
Correction: the thesis derives this from Thm 4.14, whose bound is not available for all `D(L)`
data (`FredholmCE.cxK1_exists_not_isWeakSol`); the proof here goes through `convergence_W`.
See [QuennevilleBelair2015, §4.6, remark after Thm 4.14]. -/
theorem convergence_domL {ι : Type*} {l : Filter ι} {S : ι → H.toComplex3.Sub}
    [∀ h, FiniteDimensional ℝ (S h).toV] (hd : H.toComplex3.DensityHyp l S) (T : ℝ)
    (x : H.domL) {ξh ξh' : ι → ℝ → H.toComplex3.VSp}
    (hξh : ∀ h, H.toComplex3.IsDiscreteSol (S h) T (ξh h) (ξh' h))
    (hinit : ∀ h, ξh h 0 = H.toComplex3.ellProj (S h) (H.toV x)) :
    TendstoUniformlyOn (fun h t => H.embW (ξh h t)) (fun t => H.waveGroup.S t x) l
      (Icc 0 T) :=
  H.convergence_W hd T x hξh (by simpa only [hinit] using H.tendsto_embW_ellProj hd x)

/-- Existence form of `convergence_domL`: for `ξ₀ ∈ D(L)`, `t ↦ e^{-tL} ξ₀` is a strong solution
of `ξ' = −L ξ`, `ξ(0) = ξ₀` (unique, `thm_4_6_strong_unconditional`), the discrete solutions
with `ξₕ(0) = Πₕ ξ₀` exist, and they converge to it in `W` uniformly on `[0,T]`. -/
theorem convergence_domL_exists {ι : Type*} {l : Filter ι} {S : ι → H.toComplex3.Sub}
    [∀ h, FiniteDimensional ℝ (S h).toV] (hd : H.toComplex3.DensityHyp l S) (T : ℝ)
    (x : H.domL) :
    IsStrongSolution (-H.waveOp) T x 0 (fun t => H.waveGroup.S t x) ∧
    ∃ ξh ξh' : ι → ℝ → H.toComplex3.VSp, (∀ h, H.toComplex3.IsDiscreteSol (S h) T (ξh h) (ξh' h)) ∧
      (∀ h, ξh h 0 = H.toComplex3.ellProj (S h) (H.toV x)) ∧
      TendstoUniformlyOn (fun h t => H.embW (ξh h t)) (fun t => H.waveGroup.S t x) l
        (Icc 0 T) := by
  choose ξh ξh' hinit hm hdv _ heq using fun h =>
    H.toComplex3.discrete_solution_exists (S h) (H.toComplex3.ellProj_mem (S h) (H.toV x))
  have hsol : ∀ h, H.toComplex3.IsDiscreteSol (S h) T (ξh h) (ξh' h) := fun h =>
    H.toComplex3.isDiscreteSol_of_global (S h) (hm h) (hdv h) (heq h)
  have hstr : IsStrongSolution (-H.waveOp) T x 0 (fun t => H.waveGroup.S t x) := by
    let x' : (-H.waveOp).domain := ⟨x.1, x.2⟩
    refine ⟨fun t _ => H.waveGroup.mem_domain_apply x' t, fun t _ => ?_, ?_⟩
    · simp only [Pi.zero_apply, add_zero]
      rw [H.waveGroup.apply_comm x' t]
      exact (H.waveGroup.hasDerivAt_apply x' t).hasDerivWithinAt
    · simp [H.waveGroup.map_zero]
  exact ⟨hstr, ξh, ξh', hsol, hinit,
    H.convergence_domL hd T x hsol hinit⟩

/-- For every `ξ₀ ∈ W` there are discrete initial data `vₕ ∈ Vₕ` with `vₕ → ξ₀` in `W`: the
`W`-orthogonal projection of `ξ₀` onto `Vₕ` (density of `D(L)` in `W` and of `Vₕ` in `V`). -/
theorem exists_init_W {ι : Type*} {l : Filter ι} {S : ι → H.toComplex3.Sub}
    [∀ h, FiniteDimensional ℝ (S h).toV] (hd : H.toComplex3.DensityHyp l S)
    (ξ₀ : Tot W0 W1 W2) :
    ∃ v : ι → H.toComplex3.VSp, (∀ h, v h ∈ (S h).toV) ∧
      Tendsto (fun h => H.embW (v h)) l (𝓝 ξ₀) := by
  set K : ι → Submodule ℝ (Tot W0 W1 W2) := fun h => (S h).toV.map H.embW with hK
  have : ∀ h, FiniteDimensional ℝ (K h) := fun h => inferInstance
  have : ∀ h, CompleteSpace (K h) := fun h => FiniteDimensional.complete ℝ (K h)
  have hmem : ∀ h, (K h).starProjection ξ₀ ∈ (S h).toV.map H.embW := fun h =>
    (K h).starProjection_apply_mem ξ₀
  choose v hv hve using fun h => Submodule.mem_map.1 (hmem h)
  refine ⟨v, hv, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x, -, hξx⟩ := H.exists_domL2_near ξ₀ (half_pos hε)
  filter_upwards [hd.approx (H.toV x) (half_pos hε)] with h ⟨w, hw, hxw⟩
  rw [hve h, dist_comm, Submodule.dist_starProjection_eq_infDist]
  have hwK : H.embW w ∈ K h := Submodule.mem_map_of_mem hw
  refine (Metric.infDist_le_dist_of_mem hwK).trans_lt ?_
  rw [dist_eq_norm]
  have h2 : ‖(x : Tot W0 W1 W2) - H.embW w‖ < ε / 2 := by
    rw [← H.embW_toV x, ← map_sub]
    exact (H.norm_embW_le _).trans_lt hxw
  calc ‖ξ₀ - H.embW w‖ = ‖(ξ₀ - x) + ((x : Tot W0 W1 W2) - H.embW w)‖ := by congr 1; abel
    _ ≤ ‖ξ₀ - x‖ + ‖(x : Tot W0 W1 W2) - H.embW w‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hξx h2
    _ = ε := add_halves ε

/-- Existence form of `convergence_W`: for every `ξ₀ ∈ W` there are discrete solutions of
(4.10) with `ξₕ(0) → ξ₀` in `W`, and every such family converges to `e^{-tL} ξ₀` in `W`
uniformly on `[0,T]`. -/
theorem convergence_W_exists {ι : Type*} {l : Filter ι} {S : ι → H.toComplex3.Sub}
    [∀ h, FiniteDimensional ℝ (S h).toV] (hd : H.toComplex3.DensityHyp l S) (T : ℝ)
    (ξ₀ : Tot W0 W1 W2) :
    ∃ ξh ξh' : ι → ℝ → H.toComplex3.VSp, (∀ h, H.toComplex3.IsDiscreteSol (S h) T (ξh h) (ξh' h)) ∧
      Tendsto (fun h => H.embW (ξh h 0)) l (𝓝 ξ₀) ∧
      TendstoUniformlyOn (fun h t => H.embW (ξh h t)) (fun t => H.waveGroup.S t ξ₀) l
        (Icc 0 T) := by
  obtain ⟨v, hv, hvt⟩ := H.exists_init_W hd ξ₀
  choose ξh ξh' hinit hm hdv _ heq using fun h => H.toComplex3.discrete_solution_exists (S h) (hv h)
  have hsol : ∀ h, H.toComplex3.IsDiscreteSol (S h) T (ξh h) (ξh' h) := fun h =>
    H.toComplex3.isDiscreteSol_of_global (S h) (hm h) (hdv h) (heq h)
  have h0 : Tendsto (fun h => H.embW (ξh h 0)) l (𝓝 ξ₀) := by simpa only [hinit] using hvt
  exact ⟨ξh, ξh', hsol, h0, H.convergence_W hd T ξ₀ hsol h0⟩

/-- For `ξ₀ ∈ D(L)`, the orbit `t ↦ e^{-tL} ξ₀` of the Stone group is a strong solution of
`ξ' = −L ξ`, `ξ(0) = ξ₀` on `[0,T]`. See [QuennevilleBelair2015, Thm 4.6]; [Pazy1983, §1.2]. -/
theorem isStrongSolution_waveGroup (T : ℝ) (x : H.domL) :
    IsStrongSolution (-H.waveOp) T x 0 (fun t => H.waveGroup.S t x) := by
  let x' : (-H.waveOp).domain := ⟨x.1, x.2⟩
  refine ⟨fun t _ => H.waveGroup.mem_domain_apply x' t, fun t _ => ?_, ?_⟩
  · simp only [Pi.zero_apply, add_zero]
    rw [H.waveGroup.apply_comm x' t]
    exact (H.waveGroup.hasDerivAt_apply x' t).hasDerivWithinAt
  · simp [H.waveGroup.map_zero]

/-- **Every thesis-class weak solution is the Stone orbit.** For `ξ₀ ∈ D(L)` and every weak
solution `ξ` of (4.7)–(4.8) on `[0,T]` (`HilbertComplex2.IsWeakSolution`, which contains the
thesis's class `C⁰([0,T]; V) ∩ C¹([0,T]; W)`), `ξ(t) = e^{-tL} ξ₀` on `[0,T]`. Weak ⇒ strong
(`weak_imp_strong_unconditional`, Thm 4.7) and uniqueness of strong solutions
(`thm_4_6_strong_unconditional`, Thm 4.6). See [QuennevilleBelair2015, Thms 4.6, 4.7]. -/
theorem eqOn_waveGroup_of_isWeakSolution {T : ℝ} (x : H.domL) {ξ : ℝ → Tot W0 W1 W2}
    (hξ : H.IsWeakSolution T x ξ) : EqOn ξ (fun t => H.waveGroup.S t x) (Icc 0 T) := by
  have hstr := H.weak_imp_strong_unconditional (ξ₀ := (x : Tot W0 W1 W2)) x.2 hξ
  obtain ⟨-, -, η, -, huniq, -⟩ := H.thm_4_6_strong_unconditional T (ξ₀ := (x : Tot W0 W1 W2)) x.2
  intro t ht
  rw [huniq ξ hstr ht, huniq _ (H.isStrongSolution_waveGroup T x) ht]

/-- **The remark after Thm 4.14, for the thesis's weak solutions.** For `ξ₀ ∈ D(L)`, every weak
solution `ξ` of (4.7)–(4.8) with `ξ(0) = ξ₀` and every family of discrete solutions of (4.10)
with `ξₕ(0) = Πₕ ξ₀`: `ξₕ → ξ` in `W`, uniformly on `[0,T]`. No `D(L²)` assumption and no
`C¹([0,T]; V)` regularity of `ξ` is needed (compare `Complex3.convergence`).
Correction: the thesis derives this from the bound of Thm 4.14, which is not available for all
`D(L)` data (`FredholmCE.cxK1_exists_not_isWeakSol`); the proof is `convergence_domL` plus
`eqOn_waveGroup_of_isWeakSolution`.
See [QuennevilleBelair2015, §4.6, remark after Thm 4.14]. -/
theorem convergence_domL_weakSolution {ι : Type*} {l : Filter ι} {S : ι → H.toComplex3.Sub}
    [∀ h, FiniteDimensional ℝ (S h).toV] (hd : H.toComplex3.DensityHyp l S) (T : ℝ)
    (x : H.domL) {ξ : ℝ → Tot W0 W1 W2} (hξ : H.IsWeakSolution T x ξ)
    {ξh ξh' : ι → ℝ → H.toComplex3.VSp}
    (hξh : ∀ h, H.toComplex3.IsDiscreteSol (S h) T (ξh h) (ξh' h))
    (hinit : ∀ h, ξh h 0 = H.toComplex3.ellProj (S h) (H.toV x)) :
    TendstoUniformlyOn (fun h t => H.embW (ξh h t)) ξ l (Icc 0 T) :=
  (H.convergence_domL hd T x hξh hinit).congr_right
    (fun _ ht => (H.eqOn_waveGroup_of_isWeakSolution x hξ ht).symm)

/-- Existence form of `convergence_domL_weakSolution`: for `ξ₀ ∈ D(L)` there is a weak solution
`ξ` in the thesis's class `C⁰([0,T]; V) ∩ C¹([0,T]; W)` (`IsClassicalWeakSolution`), unique among
weak solutions, and the discrete solutions with `ξₕ(0) = Πₕ ξ₀` exist and converge to it in `W`
uniformly on `[0,T]`. See [QuennevilleBelair2015, §4.4, §4.6, remark after Thm 4.14]. -/
theorem convergence_domL_classicalWeak_exists {ι : Type*} {l : Filter ι}
    {S : ι → H.toComplex3.Sub} [∀ h, FiniteDimensional ℝ (S h).toV]
    (hd : H.toComplex3.DensityHyp l S) (T : ℝ) (x : H.domL) :
    ∃ ξ, H.IsClassicalWeakSolution T x ξ ∧
      (∀ ξ', H.IsWeakSolution T x ξ' → EqOn ξ' ξ (Icc 0 T)) ∧
      ∃ ξh ξh' : ι → ℝ → H.toComplex3.VSp,
        (∀ h, H.toComplex3.IsDiscreteSol (S h) T (ξh h) (ξh' h)) ∧
        (∀ h, ξh h 0 = H.toComplex3.ellProj (S h) (H.toV x)) ∧
        TendstoUniformlyOn (fun h t => H.embW (ξh h t)) ξ l (Icc 0 T) := by
  obtain ⟨ξ, hξ, huniq⟩ :=
    H.exists_classicalWeakSolution_unconditional T (ξ₀ := (x : Tot W0 W1 W2)) x.2
  obtain ⟨-, ξh, ξh', hsol, hinit, -⟩ := H.convergence_domL_exists hd T x
  exact ⟨ξ, hξ, huniq, ξh, ξh', hsol, hinit,
    H.convergence_domL_weakSolution hd T x hξ.toIsWeakSolution hsol hinit⟩

end HilbertComplex2

namespace FredholmCE

open HilbertComplex2

/-- `A = diag(1/(n+1))` is symmetric on `ℓ²`. -/
theorem inner_A_left (a b : L2) : ⟪A a, b⟫ = ⟪a, A b⟫ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1; funext n
  simp only [A_apply, RCLike.inner_apply, conj_trivial]
  ring

/-- `A⁻¹ = diag(n+1)` is symmetric (hence `A⁻¹ ≤ (A⁻¹)*`). -/
theorem invA_isFormalAdjoint : invA.IsFormalAdjoint invA := by
  intro p q
  have hp := A_invA p
  have hq := A_invA q
  rw [← hp, ← hq, inner_A_left]

/-- The sequence `(1/(n+1))ₙ ∈ ℓ²`. -/
def harm : L2 :=
  ⟨fun n => 1 / ((n : ℝ) + 1), (memℓp_gen_iff (by norm_num : (0:ℝ) < (2 : ENNReal).toReal)).2 (by
    have h : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
      simpa [Nat.cast_add, Nat.cast_one] using h
    refine h.congr fun n => ?_
    have hn : (0:ℝ) < (n : ℝ) + 1 := by positivity
    rw [ENNReal.toReal_ofNat, Real.norm_eq_abs, abs_of_pos (by positivity), Real.rpow_two,
      div_pow, one_pow])⟩

/-- Coordinates of `harm`. -/
theorem harm_apply (n : ℕ) : harm n = 1 / ((n : ℝ) + 1) := rfl

/-- `(1/(n+1))ₙ ∉ R(A) = D(A⁻¹)`. -/
theorem harm_not_mem : harm ∉ invA.domain := by
  rw [invA_domain]
  rintro ⟨f, hf⟩
  have h1 : ∀ n, f n = 1 := fun n => by
    have := congrArg (fun y : L2 => y n) hf
    change f n / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) at this
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    exact (div_left_inj' hn).1 this
  have hs := (lp.memℓp f).summable (by norm_num : (0:ℝ) < (2 : ENNReal).toReal)
  have ht := hs.tendsto_atTop_zero
  simp only [h1, norm_one, Real.one_rpow] at ht
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)

/-- **Thm 4.14 does not cover all `D(L)` data.** For the Hilbert complex
`0 → ℓ² --diag(n+1)--> ℓ²` (`FredholmCE.cxK1`) the datum `ξ₀ = (0, 0, ρ)`,
`ρ = (1/(n+1)²)ₙ`, lies in `D(L)` but not in `D(L²)`, and for every `T > 0` there is no weak
solution in `C¹([0,T]; V)` starting at `ξ₀`: `L ξ₀ = (0, (1/(n+1))ₙ, 0)` and
`(1/(n+1))ₙ ∉ D(diag(n+1))`. Convergence still holds for this datum (`convergence_domL`;
concretely with coordinate truncations, `cxK1_convergence_without_C1`).
See [QuennevilleBelair2015, Thm 4.14]. -/
theorem cxK1_exists_not_isWeakSol :
    ∃ x : cxK1.domL, (cxK1.waveOp ⟨x.1, x.2⟩ : Tot R0 L2 L2) ∉ cxK1.domL ∧
      ∀ T > 0, ¬ ∃ ξ ξ' : ℝ → cxK1.toComplex3.VSp, ξ 0 = cxK1.toV x ∧
        cxK1.toComplex3.IsWeakSol T ξ ξ' := by
  set ρ : L2 := A harm with hρdef
  have hρ : ρ ∈ invA.domain := by rw [invA_domain]; exact ⟨harm, rfl⟩
  have hinv : invA ⟨ρ, hρ⟩ = harm := A_injective (A_invA ⟨ρ, hρ⟩)
  have hle : invA ≤ invA† :=
    LinearPMap.IsFormalAdjoint.le_adjoint dense_invA_domain invA_isFormalAdjoint
  have hρ' : ρ ∈ (invA†).domain := hle.1 hρ
  have hinv' : invA† ⟨ρ, hρ'⟩ = harm := (hle.2 rfl).symm.trans hinv
  have hxmem : (tot R0 L2 L2).symm (0, 0, ρ) ∈ cxK1.domL := by
    change (tot R0 L2 L2) ((tot R0 L2 L2).symm (0, 0, ρ)) ∈
      cxK1.d0.domain.prod (cxK1.midDomain.prod cxK1.d1†.domain)
    rw [LinearEquiv.apply_symm_apply]
    exact ⟨zero_mem _, zero_mem _, hρ'⟩
  set x : cxK1.domL := ⟨_, hxmem⟩ with hxdef
  have hmid : (tot R0 L2 L2 (cxK1.waveOp ⟨x.1, x.2⟩)).2.1 = harm := by
    rw [tot_waveOp]
    have h0 : cxK1.pr0 ⟨x.1, x.2⟩ = 0 := Subsingleton.elim _ _
    have h2 : cxK1.prV2s ⟨x.1, x.2⟩ = ⟨ρ, hρ'⟩ := by
      apply Subtype.ext
      change (tot R0 L2 L2 ((tot R0 L2 L2).symm (0, 0, ρ))).2.2 = ρ
      rw [LinearEquiv.apply_symm_apply]
    rw [h0, h2, LinearPMap.map_zero, zero_add]
    exact hinv'
  have hnot : ∀ T > 0, ¬ ∃ ξ ξ' : ℝ → cxK1.toComplex3.VSp, ξ 0 = cxK1.toV x ∧
      cxK1.toComplex3.IsWeakSol T ξ ξ' := by
    intro T hT
    refine cxK1.not_isWeakSol_of_not_mem hT x fun ψ hψ => harm_not_mem ?_
    have hm := cxK1.tot_embW_mem ψ
    rw [hψ, _root_.map_neg, Prod.snd_neg, Prod.fst_neg, hmid] at hm
    have := (cxK1.d1.domain).neg_mem hm
    rw [neg_neg] at this
    exact this
  refine ⟨x, fun hx => ?_, hnot⟩
  obtain ⟨ξ, ξ', h0, hξ, -⟩ := cxK1.exists_isWeakSol_unconditional 1 x hx
  exact hnot 1 one_pos ⟨ξ, ξ', h0, hξ⟩

/-! ### A concrete family of subcomplexes for `cxK1`: coordinate truncation -/

/-- Sequences supported in `{0, …, N-1}`: `span{e_0, …, e_{N-1}} ⊆ ℓ²`. -/
def trunc (N : ℕ) : Submodule ℝ L2 where
  carrier := {x | ∀ n, N ≤ n → x n = 0}
  add_mem' {x y} hx hy n hn := by rw [lp.coeFn_add, Pi.add_apply, hx n hn, hy n hn, add_zero]
  zero_mem' n _ := rfl
  smul_mem' c x hx n hn := by rw [lp.coeFn_smul, Pi.smul_apply, hx n hn, smul_zero]

theorem mem_trunc {N : ℕ} {x : L2} : x ∈ trunc N ↔ ∀ n, N ≤ n → x n = 0 := Iff.rfl

/-- The truncation `P_N x = Σ_{n<N} x_n e_n`. -/
def truncSum (N : ℕ) (x : L2) : L2 := ∑ n ∈ Finset.range N, lp.single 2 n (x n)

theorem truncSum_apply (N : ℕ) (x : L2) (m : ℕ) :
    truncSum N x m = if m < N then x m else 0 := by
  unfold truncSum
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb.symm]
    · intro hm; exact absurd (Finset.mem_range.2 h) hm
  · refine Finset.sum_eq_zero fun b hb => ?_
    have : m ≠ b := fun e => h (e ▸ Finset.mem_range.1 hb)
    simp [Pi.single_eq_of_ne this]

theorem truncSum_mem (N : ℕ) (x : L2) : truncSum N x ∈ trunc N := fun n hn => by
  rw [truncSum_apply]; simp [not_lt.2 hn]

theorem truncSum_eq_self {N : ℕ} {x : L2} (hx : x ∈ trunc N) : truncSum N x = x :=
  lp.ext <| funext fun m => by
    rw [truncSum_apply]
    split_ifs with h
    · rfl
    · exact (hx m (not_lt.1 h)).symm

/-- `P_N x → x` in `ℓ²`. -/
theorem tendsto_truncSum (x : L2) : Tendsto (fun N => truncSum N x) atTop (𝓝 x) :=
  (lp.hasSum_single (by norm_num) x).tendsto_sum_nat

instance (N : ℕ) : FiniteDimensional ℝ (trunc N) := by
  have := FiniteDimensional.span_of_finite ℝ
    (Set.finite_range fun n : Fin N => (lp.single 2 (n : ℕ) (1 : ℝ) : L2))
  refine Submodule.finiteDimensional_of_le
    (S₂ := Submodule.span ℝ (Set.range fun n : Fin N => (lp.single 2 (n : ℕ) (1 : ℝ) : L2)))
    fun x hx => ?_
  rw [← truncSum_eq_self hx]
  refine Submodule.sum_mem _ fun n hn => ?_
  have e : (lp.single 2 n (x n) : L2) = x n • lp.single 2 n (1 : ℝ) :=
    lp.ext <| funext fun m => by
      by_cases h : m = n
      · subst h; simp
      · simp [lp.single_apply, Pi.single_eq_of_ne h]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨n, Finset.mem_range.1 hn⟩, rfl⟩)

/-- `‖A x‖ ≤ ‖x‖`. -/
theorem norm_A_apply_le (x : L2) : ‖A x‖ ≤ ‖x‖ :=
  lp.norm_mono two_ne_zero fun n => by rw [A_apply]; exact norm_div_succ_le _ n

/-- `A` preserves `trunc N`. -/
theorem A_mem_trunc {N : ℕ} {x : L2} (hx : x ∈ trunc N) : A x ∈ trunc N := fun n hn => by
  rw [A_apply, hx n hn, zero_div]

/-- `trunc N ⊆ D(A⁻¹) = R(A)`. -/
theorem trunc_le_domain (N : ℕ) : trunc N ≤ invA.domain := by
  intro x hx
  rw [invA_domain]
  refine ⟨(∑ n ∈ Finset.range N, lp.single 2 n (((n : ℝ) + 1) * x n) : L2), ?_⟩
  · refine lp.ext <| funext fun m => ?_
    change A _ m = x m
    rw [A_apply, lp.coeFn_sum, Finset.sum_apply]
    simp only [lp.single_apply]
    by_cases h : m < N
    · rw [Finset.sum_eq_single m]
      · have : (m : ℝ) + 1 ≠ 0 := by positivity
        simp only [Pi.single_eq_same]; field_simp
      · intro b _ hb; simp [Pi.single_eq_of_ne hb.symm]
      · intro hm; exact absurd (Finset.mem_range.2 h) hm
    · rw [Finset.sum_eq_zero fun b hb => ?_, zero_div, hx m (not_lt.1 h)]
      have : m ≠ b := fun e => h (e ▸ Finset.mem_range.1 hb)
      simp [Pi.single_eq_of_ne this]

/-- `A⁻¹` preserves `trunc N`. -/
theorem invA_mem_trunc {N : ℕ} (u : invA.domain) (hu : (u : L2) ∈ trunc N) :
    invA u ∈ trunc N := fun n hn => by
  have h := congrArg (fun y : L2 => y n) (A_invA u)
  simp only [A_apply] at h
  rw [hu n hn] at h
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  simpa [div_eq_zero_iff, this] using h

/-- **Coordinate truncation subcomplexes of `cxK1`**: `V⁰ₕ = 0`, `V¹ₕ = V²ₕ = span{e_0, …, e_{N-1}}`
(`d1 = diag(n+1)` maps `V¹ₕ` into `V²ₕ`). The spectral Galerkin spaces of the model operator. -/
def cxK1Sub (N : ℕ) : cxK1.toComplex3.Sub where
  V0h := ⊥
  V1h := (trunc N).comap (cxK1.d1.domain.subtype)
  V2h := trunc N
  d0_mem σ _ := by
    have : σ = 0 := Subsingleton.elim _ _
    rw [this, map_zero]; exact zero_mem _
  d1_mem u hu := invA_mem_trunc u hu

instance (N : ℕ) : FiniteDimensional ℝ (cxK1Sub N).V0h :=
  inferInstanceAs (FiniteDimensional ℝ (⊥ : Submodule ℝ cxK1.d0.domain))

instance (N : ℕ) : FiniteDimensional ℝ (cxK1Sub N).V1h :=
  LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe (trunc_le_domain N)).symm

instance (N : ℕ) : FiniteDimensional ℝ (cxK1Sub N).V2h :=
  inferInstanceAs (FiniteDimensional ℝ (trunc N))

/-- Eventually `‖x − P_N x‖² < δ`. -/
theorem eventually_norm_sub_truncSum_sq_lt (x : L2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N in atTop, ‖x - truncSum N x‖ ^ 2 < δ := by
  have hε : 0 < min 1 δ := lt_min one_pos hδ
  filter_upwards [Metric.tendsto_nhds.1 (tendsto_truncSum x) _ hε] with N hN
  rw [dist_eq_norm, norm_sub_rev] at hN
  have h1 : ‖x - truncSum N x‖ < 1 := hN.trans_le (min_le_left _ _)
  have h2 : ‖x - truncSum N x‖ < δ := hN.trans_le (min_le_right _ _)
  nlinarith [norm_nonneg (x - truncSum N x)]

/-- **The truncation family satisfies the density hypothesis** (as `N → ∞`): a concrete,
infinite-dimensional instance of `Complex3.DensityHyp`. For `u ∈ D(A⁻¹)` with `f = A⁻¹ u`, the
approximant `A (P_N f) ∈ V¹ₕ` has `‖u − A P_N f‖ ≤ ‖f − P_N f‖` and `A⁻¹ (u − A P_N f) = f − P_N f`.
See [QuennevilleBelair2015, §4.6] (density hypothesis). -/
theorem cxK1Sub_densityHyp : cxK1.toComplex3.DensityHyp atTop cxK1Sub := by
  refine ⟨fun σ δ hδ => Eventually.of_forall fun N => ⟨0, zero_mem _, ?_⟩,
    fun u δ hδ => ?_, fun ρ δ hδ => ?_⟩
  · have : σ = 0 := Subsingleton.elim _ _
    subst this
    simpa using hδ
  · set f : L2 := invA u
    filter_upwards [eventually_norm_sub_truncSum_sq_lt f (half_pos hδ)] with N hN
    have hmem : A (truncSum N f) ∈ invA.domain :=
      trunc_le_domain N (A_mem_trunc (truncSum_mem N f))
    let v' : invA.domain := ⟨A (truncSum N f), hmem⟩
    have hv : invA v' = truncSum N f := A_injective (A_invA v')
    set v : cxK1.d1.domain := v'
    refine ⟨v, A_mem_trunc (truncSum_mem N f), ?_⟩
    have e1 : ‖u - v‖ ≤ ‖f - truncSum N f‖ := by
      change ‖(u : L2) - A (truncSum N f)‖ ≤ _
      rw [← A_invA u, ← map_sub]
      exact norm_A_apply_le _
    have e2 : cxK1.toComplex3.d1 (u - v) = f - truncSum N f := by
      change cxK1.d1 (u - v) = _
      rw [LinearPMap.map_sub]
      change invA u - invA v' = _
      rw [hv]
    rw [e2]
    have := norm_nonneg (u - v)
    nlinarith
  · filter_upwards [eventually_norm_sub_truncSum_sq_lt ρ hδ] with N hN
    exact ⟨truncSum N ρ, truncSum_mem N ρ, hN⟩

/-- **Convergence without Thm 4.14's regularity, on a concrete infinite-dimensional example.**
For the complex `0 → ℓ² --diag(n+1)--> ℓ²` (`cxK1`) with the coordinate truncation subcomplexes
(`cxK1Sub`, which satisfy the density hypothesis), there is `ξ₀ ∈ D(L) \ D(L²)` such that
* for no `T > 0` is there a weak solution in `C¹([0,T]; V)` starting at `ξ₀` (it fails already at
  `t = 0`: `ξ̇(0) = −L ξ₀ ∉ V`), so `Complex3.thm_4_14` does not apply; yet
* for every `T`, the discrete solutions with `ξₕ(0) = Πₕ ξ₀` exist and converge to the
  thesis-class weak solution (equivalently, to `e^{-tL} ξ₀`) in `W`, uniformly on `[0,T]`.
See [QuennevilleBelair2015, Thm 4.14 and the remark after it]. -/
theorem cxK1_convergence_without_C1 :
    ∃ x : cxK1.domL, (cxK1.waveOp ⟨x.1, x.2⟩ : Tot R0 L2 L2) ∉ cxK1.domL ∧
      (∀ T > 0, ¬ ∃ ξ ξ' : ℝ → cxK1.toComplex3.VSp, ξ 0 = cxK1.toV x ∧
        cxK1.toComplex3.IsWeakSol T ξ ξ') ∧
      ∀ T : ℝ, ∃ ξ, cxK1.IsClassicalWeakSolution T x ξ ∧
        ∃ ξh ξh' : ℕ → ℝ → cxK1.toComplex3.VSp,
          (∀ N, cxK1.toComplex3.IsDiscreteSol (cxK1Sub N) T (ξh N) (ξh' N)) ∧
          (∀ N, ξh N 0 = cxK1.toComplex3.ellProj (cxK1Sub N) (cxK1.toV x)) ∧
          TendstoUniformlyOn (fun N t => cxK1.embW (ξh N t)) ξ atTop (Icc 0 T) := by
  obtain ⟨x, hx, hnot⟩ := cxK1_exists_not_isWeakSol
  refine ⟨x, hx, hnot, fun T => ?_⟩
  obtain ⟨ξ, hξ, -, ξh, ξh', hsol, hinit, hc⟩ :=
    cxK1.convergence_domL_classicalWeak_exists cxK1Sub_densityHyp T x
  exact ⟨ξ, hξ, ξh, ξh', hsol, hinit, hc⟩

end FredholmCE

end Feec
