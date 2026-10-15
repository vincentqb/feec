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
  `HilbertComplex2.convergence_W`: for every `ξ₀ ∈ W` (the solution is then the mild solution
  `e^{-tL} ξ₀` of the Stone group) and every choice of discrete data with `ξₕ(0) → ξ₀` in `W`,
  the same uniform convergence holds; `HilbertComplex2.exists_init_W` constructs such data
  (the `W`-orthogonal projection onto `Vₕ`), and `convergence_W_exists` packages both.
  The proof is a stability-plus-density argument: approximate `ξ₀` in `W` by `ζ₀ ∈ D(L²)`
  (`IsSkewAdjoint.exists_mem_domain_sq_near`, via the resolvent `c (c - A)⁻¹`), apply the
  `D(L²)` result to `ζ₀`, and control the rest by `‖e^{-tL}‖ = 1` and the `W`-stability of the
  semi-discrete flow (`Complex3.discrete_stability`, uniform in `h`).
* **An error estimate in terms of the regularity of `ξ₀`** (`HilbertComplex2.error_bound_W`,
  `error_bound_W'`): for every `ζ₀ ∈ D(L²)`, with `ζ` its exact solution and `e = Πₕζ − ζ`,
  `‖e^{-tL}ξ₀ − ξₕ(t)‖_W ≤ 2‖ξ₀ − ζ₀‖_W + ‖ξ₀ − ξₕ(0)‖_W + ‖e(t)‖_W + (1 + t)(‖e(0)‖_W +
  ∫₀ᵗ ‖ė‖_W)`. Minimizing over `ζ₀` gives a K-functional bound between `W` and `D(L²)`; rates
  for `ξ₀ ∈ D(L)` or `W` follow from rates of approximation of `ξ₀` by `D(L²)` data, which are
  not formalized.
* **Thm 4.14 itself does not cover `D(L)` data.** `HilbertComplex2.embW_deriv_zero_of_isWeakSol`:
  a weak solution in `C¹([0,T]; V)` (`T > 0`) has `ξ̇(0) = −L ξ₀`, so `L ξ₀ ∈ V` is necessary
  (`not_isWeakSol_of_not_mem`). `FredholmCE.cxK1_exists_not_isWeakSol`: for the complex
  `0 → ℓ² --diag(n+1)--> ℓ²` there is `ξ₀ ∈ D(L) \ D(L²)` for which no weak solution in
  `C¹([0,T]; V)` exists for any `T > 0`; so the right side of Thm 4.14, which involves
  `Πₕ ξ̇`, is not available, while `convergence_domL` still gives convergence (without rate).

Thesis gap: the remark after Thm 4.14 does not say which data are allowed; Thm 4.14's bound
needs `ξ̇ ∈ V` (`ξ ∈ C¹([0,T]; V)` in the corrected form), which fails for some `D(L)` data
(`cxK1_exists_not_isWeakSol`). Convergence nevertheless holds for all `D(L)` data, and even for
all `W` data, but by a density argument, not from the bound of Thm 4.14.

Scope: the density hypothesis `Complex3.DensityHyp` on the subcomplexes is assumed as in the
thesis; this module does not construct a family satisfying it in infinite dimensions (in
particular not for `cxK1`).

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
See [QuennevilleBelair2015, §4.6]; this is the estimate behind `Complex3.discrete_solution_unique`. -/
theorem discrete_stability (S : C.Sub) {T : ℝ} {ξ₁ ξ₁' ξ₂ ξ₂' : ℝ → C.VSp}
    (h₁ : C.IsDiscreteSol S T ξ₁ ξ₁') (h₂ : C.IsDiscreteSol S T ξ₂ ξ₂') :
    ∀ t ∈ Icc 0 T, ‖C.toW (ξ₁ t - ξ₂ t)‖ ≤ ‖C.toW (ξ₁ 0 - ξ₂ 0)‖ := by
  obtain ⟨c₁, m₁, d₁, e₁⟩ := h₁
  obtain ⟨c₂, m₂, d₂, e₂⟩ := h₂
  set e : ℝ → Tot X0 X1 X2 := fun t => C.toW (ξ₁ t - ξ₂ t) with he
  have hec : ContinuousOn e (Icc 0 T) := C.toW.continuous.comp_continuousOn (c₁.sub c₂)
  have hed : ∀ t ∈ Ico 0 T, HasDerivWithinAt e (C.toW (ξ₁' t - ξ₂' t)) (Ici t) t :=
    fun t ht => C.toW.hasFDerivAt.comp_hasDerivWithinAt t ((d₁ t ht).sub (d₂ t ht))
  have key := lemma_4_12 (Q := fun t => ‖e t‖) (q' := fun t => 2 * ⟪e t, C.toW (ξ₁' t - ξ₂' t)⟫)
    (F := fun _ => 0) (G := fun _ => 0) hec.norm (fun _ _ => norm_nonneg _)
    (fun t ht => (hed t ht).norm_sq) continuousOn_const
    (fun t _ => hasDerivWithinAt_const _ _ _) (fun _ _ => le_rfl)
    (fun t ht => by
      have hm : ξ₁ t - ξ₂ t ∈ S.toV :=
        S.toV.sub_mem (m₁ t (Ico_subset_Icc_self ht)) (m₂ t (Ico_subset_Icc_self ht))
      have E1 := e₁ t ht _ hm
      have E2 := e₂ t ht _ hm
      have hs := C.aL_self (ξ₁ t - ξ₂ t)
      simp only [he, map_sub, inner_sub_left, inner_sub_right, LinearMap.sub_apply] at E1 E2 hs ⊢
      have r1 := real_inner_comm (C.toW (ξ₁ t)) (C.toW (ξ₁' t))
      have r2 := real_inner_comm (C.toW (ξ₁ t)) (C.toW (ξ₂' t))
      have r3 := real_inner_comm (C.toW (ξ₂ t)) (C.toW (ξ₁' t))
      have r4 := real_inner_comm (C.toW (ξ₂ t)) (C.toW (ξ₂' t))
      rw [zero_mul]
      linarith)
  intro t ht
  have h := key t ht
  simpa only [he, sub_self, zero_div, add_zero] using h

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

/-- **Error bound in terms of the regularity of `ξ₀`** (K-functional form of
`error_bound_W`): for every `x ∈ D(L²)` with exact solution `ζ` and `e = Πₕζ − ζ`,
`‖e^{-tL}ξ₀ − ξₕ(t)‖_W ≤ 2‖ξ₀ − x‖_W + ‖ξ₀ − ξₕ(0)‖_W + ‖e(t)‖_W + (1 + t) ‖e(0)‖_W
+ (1 + t) ∫₀ᵗ ‖ė‖_W`.
Only `W`-quantities of the data enter besides the elliptic-projection errors of the comparison
solution; taking the infimum over `x` bounds the error by approximation of `ξ₀` by `D(L²)` data.
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
`(1/(n+1))ₙ ∉ D(diag(n+1))`. Convergence still holds for this datum (`convergence_domL`).
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

end FredholmCE

end Feec
