module

public import Feec.TimeStepping.Rational

/-!
# Rational approximations of semigroups with unbounded generators

Let `A` be an m-dissipative, possibly unbounded, operator of a Hilbert space over `𝕜 = ℝ` or `ℂ`,
`S(t)` the contraction semigroup it generates (Lumer–Phillips,
`LinearPMap.IsMDissipative.semigroup`), and `r` an A-stable rational scheme of order `p`. Then
**Brenner–Thomée's error bound** holds with the constant of the bounded case
([BrennerThomee1979], Thms 1 and 3; [Thomee2006], Ch. 7–8):

  `‖r(τA)ⁿ x - S(nτ) x‖ ≤ K nτ τᵖ ‖A^{p+1} x‖`, `K = sup_y |ρ(iy)| + 1/(p+1)!`,

for every `τ > 0`, `n` and `x ∈ D(A^{p+1})`, with `r(τA)` the operator of `Feec.TimeStepping.Rational`
(through the Cayley transform, equivalently the resolvent). `x ∈ D(A^k)` with `Aᵏ x = y` is a
chain `u₀ = x, …, u_k = y` with `(u_j, u_{j+1})` in the graph of `A`.

## Main results

* **`RationalScheme.norm_step_pow_sub_semigroup_le`**: real `r`, Hilbert spaces over `𝕜`;
* **`norm_resolventEval_mul_inverse_pow_sub_semigroup_le`**: complex `r = p/q` on complex Hilbert
  spaces, `r(τA) = P(S) Q(S)⁻¹` at the resolvent `S = (1 - τA)⁻¹`;
* **`norm_thetaStep_pow_sub_semigroup_le`** (θ-schemes, `θ ≥ 1/2`: `K = θ + 1/2`, order `1`) and
  **`norm_cayley_pow_sub_semigroup_le`** (Crank–Nicolson: `K = 5/12`, order `2`).

## Proof

Through the Yosida approximations `A_m = c_m A (c_m - A)⁻¹` (`Feec.LumerPhillips.yosida`), bounded
and dissipative: the bounded theorem (`RationalScheme.norm_apply_pow_sub_exp_le`) holds for each
`A_m` with the same constant, `A_m^k x = J_mᵏ Aᵏ x` on `D(Aᵏ)` with the contractions
`J_m = c_m (c_m - A)⁻¹` (`yosida_pow_apply`), and both sides converge: `exp(t A_m) x → S(t) x` by
construction of `S`, and `r(τ A_m) → r(τ A)` strongly. For the latter, the resolvents converge
strongly (`tendsto_resolvent_yosida`: `(z - A_m)⁻¹ y - (z - A)⁻¹ y = (z - A_m)⁻¹ (A_m x - A x)` at
`x = (z - A)⁻¹ y`), hence the Cayley transforms; polynomials in uniformly bounded, strongly
convergent operators converge strongly (`tendsto_aeval_apply`), and so do the inverses
`q̃(C_m)⁻¹`, uniformly bounded by von Neumann's inequality for `1/q̃` (`tendsto_inverse_apply`).
No Taylor formula for the unbounded semigroup is needed: it is inherited from the bounded case.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979],
  Thms 1, 3
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7–8
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.3 (the Yosida approximation), §1.4

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Filter Polynomial LinearPMap Feec.Operator Feec.LumerPhillips NormedSpace

@[expose] public noncomputable section

namespace Feec.TimeStepping

/-! ### Strong convergence of bounded operators -/

section Strong

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] {ι : Type*}
  {l : Filter ι}

/-- **Uniformly bounded, strongly convergent operators at a convergent sequence**: if
`‖Pᵢ‖ ≤ M`, `Pᵢ y → P y` for every `y` and `wᵢ → w`, then `Pᵢ wᵢ → P w`. -/
theorem tendsto_apply_of_tendsto {P : ι → V →L[𝕜] V} {P₀ : V →L[𝕜] V} {M : ℝ}
    (hM : ∀ i, ‖P i‖ ≤ M) (hP : ∀ y, Tendsto (fun i => P i y) l (𝓝 (P₀ y))) {w : ι → V}
    {w₀ : V} (hw : Tendsto w l (𝓝 w₀)) : Tendsto (fun i => P i (w i)) l (𝓝 (P₀ w₀)) := by
  have h0 : Tendsto (fun i => P i (w i - w₀)) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ((P i).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hM i) (norm_nonneg _))) ?_
    simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hw).const_mul M
  have := h0.add (hP w₀)
  rw [zero_add] at this
  exact this.congr fun i => by rw [← _root_.map_add, sub_add_cancel]

/-- Powers of uniformly bounded, strongly convergent operators converge strongly. -/
theorem tendsto_pow_apply {P : ι → V →L[𝕜] V} {P₀ : V →L[𝕜] V} {M : ℝ} (hM : ∀ i, ‖P i‖ ≤ M)
    (hP : ∀ y, Tendsto (fun i => P i y) l (𝓝 (P₀ y))) (k : ℕ) (y : V) :
    Tendsto (fun i => (P i ^ k) y) l (𝓝 ((P₀ ^ k) y)) := by
  induction k with
  | zero => simpa using tendsto_const_nhds
  | succ k ih =>
    simpa only [pow_succ', mul_apply_eq_comp] using tendsto_apply_of_tendsto hM hP ih

/-- **Polynomials** in uniformly bounded, strongly convergent operators converge strongly. -/
theorem tendsto_aeval_apply {T : ι → V →L[𝕜] V} {T₀ : V →L[𝕜] V} {M : ℝ} (hM : ∀ i, ‖T i‖ ≤ M)
    (hT : ∀ y, Tendsto (fun i => T i y) l (𝓝 (T₀ y))) (f : 𝕜[X]) (y : V) :
    Tendsto (fun i => aeval (T i) f y) l (𝓝 (aeval T₀ f y)) := by
  simp only [aeval_eq_sum_range, sum_apply, _root_.smul_apply]
  exact tendsto_finsetSum _ fun k _ => (tendsto_pow_apply hM hT k y).const_smul _

/-- **Inverses** of strongly convergent invertible operators with uniformly bounded inverses
converge strongly: `Bᵢ⁻¹ y - B⁻¹ y = Bᵢ⁻¹ (B - Bᵢ) B⁻¹ y`. -/
theorem tendsto_inverse_apply {B : ι → V →L[𝕜] V} {B₀ : V →L[𝕜] V}
    (hB : ∀ y, Tendsto (fun i => B i y) l (𝓝 (B₀ y))) (hu : ∀ i, IsUnit (B i)) (hu₀ : IsUnit B₀)
    {M : ℝ} (hM : ∀ i, ‖Ring.inverse (B i)‖ ≤ M) (y : V) :
    Tendsto (fun i => Ring.inverse (B i) y) l (𝓝 (Ring.inverse B₀ y)) := by
  set z := Ring.inverse B₀ y
  have hz : B₀ z = y := congrArg (fun T : V →L[𝕜] V => T y) (Ring.mul_inverse_cancel B₀ hu₀)
  have e : ∀ i, Ring.inverse (B i) y - z = Ring.inverse (B i) (B₀ z - B i z) := fun i => by
    have h : Ring.inverse (B i) (B i z) = z :=
      congrArg (fun T : V →L[𝕜] V => T z) (Ring.inverse_mul_cancel (B i) (hu i))
    rw [_root_.map_sub, h, hz]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_)
    (by simpa [norm_sub_rev] using (tendsto_iff_norm_sub_tendsto_zero.1 (hB z)).const_mul M)
  rw [e]
  exact ((Ring.inverse (B i)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hM i) (norm_nonneg _))

/-- **Rational functions** `f(Tᵢ) g(Tᵢ)⁻¹` of uniformly bounded, strongly convergent operators
converge strongly when the inverses are uniformly bounded. -/
theorem tendsto_aeval_mul_inverse_apply {T : ι → V →L[𝕜] V} {T₀ : V →L[𝕜] V} {M : ℝ}
    (hM : ∀ i, ‖T i‖ ≤ M) (hT : ∀ y, Tendsto (fun i => T i y) l (𝓝 (T₀ y))) (f g : 𝕜[X])
    (hu : ∀ i, IsUnit (aeval (T i) g)) (hu₀ : IsUnit (aeval T₀ g)) {M' : ℝ}
    (hM' : ∀ i, ‖Ring.inverse (aeval (T i) g)‖ ≤ M') (y : V) :
    Tendsto (fun i => (aeval (T i) f * Ring.inverse (aeval (T i) g)) y) l
      (𝓝 ((aeval T₀ f * Ring.inverse (aeval T₀ g)) y)) := by
  have hc : ∀ T : V →L[𝕜] V, aeval T f * Ring.inverse (aeval T g) =
      Ring.inverse (aeval T g) * aeval T f := fun T =>
    (RationalScheme.commute_ringInverse ((Commute.all f g).map (aeval T))).eq
  simp only [hc]
  exact tendsto_apply_of_tendsto hM' (tendsto_inverse_apply (tendsto_aeval_apply hM hT g) hu hu₀
    hM') (tendsto_aeval_apply hM hT f y)

end Strong

/-! ### The Yosida approximations -/

section Yosida

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {A : E →ₗ.[𝕜] E}

/-- The Yosida approximation `A_m`, everywhere defined, is m-dissipative. -/
theorem isMDissipative_yosida (hA : A.IsMDissipative) (m : ℕ) :
    ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤).IsMDissipative :=
  (yosida A m).isMDissipative_toPMap_top (re_inner_yosida_le hA m)

/-- **The resolvents of the Yosida approximations converge strongly**: for `re z > 0`,
`(z - A_m)⁻¹ y → (z - A)⁻¹ y`, since `(z - A_m)⁻¹ y - x = (z - A_m)⁻¹ (A_m x - A x)` at
`x = (z - A)⁻¹ y ∈ D(A)`, `‖(z - A_m)⁻¹‖ ≤ 1/re z` and `A_m x → A x`. -/
theorem tendsto_resolvent_yosida (hA : A.IsMDissipative) {z : 𝕜} (hz : 0 < RCLike.re z)
    (y : E) :
    Tendsto (fun m => resolvent ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) z y) atTop
      (𝓝 (resolvent A z y)) := by
  have hR := hA.isResolvent_of_re_pos hz
  set x : A.domain := hR.toDomain y
  have hRm : ∀ m, IsResolvent ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) z
      (resolvent ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) z) := fun m =>
    (isMDissipative_yosida hA m).isResolvent_of_re_pos hz
  have e : ∀ m, resolvent ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) z y - resolvent A z y =
      resolvent ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) z (yosida A m x - A x) := fun m => by
    have h1 : resolvent ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) z (z • (x : E) - yosida A m x) =
        x := (hRm m).apply_sub ⟨(x : E), trivial⟩
    have h2 : z • (x : E) - A x = y := hR.sub_apply_toDomain y
    calc _ = resolvent ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) z y -
          resolvent ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) z (z • (x : E) - yosida A m x) := by
          rw [h1]; rfl
      _ = _ := by rw [← _root_.map_sub]; congr 1; rw [← h2]; abel
  have hA' := (tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_yosida hA x)).const_mul
    (RCLike.re z)⁻¹
  rw [mul_zero] at hA'
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) hA'
  rw [e]
  exact ((Operator.resolvent _ z).le_opNorm _).trans (mul_le_mul_of_nonneg_right
    ((hRm m).norm_le_of_isDissipative (isMDissipative_yosida hA m).dissipative hz)
    (norm_nonneg _))

/-- The Cayley transforms of the Yosida approximations converge strongly. -/
theorem tendsto_cayley_yosida (hA : A.IsMDissipative) {τ : ℝ} (hτ : 0 < τ) (y : E) :
    Tendsto (fun m => cayley ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) τ y) atTop
      (𝓝 (cayley A τ y)) := by
  have hz : 0 < RCLike.re ((τ : 𝕜)⁻¹) := by
    rw [← RCLike.ofReal_inv, RCLike.ofReal_re]; positivity
  simp only [cayley, _root_.sub_apply, _root_.smul_apply,
    one_apply_eq_self]
  exact ((tendsto_resolvent_yosida hA hz y).const_smul _).sub_const _

/-- The θ-steps of the Yosida approximations converge strongly (`re θ > 0`, `τ > 0`). -/
theorem tendsto_thetaStep_yosida (hA : A.IsMDissipative) {θ : 𝕜} (hθ : 0 < RCLike.re θ)
    {τ : ℝ} (hτ : 0 < τ) (y : E) :
    Tendsto (fun m => thetaStep ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) θ τ y) atTop
      (𝓝 (thetaStep A θ τ y)) := by
  simp only [thetaStep, _root_.sub_apply, _root_.smul_apply]
  exact ((tendsto_resolvent_yosida hA (re_inv_mul_pos hθ hτ) y).const_smul _).sub_const _

/-- **The Yosida approximations on `D(Aᵏ)`**: for a chain `u₀, …, u_k` with `(u_j, u_{j+1})` in
the graph of `A` (so `u₀ ∈ D(Aᵏ)`, `Aᵏ u₀ = u_k`), `A_mᵏ u₀ = J_mᵏ u_k` with `J_m = c_m R(c_m)`. -/
theorem yosida_pow_apply (hA : A.IsMDissipative) (m : ℕ) {k : ℕ} {u : ℕ → E}
    (hu : ∀ j < k, (u j, u (j + 1)) ∈ A.graph) : (yosida A m ^ k) (u 0) = (approxJ A m ^ k) (u k) := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih =>
    obtain ⟨x, hx1, hx2⟩ := (mem_graph_iff A).1 (hu 0 (Nat.succ_pos k))
    simp only [zero_add] at hx1 hx2
    have hy : yosida A m (u 0) = approxJ A m (u 1) := by
      rw [← hx1, yosida_apply_domain hA, hx2]
    have hc : Commute (yosida A m) (approxJ A m) :=
      ((Commute.refl _).smul_left _).sub_left ((Commute.one_left _).smul_left _)
    have ih' := ih (u := fun j => u (j + 1)) fun j hj => hu (j + 1) (by omega)
    simp only [zero_add] at ih'
    calc (yosida A m ^ (k + 1)) (u 0) = (yosida A m ^ k) (approxJ A m (u 1)) := by
          rw [pow_succ, mul_apply_eq_comp, hy]
      _ = approxJ A m ((yosida A m ^ k) (u 1)) := by
          rw [← mul_apply_eq_comp, (hc.pow_left k).eq, mul_apply_eq_comp]
      _ = (approxJ A m ^ (k + 1)) (u (k + 1)) := by
          rw [ih', pow_succ', mul_apply_eq_comp]

/-- `‖J_mᵏ y‖ ≤ ‖y‖`. -/
theorem norm_approxJ_pow_apply_le (hA : A.IsMDissipative) (m k : ℕ) (y : E) :
    ‖(approxJ A m ^ k) y‖ ≤ ‖y‖ := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, mul_apply_eq_comp]
    exact (ih _).trans (norm_approxJ_apply_le hA m y)

/-- `‖A_mᵏ u₀‖ ≤ ‖Aᵏ u₀‖` on `D(Aᵏ)`, uniformly in `m`. -/
theorem norm_yosida_pow_apply_le (hA : A.IsMDissipative) (m : ℕ) {k : ℕ} {u : ℕ → E}
    (hu : ∀ j < k, (u j, u (j + 1)) ∈ A.graph) : ‖(yosida A m ^ k) (u 0)‖ ≤ ‖u k‖ := by
  rw [yosida_pow_apply hA m hu]
  exact norm_approxJ_pow_apply_le hA m k _

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **Error bounds pass to the limit of the Yosida approximations**: if `Pₘ → P` strongly with
`‖Pₘ‖ ≤ 1`, and `‖Pₘⁿ u₀ - exp(t A_m) u₀‖ ≤ C ‖A_mᵏ u₀‖` for every `m`, then
`‖Pⁿ u₀ - S(t) u₀‖ ≤ C ‖Aᵏ u₀‖` for the Lumer–Phillips semigroup `S` and `u₀ ∈ D(Aᵏ)`. -/
theorem norm_pow_apply_sub_semigroup_le (hA : A.IsMDissipative) {P : E →L[𝕜] E}
    {Pm : ℕ → E →L[𝕜] E} (hPm : ∀ m, ‖Pm m‖ ≤ 1)
    (hP : ∀ y, Tendsto (fun m => Pm m y) atTop (𝓝 (P y))) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    {u : ℕ → E} (hu : ∀ j < k, (u j, u (j + 1)) ∈ A.graph) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ m, ‖(Pm m ^ n) (u 0) - exp ((t : 𝕜) • yosida A m) (u 0)‖ ≤
      C * ‖(yosida A m ^ k) (u 0)‖) :
    ‖(P ^ n) (u 0) - hA.semigroup.S t (u 0)‖ ≤ C * ‖u k‖ :=
  le_of_tendsto' ((tendsto_pow_apply hPm hP n (u 0)).sub (tendsto_approxS hA ht (u 0))).norm
    fun m => (hb m).trans (mul_le_mul_of_nonneg_left (norm_yosida_pow_apply_le hA m hu) hC)

end Yosida

/-! ### Brenner–Thomée for unbounded generators -/

section Unbounded

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {A : E →ₗ.[𝕜] E}

/-- The inverse `Ring.inverse (aeval T (d̃.map _))` is bounded uniformly in the contraction `T`:
von Neumann's inequality for `1/d̃`, with `d̃` free of zeros in the closed unit disc. -/
theorem RationalScheme.exists_norm_inverse_le (r : RationalScheme) :
    ∃ M : ℝ, ∀ T : E →L[𝕜] E, ‖T‖ ≤ 1 →
      ‖Ring.inverse (aeval T (r.cden.map (algebraMap ℝ 𝕜)))‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn
    (f := fun w : ℂ => aeval w (1 : ℝ[X]) / aeval w r.cden)
    ((Polynomial.continuous_aeval _).continuousOn.div (Polynomial.continuous_aeval _).continuousOn
      fun w hw => r.aeval_cden_ne_zero (mem_sphere_zero_iff_norm.1 hw).le)
  refine ⟨M, fun T hT => ?_⟩
  have h := (ContinuousLinearMap.norm_aeval_map_mul_inverse_le hT (p := 1) (q := r.cden)
    (fun w hw => r.aeval_cden_ne_zero hw) fun ζ hζ _ =>
      hM ζ (mem_sphere_zero_iff_norm.2 hζ)).2
  rwa [Polynomial.map_one, map_one, one_mul] at h

/-- **`r(τ A_m) → r(τ A)` strongly** for the Yosida approximations `A_m` of an m-dissipative `A`
and `τ > 0`. -/
theorem RationalScheme.tendsto_step_yosida (r : RationalScheme) (hA : A.IsMDissipative) {τ : ℝ}
    (hτ : 0 < τ) (y : E) :
    Tendsto (fun m => r.step ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) τ y) atTop
      (𝓝 (r.step A τ y)) := by
  obtain ⟨M, hM⟩ := r.exists_norm_inverse_le (E := E) (𝕜 := 𝕜)
  exact tendsto_aeval_mul_inverse_apply (fun m => norm_cayley_le (isMDissipative_yosida hA m) hτ)
    (tendsto_cayley_yosida hA hτ) _ _ (fun m => (r.norm_step_le (isMDissipative_yosida hA m) hτ).1)
    (r.norm_step_le hA hτ).1 (fun m => hM _ (norm_cayley_le (isMDissipative_yosida hA m) hτ)) y

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **Brenner–Thomée for unbounded generators**: for an A-stable rational scheme `r` of order `p`,
every m-dissipative `A` with semigroup `S`, `τ > 0`, `n` and `u₀ ∈ D(A^{p+1})` (a chain
`u₀, …, u_{p+1}` in the graph of `A`, `A^{p+1} u₀ = u_{p+1}`),
`‖r(τA)ⁿ u₀ - S(nτ) u₀‖ ≤ K nτ τᵖ ‖A^{p+1} u₀‖` with `K = sup_y |ρ(iy)| + 1/(p+1)!` (`ρ` the
remainder), the constant of the bounded case. [BrennerThomee1979], Thms 1, 3; [Thomee2006],
Ch. 7–8 -/
theorem RationalScheme.norm_step_pow_sub_semigroup_le (r : RationalScheme) (hA : A.IsMDissipative)
    (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {u : ℕ → E}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ A.graph) :
    ‖(r.step A τ ^ n) (u 0) - hA.semigroup.S (n * τ) (u 0)‖ ≤
      ((r.remainder p).supNorm + 1 / (p + 1).factorial) * (n * τ) * τ ^ p * ‖u (p + 1)‖ := by
  have hK : 0 ≤ (r.remainder p).supNorm + 1 / ((p + 1).factorial : ℝ) :=
    add_nonneg (r.remainder p).supNorm_nonneg (by positivity)
  refine norm_pow_apply_sub_semigroup_le hA
    (fun m => r.norm_step_le_one (isMDissipative_yosida hA m) hτ hr) (r.tendsto_step_yosida hA hτ)
    n (by positivity) hu (by positivity) fun m => ?_
  rw [r.step_toPMap (re_inner_yosida_le hA m) hτ]
  exact r.norm_apply_pow_sub_exp_le (re_inner_yosida_le hA m) hr hp hτ.le n (u 0)

/-- **Brenner–Thomée for the θ-schemes** (`θ ≥ 1/2`): for every m-dissipative `A`, `τ > 0`, `n`
and `u₀ ∈ D(A²)`, `‖r_θ(τA)ⁿ u₀ - S(nτ) u₀‖ ≤ (θ + 1/2) nτ τ ‖A² u₀‖`; `θ = 1` is implicit
Euler. [Thomee2006], Ch. 7 -/
theorem norm_thetaStep_pow_sub_semigroup_le (hA : A.IsMDissipative) {θ : ℝ} (hθ : 1 / 2 ≤ θ)
    {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {u : ℕ → E} (hu : ∀ j < 2, (u j, u (j + 1)) ∈ A.graph) :
    ‖(thetaStep A θ τ ^ n) (u 0) - hA.semigroup.S (n * τ) (u 0)‖ ≤
      (θ + 1 / 2) * (n * τ) * τ * ‖u 2‖ := by
  have hθ' : 1 / 2 ≤ RCLike.re (θ : 𝕜) := by rwa [RCLike.ofReal_re]
  exact norm_pow_apply_sub_semigroup_le hA
    (fun m => norm_thetaStep_le (isMDissipative_yosida hA m) hθ' hτ)
    (tendsto_thetaStep_yosida hA (by linarith) hτ) n (by positivity) hu (by positivity)
    fun m => norm_thetaStep_pow_sub_exp_le (re_inner_yosida_le hA m) hθ hτ n (u 0)

/-- **Brenner–Thomée for Crank–Nicolson** (the Cayley transform with half step `τ/2`): for every
m-dissipative `A`, `τ > 0`, `n` and `u₀ ∈ D(A³)`,
`‖C_{τ/2}ⁿ u₀ - S(nτ) u₀‖ ≤ 5/12 nτ τ² ‖A³ u₀‖`. [BrennerThomee1979]; [Thomee2006], Ch. 7 -/
theorem norm_cayley_pow_sub_semigroup_le (hA : A.IsMDissipative) {τ : ℝ} (hτ : 0 < τ) (n : ℕ)
    {u : ℕ → E} (hu : ∀ j < 3, (u j, u (j + 1)) ∈ A.graph) :
    ‖(cayley A (τ / 2) ^ n) (u 0) - hA.semigroup.S (n * τ) (u 0)‖ ≤
      5 / 12 * (n * τ) * τ ^ 2 * ‖u 3‖ :=
  norm_pow_apply_sub_semigroup_le hA (fun m => norm_cayley_le (isMDissipative_yosida hA m)
    (half_pos hτ)) (tendsto_cayley_yosida hA (half_pos hτ)) n (by positivity) hu (by positivity)
    fun m => norm_cayley_pow_sub_exp_le (re_inner_yosida_le hA m) hτ n (u 0)

end Unbounded

/-! ### Complex coefficients -/

section Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : E →ₗ.[ℂ] E}

/-- **Brenner–Thomée for unbounded generators, complex coefficients**: let `r = p/q` be complex,
without poles for `re z ≤ 0`, A-stable (`|r(iy)| ≤ 1`) and of order `m`
(`X^{m+1} ∣ p - q Tₘ`). For every m-dissipative `A` of a complex Hilbert space with semigroup
`S`, `τ > 0`, `n` and `u₀ ∈ D(A^{m+1})` (a chain in the graph of `A`), with
`r(τA) = P(S') Q(S')⁻¹` at the resolvent `S' = (1 - τA)⁻¹` (`resolventEval`, `N = deg q`),
`‖r(τA)ⁿ u₀ - S(nτ) u₀‖ ≤ K nτ τᵐ ‖A^{m+1} u₀‖` with `K = sup_y |ρ(iy)/q(iy)| + 1/(m+1)!`,
`ρ = (p - q Tₘ)/X^{m+1}`. [BrennerThomee1979], Thms 1, 3 -/
theorem norm_resolventEval_mul_inverse_pow_sub_semigroup_le (hA : A.IsMDissipative) {p q : ℂ[X]}
    (hq : ∀ z : ℂ, z.re ≤ 0 → q.eval z ≠ 0)
    (hr : ∀ y : ℝ, ‖p.eval (y * Complex.I) / q.eval (y * Complex.I)‖ ≤ 1) {m : ℕ}
    (hm : X ^ (m + 1) ∣ p - q * (expTaylor m).map (algebraMap ℝ ℂ)) {τ : ℝ} (hτ : 0 < τ)
    (n : ℕ) {u : ℕ → E} (hu : ∀ j < m + 1, (u j, u (j + 1)) ∈ A.graph) :
    ‖((resolventEval q.natDegree p ((τ : ℂ)⁻¹ • resolvent A (τ : ℂ)⁻¹) *
          Ring.inverse (resolventEval q.natDegree q ((τ : ℂ)⁻¹ • resolvent A (τ : ℂ)⁻¹))) ^ n)
          (u 0) - hA.semigroup.S (n * τ) (u 0)‖ ≤
      ((⨆ y : ℝ, ‖((p - q * (expTaylor m).map (algebraMap ℝ ℂ)) /ₘ X ^ (m + 1)).eval
          (y * Complex.I) / q.eval (y * Complex.I)‖) + 1 / (m + 1).factorial) *
        (n * τ) * τ ^ m * ‖u (m + 1)‖ := by
  set N := q.natDegree
  have hpq := natDegree_le_of_norm_div_imaginary_le hq hr
  -- the Cayley form, at `A` and at its Yosida approximations
  set F : (E →ₗ.[ℂ] E) → E →L[ℂ] E := fun B =>
    aeval (cayley B τ) (cayleyPoly N p) * Ring.inverse (aeval (cayley B τ) (cayleyPoly N q))
  have hF : ∀ k, F ((yosida A k : E →ₗ[ℂ] E).toPMap ⊤) =
      aeval ((τ : ℂ) • yosida A k) p * Ring.inverse (aeval ((τ : ℂ) • yosida A k) q) := fun k =>
    aeval_cayley_mul_inverse (re_inner_yosida_le hA k) hτ hpq le_rfl
  -- `q̃` has no zero in the closed disc, so `‖q̃(C)⁻¹‖` is bounded uniformly in the contraction `C`
  have hq' : ∀ w : ℂ, ‖w‖ ≤ 1 → (cayleyPoly N q).eval w ≠ 0 := fun w hw =>
    eval_cayleyPoly_ne_zero hq hw
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn
    (f := fun w : ℂ => (1 : ℂ[X]).eval w / (cayleyPoly N q).eval w)
    ((Polynomial.continuous _).continuousOn.div (Polynomial.continuous _).continuousOn
      fun w hw => hq' w (mem_sphere_zero_iff_norm.1 hw).le)
  have hinv : ∀ {T : E →L[ℂ] E}, ‖T‖ ≤ 1 → IsUnit (aeval T (cayleyPoly N q)) ∧
      ‖Ring.inverse (aeval T (cayleyPoly N q))‖ ≤ M := fun hT => by
    have h := ContinuousLinearMap.norm_aeval_mul_inverse_le hT (p := 1) hq' fun ζ hζ _ =>
      hM ζ (mem_sphere_zero_iff_norm.2 hζ)
    rwa [map_one, one_mul] at h
  have hCk : ∀ k, ‖cayley ((yosida A k : E →ₗ[ℂ] E).toPMap ⊤) τ‖ ≤ 1 := fun k =>
    norm_cayley_le (isMDissipative_yosida hA k) hτ
  rw [show resolventEval N p ((τ : ℂ)⁻¹ • resolvent A (τ : ℂ)⁻¹) *
      Ring.inverse (resolventEval N q ((τ : ℂ)⁻¹ • resolvent A (τ : ℂ)⁻¹)) = F A from
    resolventEval_mul_inverse_eq A τ N p q]
  have hb := bddAbove_norm_div_imaginary (p := (p - q * (expTaylor m).map (algebraMap ℝ ℂ)) /ₘ
    X ^ (m + 1)) (q := q) (by
      rw [natDegree_divByMonic _ (monic_X_pow _), natDegree_X_pow]
      have h1 := natDegree_sub_le p (q * (expTaylor m).map (algebraMap ℝ ℂ))
      have h2 := natDegree_mul_le (p := q) (q := (expTaylor m).map (algebraMap ℝ ℂ))
      have h3 : ((expTaylor m).map (algebraMap ℝ ℂ)).natDegree ≤ m :=
        natDegree_map_le.trans (RationalScheme.natDegree_expTaylor_le m)
      omega) hq
  refine norm_pow_apply_sub_semigroup_le hA (Pm := fun k => F ((yosida A k : E →ₗ[ℂ] E).toPMap ⊤))
    (fun k => ?_) (tendsto_aeval_mul_inverse_apply hCk (tendsto_cayley_yosida hA hτ) _ _
      (fun k => (hinv (hCk k)).1) (hinv (norm_cayley_le hA hτ)).1 (fun k => (hinv (hCk k)).2))
    n (by positivity) hu (by positivity [(norm_nonneg _).trans (le_ciSup hb 0)]) fun k => ?_
  · rw [hF]
    exact (norm_aeval_mul_inverse_le_of_dissipative
      (RationalScheme.dissipative_smul (re_inner_yosida_le hA k) hτ.le) hpq hq hr).2
  · rw [hF]
    exact norm_aeval_mul_inverse_pow_sub_exp_le (re_inner_yosida_le hA k) hq hr hm hτ.le n (u 0)

end Complex

end Feec.TimeStepping
