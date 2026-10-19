module

public import Feec.Models.Cube.RegularDecomposition
public import Feec.Models.Cube.PolyFiniteElementConvergence

/-!
# Convergence of the scheme (6.5) on the cube without rate

The scheme (6.5) of [QuennevilleBelair2015], §6.3, on `Q = (0, ½)³` with the elements of
Table 6.1 and the thesis' boundary conditions (`Feec.Models.Cube.WeakSymmetry.cubeWave`)
converges to every classical solution of the multiplier problem (6.2) in the energy class of
`Feec.BGG.ExactWave` whose multiplier is represented on `dV⁰ − S₀Ṽ⁰` by `L²` data: no smoothness,
no boundary flatness and no `L²` bound on the multiplier itself.

**The multiplier.** For a classical solution, (6.2a) fixes the multiplier functional on
`{dτ − S₀ψ}`: `ℓ(dτ − S₀ψ) = ⟪σ', τ⟫ − ⟪u, dψ⟫`. The regular decomposition
(`Feec.BGG.Stability.exists_decomp`, from `CurlPotential` and the Poincaré inequalities) bounds
such a functional in the graph norm of `H̊(curl)` (`Feec.BGG.abs_le_of_rep`); it is in general not
`L²`-bounded (`ℓ(S₀ψ) = ⟪u, dψ⟫` with `u` only in the domain of `div div`). The Riesz
representation in the graph space and the density of `D(d¹*)` approximate it by `L²` functionals
up to `δ ‖d μ‖` (`exists_inner_approx`), and the consistency constant `K₀` of the Strang bound
tends to `0` uniformly on compact families of data (`Feec.BGG.abs_K0_le_of_approx`,
`eventually_cubeFEM_K0`).

**The other constants.** `K₁ → 0` by density of `D(d¹*)` and the regular potentials of
`cubeFEMReg` (`eventually_cubeFEM_K1`), and the smoothed projections converge strongly, hence
uniformly on compact trajectories (`PolySmoothingEstimatesMin.tendsto_norm_sub_proj`,
`eventually_cubeClose`). With the end-to-end theorem
`Feec.BGG.ExactWave.exists_discreteSolution_rate` this gives `cubeWave_converges`.

## Main results

* `Feec.BGG.Stability.exists_decomp`, `Feec.BGG.abs_le_of_rep`, `Feec.BGG.abs_K0_le_of_approx`.
* `exists_inner_approx`, `exists_adjoint_approx_D1`.
* `Feec.Models.Cube.FEM.PolySmoothingEstimatesMin.tendsto_norm_sub_proj`,
  `PolySmoothingEstimatesMin.eventually_norm_sub_proj_le`.
* `cubeFEM_strangData_le_of_close`, `eventually_cubeFEM_K0`, `eventually_cubeFEM_K1`,
  `eventually_cubeClose`.
* **`cubeWave_converges`**: for every `ε > 0` and all large `N`, the solution of (6.5) from the
  elliptic projection (6.4) of the exact initial state stays within `ε` of the exact solution on
  `[0,T]`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2 ((6.3), (6.4), Prop 6.2), §6.3 ((6.5), Table 6.1), Prop 5.9
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.4 (smoothed projections)
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], Lemma 2.4
  (regular decomposition)
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002] (Strang's lemma)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open MeasureTheory Set Filter Topology

@[expose] public noncomputable section

/-! ### The multiplier functional in the graph norm, abstractly -/

namespace Feec.BGG

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
  {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} {Cp CR CS : ℝ}

/-- The constant of `Stability.exists_decomp`. -/
def decompConst (Cp CR CS : ℝ) : ℝ := Cp * (1 + CS * (Cp + 1) * CR) + CR

theorem decompConst_nonneg (H : Stability D Cp CR CS) : 0 ≤ decompConst Cp CR CS := by
  have := H.Cp_nonneg; have := H.CR_nonneg; have := H.CS_nonneg
  unfold decompConst; positivity

/-- **Regular decomposition with bounds**: every `μ ∈ V¹` is `dτ − S₀ψ` with
`‖τ‖, ‖dψ‖ ≤ C (‖μ‖ + ‖dμ‖)` (`reg` gives `ψ`, `exact1` and `poinc0` give `τ`). See
[Hiptmair2002], Lemma 2.4. -/
theorem Stability.exists_decomp (H : Stability D Cp CR CS) (μ : V1) :
    ∃ τ ψ, D.d0 τ - D.S0 ψ = μ ∧ ‖τ‖ ≤ decompConst Cp CR CS * (‖μ‖ + ‖D.d1 μ‖) ∧
      ‖D.dt0 ψ‖ ≤ decompConst Cp CR CS * (‖μ‖ + ‖D.d1 μ‖) := by
  have hp := H.Cp_nonneg; have hr := H.CR_nonneg; have hs := H.CS_nonneg
  obtain ⟨φ, hφ1, hφ2⟩ := H.reg μ
  have hker : D.d1 (μ - D.S0 φ) = 0 := by rw [map_sub, hφ1, sub_self]
  obtain ⟨ρ, hρ⟩ := H.exact1 _ hker
  have hdn := norm_nonneg (D.dt0 φ)
  have hmn := norm_nonneg μ
  have hd1n := norm_nonneg (D.d1 μ)
  have hS : ‖D.S0 φ‖ ≤ CS * ((Cp + 1) * ‖D.dt0 φ‖) := by
    have h1 := H.boundS0 φ
    have h2 := pow_le_pow_left₀ (norm_nonneg φ) (H.poinct0 φ) 2
    unfold graphSq at h1
    have h4 : ‖φ‖ ^ 2 + ‖D.dt0 φ‖ ^ 2 ≤ ((Cp + 1) * ‖D.dt0 φ‖) ^ 2 := by
      nlinarith [mul_nonneg hp (sq_nonneg ‖D.dt0 φ‖)]
    have h5 := mul_le_mul_of_nonneg_left h4 (sq_nonneg CS)
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    nlinarith [sq_nonneg ‖D.d1 (D.S0 φ)‖]
  have hS' : ‖D.S0 φ‖ ≤ CS * (Cp + 1) * CR * ‖D.d1 μ‖ := by
    refine hS.trans ?_
    have := mul_le_mul_of_nonneg_left hφ2 (by positivity : 0 ≤ CS * (Cp + 1))
    linarith
  refine ⟨ρ, -φ, by rw [hρ, map_neg, sub_neg_eq_add, sub_add_cancel], ?_, ?_⟩
  · have h1 : ‖ρ‖ ≤ Cp * (‖μ‖ + ‖D.S0 φ‖) := by
      refine (H.poinc0 ρ).trans (mul_le_mul_of_nonneg_left ?_ hp)
      rw [hρ]; exact norm_sub_le _ _
    have h2 : Cp * (‖μ‖ + ‖D.S0 φ‖) ≤ Cp * (1 + CS * (Cp + 1) * CR) * (‖μ‖ + ‖D.d1 μ‖) := by
      have : ‖μ‖ + ‖D.S0 φ‖ ≤ (1 + CS * (Cp + 1) * CR) * (‖μ‖ + ‖D.d1 μ‖) := by
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hs (by linarith : (0 : ℝ) ≤ Cp + 1)) hr) hmn]
      calc Cp * (‖μ‖ + ‖D.S0 φ‖) ≤ Cp * ((1 + CS * (Cp + 1) * CR) * (‖μ‖ + ‖D.d1 μ‖)) :=
            mul_le_mul_of_nonneg_left this hp
        _ = _ := by ring
    have h3 : Cp * (1 + CS * (Cp + 1) * CR) * (‖μ‖ + ‖D.d1 μ‖) ≤
        decompConst Cp CR CS * (‖μ‖ + ‖D.d1 μ‖) := by
      unfold decompConst
      nlinarith [mul_nonneg hr (add_nonneg hmn hd1n)]
    linarith
  · rw [map_neg, norm_neg]
    unfold decompConst
    have : CR * ‖D.d1 μ‖ ≤ CR * (‖μ‖ + ‖D.d1 μ‖) := mul_le_mul_of_nonneg_left (by linarith) hr
    nlinarith [mul_nonneg (mul_nonneg hp (by positivity : (0 : ℝ) ≤ 1 + CS * (Cp + 1) * CR))
      (add_nonneg hmn hd1n)]

/-- **A functional represented on `dV⁰ − S₀Ṽ⁰` is bounded in the graph norm**: if
`ℓ(dτ − S₀ψ) = α τ − β (dψ)` with `|α τ| ≤ A ‖τ‖`, `|β v| ≤ B ‖v‖`, then
`|ℓ μ| ≤ (A + B) C (‖μ‖ + ‖dμ‖)` (`Stability.exists_decomp`). -/
theorem abs_le_of_rep (H : Stability D Cp CR CS) (ℓ : V1 → ℝ) (α : V0 → ℝ) (β : Vt1 → ℝ)
    (hrep : ∀ τ ψ, ℓ (D.d0 τ - D.S0 ψ) = α τ - β (D.dt0 ψ)) {A B : ℝ} (hA0 : 0 ≤ A)
    (hB0 : 0 ≤ B) (hA : ∀ τ, |α τ| ≤ A * ‖τ‖) (hB : ∀ v, |β v| ≤ B * ‖v‖) (μ : V1) :
    |ℓ μ| ≤ (A + B) * decompConst Cp CR CS * (‖μ‖ + ‖D.d1 μ‖) := by
  obtain ⟨τ, ψ, rfl, hτ, hψ⟩ := H.exists_decomp μ
  rw [hrep]
  have h1 := (hA τ).trans (mul_le_mul_of_nonneg_left hτ hA0)
  have h2 := (hB (D.dt0 ψ)).trans (mul_le_mul_of_nonneg_left hψ hB0)
  calc |α τ - β (D.dt0 ψ)| ≤ |α τ| + |β (D.dt0 ψ)| := abs_sub _ _
    _ ≤ _ := by nlinarith

/-- **`K₀` for a functional close to an `L²`-bounded one in the graph-dual norm**: if
`|ℓ μ − g μ| ≤ δ (‖μ‖ + ‖dμ‖)` and `|g μ| ≤ Λ ‖μ‖`, then, with the consistency of `S₀,ₕ`
(Prop 5.9(1), `happ0`) and the uniform bound of `Π²`,
`|ℓ((S₀ − S₀,ₕ)ψ)| ≤ (δ (C_app h + (1 + C_P) C_S) + Λ C_app h) ‖ψ‖_V` on `Ṽₕ⁰`. -/
theorem abs_K0_le_of_approx (H : Stability D Cp CR CS) {Q : Discrete D} {CP : ℝ}
    (B : Q.Bounded CP) {Capp h : ℝ} (hh : 0 ≤ h) (hCapp : 0 ≤ Capp)
    (happ0 : ∀ ψ ∈ Q.Vt0h, ‖D.S0 ψ - Q.S0h ψ‖ ^ 2 ≤ (Capp * h) ^ 2 * graphSq D.dt0 ψ)
    (ℓ g : V1 → ℝ) {δ Λ : ℝ} (hδ : 0 ≤ δ) (hΛ : 0 ≤ Λ)
    (happ : ∀ μ, |ℓ μ - g μ| ≤ δ * (‖μ‖ + ‖D.d1 μ‖)) (hg : ∀ μ, |g μ| ≤ Λ * ‖μ‖) :
    ∀ ψ ∈ Q.Vt0h, |ℓ ((D.S0 - Q.S0h) ψ)| ≤
      (δ * (Capp * h + (1 + CP) * CS) + Λ * Capp * h) * √(graphSq D.dt0 ψ) := by
  intro ψ hψ
  have hP := B.CP_nonneg
  have hs := H.CS_nonneg
  set G := √(graphSq D.dt0 ψ) with hG
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  have hμ : ‖(D.S0 - Q.S0h) ψ‖ ≤ Capp * h * G := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow, hG, Real.sq_sqrt (graphSq_nonneg _ _)]; exact happ0 ψ hψ
  have hdS : ‖D.d1 (D.S0 ψ)‖ ≤ CS * G := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow, hG, Real.sq_sqrt (graphSq_nonneg _ _)]
    have := H.boundS0 ψ
    unfold graphSq at this ⊢
    nlinarith [sq_nonneg ‖D.S0 ψ‖]
  have hd : ‖D.d1 ((D.S0 - Q.S0h) ψ)‖ ≤ (1 + CP) * CS * G := by
    rw [LinearMap.sub_apply, map_sub, Discrete.S0h_apply, Q.comm1]
    calc ‖D.d1 (D.S0 ψ) - Q.P2 (D.d1 (D.S0 ψ))‖
        ≤ ‖D.d1 (D.S0 ψ)‖ + ‖Q.P2 (D.d1 (D.S0 ψ))‖ := norm_sub_le _ _
      _ ≤ ‖D.d1 (D.S0 ψ)‖ + CP * ‖D.d1 (D.S0 ψ)‖ := add_le_add le_rfl (B.P2 _)
      _ = (1 + CP) * ‖D.d1 (D.S0 ψ)‖ := by ring
      _ ≤ (1 + CP) * (CS * G) := mul_le_mul_of_nonneg_left hdS (by linarith)
      _ = _ := by ring
  have h1 := happ ((D.S0 - Q.S0h) ψ)
  have h2 := (hg ((D.S0 - Q.S0h) ψ)).trans (mul_le_mul_of_nonneg_left hμ hΛ)
  have h3 : δ * (‖(D.S0 - Q.S0h) ψ‖ + ‖D.d1 ((D.S0 - Q.S0h) ψ)‖) ≤
      δ * (Capp * h * G + (1 + CP) * CS * G) :=
    mul_le_mul_of_nonneg_left (add_le_add hμ hd) hδ
  calc |ℓ ((D.S0 - Q.S0h) ψ)| ≤ |ℓ ((D.S0 - Q.S0h) ψ) - g ((D.S0 - Q.S0h) ψ)| +
        |g ((D.S0 - Q.S0h) ψ)| := by
        have := abs_add_le (ℓ ((D.S0 - Q.S0h) ψ) - g ((D.S0 - Q.S0h) ψ)) (g ((D.S0 - Q.S0h) ψ))
        rwa [sub_add_cancel] at this
    _ ≤ δ * (Capp * h * G + (1 + CP) * CS * G) + Λ * (Capp * h * G) := by linarith
    _ = _ := by ring

end Feec.BGG

/-! ### Strong convergence of the smoothed projections with vanishing boundary DOFs -/

namespace Feec.Models.Cube.FEM.PolySmoothingEstimatesMin

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex

variable {S : PolySeq} {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hE : PolySmoothingEstimatesMin 3 S p C)
include hE

/-- **The smoothed projections converge strongly**: `‖x − π̊_N x‖ → 0` for every `x ∈ L²Λᵏ(Q)`
(`‖x − π̊_N x‖ ≤ (1 + 2C) dist(x, V̊ₕᵏ)` and the spaces `V̊ₕᵏ` are dense). -/
theorem tendsto_norm_sub_proj (k : ℤ) (x : L2F ℝ (cubeDomain 3) (formIdx 3 k)) :
    Tendsto (fun N => ‖x - (hE.proj N).π k x‖) atTop (𝓝 0) := by
  have hC := hE.two_mul_nonneg
  have hlim := (tendsto_infDist_polyMin (n := 3) S k x).const_mul (1 + 2 * C)
  rw [mul_zero] at hlim
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hlim
  exact (hE.proj N).norm_sub_π_le_infDist hC (hE.norm_proj_le N k) x

theorem norm_sub_proj_le_add (N : ℕ) (k : ℤ) (x y : L2F ℝ (cubeDomain 3) (formIdx 3 k)) :
    ‖x - (hE.proj N).π k x‖ ≤ ‖y - (hE.proj N).π k y‖ + (1 + 2 * C) * dist x y := by
  have e : x - (hE.proj N).π k x =
      (y - (hE.proj N).π k y) + ((x - y) - (hE.proj N).π k (x - y)) := by
    rw [map_sub]; abel
  rw [e, dist_eq_norm]
  refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
  refine (norm_sub_le _ _).trans ?_
  have := hE.norm_proj_le N k (x - y)
  linarith

omit hE in
/-- **Uniform convergence on compact sets** of a family of functions, Lipschitz with a common
constant and tending to `0` pointwise. -/
theorem eventually_forall_le_of_isCompact' {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK : IsCompact K) {F : ℕ → E → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hlip : ∀ N x y, F N x ≤ F N y + B * dist x y)
    (hF : ∀ x, Tendsto (fun N => F N x) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ x ∈ K, F N x ≤ ε := by
  have hδ : 0 < ε / (2 * (B + 1)) := by positivity
  obtain ⟨t, htK, htf, hcov⟩ := finite_cover_balls_of_compact hK hδ
  have hev : ∀ᶠ N in atTop, ∀ y ∈ t, F N y < ε / 2 :=
    (Filter.eventually_all_finite htf).2 fun y _ =>
      (hF y).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hev] with N hN x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcov hx)
  have h1 := hlip N x y
  have h2 := hN y hy
  have h3 : B * dist x y ≤ B * (ε / (2 * (B + 1))) :=
    mul_le_mul_of_nonneg_left (Metric.mem_ball.1 hxy).le hB
  have h4 : B * (ε / (2 * (B + 1))) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- **Uniform convergence of the projections along a continuous trajectory** on `[0,T]`. -/
theorem eventually_norm_sub_proj_le (k : ℤ) {T : ℝ}
    {g : ℝ → L2F ℝ (cubeDomain 3) (formIdx 3 k)} (hg : ContinuousOn g (Icc 0 T)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T, ‖g t - (hE.proj N).π k (g t)‖ ≤ ε := by
  have hK := isCompact_Icc.image_of_continuousOn hg
  have h := eventually_forall_le_of_isCompact' hK
    (F := fun N x => ‖x - (hE.proj N).π k x‖)
    (by linarith [hE.two_mul_nonneg] : 0 ≤ 1 + 2 * C)
    (fun N x y => hE.norm_sub_proj_le_add N k x y) (fun x => hE.tendsto_norm_sub_proj k x) hε
  filter_upwards [h] with N hN t ht
  exact hN _ (mem_image_of_mem g ht)

end Feec.Models.Cube.FEM.PolySmoothingEstimatesMin

namespace Feec.Models.Cube.WeakSymmetry

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM

/-! ### `L²` approximation of graph-bounded functionals on `H̊Λ¹(Q)` -/

theorem dense_D1_domain : Dense (D1.domain : Set W1) := by
  have h := (complexMin 3).dense 1 2
  rwa [complexMin_d12] at h

theorem dense_D1_adjoint_domain : Dense ((D1†).domain : Set W2) :=
  LinearPMap.dense_adjoint_domain D1 dense_D1_domain D1_isClosed

/-- **Graph-bounded functionals on `H̊Λ¹(Q)` are `L²` functionals up to `δ ‖dμ‖`**: if
`|f μ| ≤ Λ (‖μ‖ + ‖dμ‖)`, then for every `δ > 0` there is `λ ∈ L²Λ¹(Q)` with
`|f μ − ⟪λ, μ⟫| ≤ δ ‖dμ‖` (Riesz in the graph space `f μ = ⟪a, μ⟫ + ⟪b, dμ⟫`, and `b` is
approximated by `b' ∈ D(d¹*)`: `⟪b', dμ⟫ = ⟪d¹*b', μ⟫`). -/
theorem exists_inner_approx (f : U1 → ℝ) (hf : IsLinearMap ℝ f) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hfb : ∀ μ, |f μ| ≤ Λ * (‖μ‖ + ‖segD1 μ‖)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ lam : W1, ∀ μ : U1, |f μ - ⟪lam, (μ : W1)⟫| ≤ δ * ‖segD1 μ‖ := by
  have : CompleteSpace V1 := D1_isClosed.completeSpace_graphSpace
  let fl : U1 →ₗ[ℝ] ℝ := hf.mk' f
  have hfl : ∀ μ, fl μ = f μ := fun _ => rfl
  let F0 : V1 →ₗ[ℝ] ℝ := fl ∘ₗ graphDom1ₗ
  have hF0 : ∀ v : V1, ‖F0 v‖ ≤ (Λ * √2) * ‖v‖ := by
    intro v
    have e1 : ((graphDom1ₗ v : U1) : W1) = D1.graphFst v := rfl
    have e2 : segD1 (graphDom1ₗ v) = D1.graphSnd v := apply_graphDom D1 v
    have h := hfb (graphDom1ₗ v)
    have hn : ‖(graphDom1ₗ v : U1)‖ = ‖D1.graphFst v‖ := by rw [← e1]; rfl
    rw [hn, e2] at h
    have hsq : ‖D1.graphFst v‖ + ‖D1.graphSnd v‖ ≤ √2 * ‖v‖ := by
      have hv := norm_sq_graphSpace D1 v
      refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hv]
      nlinarith [sq_nonneg (‖D1.graphFst v‖ - ‖D1.graphSnd v‖)]
    rw [Real.norm_eq_abs]
    calc |F0 v| = |f (graphDom1ₗ v)| := rfl
      _ ≤ Λ * (‖D1.graphFst v‖ + ‖D1.graphSnd v‖) := h
      _ ≤ Λ * (√2 * ‖v‖) := mul_le_mul_of_nonneg_left hsq hΛ
      _ = _ := by ring
  let F : V1 →L[ℝ] ℝ := LinearMap.mkContinuous F0 (Λ * √2) hF0
  set r : V1 := (InnerProductSpace.toDual ℝ V1).symm F with hr
  have hrep : ∀ μ : U1, f μ = ⟪D1.graphFst r, (μ : W1)⟫ + ⟪D1.graphSnd r, D1 μ⟫ := by
    intro μ
    have h1 : F (D1.toGraphSpace μ) = f μ := by
      change fl (graphDom1ₗ (D1.toGraphSpace μ)) = f μ
      rw [hfl]; rfl
    have h2 : F (D1.toGraphSpace μ) = ⟪r, D1.toGraphSpace μ⟫ := by
      rw [hr, InnerProductSpace.toDual_symm_apply]
    rw [← h1, h2, inner_graphSpace, LinearPMap.graphFst_toGraphSpace,
      LinearPMap.graphSnd_toGraphSpace]
  obtain ⟨z, hz, hzd⟩ := dense_D1_adjoint_domain.exists_dist_lt (D1.graphSnd r) hδ
  refine ⟨D1.graphFst r + D1† ⟨z, hz⟩, fun μ => ?_⟩
  have hadj : ⟪D1† ⟨z, hz⟩, (μ : W1)⟫ = ⟪z, D1 μ⟫ :=
    LinearPMap.adjoint_isFormalAdjoint dense_D1_domain ⟨z, hz⟩ μ
  have e : f μ - ⟪D1.graphFst r + D1† ⟨z, hz⟩, (μ : W1)⟫ = ⟪D1.graphSnd r - z, D1 μ⟫ := by
    rw [hrep, inner_add_left, hadj, inner_sub_left]; ring
  rw [e]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [← dist_eq_norm]
  exact mul_le_mul_of_nonneg_right hzd.le (norm_nonneg _)

/-- **Dense multipliers in degree `2`**: on a compact set of `L²Λ²(Q)`, every point is `δ`-close
to a point of `D(d¹*)` (here `|⟪z, d w⟫| ≤ c ‖w‖` on `H̊Λ¹(Q)`), with a common bound `c`. -/
theorem exists_adjoint_approx_D1 {K : Set W2} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ y ∈ K, ∃ z : W2, ‖y - z‖ < δ ∧ ‖z‖ ≤ c ∧
      ∀ w : U1, |⟪z, segD1 w⟫| ≤ c * ‖w‖ := by
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact hK (half_pos hδ)
  have hz : ∀ y : W2, ∃ z ∈ (D1†).domain, dist y z < δ / 2 := fun y =>
    dense_D1_adjoint_domain.exists_dist_lt y (half_pos hδ)
  choose Z hZ hZd using hz
  let c : ℝ := ∑ y ∈ htf.toFinset, (‖Z y‖ + ‖D1† ⟨Z y, hZ y⟩‖)
  have hc : ∀ y ∈ t, ‖Z y‖ + ‖D1† ⟨Z y, hZ y⟩‖ ≤ c := fun y hy =>
    Finset.single_le_sum (f := fun y => ‖Z y‖ + ‖D1† ⟨Z y, hZ y⟩‖)
      (fun _ _ => by positivity) (htf.mem_toFinset.2 hy)
  refine ⟨c, Finset.sum_nonneg fun _ _ => by positivity, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcov hx)
  have hcy := hc y hy
  refine ⟨Z y, ?_, ?_, fun w => ?_⟩
  · have h1 := dist_triangle x y (Z y)
    have h2 := Metric.mem_ball.1 hxy
    have h3 := hZd y
    rw [← dist_eq_norm]
    linarith
  · have := norm_nonneg (D1† ⟨Z y, hZ y⟩)
    linarith
  · have e : ⟪Z y, segD1 w⟫ = ⟪D1† ⟨Z y, hZ y⟩, (w : W1)⟫ :=
      (LinearPMap.adjoint_isFormalAdjoint dense_D1_domain ⟨Z y, hZ y⟩ w).symm
    rw [e]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := norm_nonneg (D1† ⟨Z y, hZ y⟩)
    have hw : ‖(w : W1)‖ = ‖w‖ := rfl
    rw [hw]
    exact mul_le_mul_of_nonneg_right (by linarith [norm_nonneg (Z y)]) (norm_nonneg _)

/-! ### Multipliers represented by `L²` data -/

/-- **A multiplier functional represented by `L²` data** `(a, b) ∈ L²Λ⁰ × (L²Λ¹)³` on
`dH̊Λ⁰ − S₀H̊Λ⁰(Q)³`: `ℓ(dτ − S₀ψ) = ⟪a, τ⟫ − ⟪b, dψ⟫` (for a classical solution of (6.2):
`a = σ'`, `b = u`). -/
def IsMultRep (ℓ : U1 →ₗ[ℝ] ℝ) (a : W0) (b : Wv W1) : Prop :=
  ∀ τ ψ, ℓ (bggSegment.d0 τ - bggSegment.S0 ψ) = ⟪a, (τ : W0)⟫ - ⟪b, incl1 (bggSegment.dt0 ψ)⟫

/-- The graph-norm constant of represented multipliers. -/
abbrev multConst : ℝ := Feec.BGG.decompConst (2 * Real.pi)⁻¹ curlPotentialConst (Real.sqrt 2)

theorem multConst_nonneg : 0 ≤ multConst :=
  Feec.BGG.decompConst_nonneg bggStability_curlPotentialConst

theorem IsMultRep.sub {ℓ ℓ' : U1 →ₗ[ℝ] ℝ} {a a' : W0} {b b' : Wv W1} (h : IsMultRep ℓ a b)
    (h' : IsMultRep ℓ' a' b') : IsMultRep (ℓ - ℓ') (a - a') (b - b') := fun τ ψ => by
  rw [LinearMap.sub_apply, h, h', inner_sub_left, inner_sub_left]; ring

/-- **A represented multiplier is bounded in the graph norm of `H̊(curl)`**:
`|ℓ μ| ≤ (‖a‖ + ‖b‖) C (‖μ‖ + ‖dμ‖)` (`Feec.BGG.abs_le_of_rep` with `curlPotential`). -/
theorem IsMultRep.abs_le {ℓ : U1 →ₗ[ℝ] ℝ} {a : W0} {b : Wv W1} (h : IsMultRep ℓ a b) (μ : U1) :
    |ℓ μ| ≤ (‖a‖ + ‖b‖) * multConst * (‖μ‖ + ‖segD1 μ‖) :=
  Feec.BGG.abs_le_of_rep bggStability_curlPotentialConst ℓ (fun τ => ⟪a, (τ : W0)⟫)
    (fun v => ⟪b, incl1 v⟫) h (norm_nonneg a) (norm_nonneg b)
    (fun τ => abs_real_inner_le_norm a _) (fun v => by
      have := abs_real_inner_le_norm b (incl1 v); rwa [norm_incl1] at this) μ

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

set_option maxHeartbeats 1000000 in
/-- **`K₀ → 0` uniformly on a continuous family of represented multipliers** (no `L²` bound on the
multipliers): cover the compact set of data by finitely many `δ`-balls, approximate the multiplier
of each centre by an `L²` functional (`exists_inner_approx`) and apply
`Feec.BGG.abs_K0_le_of_approx`. -/
theorem eventually_cubeFEM_K0 {T : ℝ} {ℓ : ℝ → U1 →ₗ[ℝ] ℝ} {a : ℝ → W0} {b : ℝ → Wv W1}
    (ha : ContinuousOn a (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T))
    (hrep : ∀ t ∈ Icc 0 T, IsMultRep (ℓ t) (a t) (b t)) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T, ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
      |ℓ t ((bggSegment.S0 - (cubeFEM hT hB N).S0h) ψ)| ≤
        θ * √(Feec.BGG.graphSq bggSegment.dt0 ψ) := by
  obtain ⟨C0, hC00, hhapp⟩ := cubeFEM_happ0 hT hB
  have hC := hT.two_mul_nonneg
  have hK0 := multConst_nonneg
  set A : ℝ := (1 + 2 * C) * Real.sqrt 2 with hA
  have hA0 : 0 ≤ A := by positivity
  set δ : ℝ := θ / (4 * (2 * multConst + 1) * (C0 + A + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hδθ : (2 * multConst * δ + δ) * (C0 + A) ≤ θ / 2 := by
    have e : (2 * multConst * δ + δ) * (C0 + A + 1) = θ / 4 := by
      rw [hδdef]; field_simp
    have : (2 * multConst * δ + δ) * (C0 + A) ≤ (2 * multConst * δ + δ) * (C0 + A + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hK : IsCompact ((fun t => (a t, b t)) '' Icc 0 T) :=
    isCompact_Icc.image_of_continuousOn (ha.prodMk hb)
  obtain ⟨cs, hcsK, hcsf, hcov⟩ := finite_cover_balls_of_compact hK hδ
  have hchoice : ∀ c ∈ cs, ∃ s, s ∈ Icc 0 T ∧ (a s, b s) = c ∧
      ∃ lam : W1, ∀ μ : U1, |ℓ s μ - ⟪lam, (μ : W1)⟫| ≤ δ * ‖segD1 μ‖ := by
    intro c hc
    obtain ⟨s, hs, hsc⟩ := hcsK hc
    obtain ⟨lam, hlam⟩ := exists_inner_approx (ℓ s) (ℓ s).isLinear
      (by positivity : 0 ≤ (‖a s‖ + ‖b s‖) * multConst) (hrep s hs).abs_le hδ
    exact ⟨s, hs, hsc, lam, hlam⟩
  choose! S hS hSc LAM hLAM using hchoice
  set Λ : ℝ := ∑ c ∈ hcsf.toFinset, ‖LAM c‖ with hΛdef
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hΛc : ∀ c ∈ cs, ‖LAM c‖ ≤ Λ := fun c hc =>
    Finset.single_le_sum (f := fun c => ‖LAM c‖) (fun _ _ => norm_nonneg _)
      (hcsf.mem_toFinset.2 hc)
  have hlim : Tendsto (fun N => Λ * C0 * meshSize N) atTop (𝓝 0) := by
    simpa using tendsto_meshSize.const_mul (Λ * C0)
  filter_upwards [hlim.eventually (Iic_mem_nhds (half_pos hθ)),
    tendsto_meshSize.eventually (Iic_mem_nhds one_pos)] with N hN1 hN2 t ht ψ hψ
  have hN1' : Λ * C0 * meshSize N ≤ θ / 2 := hN1
  have hN2' : meshSize N ≤ 1 := hN2
  have hh := (meshSize_pos N).le
  obtain ⟨c, hc, hct⟩ := mem_iUnion₂.1 (hcov (mem_image_of_mem _ ht))
  have hdist := Metric.mem_ball.1 hct
  rw [← hSc c hc, Prod.dist_eq, max_lt_iff] at hdist
  obtain ⟨hda, hdb⟩ := hdist
  rw [dist_eq_norm] at hda hdb
  have happ : ∀ μ : U1, |ℓ t μ - ⟪LAM c, (μ : W1)⟫| ≤
      (2 * multConst * δ + δ) * (‖μ‖ + ‖segD1 μ‖) := by
    intro μ
    have h1 := ((hrep t ht).sub (hrep (S c) (hS c hc))).abs_le μ
    rw [LinearMap.sub_apply] at h1
    have h2 := hLAM c hc μ
    have h3 : (‖a t - a (S c)‖ + ‖b t - b (S c)‖) * multConst * (‖μ‖ + ‖segD1 μ‖) ≤
        (2 * δ) * multConst * (‖μ‖ + ‖segD1 μ‖) := by
      have := add_le_add hda.le hdb.le
      have hm : 0 ≤ ‖μ‖ + ‖segD1 μ‖ := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hK0) hm
    have h4 : δ * ‖segD1 μ‖ ≤ δ * (‖μ‖ + ‖segD1 μ‖) :=
      mul_le_mul_of_nonneg_left (by linarith [norm_nonneg μ]) hδ.le
    calc |ℓ t μ - ⟪LAM c, (μ : W1)⟫| ≤ |ℓ t μ - ℓ (S c) μ| + |ℓ (S c) μ - ⟪LAM c, (μ : W1)⟫| := by
          have := abs_add_le (ℓ t μ - ℓ (S c) μ) (ℓ (S c) μ - ⟪LAM c, (μ : W1)⟫)
          rwa [sub_add_sub_cancel] at this
      _ ≤ (2 * δ) * multConst * (‖μ‖ + ‖segD1 μ‖) + δ * (‖μ‖ + ‖segD1 μ‖) := by linarith
      _ = _ := by ring
  have hg : ∀ μ : U1, |⟪LAM c, (μ : W1)⟫| ≤ Λ * ‖μ‖ := fun μ =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hΛc c hc) (norm_nonneg _))
  have hkey := Feec.BGG.abs_K0_le_of_approx bggStability_curlPotentialConst
    (cubeFEM_bounded hT hB N) hh hC00 (hhapp N) (ℓ t) (fun μ => ⟪LAM c, (μ : W1)⟫)
    (by positivity) hΛ0 happ hg ψ hψ
  refine hkey.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  have h5 : (2 * multConst * δ + δ) * (C0 * meshSize N + (1 + 2 * C) * Real.sqrt 2) ≤
      (2 * multConst * δ + δ) * (C0 + A) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : C0 * meshSize N ≤ C0 := by nlinarith
    linarith
  linarith

/-! ### `K₁ → 0` -/

set_option maxHeartbeats 1000000 in
/-- `K₁` of the Strang bound for a multiplier `z ∈ D(d¹*)`: `|⟪z, (S₁ − S₁,ₕ)v⟫| ≤ K h_N c ‖v‖`
when `‖z‖ ≤ c` and `|⟪z, dw⟫| ≤ c ‖w‖` (regular potentials `cubeFEMReg`). -/
theorem exists_cubeFEM_K1 : ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (z : W2) (c : ℝ), 0 ≤ c → ‖z‖ ≤ c →
    (∀ w : U1, |⟪z, segD1 w⟫| ≤ c * ‖w‖) → ∀ v ∈ (cubeFEM hT hB N).Vt1h,
      |⟪z, (bggSegment.S1 - (cubeFEM hT hB N).S1h) v⟫| ≤
        K * meshSize N * c * √((cubeFEM hT hB N).gnSq v) := by
  obtain ⟨C0, hh1⟩ := cubeFEM_happ0 hT hB
  have hC00 := hh1.1
  have hhapp := hh1.2
  have hC := hT.two_mul_nonneg
  have hreg := regConst_nonneg hT
  have hCR0 := curlPotentialConst_nonneg
  have ex1 : ∃ x : ℝ, x = C0 + regConst C := ⟨_, rfl⟩
  obtain ⟨Capp, hCapp_def⟩ := ex1
  have hCapp0 : 0 ≤ Capp := by rw [hCapp_def]; linarith
  have ex2 : ∃ x : ℝ, x = (2 * Real.pi)⁻¹ := ⟨_, rfl⟩
  obtain ⟨Cp, hCp⟩ := ex2
  have hCp0 : 0 ≤ Cp := by rw [hCp]; positivity
  have ex4 : ∃ x : ℝ, x = √(1 + Cp ^ 2) * (1 + 2 * C * (1 + 1 * curlPotentialConst)) :=
    ⟨_, rfl⟩
  obtain ⟨wa, hwa⟩ := ex4
  have ex5 : ∃ x : ℝ, x = (1 + (1 + 2 * C) * Real.sqrt 2) * curlPotentialConst := ⟨_, rfl⟩
  obtain ⟨wb, hwb⟩ := ex5
  have hwa0 : 0 ≤ wa := by rw [hwa]; positivity
  have hwb0 : 0 ≤ wb := by rw [hwb]; positivity
  refine ⟨Capp * (wa + wb), mul_nonneg hCapp0 (add_nonneg hwa0 hwb0),
    fun N z c hc0 hzn hzd v hv => ?_⟩
  have hh : 0 ≤ meshSize N := (meshSize_pos N).le
  have H := bggStability_curlPotentialConst
  rw [← hCp] at H
  have Bd := cubeFEM_bounded hT hB N
  have happ : ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
      ‖bggSegment.S0 ψ - (cubeFEM hT hB N).S0h ψ‖ ^ 2 ≤
        (Capp * meshSize N) ^ 2 * Feec.BGG.graphSq bggSegment.dt0 ψ := fun ψ hψ => by
    refine (hhapp N ψ hψ).trans (mul_le_mul_of_nonneg_right ?_ (Feec.BGG.graphSq_nonneg _ _))
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right
      (by rw [hCapp_def]; linarith) hh) 2
  have Rg := cubeFEMReg hT hB N hCR0 exists_curlPotential_le
    (by rw [hCapp_def]; linarith : regConst C ≤ Capp)
  have hw := Feec.BGG.Discrete.weakConsistency_of_regularPotential_of_bound H Bd hh hCapp0 Rg
    happ hc0 hzd v hv
  have hwc : Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1
      curlPotentialConst (‖z‖) c ≤ (wa + wb) * c := by
    have e : Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1
        curlPotentialConst (‖z‖) c = c * wa + ‖z‖ * wb := by
      rw [hwa, hwb]; unfold Feec.BGG.Discrete.weakConsistencyConst; ring
    rw [e]; nlinarith
  refine hw.trans ?_
  have hg := Feec.BGG.Discrete.sqrt_graphSq_le_sqrt_gnSq (Q := cubeFEM hT hB N) v
  have hm : 0 ≤ Capp * meshSize N := by positivity
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwc hm)
    (Real.sqrt_nonneg (Feec.BGG.graphSq bggSegment.dt1 v))
  have h2 := mul_le_mul_of_nonneg_left hg
    (by positivity : 0 ≤ Capp * meshSize N * ((wa + wb) * c))
  refine (h1.trans h2).trans (le_of_eq ?_)
  ring

/-- The `L²` part of `K₁`: `|⟪z, (S₁ − S₁,ₕ)v⟫| ≤ ‖z‖ (1 + 2C) √2 ‖v‖_{Γₕ}` for every `z`. -/
theorem cubeFEM_K1_rest (N : ℕ) (z : W2) (v : Wv U1) :
    |⟪z, (bggSegment.S1 - (cubeFEM hT hB N).S1h) v⟫| ≤
      ‖z‖ * ((1 + 2 * C) * √2) * √((cubeFEM hT hB N).gnSq v) := by
  have hC := hT.two_mul_nonneg
  have e : (bggSegment.S1 - (cubeFEM hT hB N).S1h) v =
      segS1 v - (hT.proj N).π 2 (segS1 v) := rfl
  have h1 : ‖segS1 v - (hT.proj N).π 2 (segS1 v)‖ ≤ (1 + 2 * C) * ‖segS1 v‖ := by
    have := hT.norm_proj_le N 2 (segS1 v)
    have := norm_sub_le (segS1 v) ((hT.proj N).π 2 (segS1 v))
    linarith
  have h2 : ‖segS1 v‖ ≤ √2 * ‖v‖ := by
    have h := norm_wsL2_one_incl1_sq_le v
    have h' : ‖segS1 v‖ ^ 2 ≤ (√2 * ‖v‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; exact h
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h'
  have h3 : ‖v‖ ≤ √((cubeFEM hT hB N).gnSq v) := by
    have h := Real.abs_le_sqrt (x := ‖v‖) (y := (cubeFEM hT hB N).gnSq v) (by
      unfold Feec.BGG.Discrete.gnSq
      exact le_add_of_le_of_nonneg (le_add_of_nonneg_right (by positivity)) (by positivity))
    rwa [abs_norm] at h
  rw [e]
  refine (abs_real_inner_le_norm _ _).trans ?_
  have h4 : ‖segS1 v - (hT.proj N).π 2 (segS1 v)‖ ≤
      (1 + 2 * C) * √2 * √((cubeFEM hT hB N).gnSq v) := by
    refine h1.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
      (by linarith)
  calc ‖z‖ * ‖segS1 v - (hT.proj N).π 2 (segS1 v)‖ ≤
      ‖z‖ * ((1 + 2 * C) * √2 * √((cubeFEM hT hB N).gnSq v)) :=
        mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    _ = _ := by ring

/-- **`K₁ → 0` uniformly on a compact set of multipliers** (no regularity): split
`z = z' + (z − z')` with `z' ∈ D(d¹*)` close to `z` (`exists_adjoint_approx_D1`). -/
theorem eventually_cubeFEM_K1 {K : Set W2} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ z ∈ K, ∀ v ∈ (cubeFEM hT hB N).Vt1h,
      |⟪z, (bggSegment.S1 - (cubeFEM hT hB N).S1h) v⟫| ≤
        ε * √((cubeFEM hT hB N).gnSq v) := by
  have hC := hT.two_mul_nonneg
  have hA : 0 ≤ (1 + 2 * C) * √2 := by positivity
  have ex : ∃ A : ℝ, A = (1 + 2 * C) * √2 := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ := ex
  rw [← hAdef] at hA
  have hδ : 0 < ε / (2 * (A + 1)) := by positivity
  obtain ⟨c, hc0, hc⟩ := exists_adjoint_approx_D1 hK hδ
  obtain ⟨K1, hK10, hK1⟩ := exists_cubeFEM_K1 hT hB
  have hlim : Tendsto (fun N => K1 * meshSize N * c) atTop (𝓝 0) := by
    have := (tendsto_meshSize.const_mul K1).mul_const c
    simpa using this
  have hhalf : ∀ x : ℝ, x < ε / (2 * (A + 1)) → x * A ≤ ε / 2 := fun x hx => by
    have h4 : x * A ≤ ε / (2 * (A + 1)) * A := mul_le_mul_of_nonneg_right hx.le hA
    have h5 : ε / (2 * (A + 1)) * A ≤ ε / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  filter_upwards [hlim.eventually (Iic_mem_nhds (half_pos hε))] with N hN z hz v hv
  obtain ⟨z', hzz', hz'n, hz'd⟩ := hc z hz
  have h1 := hK1 N z' c hc0 hz'n hz'd v hv
  have h2 := cubeFEM_K1_rest hT hB N (z - z') v
  rw [← hAdef] at h2
  have h3 := hhalf _ hzz'
  have hN' : K1 * meshSize N * c ≤ ε / 2 := hN
  have ex1 : ∃ X : W2, X = (bggSegment.S1 - (cubeFEM hT hB N).S1h) v := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ := ex1
  have ex2 : ∃ G : ℝ, G = √((cubeFEM hT hB N).gnSq v) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ := ex2
  rw [← hX, ← hG] at h1 h2 ⊢
  have hg : 0 ≤ G := by rw [hG]; exact Real.sqrt_nonneg _
  clear hX hG hz'd hc hK1 hlim hN
  have e : ⟪z, X⟫ = ⟪z - z', X⟫ + ⟪z', X⟫ := by rw [inner_sub_left]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have h6 : ‖z - z'‖ * A * G ≤ ε / 2 * G := mul_le_mul_of_nonneg_right h3 hg
  have h7 : K1 * meshSize N * c * G ≤ ε / 2 * G := mul_le_mul_of_nonneg_right hN' hg
  linarith

/-! ### Closeness to the projections and the Strang data -/

/-- **Closeness of a state to its projections** at level `δ`: the `L²` projection errors of
`σ`, `dφ`, `u`, `du`, `M`, `ρ` and `S¹u` that make up the Strang data of (6.4). -/
def CubeClose (N : ℕ) (δ : ℝ) (σ : U0) (φ : Wv U0) (u : Wv U1) (M : W2) (ρ : Wv W2) : Prop :=
  ‖(σ : W0) - (hT.proj N).π 0 (σ : W0)‖ ≤ δ ∧
    (∀ a, ‖D0 (φ a) - (hB.proj N).π 1 (D0 (φ a))‖ ≤ δ) ∧
    (∀ a, ‖(u a : W1) - (hB.proj N).π 1 (u a : W1)‖ ≤ δ) ∧
    (∀ a, ‖D1 (u a) - (hB.proj N).π 2 (D1 (u a))‖ ≤ δ) ∧
    ‖M - (hT.proj N).π 2 M‖ ≤ δ ∧
    (∀ a, ‖ρ a - (hB.proj N).π 2 (ρ a)‖ ≤ δ) ∧
    ‖segS1 u - (hT.proj N).π 2 (segS1 u)‖ ≤ δ

/-- The constant of `cubeFEM_strangData_le_of_close`. -/
def cubeCloseConst (C : ℝ) : ℝ := 1 + 3 + (1 + 8 * C ^ 2) * 3 + 3 + 1 + 3 + 1

theorem cubeCloseConst_nonneg (C : ℝ) : 0 ≤ cubeCloseConst C := by
  unfold cubeCloseConst; positivity

theorem sum_sq_le_three' {f : Fin 3 → ℝ} {B : ℝ} (h : ∀ a, f a ^ 2 ≤ B) :
    ∑ a, f a ^ 2 ≤ 3 * B := by
  have := Finset.sum_le_sum (s := Finset.univ) fun a (_ : a ∈ Finset.univ) => h a
  simpa [Finset.sum_const, Finset.card_univ] using this

set_option maxHeartbeats 1000000 in
/-- **The Strang data of (6.4) from the projection errors**: `≤ cubeCloseConst C · δ² + K₀² + K₁²`
for a state `δ`-close to its projections (no regularity). -/
theorem cubeFEM_strangData_le_of_close (N : ℕ) {δ : ℝ} {σ : U0} {φ : Wv U0} {u : Wv U1}
    {M : W2} {ρ : Wv W2} (hc : CubeClose hT hB N δ σ φ u M ρ) (K0 K1 : ℝ) :
    (cubeFEM hT hB N).strangData σ φ u M ρ K0 K1 ≤
      cubeCloseConst C * δ ^ 2 + K0 ^ 2 + K1 ^ 2 := by
  obtain ⟨hσ, hφ, hu, hdu, hM, hρ, hSu⟩ := hc
  have h1 : ‖(cubeFEM hT hB N).P0 σ - σ‖ ≤ δ := by
    change ‖(hT.proj N).π 0 (σ : W0) - (σ : W0)‖ ≤ δ
    rw [norm_sub_rev]; exact hσ
  have h2 : ‖bggSegment.dt0 ((cubeFEM hT hB N).Pt0 φ - φ)‖ ^ 2 ≤ 3 * δ ^ 2 := by
    rw [norm_sq_wv]
    refine sum_sq_le_three' fun a => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    have e : ‖(bggSegment.dt0 ((cubeFEM hT hB N).Pt0 φ - φ)) a‖ =
        ‖(hB.proj N).π 1 (D0 (φ a)) - D0 (φ a)‖ := by
      change ‖D0 (projU0 (hB.proj N) (φ a) - φ a)‖ = _
      rw [LinearPMap.map_sub]
      congr 2
      exact D0_π (hB.proj N) (φ a)
    rw [e, norm_sub_rev]
    exact hφ a
  have h3a : ‖(cubeFEM hT hB N).Pt1 u - u‖ ^ 2 ≤ 3 * δ ^ 2 := by
    rw [norm_sq_wv]
    refine sum_sq_le_three' fun a => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    change ‖(hB.proj N).π 1 (u a : W1) - (u a : W1)‖ ≤ _
    rw [norm_sub_rev]
    exact hu a
  have h3b := norm_cubeFEM_S1h_sq_le hT hB N ((cubeFEM hT hB N).Pt1 u - u)
  have h3c : ‖bggSegment.dt1 ((cubeFEM hT hB N).Pt1 u - u)‖ ^ 2 ≤ 3 * δ ^ 2 := by
    rw [norm_sq_wv]
    refine sum_sq_le_three' fun a => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    have e : ‖(bggSegment.dt1 ((cubeFEM hT hB N).Pt1 u - u)) a‖ =
        ‖(hB.proj N).π 2 (D1 (u a)) - D1 (u a)‖ := by
      change ‖D1 (projU1 (hB.proj N) (u a) - u a)‖ = _
      rw [LinearPMap.map_sub]
      congr 2
      exact D1_π (hB.proj N) (u a)
    rw [e, norm_sub_rev]
    exact hdu a
  have h4 : ‖(cubeFEM hT hB N).P2 M - M‖ ≤ δ := by
    change ‖(hT.proj N).π 2 M - M‖ ≤ δ
    rw [norm_sub_rev]; exact hM
  have h5 : ‖(cubeFEM hT hB N).Pt2 ρ - ρ‖ ^ 2 ≤ 3 * δ ^ 2 := by
    rw [norm_sq_wv]
    refine sum_sq_le_three' fun a => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    change ‖(hB.proj N).π 2 (ρ a) - ρ a‖ ≤ _
    rw [norm_sub_rev]
    exact hρ a
  have h6 : ‖bggSegment.S1 u - (cubeFEM hT hB N).S1h u‖ ≤ δ := hSu
  have q1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have q4 := pow_le_pow_left₀ (norm_nonneg _) h4 2
  have q6 := pow_le_pow_left₀ (norm_nonneg _) h6 2
  have e1 : (cubeFEM hT hB N).strangData σ φ u M ρ K0 K1 =
      ‖(cubeFEM hT hB N).P0 σ - σ‖ ^ 2 +
        ‖bggSegment.dt0 ((cubeFEM hT hB N).Pt0 φ - φ)‖ ^ 2 +
        (‖(cubeFEM hT hB N).Pt1 u - u‖ ^ 2 +
          ‖(cubeFEM hT hB N).S1h ((cubeFEM hT hB N).Pt1 u - u)‖ ^ 2 +
          ‖bggSegment.dt1 ((cubeFEM hT hB N).Pt1 u - u)‖ ^ 2) +
        ‖(cubeFEM hT hB N).P2 M - M‖ ^ 2 + ‖(cubeFEM hT hB N).Pt2 ρ - ρ‖ ^ 2 + K0 ^ 2 +
        K1 ^ 2 + ‖bggSegment.S1 u - (cubeFEM hT hB N).S1h u‖ ^ 2 := rfl
  have hS1h : ‖(cubeFEM hT hB N).S1h ((cubeFEM hT hB N).Pt1 u - u)‖ ^ 2 ≤
      8 * C ^ 2 * (3 * δ ^ 2) :=
    h3b.trans (mul_le_mul_of_nonneg_left h3a (by positivity))
  rw [e1]
  unfold cubeCloseConst
  nlinarith

/-- **A continuous trajectory is uniformly close to its projections** for `N` large. -/
theorem eventually_cubeClose {T : ℝ} {σ : ℝ → U0} {φ : ℝ → Wv U0} {u : ℝ → Wv U1}
    {M : ℝ → W2} {ρ : ℝ → Wv W2} (hσ : ContinuousOn σ (Icc 0 T))
    (hφ : ContinuousOn (fun t => bggSegment.dt0 (φ t)) (Icc 0 T))
    (hu : ContinuousOn u (Icc 0 T))
    (hdu : ContinuousOn (fun t => bggSegment.dt1 (u t)) (Icc 0 T))
    (hM : ContinuousOn M (Icc 0 T)) (hρ : ContinuousOn ρ (Icc 0 T))
    (hSu : ContinuousOn (fun t => bggSegment.S1 (u t)) (Icc 0 T))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T, CubeClose hT hB N δ (σ t) (φ t) (u t) (M t) (ρ t) := by
  have c1 : ContinuousOn (fun t => (σ t : W0)) (Icc 0 T) :=
    continuous_subtype_val.comp_continuousOn hσ
  have c2 : ∀ a : Fin 3, ContinuousOn (fun t => D0 (φ t a)) (Icc 0 T) := fun a =>
    (continuous_subtype_val.comp
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => U1) a)).comp_continuousOn hφ
  have c3 : ∀ a : Fin 3, ContinuousOn (fun t => (u t a : W1)) (Icc 0 T) := fun a =>
    (continuous_subtype_val.comp
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => U1) a)).comp_continuousOn hu
  have c4 : ∀ a : Fin 3, ContinuousOn (fun t => D1 (u t a)) (Icc 0 T) := fun a =>
    (PiLp.continuous_apply 2 _ a).comp_continuousOn hdu
  have c6 : ∀ a : Fin 3, ContinuousOn (fun t => ρ t a) (Icc 0 T) := fun a =>
    (PiLp.continuous_apply 2 _ a).comp_continuousOn hρ
  have e1 := hT.eventually_norm_sub_proj_le 0 c1 hδ
  have e2 := Filter.eventually_all.2 fun a => hB.eventually_norm_sub_proj_le 1 (c2 a) hδ
  have e3 := Filter.eventually_all.2 fun a => hB.eventually_norm_sub_proj_le 1 (c3 a) hδ
  have e4 := Filter.eventually_all.2 fun a => hB.eventually_norm_sub_proj_le 2 (c4 a) hδ
  have e5 := hT.eventually_norm_sub_proj_le 2 hM hδ
  have e6 := Filter.eventually_all.2 fun a => hB.eventually_norm_sub_proj_le 2 (c6 a) hδ
  have e7 := hT.eventually_norm_sub_proj_le 2 hSu hδ
  filter_upwards [e1, e2, e3, e4, e5, e6, e7] with N h1 h2 h3 h4 h5 h6 h7 t ht
  exact ⟨h1 t ht, fun a => h2 a t ht, fun a => h3 a t ht, fun a => h4 a t ht, h5 t ht,
    fun a => h6 a t ht, h7 t ht⟩

/-! ### Convergence of (6.5) -/

set_option maxHeartbeats 4000000 in
/-- **Convergence of the scheme (6.5) on the cube without rate** ([QuennevilleBelair2015], §6.3,
(6.5), Table 6.1, thesis' boundary conditions; new: the thesis states no convergence result for
(6.5)). For every `T > 0`, every `L²` source `f` continuous on `[0,T]`, every classical solution
`s` of (6.2) (`Feec.BGG.ExactWave`, whose regularity is the continuity in `L²` of
`σ, u, M, ρ, dφ, du, S¹u` and of their time derivatives) whose multiplier functionals `ℓ`, `ℓ'`
are represented on `dH̊Λ⁰ − S₀H̊Λ⁰(Q)³` by `L²` data continuous on `[0,T]` (`IsMultRep`; no `L²`
bound on the multiplier, no smoothness, no flatness at `∂Q`), and every `ε > 0`: for all `N`
large, the scheme with source `P_{Ṽₕ¹} f` has a solution starting from the dynamic part of the
elliptic projection (6.4) of the exact initial state, with
`(‖σ − σₕ‖² + ‖u − uₕ‖² + ‖M − Mₕ‖² + ‖ρ − ρₕ‖²)^{1/2}(t) ≤ ε` on `[0,T]`.
Proof: the end-to-end theorem `Feec.BGG.ExactWave.exists_discreteSolution_rate` with `h = 1`,
`c = η`: the projection errors tend to `0` uniformly on the compact trajectories
(`eventually_cubeClose`), `K₀ → 0` (`eventually_cubeFEM_K0`) and `K₁ → 0`
(`eventually_cubeFEM_K1`). -/
theorem cubeWave_converges {T : ℝ} (hT0 : 0 < T) {f : ℝ → Wv W1}
    (hf : ContinuousOn f (Icc 0 T)) (s : Feec.BGG.ExactWave bggSegment T (srcFun f))
    {a a' : ℝ → W0} {b b' : ℝ → Wv W1} (ha : ContinuousOn a (Icc 0 T))
    (hb : ContinuousOn b (Icc 0 T)) (ha' : ContinuousOn a' (Icc 0 T))
    (hb' : ContinuousOn b' (Icc 0 T)) (hrep : ∀ t ∈ Icc 0 T, IsMultRep (s.ℓ t) (a t) (b t))
    (hrep' : ∀ t ∈ Icc 0 T, IsMultRep (s.ℓ' t) (a' t) (b' t)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop,
      ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N f),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (cubeWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((cubeFEM hT hB N).ellipticDataH (s.σ 0) (s.φ 0) (s.u 0)
              (s.M 0) (s.ρ 0) (s.ℓ 0)) 0)).1.1 ∧
        ∀ t ∈ Icc 0 T, √(‖s.σ t - sh.σ t‖ ^ 2 + ‖s.u t - sh.u t‖ ^ 2 +
          ‖s.M t - sh.M t‖ ^ 2 + ‖s.ρ t - sh.ρ t‖ ^ 2) ≤ ε := by
  have H := bggStability_curlPotentialConst
  have ex1 : ∃ Ks : ℝ, Ks = √(2 * (Feec.BGG.Discrete.strangConst (2 * Real.pi)⁻¹ + 1)) :=
    ⟨_, rfl⟩
  obtain ⟨Ks, hKs⟩ := ex1
  have hKs0 : 0 ≤ Ks := by rw [hKs]; exact Real.sqrt_nonneg _
  have ex2 : ∃ η : ℝ, η = ε / (Ks * (2 + 2 * T) + 1) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ := ex2
  have hden : 0 < Ks * (2 + 2 * T) + 1 := by nlinarith
  have hη0 : 0 < η := by rw [hη]; exact div_pos hε hden
  have hηε : η * (Ks * (2 + 2 * T) + 1) = ε := by rw [hη]; exact div_mul_cancel₀ _ hden.ne'
  have hmc := cubeCloseConst_nonneg C
  have ex3 : ∃ θ : ℝ, θ = η / (cubeCloseConst C + 2) := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ := ex3
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθη : θ * (cubeCloseConst C + 2) = η := by
    rw [hθ]; exact div_mul_cancel₀ _ (by positivity)
  have hθle : θ ≤ η := by nlinarith
  have hdat : ∀ x : ℝ, x ≤ cubeCloseConst C * θ ^ 2 + θ ^ 2 + θ ^ 2 → x ≤ (η * 1) ^ 2 :=
    fun x hx => by nlinarith
  have hKc : IsCompact ((s.M '' Icc 0 T) ∪ (s.M' '' Icc 0 T)) :=
    (isCompact_Icc.image_of_continuousOn s.cM).union (isCompact_Icc.image_of_continuousOn s.cM')
  have ev0 := eventually_cubeFEM_K0 hT hB ha hb hrep hθ0
  have ev0' := eventually_cubeFEM_K0 hT hB ha' hb' hrep' hθ0
  have ev2 := eventually_cubeFEM_K1 hT hB hKc hθ0
  have ev3 := eventually_cubeClose hT hB (σ := s.σ) (φ := s.φ) (u := s.u) (M := s.M)
    (ρ := s.ρ) s.cσ s.cdφ s.cu s.cdu s.cM s.cρ s.cSu hθ0
  have ev4 := eventually_cubeClose hT hB (σ := s.σ') (φ := s.φ') (u := s.u') (M := s.M')
    (ρ := s.ρ') s.cσ' s.cdφ' s.cu' s.cdu' s.cM' s.cρ' s.cSu' hθ0
  filter_upwards [ev0, ev0', ev2, ev3, ev4] with N h0 h0' h2 h3 h4
  have hrate := s.exists_discreteSolution_rate (cubeFEM hT hB N) H
    (cubeFEM_compatible hT hB N) (K0 := θ) (K1 := θ) (c := η) (h := 1)
    (cubeWave_S0_surjective hT hB N) hT0
    (continuousOn_cubeSource hT hB N hf) (fun t _ v => (inner_cubeSource hT hB N f t v).symm)
    h0 h0'
    (fun t ht v hv => h2 (s.M t) (Or.inl (mem_image_of_mem _ ht)) v hv)
    (fun t ht v hv => h2 (s.M' t) (Or.inr (mem_image_of_mem _ ht)) v hv)
    (fun t ht => hdat _ (cubeFEM_strangData_le_of_close hT hB N (h3 t ht) θ θ))
    (fun t ht => hdat _ (cubeFEM_strangData_le_of_close hT hB N (h4 t ht) θ θ))
  obtain ⟨sh, hinit, hbd⟩ := hrate
  refine ⟨sh, hinit, fun t ht => (hbd t ht).trans ?_⟩
  rw [← hKs, abs_of_pos hη0, abs_one, mul_one]
  have ht2 : 2 + 2 * t ≤ 2 + 2 * T := by linarith [ht.2]
  have h5 : Ks * η * (2 + 2 * t) ≤ Ks * η * (2 + 2 * T) :=
    mul_le_mul_of_nonneg_left ht2 (by positivity)
  nlinarith

end Feec.Models.Cube.WeakSymmetry
