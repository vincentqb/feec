module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Strong convergence of bounded operators

Calculus of strong (pointwise) limits of continuous linear maps `Pᵢ : V →L[𝕜] V` along a filter,
under uniform bounds:

* `ContinuousLinearMap.tendsto_apply_of_tendsto`: if `‖Pᵢ‖ ≤ M`, `Pᵢ → P` strongly and `wᵢ → w`,
  then `Pᵢ wᵢ → P w`;
* `ContinuousLinearMap.tendsto_apply_of_dense`, `ContinuousLinearMap.cauchySeq_apply_of_dense`:
  for contractions, `Tₙ x → x` (resp. `(Tₙ x)ₙ` Cauchy) on a dense set holds everywhere;
* `ContinuousLinearMap.tendsto_pow_apply`, `ContinuousLinearMap.tendsto_aeval_apply`: powers and
  polynomials of uniformly bounded, strongly convergent operators converge strongly;
* `ContinuousLinearMap.tendsto_inverse_apply`: inverses with uniformly bounded inverses converge
  strongly, `Bᵢ⁻¹ y - B⁻¹ y = Bᵢ⁻¹ (B - Bᵢ) B⁻¹ y`;
* `ContinuousLinearMap.tendsto_aeval_mul_inverse_apply`: rational functions `f(Tᵢ) g(Tᵢ)⁻¹`;
* `Commute.ringInverse_right`: `a` commutes with `Ring.inverse b` when it commutes with `b`.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.3 (the strong limits of the Hille–Yosida theorem)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public section

open Filter Topology Polynomial

/-- `a` commutes with `Ring.inverse b` when it commutes with `b`. -/
theorem Commute.ringInverse_right {M : Type*} [MonoidWithZero M] {a b : M} (h : Commute a b) :
    Commute a (Ring.inverse b) := by
  by_cases hb : IsUnit b
  · obtain ⟨u, rfl⟩ := hb
    rw [Ring.inverse_unit]
    exact (Commute.units_inv_right h)
  · rw [Ring.inverse_non_unit _ hb]
    exact Commute.zero_right a

namespace ContinuousLinearMap

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {ι : Type*} {l : Filter ι}

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

/-- Strong convergence on a dense set plus `‖T n x‖ ≤ ‖x‖` gives strong convergence. -/
theorem tendsto_apply_of_dense {T : ℕ → V →L[𝕜] V} (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖)
    {D : Set V} (hD : Dense D) (h : ∀ x ∈ D, Tendsto (fun n => T n x) atTop (𝓝 x)) (x : V) :
    Tendsto (fun n => T n x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨d, hd, hdD⟩ := Metric.dense_iff.1 hD x (ε / 3) (by positivity)
  rw [Metric.mem_ball] at hd
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (h d hdD) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : dist (T n x) (T n d) ≤ dist x d := by
    rw [dist_eq_norm, dist_eq_norm, ← _root_.map_sub]; exact hT n _
  have := hN n hn
  calc dist (T n x) x ≤ dist (T n x) (T n d) + dist (T n d) d + dist d x :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have hd' : dist x d < ε / 3 := by rwa [dist_comm]
        linarith
    _ = ε := by ring

/-- Strong Cauchy-ness on a dense set plus `‖T n x‖ ≤ ‖x‖` gives strong Cauchy-ness. -/
theorem cauchySeq_apply_of_dense {T : ℕ → V →L[𝕜] V}
    (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖) {D : Set V} (hD : Dense D)
    (h : ∀ x ∈ D, CauchySeq fun n => T n x) (x : V) : CauchySeq fun n => T n x := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨d, hd, hdD⟩ := Metric.dense_iff.1 hD x (ε / 3) (by positivity)
  rw [Metric.mem_ball, dist_comm] at hd
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (h d hdD) (ε / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 : ∀ k, dist (T k x) (T k d) ≤ dist x d := fun k => by
    rw [dist_eq_norm, dist_eq_norm, ← _root_.map_sub]; exact hT k _
  have := hN m hm n hn
  have h2 := h1 n
  rw [dist_comm] at h2
  calc dist (T m x) (T n x) ≤ dist (T m x) (T m d) + dist (T m d) (T n d) + dist (T n d) (T n x) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith [h1 m]
    _ = ε := by ring

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
    ((Commute.all f g).map (aeval T)).ringInverse_right.eq
  simp only [hc]
  exact tendsto_apply_of_tendsto hM' (tendsto_inverse_apply (tendsto_aeval_apply hM hT g) hu hu₀
    hM') (tendsto_aeval_apply hM hT f y)

end ContinuousLinearMap
