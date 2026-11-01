module

public import Feec.Semigroup.Orbit
public import Feec.ForMathlib.Analysis.HalfLineAlgebra

/-!
# The Hille–Phillips functional calculus

For a strongly continuous semigroup `G` on a complex Banach space `E` with `‖S(t)‖ ≤ M`
(`t ≥ 0`), the **Hille–Phillips calculus** (`C0Semigroup.hillePhillips`) is the algebra
homomorphism from the half-line algebra (`Feec.HalfLineAlgebra`)

  `Φ(a δ₀ + g) = a + ∫₀^∞ g(t) S(t) dt`,

multiplicative by Fubini and `S(s + u) = S(s) S(u)` (`hillePhillipsKernel_mul`), and bounded by
the total variation, `‖Φ(μ)‖ ≤ M ‖μ‖` (`norm_hillePhillips_le`). For the dilated semigroup
`S(τ ·)` (`C0Semigroup.dilate`), `Φ(e^{-t} dt)` is the **resolvent `(1 - τA)⁻¹` as a Laplace
transform**, `R y = ∫₀^∞ e^{-t} S(τt) y dt` (`C0Semigroup.laplaceResolvent`): it inverts
`1 - τA` on both sides (`laplaceResolvent_apply_sub`, `laplaceResolvent_mem_graph`), is injective,
and is the only operator with `R (x - τ A x) = x` on `D(A)` (`eq_laplaceResolvent`).

## Main results

* `C0Semigroup.hillePhillips`, `C0Semigroup.hillePhillips_apply`, `norm_hillePhillips_le`;
* `C0Semigroup.laplaceResolvent_apply_sub`: `R (x - τ A x) = x` on `D(A)` (integration by parts);
* `C0Semigroup.laplaceResolvent_mem_graph`: `(R y, τ⁻¹ (R y - y)) ∈ graph A`, from
  `S(τk) R y = e^k (R y - ∫₀^k e^{-t} S(τt) y dt)`;
* `C0Semigroup.eq_laplaceResolvent`, `C0Semigroup.injective_laplaceResolvent`.

## References

* [E. Hille, R. S. Phillips, *Functional Analysis and Semi-Groups*][HillePhillips1957]
  (the operational calculus of a semigroup)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.3 (the resolvent as a Laplace transform)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter Topology MeasureTheory Unitization

@[expose] public noncomputable section

namespace Feec

namespace C0Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (G : C0Semigroup ℂ E) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M)

include hM

omit [CompleteSpace E] in
theorem norm_extS_le (t : ℝ) : ‖G.extS t‖ ≤ M := hM _ (le_max_right t 0)

omit [CompleteSpace E] in
theorem integrable_smul_extS {g : ℝ → ℂ} (hg : Integrable g) (x : E) :
    Integrable fun t => g t • G.extS t x :=
  hg.smul_of_top_left (memLp_top_of_bound (G.continuous_extS_apply x).aestronglyMeasurable
    (M * ‖x‖) (ae_of_all _ fun t =>
      ((G.extS t).le_opNorm x).trans (mul_le_mul_of_nonneg_right (G.norm_extS_le hM t)
        (norm_nonneg _))))

/-- `x ↦ ∫ g(t) S(t) x dt` as a linear map. -/
def hillePhillipsKernelₗ (g : HalfLineKernel) : E →ₗ[ℂ] E where
  toFun x := ∫ t, g t • G.extS t x
  map_add' x y := by
    show ∫ t, g t • G.extS t (x + y) = (∫ t, g t • G.extS t x) + ∫ t, g t • G.extS t y
    rw [← integral_add (G.integrable_smul_extS hM g.integrable x)
      (G.integrable_smul_extS hM g.integrable y)]
    congr 1; ext t; rw [_root_.map_add, smul_add]
  map_smul' c x := by
    show ∫ t, g t • G.extS t (c • x) = c • ∫ t, g t • G.extS t x
    rw [← integral_smul]
    congr 1; ext t; rw [_root_.map_smul, smul_comm]

/-- **The Hille–Phillips operator of a kernel**: `Φ(g) x = ∫₀^∞ g(t) S(t) x dt`, with
`‖Φ(g)‖ ≤ M ∫ |g|`. -/
def hillePhillipsKernel (g : HalfLineKernel) : E →L[ℂ] E :=
  (G.hillePhillipsKernelₗ hM g).mkContinuous (M * ∫ t, ‖g t‖) fun x => by
    show ‖∫ t, g t • G.extS t x‖ ≤ _
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [mul_assoc, ← integral_mul_const, mul_comm, ← integral_mul_const]
    refine integral_mono (G.integrable_smul_extS hM g.integrable x).norm
      ((g.integrable.norm.mul_const _).mul_const _) fun t => ?_
    rw [norm_smul]
    calc ‖g t‖ * ‖G.extS t x‖ ≤ ‖g t‖ * (M * ‖x‖) := by
          gcongr
          exact ((G.extS t).le_opNorm x).trans (mul_le_mul_of_nonneg_right
            (G.norm_extS_le hM t) (norm_nonneg _))
      _ = _ := by ring

omit [CompleteSpace E] in
theorem hillePhillipsKernel_apply (g : HalfLineKernel) (x : E) :
    G.hillePhillipsKernel hM g x = ∫ t, g t • G.extS t x := rfl

omit [CompleteSpace E] in
theorem norm_hillePhillipsKernel_le (g : HalfLineKernel) :
    ‖G.hillePhillipsKernel hM g‖ ≤ M * ∫ t, ‖g t‖ :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg ((norm_nonneg _).trans (hM 0 le_rfl))
    (integral_nonneg fun _ => norm_nonneg _)) _

/-- `∫ g(u) S(u + s) x du = S(s) ∫ g(u) S(u) x du` for `s ≥ 0` and `g` vanishing on `(-∞, 0)`. -/
theorem integral_smul_extS_add {g : HalfLineKernel} {s : ℝ} (hs : 0 ≤ s) (x : E) :
    ∫ u, g u • G.extS (u + s) x = G.S s (∫ u, g u • G.extS u x) := by
  rw [← (G.S s).integral_comp_comm (G.integrable_smul_extS hM g.integrable x)]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  rcases lt_or_ge u 0 with hu | hu
  · simp [g.eq_zero_of_neg u hu]
  · simp only [_root_.map_smul]
    rw [G.extS_of_nonneg (add_nonneg hu hs), G.extS_of_nonneg hu, add_comm, G.S_add_apply hs hu]

/-- **Multiplicativity**: `Φ(f ⋆ g) = Φ(f) Φ(g)` (Fubini and `S(s + u) = S(s) S(u)`). -/
theorem hillePhillipsKernel_mul (f g : HalfLineKernel) :
    G.hillePhillipsKernel hM (f * g) = G.hillePhillipsKernel hM f * G.hillePhillipsKernel hM g := by
  ext x
  simp only [hillePhillipsKernel_apply, mul_apply_eq_comp, HalfLineKernel.coe_mul,
    HalfLineKernel.conv, convolution_def, ContinuousLinearMap.mul_apply']
  have hint : Integrable (fun p : ℝ × ℝ => (f p.2 * g (p.1 - p.2)) • G.extS p.1 x)
      (volume.prod volume) := by
    refine Integrable.mono' ((f.integrable.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ)
      g.integrable).norm.mul_const (M * ‖x‖)) ?_ (ae_of_all _ fun p => ?_)
    · exact ((f.integrable.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ)
        g.integrable).aestronglyMeasurable).smul
        ((G.continuous_extS_apply x).comp continuous_fst).aestronglyMeasurable
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (((G.extS p.1).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (G.norm_extS_le hM _) (norm_nonneg _))) (norm_nonneg _)
  calc ∫ t, (∫ s, f s * g (t - s)) • G.extS t x
      = ∫ t, ∫ s, (f s * g (t - s)) • G.extS t x := by
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        exact (integral_smul_const _ _).symm
    _ = ∫ s, ∫ t, (f s * g (t - s)) • G.extS t x := integral_integral_swap hint
    _ = ∫ s, f s • ∫ u, g u • G.extS (u + s) x := by
        refine integral_congr_ae (ae_of_all _ fun s => ?_)
        dsimp only
        calc ∫ t, (f s * g (t - s)) • G.extS t x
            = ∫ t, (fun u => f s • g u • G.extS (u + s) x) (t - s) := by
              congr 1; ext t; simp [mul_smul]
          _ = ∫ u, f s • g u • G.extS (u + s) x := by
            rw [integral_sub_right_eq_self (fun u => f s • g u • G.extS (u + s) x) s]
          _ = _ := integral_smul _ _
    _ = ∫ s, f s • G.extS s (∫ u, g u • G.extS u x) := by
        refine integral_congr_ae (ae_of_all _ fun s => ?_)
        dsimp only
        rcases lt_or_ge s 0 with hs | hs
        · simp [f.eq_zero_of_neg s hs]
        · rw [G.integral_smul_extS_add hM hs, G.extS_of_nonneg hs]

/-- The Hille–Phillips calculus on kernels, a non-unital algebra homomorphism. -/
def hillePhillipsKernelHom : HalfLineKernel →ₙₐ[ℂ] (E →L[ℂ] E) where
  toFun := G.hillePhillipsKernel hM
  map_smul' c g := by
    ext x
    simp only [hillePhillipsKernel_apply, HalfLineKernel.coe_smul, Pi.smul_apply, smul_assoc,
      integral_smul, smul_apply]
    rfl
  map_zero' := by ext x; simp [hillePhillipsKernel_apply]
  map_add' f g := by
    ext x
    simp only [hillePhillipsKernel_apply, HalfLineKernel.coe_add, Pi.add_apply, add_smul,
      add_apply]
    exact integral_add (G.integrable_smul_extS hM f.integrable x)
      (G.integrable_smul_extS hM g.integrable x)
  map_mul' := G.hillePhillipsKernel_mul hM

/-- **The Hille–Phillips functional calculus** of a bounded semigroup, `‖S(t)‖ ≤ M`: the algebra
homomorphism `a δ₀ + g ↦ a + ∫₀^∞ g(t) S(t) dt` from the half-line algebra. [HillePhillips1957] -/
def hillePhillips : HalfLineAlgebra →ₐ[ℂ] (E →L[ℂ] E) := lift (G.hillePhillipsKernelHom hM)

theorem hillePhillips_apply (μ : HalfLineAlgebra) :
    G.hillePhillips hM μ = algebraMap ℂ (E →L[ℂ] E) μ.fst + G.hillePhillipsKernel hM μ.snd := by
  simp [hillePhillips, hillePhillipsKernelHom]

/-- **`‖Φ(μ)‖ ≤ M ‖μ‖`**: the calculus is bounded by the total variation. -/
theorem norm_hillePhillips_le (μ : HalfLineAlgebra) :
    ‖G.hillePhillips hM μ‖ ≤ M * μ.variation := by
  rw [hillePhillips_apply, HalfLineAlgebra.variation, mul_add]
  refine (norm_add_le _ _).trans (add_le_add ?_ (G.norm_hillePhillipsKernel_le hM _))
  rw [Algebra.algebraMap_eq_smul_one, ← G.map_zero, mul_comm]
  exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hM 0 le_rfl) (norm_nonneg _))

/-! ### The resolvent as a Laplace transform -/

omit hM [CompleteSpace E] in
/-- The dilated semigroup `t ↦ S(τ t)`, `τ ≥ 0`, generated by `τ A`. -/
def dilate (τ : ℝ) (hτ : 0 ≤ τ) : C0Semigroup ℂ E where
  S t := G.S (τ * t)
  map_zero := by simp [G.map_zero]
  map_add s t hs ht := by rw [mul_add, G.map_add _ _ (mul_nonneg hτ hs) (mul_nonneg hτ ht)]
  strongCont x := (G.strongCont x).comp (continuous_const.mul continuous_id).continuousOn
    fun t ht => mul_nonneg hτ ht

omit [CompleteSpace E] in
theorem norm_dilate_S_le {τ : ℝ} (hτ : 0 ≤ τ) (t : ℝ) (ht : 0 ≤ t) : ‖(G.dilate τ hτ).S t‖ ≤ M :=
  hM _ (mul_nonneg hτ ht)

/-- **The resolvent `(1 - τA)⁻¹` as a Laplace transform**: `R y = ∫₀^∞ e^{-t} S(τt) y dt`, the
Hille–Phillips operator of `ν = e^{-t} dt` for the dilated semigroup. -/
def laplaceResolvent (τ : ℝ) (hτ : 0 ≤ τ) : E →L[ℂ] E :=
  (G.dilate τ hτ).hillePhillips (G.norm_dilate_S_le hM hτ) HalfLineAlgebra.resolvent

theorem laplaceResolvent_apply {τ : ℝ} (hτ : 0 ≤ τ) (y : E) :
    G.laplaceResolvent hM τ hτ y =
      ∫ t : ℝ in Ioi 0, Complex.exp (-(t : ℂ)) • G.S (τ * t) y := by
  rw [laplaceResolvent, hillePhillips_apply]
  simp only [HalfLineAlgebra.resolvent, fst_inr, snd_inr]
  rw [_root_.map_zero, zero_add, hillePhillipsKernel_apply,
    ← integral_indicator (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · show HalfLineKernel.expFun 1 t • (G.dilate τ hτ).extS t y = _
    rw [HalfLineKernel.expFun, indicator_of_mem ht, extS_of_nonneg _ (le_of_lt ht),
      indicator_of_mem ht]
    simp [dilate]
  · show HalfLineKernel.expFun 1 t • (G.dilate τ hτ).extS t y = _
    rw [HalfLineKernel.expFun, indicator_of_notMem ht, zero_smul, indicator_of_notMem ht]

omit hM [CompleteSpace E] in
theorem continuousOn_exp_smul_S {τ : ℝ} (hτ : 0 ≤ τ) (z : E) :
    ContinuousOn (fun t : ℝ => Complex.exp (-(t : ℂ)) • G.S (τ * t) z) (Ici 0) :=
  (Continuous.continuousOn (by fun_prop)).smul ((G.strongCont z).comp
    (continuous_const.mul continuous_id).continuousOn fun t ht => mul_nonneg hτ ht)

omit [CompleteSpace E] in
theorem norm_exp_smul_S_le {τ : ℝ} (hτ : 0 ≤ τ) (z : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.exp (-(t : ℂ)) • G.S (τ * t) z‖ ≤ Real.exp (-t) * (M * ‖z‖) := by
  rw [norm_smul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_left (((G.S _).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right (hM _ (mul_nonneg hτ ht)) (norm_nonneg _))) (Real.exp_pos _).le

omit [CompleteSpace E] in
theorem integrableOn_exp_smul_S {τ : ℝ} (hτ : 0 ≤ τ) (z : E) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ)) • G.S (τ * t) z) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 one_pos).mul_const (M * ‖z‖))
    (((G.continuousOn_exp_smul_S hτ z).mono Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa using G.norm_exp_smul_S_le hM hτ z (le_of_lt ht)

/-- **`R (x - τ A x) = x`** on `D(A)`: integration by parts against `e^{-t}`. -/
theorem laplaceResolvent_apply_sub {τ : ℝ} (hτ : 0 ≤ τ) {x y : E}
    (h : (x, y) ∈ G.generator.graph) : G.laplaceResolvent hM τ hτ (x - (τ : ℂ) • y) = x := by
  obtain ⟨hx, rfl⟩ := LinearPMap.mem_graph_iff_exists.1 h
  rw [laplaceResolvent_apply]
  set f : ℝ → E := fun t => -(Complex.exp (-(t : ℂ)) • G.S (τ * t) x)
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (Complex.exp (-(t : ℂ)) •
      G.S (τ * t) (x - (τ : ℂ) • G.generator ⟨x, hx⟩)) t := by
    intro t ht
    have h1 := (G.hasDerivWithinAt_apply ⟨x, hx⟩ (mul_nonneg hτ (le_of_lt ht))).scomp t
      ((hasDerivAt_id t).const_mul τ).hasDerivWithinAt (s := Ici 0)
      fun u hu => mul_nonneg hτ hu
    have h2 := (h1.hasDerivAt (Ici_mem_nhds ht))
    have h3 := (((hasDerivAt_id t).ofReal_comp).neg.cexp).smul h2
    have h5 : HasDerivAt f _ t := h3.neg
    refine h5.congr_deriv ?_
    show -(Complex.exp (-(t : ℂ)) • (τ * 1) • G.S (τ * t) (G.generator ⟨x, hx⟩) +
        (Complex.exp (-(t : ℂ)) * -((1 : ℝ) : ℂ)) • G.S (τ * t) x) = _
    rw [_root_.map_sub, _root_.map_smul, Complex.ofReal_one, mul_one, ← Complex.coe_smul]
    module
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => Real.exp (-t) * (M * ‖x‖)) atTop (𝓝 0) := by
      simpa using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const (M * ‖x‖)
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [norm_neg]
    exact G.norm_exp_smul_S_le hM hτ x ht
  have hc : ContinuousWithinAt f (Ici 0) 0 :=
    ((G.continuousOn_exp_smul_S hτ x).neg) 0 self_mem_Ici
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hc hd (G.integrableOn_exp_smul_S hM hτ _) hlim]
  simp [f, G.map_zero]

omit hM [CompleteSpace E] in
/-- Shifting an integral over `(0, ∞)`: `∫_{t > 0} F(t + k) dt = ∫_{s > k} F(s) ds`. -/
theorem integral_Ioi_comp_add (F : ℝ → E) (k : ℝ) :
    ∫ t in Ioi (0 : ℝ), F (t + k) = ∫ s in Ioi k, F s := by
  have h := (measurePreserving_add_right volume k).setIntegral_preimage_emb
    (measurableEmbedding_addRight k) F (Ioi k)
  rwa [Set.preimage_add_const_Ioi, sub_self] at h

/-- **The resolvent maps into `D(A)`**: `(R y, τ⁻¹ (R y - y)) ∈ graph A`, so `R` is onto `D(A)`
with `(1 - τA) R = 1`. From `S(τk) R y = e^k (R y - ∫₀^k e^{-t} S(τt) y dt)`. -/
theorem laplaceResolvent_mem_graph {τ : ℝ} (hτ : 0 < τ) (y : E) :
    (G.laplaceResolvent hM τ hτ.le y, τ⁻¹ • (G.laplaceResolvent hM τ hτ.le y - y)) ∈
      G.generator.graph := by
  set u := G.laplaceResolvent hM τ hτ.le y
  set φ : ℝ → E := fun t => Complex.exp (-(t : ℂ)) • G.extS (τ * t) y
  have hφc : Continuous φ := by
    have := G.continuous_extS_apply y
    fun_prop
  have hφ : ∀ t, 0 ≤ t → φ t = Complex.exp (-(t : ℂ)) • G.S (τ * t) y := fun t ht => by
    simp only [φ, G.extS_of_nonneg (mul_nonneg hτ.le ht)]
  have hu : u = ∫ t in Ioi (0 : ℝ), φ t := by
    simp only [u]
    rw [laplaceResolvent_apply]
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht => (hφ t (le_of_lt ht)).symm
  have hint : IntegrableOn φ (Ioi 0) :=
    (G.integrableOn_exp_smul_S hM hτ.le y).congr_fun (fun t ht => (hφ t (le_of_lt ht)).symm)
      measurableSet_Ioi
  -- the shift identity
  have hshift : ∀ k, 0 ≤ k →
      G.S (τ * k) u = Complex.exp (k : ℂ) • (u - ∫ t in (0 : ℝ)..k, φ t) := by
    intro k hk
    have h1 : G.S (τ * k) u = ∫ t in Ioi (0 : ℝ), Complex.exp (k : ℂ) • φ (t + k) := by
      rw [hu, ← (G.S (τ * k)).integral_comp_comm hint]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht' : (0 : ℝ) ≤ t := le_of_lt ht
      have e1 : (k : ℂ) + -((t + k : ℝ) : ℂ) = -(t : ℂ) := by push_cast; ring
      have e2 : τ * (t + k) = τ * k + τ * t := by ring
      rw [hφ t ht', hφ (t + k) (by positivity), _root_.map_smul, smul_smul, ← Complex.exp_add,
        e1, e2, G.S_add_apply (mul_nonneg hτ.le hk) (mul_nonneg hτ.le ht')]
    rw [h1, integral_smul, integral_Ioi_comp_add φ k, hu,
      ← intervalIntegral.integral_interval_add_Ioi hint (hint.mono_set (Ioi_subset_Ioi hk)),
      add_sub_cancel_left]
  -- differentiate at `0`
  set F : ℝ → E := fun k => Complex.exp (k : ℂ) • (u - ∫ t in (0 : ℝ)..k, φ t)
  have hF : HasDerivAt F (u - y) 0 := by
    have h1 : HasDerivAt F _ 0 := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.cexp).smul
      ((hφc.integral_hasStrictDerivAt 0 0).hasDerivAt.const_sub u)
    refine h1.congr_deriv ?_
    simp [φ, extS, G.map_zero]
    abel
  have hdiv : HasDerivAt (fun h : ℝ => h / τ) τ⁻¹ 0 := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id (0 : ℝ)).div_const τ
  have hd : HasDerivWithinAt (fun h => G.S h u) (τ⁻¹ • (u - y)) (Ici 0) 0 := by
    have h2 : HasDerivAt (F ∘ fun h : ℝ => h / τ) (τ⁻¹ • (u - y)) 0 :=
      HasDerivAt.scomp (g₁ := F) 0 (by rwa [zero_div]) hdiv
    refine h2.hasDerivWithinAt.congr_of_mem (fun h (hh : 0 ≤ h) => ?_) self_mem_Ici
    simp only [Function.comp_apply, F]
    rw [← hshift (h / τ) (div_nonneg hh hτ.le), mul_div_cancel₀ _ hτ.ne']
  exact LinearPMap.mem_graph_iff_exists.2 ⟨⟨_, hd⟩, G.generator_apply_eq hd⟩

/-- `(1 - τA) R = 1`: `R y - τ A (R y) = y`. -/
theorem laplaceResolvent_sub_smul {τ : ℝ} (hτ : 0 < τ) (y : E) :
    G.laplaceResolvent hM τ hτ.le y - (τ : ℂ) • (τ⁻¹ • (G.laplaceResolvent hM τ hτ.le y - y)) =
      y := by
  rw [← Complex.coe_smul, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ (by exact_mod_cast hτ.ne'),
    one_smul, sub_sub_cancel]

/-- **`R` is the resolvent**: every `R'` with `R' (x - τ A x) = x` on `D(A)` is `R`. -/
theorem eq_laplaceResolvent {τ : ℝ} (hτ : 0 < τ) {R : E → E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : ℂ) • y) = x) (y : E) :
    R y = G.laplaceResolvent hM τ hτ.le y := by
  have := hR _ _ (G.laplaceResolvent_mem_graph hM hτ y)
  rwa [G.laplaceResolvent_sub_smul hM hτ y] at this

/-- `R` is injective. -/
theorem injective_laplaceResolvent {τ : ℝ} (hτ : 0 < τ) :
    Function.Injective (G.laplaceResolvent hM τ hτ.le) := by
  intro a b hab
  have ha := G.laplaceResolvent_mem_graph hM hτ a
  have hb := G.laplaceResolvent_mem_graph hM hτ b
  have := G.generator.graph.sub_mem ha hb
  simp only [Prod.mk_sub_mk, hab, sub_self] at this
  have h0 := LinearPMap.graph_fst_eq_zero_snd _ this rfl
  have h1 : τ⁻¹ • (b - a) = 0 := by rw [← h0, ← smul_sub]; congr 1; abel
  exact (sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left (inv_ne_zero hτ.ne'))).symm

end C0Semigroup

end Feec
