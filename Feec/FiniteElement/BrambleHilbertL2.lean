module

public import Feec.FiniteElement.BrambleHilbert
public import Feec.FiniteElement.PolyInterpolation
public import Feec.FiniteElement.ShapeRegularInverse
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The `L²` Bramble–Hilbert lemma, Sobolev embedding and `L²` interpolation errors

The averaged Taylor polynomial ([BrennerScott2008], Ch. 4) gives the `L²` Bramble–Hilbert lemma,
the Sobolev embedding for `2(k + 1) > n` ([Evans2010], §5.6) and the `L²` interpolation errors.

## Main results

* `lintegral_sub_avgTaylorPoly_sq_le`: the `L²` Bramble–Hilbert lemma.
* `enorm_sub_avgTaylorPoly_le_L2`: the Sobolev embedding, in a-priori form.
* `IsRefInterpolant.lintegral_sub_sq_le_L2`: the reference interpolation error in `L²`.
* `exists_formL2Sq_sub_polyInterp_le_L2`: the `L²` error of `Π_T` for `P_rΛᵏ` on `T = t + h K`.
* `exists_formL2Sq_sub_polyMinusInterp_le_L2`: the same for `P_r⁻Λᵏ`.

## References

* [J. H. Bramble, S. R. Hilbert, *Estimation of Linear Functionals on Sobolev Spaces with Application to Fourier Transforms and Spline Interpolation*][BrambleHilbert1970]
* [S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*][BrennerScott2008], Ch. 4
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1
* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.6

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Feec.FiniteElement

variable {n : ℕ} {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### The averaged Taylor polynomial -/

section AvgTaylor

/-- The averaged Taylor polynomial `Q_m f (x) = ⨍_{y ∈ K} T_m f(y)(x)` of `f` over `K`. -/
def avgTaylorPoly [CompleteSpace G] (K : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → G) (m : ℕ)
    (x : Fin n → ℝ) : G :=
  ⨍ y in K, taylorPoly f y m x

/-- The coefficient of `∏_{l ∈ s} x_{σ l}` in the `i`-th Taylor term of `f` at `y`. -/
def taylorCoeff (f : (Fin n → ℝ) → G) (i : ℕ) (σ : Fin i → Fin n) (s : Finset (Fin i))
    (y : Fin n → ℝ) : G :=
  ((i.factorial : ℝ)⁻¹ * ∏ l ∈ sᶜ, (-y (σ l))) •
    iteratedFDeriv ℝ i f y (fun l => fun j => if σ l = j then (1 : ℝ) else 0)

theorem taylorPoly_eq_sum_taylorCoeff (f : (Fin n → ℝ) → G) (y x : Fin n → ℝ) (m : ℕ) :
    taylorPoly f y m x = ∑ i ∈ Finset.range m, ∑ σ : Fin i → Fin n, ∑ s : Finset (Fin i),
      (∏ l ∈ s, x (σ l)) • taylorCoeff f i σ s y := by
  unfold taylorPoly
  refine Finset.sum_congr rfl fun i _ => ?_
  set A := iteratedFDeriv ℝ i f y
  have hx : x - y = ∑ j, (x - y) j • (fun k => if j = k then (1 : ℝ) else 0) :=
    pi_eq_sum_univ (x - y)
  rw [hx, A.map_sum (fun _ j => (x - y) j • (fun k => if j = k then (1 : ℝ) else 0)),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [A.map_smul_univ (fun l => (x - y) (σ l))
    (fun l => fun k => if σ l = k then (1 : ℝ) else 0)]
  have hprod : ∏ l, (x - y) (σ l) =
      ∑ s : Finset (Fin i), (∏ l ∈ s, x (σ l)) * ∏ l ∈ sᶜ, (-y (σ l)) := by
    simp_rw [Pi.sub_apply, sub_eq_add_neg]
    rw [Finset.prod_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.compl_eq_univ_sdiff]
  rw [hprod, Finset.sum_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [taylorCoeff, smul_smul]
  congr 1
  ring

theorem continuousOn_iteratedFDeriv_of_isOpen {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {N : ℕ} {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U) {i : ℕ} (hi : i ≤ N) :
    ContinuousOn (iteratedFDeriv ℝ i f) U := fun y hy =>
  ((hf.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right (m := 0) (i := i)
    (by rw [zero_add]; exact_mod_cast hi)).continuousAt.continuousWithinAt

theorem continuousOn_taylorCoeff {r : ℕ} {f : (Fin n → ℝ) → G} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ r f U) {i : ℕ} (hi : i ≤ r) (σ : Fin i → Fin n)
    (s : Finset (Fin i)) : ContinuousOn (taylorCoeff f i σ s) U := by
  unfold taylorCoeff
  refine ContinuousOn.smul (continuousOn_const.mul (continuousOn_finsetProd _ fun l _ =>
    (continuous_apply (σ l)).continuousOn.neg)) ?_
  exact (continuous_eval_const _).comp_continuousOn (continuousOn_iteratedFDeriv_of_isOpen hU hf hi)

theorem prod_smul_mem_polyFunctions {i r : ℕ} (σ : Fin i → Fin n) (s : Finset (Fin i))
    (hs : s.card ≤ r) (c : G) :
    (fun x : Fin n → ℝ => (∏ l ∈ s, x (σ l)) • c) ∈ polyFunctions n r G := by
  refine Submodule.subset_span ⟨∏ l ∈ s, MvPolynomial.X (σ l), ?_, c, ?_⟩
  · refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    calc ∑ l ∈ s, (MvPolynomial.X (σ l) : MvPolynomial (Fin n) ℝ).totalDegree
        = ∑ _l ∈ s, 1 := Finset.sum_congr rfl fun l _ => MvPolynomial.totalDegree_X _
      _ ≤ r := by simpa using hs
  · funext x
    simp

theorem avgTaylorPoly_eq_sum [CompleteSpace G] {K U : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {r : ℕ} {f : (Fin n → ℝ) → G} (hf : ContDiffOn ℝ r f U)
    (x : Fin n → ℝ) :
    avgTaylorPoly K f (r + 1) x = ∑ i ∈ Finset.range (r + 1), ∑ σ : Fin i → Fin n,
      ∑ s : Finset (Fin i), (∏ l ∈ s, x (σ l)) • ⨍ y in K, taylorCoeff f i σ s y := by
  have hint : ∀ i ∈ Finset.range (r + 1), ∀ (σ : Fin i → Fin n) (s : Finset (Fin i)),
      IntegrableOn (taylorCoeff f i σ s) K := fun i hi σ s =>
    ((continuousOn_taylorCoeff hU hf (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) σ s).mono
      hKU).integrableOn_compact hK
  have hint' : ∀ i ∈ Finset.range (r + 1), ∀ (σ : Fin i → Fin n) (s : Finset (Fin i)),
      IntegrableOn (fun y => (∏ l ∈ s, x (σ l)) • taylorCoeff f i σ s y) K := fun i hi σ s =>
    (hint i hi σ s).smul _
  simp only [avgTaylorPoly, taylorPoly_eq_sum_taylorCoeff, setAverage_eq]
  rw [integral_finsetSum _ fun i hi => integrable_finsetSum _ fun σ _ =>
    integrable_finsetSum _ fun s _ => hint' i hi σ s, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ fun σ _ => integrable_finsetSum _ fun s _ => hint' i hi σ s,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_finsetSum _ fun s _ => hint' i hi σ s, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_smul, smul_comm]

theorem avgTaylorPoly_mem_polyFunctions [CompleteSpace G] {K U : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {r : ℕ} {f : (Fin n → ℝ) → G}
    (hf : ContDiffOn ℝ r f U) : avgTaylorPoly K f (r + 1) ∈ polyFunctions n r G := by
  have : avgTaylorPoly K f (r + 1) = ∑ i ∈ Finset.range (r + 1), ∑ σ : Fin i → Fin n,
      ∑ s : Finset (Fin i), fun x : Fin n → ℝ =>
        (∏ l ∈ s, x (σ l)) • ⨍ y in K, taylorCoeff f i σ s y := by
    funext x
    simp only [Finset.sum_apply]
    exact avgTaylorPoly_eq_sum hK hU hKU hf x
  rw [this]
  refine Submodule.sum_mem _ fun i hi => Submodule.sum_mem _ fun σ _ =>
    Submodule.sum_mem _ fun s _ => prod_smul_mem_polyFunctions σ s ?_ _
  calc s.card ≤ (Finset.univ : Finset (Fin i)).card := Finset.card_le_univ s
    _ = i := by simp
    _ ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)

end AvgTaylor

/-! ### Taylor's formula with integral remainder -/

section Remainder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The Taylor sum `∑_{i ≤ k} ((1 - t)^i / i!) D^i f(y + t v)(v, …, v)` along `y + t v`. -/
def taylorSegment (f : E → F) (y v : E) (k : ℕ) (t : ℝ) : F :=
  ∑ i ∈ Finset.range (k + 1),
    ((1 - t) ^ i / i.factorial) • iteratedFDeriv ℝ i f (y + t • v) (fun _ => v)

theorem hasDerivAt_iteratedFDeriv_segment {N : ℕ} {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ N f U) {i : ℕ} (hi : i < N) {y v : E} {t : ℝ} (ht : y + t • v ∈ U) :
    HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ i f (y + t • v) (fun _ => v))
      (iteratedFDeriv ℝ (i + 1) f (y + t • v) (fun _ => v)) t := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ i f) (y + t • v) :=
    (hf.contDiffAt (hU.mem_nhds ht)).differentiableAt_iteratedFDeriv (by exact_mod_cast hi)
  have hγ : HasDerivAt (fun t : ℝ => y + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add y
  have h1 := hd.hasFDerivAt.comp_hasDerivAt t hγ
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => E) F
    (fun _ => v)).hasFDerivAt.comp_hasDerivAt t h1
  have e : iteratedFDeriv ℝ (i + 1) f (y + t • v) (fun _ => v) =
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => E) F (fun _ => v))
        (fderiv ℝ (iteratedFDeriv ℝ i f) (y + t • v) v) := by
    rw [iteratedFDeriv_succ_apply_left]; rfl
  rw [e]
  exact h2

theorem hasDerivAt_taylorSegment {N : ℕ} {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ N f U) {y v : E} {t : ℝ} (ht : y + t • v ∈ U) :
    ∀ k : ℕ, k < N → HasDerivAt (taylorSegment f y v k)
      (((1 - t) ^ k / k.factorial) • iteratedFDeriv ℝ (k + 1) f (y + t • v) (fun _ => v)) t := by
  have hc : ∀ i : ℕ, HasDerivAt (fun t : ℝ => (1 - t) ^ i / (i.factorial : ℝ))
      (((i : ℝ) * (1 - t) ^ (i - 1) * (-1)) / i.factorial) t := fun i => by
    have := (((hasDerivAt_id t).const_sub 1).pow i).div_const (i.factorial : ℝ)
    simpa using this
  intro k
  induction k with
  | zero =>
    intro hN
    have h := (hc 0).smul (hasDerivAt_iteratedFDeriv_segment hU hf hN ht)
    have he : taylorSegment f y v 0 = fun t : ℝ =>
        ((1 - t) ^ 0 / (Nat.factorial 0 : ℝ)) • iteratedFDeriv ℝ 0 f (y + t • v) (fun _ => v) := by
      funext t; simp [taylorSegment]
    rw [he]
    convert h using 1
    simp
  | succ k ih =>
    intro hN
    have h1 := ih (by omega)
    have h2 := (hc (k + 1)).smul (hasDerivAt_iteratedFDeriv_segment hU hf hN ht)
    have he : taylorSegment f y v (k + 1) = fun t : ℝ => taylorSegment f y v k t +
        ((1 - t) ^ (k + 1) / ((k + 1).factorial : ℝ)) •
          iteratedFDeriv ℝ (k + 1) f (y + t • v) (fun _ => v) := by
      funext t; rw [taylorSegment, Finset.sum_range_succ]; rfl
    rw [he]
    convert h1.add h2 using 1
    rw [add_comm (((1 - t) ^ (k + 1) / _) • _), ← add_assoc, ← add_smul]
    have : (1 - t) ^ k / (k.factorial : ℝ) +
        ((k + 1 : ℕ) : ℝ) * (1 - t) ^ (k + 1 - 1) * (-1) / ((k + 1).factorial : ℝ) = 0 := by
      rw [Nat.factorial_succ, Nat.add_sub_cancel]
      push_cast
      field_simp
      ring
    rw [this, zero_smul, zero_add]

theorem sub_taylorPoly_eq_integral [CompleteSpace F] {k : ℕ} {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (k + 1) f U) {x y : E}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, y + t • (x - y) ∈ U) :
    f x - taylorPoly f y (k + 1) x = ∫ t in (0 : ℝ)..1, ((1 - t) ^ k / k.factorial) •
      iteratedFDeriv ℝ (k + 1) f (y + t • (x - y)) (fun _ => x - y) := by
  have hseg' : ∀ t ∈ uIcc (0 : ℝ) 1, y + t • (x - y) ∈ U := fun t ht =>
    hseg t (by rwa [uIcc_of_le zero_le_one] at ht)
  have hcont : ContinuousOn (fun t : ℝ => ((1 - t) ^ k / k.factorial) •
      iteratedFDeriv ℝ (k + 1) f (y + t • (x - y)) (fun _ => x - y)) (uIcc 0 1) := by
    refine ContinuousOn.smul (by fun_prop) ?_
    refine (continuous_eval_const _).comp_continuousOn ?_
    refine (continuousOn_iteratedFDeriv_of_isOpen hU hf le_rfl).comp
      (by fun_prop) fun t ht => hseg' t ht
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_taylorSegment (N := k + 1) hU (by exact_mod_cast hf) (hseg' t ht) k
      (Nat.lt_succ_self k))
    (hcont.intervalIntegrable)]
  have h1 : taylorSegment f y (x - y) k 1 = f x := by
    rw [taylorSegment, Finset.sum_range_succ']
    simp only [sub_self, one_smul, add_sub_cancel, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, iteratedFDeriv_zero_apply]
    rw [Finset.sum_eq_zero fun i _ => by simp, zero_add]
  have h0 : taylorSegment f y (x - y) k 0 = taylorPoly f y (k + 1) x := by
    rw [taylorSegment, taylorPoly]
    simp
  rw [h1, h0]

theorem enorm_sub_taylorPoly_le [CompleteSpace F] {k : ℕ} {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (k + 1) f U) {x y : E}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, y + t • (x - y) ∈ U) :
    ‖f x - taylorPoly f y (k + 1) x‖ₑ ≤ ∫⁻ t in Ioo (0 : ℝ) 1,
      ENNReal.ofReal ((1 - t) ^ k / k.factorial) *
        ‖iteratedFDeriv ℝ (k + 1) f (y + t • (x - y))‖ₑ * ‖x - y‖ₑ ^ (k + 1) := by
  rw [sub_taylorPoly_eq_integral hU hf hseg, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [setLIntegral_congr Ioo_ae_eq_Ioc.symm]
  refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
  have hc : 0 ≤ (1 - t) ^ k / (k.factorial : ℝ) := by
    have : 0 ≤ 1 - t := by linarith [ht.2]
    positivity
  rw [enorm_smul, Real.enorm_eq_ofReal hc, mul_assoc]
  gcongr
  have h := (iteratedFDeriv ℝ (k + 1) f (y + t • (x - y))).le_opNNNorm (fun _ => x - y)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  simpa [enorm, ← ENNReal.coe_pow, ← ENNReal.coe_mul] using ENNReal.coe_le_coe.2 h

end Remainder

/-! ### Two integrals -/

section Integrals

theorem integral_inv_one_sub_pow (hn : 0 < n) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1) :
    ∫ t in (0 : ℝ)..b, ((1 - t) ^ (n + 1))⁻¹ = (((1 - b) ^ n)⁻¹ - 1) / n := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) b, HasDerivAt (fun t : ℝ => ((1 - t) ^ n)⁻¹ / n)
      ((1 - t) ^ (n + 1))⁻¹ t := by
    intro t ht
    rw [uIcc_of_le hb0] at ht
    have h1 : (1 - t) ≠ 0 := by linarith [ht.2]
    have h2 : HasDerivAt (fun t : ℝ => (1 - t) ^ n) (n * (1 - t) ^ (n - 1) * (-1)) t := by
      have := (hasDerivAt_pow n (1 - t)).comp t ((hasDerivAt_id t).const_sub 1)
      convert this using 1
      exact funext fun _ => rfl
    have h := (h2.inv (pow_ne_zero n h1)).div_const (n : ℝ)
    convert h using 1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    field_simp
    ring
  have hcont : ContinuousOn (fun t : ℝ => ((1 - t) ^ (n + 1))⁻¹) (uIcc 0 b) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun t ht => ?_
    rw [uIcc_of_le hb0] at ht
    exact pow_ne_zero _ (by linarith [ht.2])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp [sub_div]

theorem lintegral_inv_one_sub_pow_indicator_le (hn : 0 < n) {a d : ℝ} (ha : 0 < a) :
    ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) *
        {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t ≤ ENNReal.ofReal (d ^ n / (n * a ^ n)) := by
  rcases le_or_gt d a with hda | hda
  · -- the indicator vanishes on `(0, 1)`
    have h0 : ∀ t ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) *
        {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t = 0 := by
      intro t ht
      have : ¬ a ≤ (1 - t) * d := by
        rcases le_or_gt d 0 with hd | hd
        · nlinarith [ht.2]
        · nlinarith [ht.1]
      simp [Set.indicator_of_notMem (show t ∉ {t : ℝ | a ≤ (1 - t) * d} from this)]
    refine (setLIntegral_mono' measurableSet_Ioo fun t ht => (h0 t ht).le).trans ?_
    simp
  have hd : 0 < d := ha.trans hda
  set b := 1 - a / d with hb_def
  have hb0 : 0 ≤ b := by
    rw [hb_def, sub_nonneg, div_le_one hd]; exact hda.le
  have hb1 : b < 1 := by rw [hb_def]; have := div_pos ha hd; linarith
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) *
      {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t ≤
        (Ioc 0 b).indicator (fun t => ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹)) t := by
    intro t ht
    by_cases hmem : a ≤ (1 - t) * d
    · have htb : t ≤ b := by
        rw [hb_def, le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hd]; linarith
      rw [Set.indicator_of_mem (show t ∈ {t : ℝ | a ≤ (1 - t) * d} from hmem),
        Set.indicator_of_mem (show t ∈ Ioc 0 b from ⟨ht.1, htb⟩)]
      simp
    · rw [Set.indicator_of_notMem (show t ∉ {t : ℝ | a ≤ (1 - t) * d} from hmem)]
      simp
  have hcont : ContinuousOn (fun t : ℝ => ((1 - t) ^ (n + 1))⁻¹) (Icc 0 b) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun t ht => pow_ne_zero _ (by linarith [ht.2])
  have hint : IntegrableOn (fun t : ℝ => ((1 - t) ^ (n + 1))⁻¹) (Ioc 0 b) :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  calc ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) *
        {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t
      ≤ ∫⁻ t in Ioo (0 : ℝ) 1,
          (Ioc 0 b).indicator (fun t => ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹)) t :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ ≤ ∫⁻ t, (Ioc 0 b).indicator (fun t => ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹)) t :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ t in Ioc 0 b, ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) :=
        lintegral_indicator measurableSet_Ioc _
    _ = ENNReal.ofReal (∫ t in Ioc 0 b, ((1 - t) ^ (n + 1))⁻¹) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioc
          fun t ht => inv_nonneg.2 (pow_nonneg (by linarith [ht.2]) _))).symm
    _ ≤ ENNReal.ofReal (d ^ n / (n * a ^ n)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← intervalIntegral.integral_of_le hb0, integral_inv_one_sub_pow hn hb0 hb1, hb_def,
          sub_sub_cancel, div_pow, inv_div]
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rw [div_le_div_iff₀ hn' (by positivity), sub_mul, one_mul]
        have : d ^ n / a ^ n * (n * a ^ n) = d ^ n * n := by field_simp
        rw [this]
        have : 0 ≤ (n : ℝ) * a ^ n := by positivity
        linarith

theorem lintegral_comp_smul_fin (g : (Fin n → ℝ) → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    ∫⁻ y, g (r • y) = ENNReal.ofReal |(r ^ n)⁻¹| * ∫⁻ z, g z := by
  let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) := (Homeomorph.smul (Units.mk0 r hr)).toMeasurableEquiv
  calc ∫⁻ y, g (r • y) = ∫⁻ y, g (e y) := rfl
    _ = ∫⁻ z, g z ∂(Measure.map e volume) := (lintegral_map_equiv g e).symm
    _ = ENNReal.ofReal |(r ^ n)⁻¹| * ∫⁻ z, g z := by
        have he : (e : (Fin n → ℝ) → (Fin n → ℝ)) = fun y => r • y := rfl
        rw [he, Measure.map_addHaar_smul volume hr, lintegral_smul_measure, Module.finrank_fin_fun]
        rfl

theorem lintegral_comp_add_smul_sub (g : (Fin n → ℝ) → ℝ≥0∞) (x : Fin n → ℝ) {t : ℝ}
    (ht : t ≠ 1) :
    ∫⁻ y, g (y + t • (x - y)) = ENNReal.ofReal |((1 - t) ^ n)⁻¹| * ∫⁻ z, g z := by
  have hs : (1 - t) ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  have e : ∀ y : Fin n → ℝ, y + t • (x - y) = (1 - t) • y + t • x := fun y => by
    rw [smul_sub, sub_smul, one_smul]; abel
  simp_rw [e]
  rw [lintegral_comp_smul_fin (fun w => g (w + t • x)) hs,
    lintegral_add_right_eq_self (fun w => g w) (t • x)]

theorem measurable_indicator_of_continuousOn {s : Set (Fin n → ℝ)} (hs : IsClosed s)
    {g : (Fin n → ℝ) → ℝ≥0∞} (hg : ContinuousOn g s) : Measurable (s.indicator g) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact hg.measurable_piecewise continuousOn_const hs.measurableSet

end Integrals

/-! ### The Riesz-potential bound for the remainder -/

section Riesz

/-- The Riesz kernel `‖x - z‖^m / ‖x - z‖^n` in `ℝ≥0∞`. -/
def rieszKernel (n m : ℕ) (x z : Fin n → ℝ) : ℝ≥0∞ := ‖x - z‖ₑ ^ m / ‖x - z‖ₑ ^ n

theorem measurable_rieszKernel (m : ℕ) :
    Measurable (Function.uncurry (rieszKernel n m)) := by
  change Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => rieszKernel n m p.1 p.2
  unfold rieszKernel
  have : Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => ‖p.1 - p.2‖ₑ :=
    (continuous_enorm.comp (continuous_fst.sub continuous_snd)).measurable
  exact (this.pow_const m).div (this.pow_const n)

theorem measurable_rieszKernel_right (m : ℕ) (x : Fin n → ℝ) :
    Measurable (rieszKernel n m x) :=
  (measurable_rieszKernel m).of_uncurry_left

theorem rieszKernel_comm (m : ℕ) (x z : Fin n → ℝ) : rieszKernel n m x z = rieszKernel n m z x := by
  simp only [rieszKernel, ← enorm_neg (x - z), neg_sub]

theorem lintegral_time_le (hn : 0 < n) (k : ℕ) {d : ℝ} (hd : 0 ≤ d) (x z : Fin n → ℝ) (c : ℝ≥0∞) :
    ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ k / k.factorial) *
        ENNReal.ofReal |((1 - t) ^ n)⁻¹| * (c * (ENNReal.ofReal (1 - t)⁻¹ * ‖x - z‖ₑ) ^ (k + 1) *
          {p : ℝ × (Fin n → ℝ) | ‖x - p.2‖ ≤ (1 - p.1) * d}.indicator 1 (t, z)) ≤
      ENNReal.ofReal (d ^ n / (n * k.factorial)) * (c * rieszKernel n (k + 1) x z) := by
  rcases eq_or_ne x z with rfl | hxz
  · simp
  have ha : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hxz)
  set a := ‖x - z‖ with ha_def
  set A := ‖x - z‖ₑ with hA_def
  have hAa : A = ENNReal.ofReal a := by rw [hA_def, ha_def, ofReal_norm]
  set Cst := c * A ^ (k + 1) * ENNReal.ofReal (k.factorial : ℝ)⁻¹
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ k / k.factorial) *
      ENNReal.ofReal |((1 - t) ^ n)⁻¹| * (c * (ENNReal.ofReal (1 - t)⁻¹ * A) ^ (k + 1) *
        {p : ℝ × (Fin n → ℝ) | ‖x - p.2‖ ≤ (1 - p.1) * d}.indicator 1 (t, z)) =
      Cst * (ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) * {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t) := by
    intro t ht
    have h1t : 0 < 1 - t := by linarith [ht.2]
    have hreal : (1 - t) ^ k / k.factorial * |((1 - t) ^ n)⁻¹| * ((1 - t)⁻¹) ^ (k + 1) =
        ((1 - t) ^ (n + 1))⁻¹ * (k.factorial : ℝ)⁻¹ := by
      rw [abs_of_pos (by positivity)]
      generalize 1 - t = u at h1t ⊢
      have hu : u ≠ 0 := h1t.ne'
      rw [inv_pow]
      field_simp
      ring
    have hind : {p : ℝ × (Fin n → ℝ) | ‖x - p.2‖ ≤ (1 - p.1) * d}.indicator
        (1 : ℝ × (Fin n → ℝ) → ℝ≥0∞) (t, z) =
        {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t := by
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, ha_def, Pi.one_apply]
    rw [hind, mul_pow, ← ENNReal.ofReal_pow (inv_nonneg.2 h1t.le)]
    calc ENNReal.ofReal ((1 - t) ^ k / k.factorial) * ENNReal.ofReal |((1 - t) ^ n)⁻¹| *
          (c * (ENNReal.ofReal ((1 - t)⁻¹ ^ (k + 1)) * A ^ (k + 1)) *
            {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t)
        = ENNReal.ofReal ((1 - t) ^ k / k.factorial * |((1 - t) ^ n)⁻¹| *
            ((1 - t)⁻¹) ^ (k + 1)) * (c * A ^ (k + 1)) *
            {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          ring
      _ = Cst * (ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) *
            {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t) := by
          rw [hreal, ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg h1t.le _))]
          ring
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) *
      {t : ℝ | a ≤ (1 - t) * d}.indicator (1 : ℝ → ℝ≥0∞) t :=
    (ENNReal.measurable_ofReal.comp ((measurable_id.const_sub (1 : ℝ)).pow_const (n + 1)).inv).mul
      (measurable_const.indicator (measurableSet_le measurable_const
        ((measurable_id.const_sub 1).mul measurable_const)))
  rw [setLIntegral_congr_fun measurableSet_Ioo hpt, lintegral_const_mul _ hmeas]
  calc Cst * ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (((1 - t) ^ (n + 1))⁻¹) *
        {t : ℝ | a ≤ (1 - t) * d}.indicator 1 t
      ≤ Cst * ENNReal.ofReal (d ^ n / (n * a ^ n)) :=
        mul_le_mul_right (lintegral_inv_one_sub_pow_indicator_le hn ha) _
    _ = ENNReal.ofReal (d ^ n / (n * k.factorial)) * (c * rieszKernel n (k + 1) x z) := by
        have hsplit : ENNReal.ofReal (k.factorial : ℝ)⁻¹ * ENNReal.ofReal (d ^ n / (n * a ^ n)) =
            ENNReal.ofReal (d ^ n / (n * k.factorial)) * (ENNReal.ofReal a ^ n)⁻¹ := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg _)), ← ENNReal.ofReal_pow ha.le,
            ← ENNReal.ofReal_inv_of_pos (pow_pos ha n),
            ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hd _) (by positivity))]
          congr 1
          field_simp
        simp only [Cst, rieszKernel, ← hA_def, ENNReal.div_eq_inv_mul]
        rw [hAa]
        calc c * ENNReal.ofReal a ^ (k + 1) * ENNReal.ofReal (k.factorial : ℝ)⁻¹ *
              ENNReal.ofReal (d ^ n / (n * a ^ n))
            = c * ENNReal.ofReal a ^ (k + 1) * (ENNReal.ofReal (k.factorial : ℝ)⁻¹ *
              ENNReal.ofReal (d ^ n / (n * a ^ n))) := by ring
          _ = _ := by rw [hsplit]; ring

theorem enorm_sub_avgTaylorPoly_le_riesz [CompleteSpace G] (hn : 0 < n) {K U : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKc : Convex ℝ K) (hK0 : volume K ≠ 0) (hU : IsOpen U) (hKU : K ⊆ U)
    {k : ℕ} {f : (Fin n → ℝ) → G} (hf : ContDiffOn ℝ (k + 1) f U) {d : ℝ}
    (hd : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ d) {x : Fin n → ℝ} (hx : x ∈ K) :
    ‖f x - avgTaylorPoly K f (k + 1) x‖ₑ ≤
      ENNReal.ofReal (d ^ n / (n * k.factorial)) / volume K *
        ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ * rieszKernel n (k + 1) x z := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hKt : volume K ≠ ∞ := hK.measure_lt_top.ne
  have hd0 : 0 ≤ d := by simpa using hd x hx x hx
  set F : (Fin n → ℝ) → ℝ≥0∞ := K.indicator fun z => ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ with hF_def
  have hFm : Measurable F := measurable_indicator_of_continuousOn hK.isClosed
    (continuous_enorm.comp_continuousOn
      ((continuousOn_iteratedFDeriv_of_isOpen hU hf le_rfl).mono hKU))
  set T : (Fin n → ℝ) → G := fun y => taylorPoly f y (k + 1) x
  have hTc : ContinuousOn T K := by
    have : T = fun y => ∑ i ∈ Finset.range (k + 1),
        ((i.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ i f y (fun _ => x - y)) := rfl
    rw [this]
    refine continuousOn_finsetSum _ fun i hi => ContinuousOn.const_smul ?_ _
    have hc := (continuousOn_iteratedFDeriv_of_isOpen hU hf
      (Nat.le_succ_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))).mono hKU
    exact continuous_eval.comp_continuousOn (hc.prodMk (by fun_prop))
  have hTint : IntegrableOn T K := hTc.integrableOn_compact hK
  -- the average of the remainder
  have h1 : ‖f x - avgTaylorPoly K f (k + 1) x‖ₑ ≤ (volume K)⁻¹ * ∫⁻ y in K, ‖f x - T y‖ₑ := by
    have hr : volume.real K ≠ 0 := by
      rw [measureReal_def]; exact ENNReal.toReal_ne_zero.2 ⟨hK0, hKt⟩
    have : f x - avgTaylorPoly K f (k + 1) x = (volume.real K)⁻¹ • ∫ y in K, (f x - T y) := by
      rw [integral_sub (integrableOn_const hKt) hTint, setIntegral_const, smul_sub, smul_smul,
        inv_mul_cancel₀ hr, one_smul, avgTaylorPoly, setAverage_eq]
    rw [this, enorm_smul]
    gcongr
    · rw [Real.enorm_eq_ofReal (inv_nonneg.2 measureReal_nonneg), ENNReal.ofReal_inv_of_pos
        (lt_of_le_of_ne measureReal_nonneg (Ne.symm hr)), measureReal_def,
        ENNReal.ofReal_toReal hKt]
    · exact enorm_integral_le_lintegral_enorm _
  -- the integral remainder at each base point
  have h2 : ∀ y ∈ K, ‖f x - T y‖ₑ ≤ ∫⁻ t in Ioo (0 : ℝ) 1,
      ENNReal.ofReal ((1 - t) ^ k / k.factorial) * F (y + t • (x - y)) * ‖x - y‖ₑ ^ (k + 1) := by
    intro y hy
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1, y + t • (x - y) ∈ K := fun t ht =>
      hKc.add_smul_sub_mem hy hx ht
    refine (enorm_sub_taylorPoly_le hU hf fun t ht => hKU (hseg t ht)).trans_eq ?_
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [hF_def, Set.indicator_of_mem (hseg t (Ioo_subset_Icc_self ht))]
  set S : Set (ℝ × (Fin n → ℝ)) := {p | ‖x - p.2‖ ≤ (1 - p.1) * d} with hS_def
  have hSm : MeasurableSet S := measurableSet_le (by fun_prop) (by fun_prop)
  set g : ℝ → (Fin n → ℝ) → ℝ≥0∞ := fun t z =>
    F z * (ENNReal.ofReal (1 - t)⁻¹ * ‖x - z‖ₑ) ^ (k + 1) * S.indicator 1 (t, z) with hg_def
  have hHm : Measurable fun p : (Fin n → ℝ) × ℝ =>
      ENNReal.ofReal ((1 - p.2) ^ k / k.factorial) * F (p.1 + p.2 • (x - p.1)) *
        ‖x - p.1‖ₑ ^ (k + 1) := by
    fun_prop
  have hΨm : Measurable fun p : ℝ × (Fin n → ℝ) =>
      ENNReal.ofReal ((1 - p.1) ^ k / k.factorial) * ENNReal.ofReal |((1 - p.1) ^ n)⁻¹| *
        g p.1 p.2 := by
    have h5 : Measurable fun p : ℝ × (Fin n → ℝ) => S.indicator (1 : ℝ × (Fin n → ℝ) → ℝ≥0∞) (p.1, p.2) :=
      (measurable_const.indicator hSm).comp (measurable_fst.prodMk measurable_snd)
    fun_prop
  -- the change of variables at fixed time
  have h4 : ∀ t ∈ Ioo (0 : ℝ) 1, ∫⁻ y in K, ENNReal.ofReal ((1 - t) ^ k / k.factorial) *
      F (y + t • (x - y)) * ‖x - y‖ₑ ^ (k + 1) ≤ ∫⁻ z, ENNReal.ofReal ((1 - t) ^ k /
        k.factorial) * ENNReal.ofReal |((1 - t) ^ n)⁻¹| * g t z := by
    intro t ht
    have h1t : 0 < 1 - t := by linarith [ht.2]
    have hpt : ∀ y ∈ K, ENNReal.ofReal ((1 - t) ^ k / k.factorial) * F (y + t • (x - y)) *
        ‖x - y‖ₑ ^ (k + 1) ≤ ENNReal.ofReal ((1 - t) ^ k / k.factorial) *
          g t (y + t • (x - y)) := by
      intro y hy
      have hxv : x - (y + t • (x - y)) = (1 - t) • (x - y) := by
        rw [sub_smul, one_smul]; abel
      have hn1 : ENNReal.ofReal (1 - t)⁻¹ * ‖x - (y + t • (x - y))‖ₑ = ‖x - y‖ₑ := by
        rw [hxv, enorm_smul, Real.enorm_eq_ofReal h1t.le, ← mul_assoc,
          ← ENNReal.ofReal_mul (inv_nonneg.2 h1t.le), inv_mul_cancel₀ h1t.ne', ENNReal.ofReal_one,
          one_mul]
      have hSmem : (t, y + t • (x - y)) ∈ S := by
        change ‖x - (y + t • (x - y))‖ ≤ (1 - t) * d
        rw [hxv, norm_smul, Real.norm_of_nonneg h1t.le]
        exact mul_le_mul_of_nonneg_left (hd x hx y hy) h1t.le
      rw [hg_def]
      simp only
      rw [hn1, Set.indicator_of_mem hSmem, Pi.one_apply, mul_one, mul_assoc]
    calc ∫⁻ y in K, ENNReal.ofReal ((1 - t) ^ k / k.factorial) * F (y + t • (x - y)) *
          ‖x - y‖ₑ ^ (k + 1)
        ≤ ∫⁻ y, ENNReal.ofReal ((1 - t) ^ k / k.factorial) * g t (y + t • (x - y)) :=
          (setLIntegral_mono' hKm hpt).trans (setLIntegral_le_lintegral _ _)
      _ = ENNReal.ofReal ((1 - t) ^ k / k.factorial) * ∫⁻ y, g t (y + t • (x - y)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal ((1 - t) ^ k / k.factorial) *
            (ENNReal.ofReal |((1 - t) ^ n)⁻¹| * ∫⁻ z, g t z) := by
          rw [lintegral_comp_add_smul_sub _ x (ne_of_lt ht.2)]
      _ = _ := by
          rw [← mul_assoc, ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            ENNReal.ofReal_ne_top)]
  calc ‖f x - avgTaylorPoly K f (k + 1) x‖ₑ ≤ (volume K)⁻¹ * ∫⁻ y in K, ‖f x - T y‖ₑ := h1
    _ ≤ (volume K)⁻¹ * ∫⁻ y in K, ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ k /
          k.factorial) * F (y + t • (x - y)) * ‖x - y‖ₑ ^ (k + 1) := by
        exact mul_le_mul_right (setLIntegral_mono' hKm h2) _
    _ = (volume K)⁻¹ * ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ y in K, ENNReal.ofReal ((1 - t) ^ k /
          k.factorial) * F (y + t • (x - y)) * ‖x - y‖ₑ ^ (k + 1) := by
        rw [lintegral_lintegral_swap hHm.aemeasurable]
    _ ≤ (volume K)⁻¹ * ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ z, ENNReal.ofReal ((1 - t) ^ k /
          k.factorial) * ENNReal.ofReal |((1 - t) ^ n)⁻¹| * g t z := by
        exact mul_le_mul_right (setLIntegral_mono' measurableSet_Ioo h4) _
    _ = (volume K)⁻¹ * ∫⁻ z, ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ k /
          k.factorial) * ENNReal.ofReal |((1 - t) ^ n)⁻¹| * g t z := by
        rw [lintegral_lintegral_swap hΨm.aemeasurable]
    _ ≤ (volume K)⁻¹ * ∫⁻ z, ENNReal.ofReal (d ^ n / (n * k.factorial)) *
          (F z * rieszKernel n (k + 1) x z) := by
        exact mul_le_mul_right (lintegral_mono fun z => lintegral_time_le hn k hd0 x z (F z)) _
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hF_def]
        simp_rw [← Set.indicator_mul_left]
        rw [lintegral_indicator hKm, ENNReal.div_eq_inv_mul]
        ring

end Riesz

/-! ### Integrals of the Riesz kernel -/

section KernelIntegral

theorem lintegral_closedBall_pow_div_pow (hn : 0 < n) {a b : ℕ} (ha : 0 < a) (hab : b < a + n)
    {d : ℝ} (hd : 0 ≤ d) :
    ∫⁻ w in Metric.closedBall (0 : Fin n → ℝ) d, ‖w‖ₑ ^ a / ‖w‖ₑ ^ b =
      ENNReal.ofReal (n * volume.real (Metric.ball (0 : Fin n → ℝ) 1) *
        (d ^ ((n : ℝ) + a - b) / ((n : ℝ) + a - b))) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hγ : (-1 : ℝ) < (n : ℝ) - 1 + a - b := by
    have : (b : ℝ) < a + n := by exact_mod_cast hab
    linarith
  set h : ℝ → ℝ := (Iic d).indicator fun y => y ^ a / y ^ b with h_def
  -- the integrand as a radial function
  have hrad : ∀ w : Fin n → ℝ, (Metric.closedBall (0 : Fin n → ℝ) d).indicator
      (fun w => ‖w‖ₑ ^ a / ‖w‖ₑ ^ b) w = ENNReal.ofReal (h ‖w‖) := by
    intro w
    by_cases hw : w ∈ Metric.closedBall (0 : Fin n → ℝ) d
    · have hw' : ‖w‖ ∈ Iic d := by simpa using hw
      rw [Set.indicator_of_mem hw, h_def, Set.indicator_of_mem hw']
      rcases eq_or_ne w 0 with rfl | hw0
      · simp [zero_pow ha.ne']
      · have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
        rw [ENNReal.ofReal_div_of_pos (pow_pos hpos b), ENNReal.ofReal_pow hpos.le,
          ENNReal.ofReal_pow hpos.le, ofReal_norm]
    · have hw' : ‖w‖ ∉ Iic d := by simpa using hw
      rw [Set.indicator_of_notMem hw, h_def, Set.indicator_of_notMem hw', ENNReal.ofReal_zero]
  -- the radial profile
  have hprof : EqOn (fun y : ℝ => y ^ (Module.finrank ℝ (Fin n → ℝ) - 1) • h y)
      ((Ioc 0 d).indicator fun y => y ^ ((n : ℝ) - 1 + a - b)) (Ioi 0) := by
    intro y hy
    have hy : 0 < y := hy
    dsimp only
    rw [Module.finrank_fin_fun, smul_eq_mul, h_def]
    by_cases hyd : y ≤ d
    · rw [Set.indicator_of_mem (show y ∈ Iic d from hyd),
        Set.indicator_of_mem (show y ∈ Ioc 0 d from ⟨hy, hyd⟩)]
      rw [Real.rpow_sub hy, Real.rpow_add hy, Real.rpow_sub hy, Real.rpow_one, Real.rpow_natCast,
        Real.rpow_natCast, Real.rpow_natCast, ← pow_sub_one_mul (by omega : n ≠ 0) y] 
      field_simp
    · rw [Set.indicator_of_notMem (show y ∉ Iic d from hyd),
        Set.indicator_of_notMem (show y ∉ Ioc 0 d from fun h => hyd h.2), mul_zero]
  have hint1 : IntegrableOn (fun y : ℝ => y ^ ((n : ℝ) - 1 + a - b)) (Ioc 0 d) :=
    (intervalIntegral.intervalIntegrable_rpow' hγ).1
  have hint2 : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ (Fin n → ℝ) - 1) • h y)
      (Ioi 0) := by
    refine (integrableOn_congr_fun hprof measurableSet_Ioi).2 ?_
    exact (hint1.integrable_indicator measurableSet_Ioc).integrableOn
  have hint : Integrable (fun w : Fin n → ℝ => h ‖w‖) :=
    (integrable_fun_norm_addHaar volume (f := h)).2 hint2
  have hval : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ (Fin n → ℝ) - 1) • h y =
      d ^ ((n : ℝ) + a - b) / ((n : ℝ) + a - b) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hprof, setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.2 Ioc_subset_Ioi_self, ← intervalIntegral.integral_of_le hd,
      integral_rpow (Or.inl hγ)]
    have : (n : ℝ) - 1 + a - b + 1 = (n : ℝ) + a - b := by ring
    rw [this, Real.zero_rpow (by linarith), sub_zero]
  have hnonneg : 0 ≤ᵐ[volume] fun w : Fin n → ℝ => h ‖w‖ := by
    refine Eventually.of_forall fun w => ?_
    simp only [h_def, Pi.zero_apply]
    exact Set.indicator_nonneg (fun y _ => div_nonneg (pow_nonneg (norm_nonneg w) _)
      (pow_nonneg (norm_nonneg w) _)) _
  rw [← lintegral_indicator measurableSet_closedBall]
  simp_rw [hrad]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg, integral_fun_norm_addHaar volume h, hval,
    Module.finrank_fin_fun, nsmul_eq_mul, smul_eq_mul, mul_assoc]

/-- The constant `n |B₁| d^{n + a - b} / (n + a - b)`. -/
def rieszConst (n a b : ℕ) (d : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (n * volume.real (Metric.ball (0 : Fin n → ℝ) 1) *
    (d ^ ((n : ℝ) + a - b) / ((n : ℝ) + a - b)))

theorem rieszConst_ne_top (n a b : ℕ) (d : ℝ) : rieszConst n a b d ≠ ∞ := ENNReal.ofReal_ne_top

theorem lintegral_rieszKernel_pow_le (hn : 0 < n) {K : Set (Fin n → ℝ)} (hKm : MeasurableSet K)
    {d : ℝ} (hd : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ d) {x : Fin n → ℝ} (hx : x ∈ K) {m q : ℕ}
    (hqm : 0 < q * m) (hq : q * n < q * m + n) :
    ∫⁻ z in K, rieszKernel n m x z ^ q ≤ rieszConst n (q * m) (q * n) d := by
  have hd0 : 0 ≤ d := by simpa using hd x hx x hx
  have hpt : ∀ z, K.indicator (fun z => rieszKernel n m x z ^ q) z ≤
      (Metric.closedBall (0 : Fin n → ℝ) d).indicator
        (fun w => ‖w‖ₑ ^ (q * m) / ‖w‖ₑ ^ (q * n)) (x - z) := by
    intro z
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (mem_closedBall_zero_iff.2 (hd x hx z hz)),
        rieszKernel]
      refine le_of_eq ?_
      simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow, ← pow_mul, mul_comm m q, mul_comm n q]
    · rw [Set.indicator_of_notMem hz]; exact zero_le
  calc ∫⁻ z in K, rieszKernel n m x z ^ q
      = ∫⁻ z, K.indicator (fun z => rieszKernel n m x z ^ q) z := (lintegral_indicator hKm _).symm
    _ ≤ ∫⁻ z, (Metric.closedBall (0 : Fin n → ℝ) d).indicator
          (fun w => ‖w‖ₑ ^ (q * m) / ‖w‖ₑ ^ (q * n)) (x - z) := lintegral_mono hpt
    _ = ∫⁻ w, (Metric.closedBall (0 : Fin n → ℝ) d).indicator
          (fun w => ‖w‖ₑ ^ (q * m) / ‖w‖ₑ ^ (q * n)) w := lintegral_sub_left_eq_self _ x
    _ = rieszConst n (q * m) (q * n) d := by
        rw [lintegral_indicator measurableSet_closedBall]
        exact lintegral_closedBall_pow_div_pow hn hqm hq hd0

theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {F k : α → ℝ≥0∞} (hF : AEMeasurable F μ) (hk : AEMeasurable k μ) :
    (∫⁻ a, F a * k a ∂μ) ^ 2 ≤ (∫⁻ a, k a ∂μ) * ∫⁻ a, F a ^ 2 * k a ∂μ := by
  set g : α → ℝ≥0∞ := fun a => k a ^ (1 / 2 : ℝ)
  have hg : AEMeasurable g μ := hk.pow_const _
  have hsq : ∀ a, g a ^ (2 : ℝ) = k a := fun a => by
    rw [← ENNReal.rpow_mul]; norm_num
  have hfg : ∀ a, F a * k a = (F * g) a * g a := fun a => by
    simp only [Pi.mul_apply]
    rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two (hF.mul hg) hg
  simp only [Pi.mul_apply] at h
  rw [show (fun a => F a * k a) = fun a => F a * g a * g a from funext fun a => hfg a]
  have h1 : ∀ a, (F a * g a) ^ (2 : ℝ) = F a ^ 2 * k a := fun a => by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsq, ENNReal.rpow_two]
  simp_rw [h1, hsq] at h
  calc (∫⁻ a, F a * g a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, F a ^ 2 * k a ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, k a ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le h 2
    _ = (∫⁻ a, k a ∂μ) * ∫⁻ a, F a ^ 2 * k a ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num
        ring

end KernelIntegral

/-! ### `L²` Bramble–Hilbert and Sobolev embedding on a convex set -/

section ConvexSet

/-- The constant `dⁿ / (n k! |K|)` of the Riesz-potential bound. -/
def avgTaylorConst (n k : ℕ) (d : ℝ) (K : Set (Fin n → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (d ^ n / (n * k.factorial)) / volume K

theorem avgTaylorConst_ne_top {k : ℕ} {d : ℝ} {K : Set (Fin n → ℝ)} (hK0 : volume K ≠ 0) :
    avgTaylorConst n k d K ≠ ∞ :=
  ENNReal.div_ne_top ENNReal.ofReal_ne_top hK0

theorem measurable_indicator_enorm_iteratedFDeriv {K U : Set (Fin n → ℝ)} (hK : IsClosed K)
    (hU : IsOpen U) (hKU : K ⊆ U) {N : ℕ} {f : (Fin n → ℝ) → G} (hf : ContDiffOn ℝ N f U) :
    Measurable (K.indicator fun z => ‖iteratedFDeriv ℝ N f z‖ₑ) :=
  measurable_indicator_of_continuousOn hK (continuous_enorm.comp_continuousOn
    ((continuousOn_iteratedFDeriv_of_isOpen hU hf le_rfl).mono hKU))

/-- The `L²` Bramble–Hilbert lemma on a compact convex set `K`, `|K| > 0`:
`∫_K ‖f - Q_{k+1} f‖² ≤ C ∫_K ‖D^{k+1} f‖²` ([BrambleHilbert1970]; [Ciarlet2002], Thm 3.1.1). -/
theorem lintegral_sub_avgTaylorPoly_sq_le [CompleteSpace G] (hn : 0 < n) {K U : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKc : Convex ℝ K) (hK0 : volume K ≠ 0) (hU : IsOpen U) (hKU : K ⊆ U)
    {k : ℕ} {f : (Fin n → ℝ) → G} (hf : ContDiffOn ℝ (k + 1) f U) {d : ℝ}
    (hd : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ d) :
    ∫⁻ x in K, ‖f x - avgTaylorPoly K f (k + 1) x‖ₑ ^ 2 ≤
      (avgTaylorConst n k d K * rieszConst n (k + 1) n d) ^ 2 *
        ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ ^ 2 := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set A := avgTaylorConst n k d K
  set B := rieszConst n (k + 1) n d
  set F : (Fin n → ℝ) → ℝ≥0∞ := K.indicator fun z => ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ with hF_def
  have hFm : Measurable F := measurable_indicator_enorm_iteratedFDeriv hK.isClosed hU hKU
    (N := k + 1) (by exact_mod_cast hf)
  have hkm : ∀ x, Measurable fun z => rieszKernel n (k + 1) x z := fun x =>
    measurable_rieszKernel_right (k + 1) x
  have hB : ∀ x ∈ K, ∫⁻ z in K, rieszKernel n (k + 1) x z ≤ B := fun x hx => by
    have := lintegral_rieszKernel_pow_le hn hKm hd hx (m := k + 1) (q := 1) (by omega)
      (by omega)
    simp only [pow_one, one_mul] at this
    exact this
  have hFK : ∀ g : (Fin n → ℝ) → ℝ≥0∞, ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ * g z =
      ∫⁻ z in K, F z * g z := fun g =>
    setLIntegral_congr_fun hKm fun z hz => by rw [hF_def, Set.indicator_of_mem hz]
  have hpt : ∀ x ∈ K, ‖f x - avgTaylorPoly K f (k + 1) x‖ₑ ^ 2 ≤
      A ^ 2 * B * ∫⁻ z in K, F z ^ 2 * rieszKernel n (k + 1) x z := by
    intro x hx
    have h := enorm_sub_avgTaylorPoly_le_riesz hn hK hKc hK0 hU hKU hf hd hx
    rw [hFK] at h
    calc ‖f x - avgTaylorPoly K f (k + 1) x‖ₑ ^ 2
        ≤ (A * ∫⁻ z in K, F z * rieszKernel n (k + 1) x z) ^ 2 := pow_le_pow_left₀ zero_le h 2
      _ = A ^ 2 * (∫⁻ z in K, F z * rieszKernel n (k + 1) x z) ^ 2 := mul_pow _ _ _
      _ ≤ A ^ 2 * ((∫⁻ z in K, rieszKernel n (k + 1) x z) *
            ∫⁻ z in K, F z ^ 2 * rieszKernel n (k + 1) x z) :=
          mul_le_mul_right (lintegral_mul_sq_le _ hFm.aemeasurable (hkm x).aemeasurable) _
      _ ≤ A ^ 2 * (B * ∫⁻ z in K, F z ^ 2 * rieszKernel n (k + 1) x z) := by
          gcongr; exact hB x hx
      _ = _ := by ring
  have hAB : A ^ 2 * B ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (avgTaylorConst_ne_top hK0)) (rieszConst_ne_top _ _ _ _)
  have hjm : Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      F p.2 ^ 2 * rieszKernel n (k + 1) p.1 p.2 :=
    ((hFm.comp measurable_snd).pow_const 2).mul (measurable_rieszKernel (n := n) (k + 1))
  calc ∫⁻ x in K, ‖f x - avgTaylorPoly K f (k + 1) x‖ₑ ^ 2
      ≤ ∫⁻ x in K, A ^ 2 * B * ∫⁻ z in K, F z ^ 2 * rieszKernel n (k + 1) x z :=
        setLIntegral_mono' hKm hpt
    _ = A ^ 2 * B * ∫⁻ x in K, ∫⁻ z in K, F z ^ 2 * rieszKernel n (k + 1) x z :=
        lintegral_const_mul' _ _ hAB
    _ = A ^ 2 * B * ∫⁻ z in K, ∫⁻ x in K, F z ^ 2 * rieszKernel n (k + 1) x z := by
        rw [lintegral_lintegral_swap hjm.aemeasurable]
    _ = A ^ 2 * B * ∫⁻ z in K, F z ^ 2 * ∫⁻ x in K, rieszKernel n (k + 1) z x := by
        congr 1
        refine lintegral_congr fun z => ?_
        rw [← lintegral_const_mul _ (hkm z)]
        exact lintegral_congr fun x => by rw [rieszKernel_comm]
    _ ≤ A ^ 2 * B * ∫⁻ z in K, F z ^ 2 * B := by
        gcongr ?_ * ?_
        · exact le_rfl
        · exact setLIntegral_mono' hKm fun z hz => mul_le_mul_right (hB z hz) _
    _ = (A * B) ^ 2 * ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ ^ 2 := by
        rw [lintegral_mul_const' _ _ (rieszConst_ne_top _ _ _ _)]
        have : ∫⁻ z in K, F z ^ 2 = ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ ^ 2 :=
          setLIntegral_congr_fun hKm fun z hz => by rw [hF_def, Set.indicator_of_mem hz]
        rw [this]
        ring

/-- The Sobolev embedding for `2(k + 1) > n`, in a-priori form for `C^{k+1}` functions: on `K`,
`‖f - Q_{k+1} f‖ ≤ C (∫_K ‖D^{k+1} f‖²)^{1/2}` ([Evans2010], §5.6). -/
theorem enorm_sub_avgTaylorPoly_le_L2 [CompleteSpace G] (hn : 0 < n) {K U : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKc : Convex ℝ K) (hK0 : volume K ≠ 0) (hU : IsOpen U) (hKU : K ⊆ U)
    {k : ℕ} (hnk : n < 2 * (k + 1)) {f : (Fin n → ℝ) → G} (hf : ContDiffOn ℝ (k + 1) f U)
    {d : ℝ} (hd : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ d) {x : Fin n → ℝ} (hx : x ∈ K) :
    ‖f x - avgTaylorPoly K f (k + 1) x‖ₑ ≤
      avgTaylorConst n k d K * rieszConst n (2 * (k + 1)) (2 * n) d ^ (1 / 2 : ℝ) *
        (∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set F : (Fin n → ℝ) → ℝ≥0∞ := K.indicator fun z => ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ with hF_def
  have hFm : Measurable F := measurable_indicator_enorm_iteratedFDeriv hK.isClosed hU hKU
    (N := k + 1) (by exact_mod_cast hf)
  have hkm : Measurable fun z => rieszKernel n (k + 1) x z := measurable_rieszKernel_right _ x
  have h := enorm_sub_avgTaylorPoly_le_riesz hn hK hKc hK0 hU hKU hf hd hx
  have hFK : ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ * rieszKernel n (k + 1) x z =
      ∫⁻ z in K, (F * fun z => rieszKernel n (k + 1) x z) z :=
    setLIntegral_congr_fun hKm fun z hz => by
      simp only [Pi.mul_apply]; rw [hF_def, Set.indicator_of_mem hz]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict K) Real.HolderConjugate.two_two
    hFm.aemeasurable hkm.aemeasurable
  have hF2 : ∫⁻ z in K, F z ^ (2 : ℝ) = ∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ ^ 2 :=
    setLIntegral_congr_fun hKm fun z hz => by
      rw [hF_def, Set.indicator_of_mem hz, ENNReal.rpow_two]
  have hk2 : ∫⁻ z in K, rieszKernel n (k + 1) x z ^ (2 : ℝ) ≤
      rieszConst n (2 * (k + 1)) (2 * n) d := by
    simp_rw [ENNReal.rpow_two]
    exact lintegral_rieszKernel_pow_le hn hKm hd hx (m := k + 1) (q := 2) (by omega) (by omega)
  rw [hFK] at h
  refine h.trans ?_
  rw [hF2] at hH
  calc avgTaylorConst n k d K * ∫⁻ z in K, (F * fun z => rieszKernel n (k + 1) x z) z
      ≤ avgTaylorConst n k d K * ((∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ ^ 2) ^ (1 / 2 : ℝ) *
          (∫⁻ z in K, rieszKernel n (k + 1) x z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_right hH _
    _ ≤ avgTaylorConst n k d K * ((∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ ^ 2) ^ (1 / 2 : ℝ) *
          rieszConst n (2 * (k + 1)) (2 * n) d ^ (1 / 2 : ℝ)) := by
        gcongr
    _ = _ := by ring

theorem norm_iteratedFDeriv_iteratedFDeriv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (i j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (iteratedFDeriv ℝ j f) x‖ = ‖iteratedFDeriv ℝ (i + j) f x‖ := by
  induction j generalizing i with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      add_zero]
  | succ j ih =>
    have e : iteratedFDeriv ℝ (j + 1) f =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).symm ∘
          fderiv ℝ (iteratedFDeriv ℝ j f) := iteratedFDeriv_succ_eq_comp_left
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ)
      (F := E →L[ℝ] E [×j]→L[ℝ] F) (G := E [×(j + 1)]→L[ℝ] F), norm_iteratedFDeriv_fderiv, ih,
      Nat.add_right_comm, Nat.add_assoc]

theorem inv_mul_setLIntegral_le_sqrt {K : Set (Fin n → ℝ)} (hK0 : volume K ≠ 0)
    (hKt : volume K ≠ ∞) {g : (Fin n → ℝ) → ℝ≥0∞} (hg : AEMeasurable g (volume.restrict K)) :
    (volume K)⁻¹ * ∫⁻ z in K, g z ≤ (⨍⁻ z in K, g z ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
  set V := volume K
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict K) Real.HolderConjugate.two_two
    hg aemeasurable_const (g := fun _ => (1 : ℝ≥0∞))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul] at hH
  have hV : V⁻¹ = (V⁻¹) ^ (1 / 2 : ℝ) * (V⁻¹) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
  have hV1 : (V⁻¹) ^ (1 / 2 : ℝ) * V ^ (1 / 2 : ℝ) = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.inv_mul_cancel hK0 hKt,
      ENNReal.one_rpow]
  have hg2 : ∫⁻ z in K, g z ^ (2 : ℝ) = ∫⁻ z in K, g z ^ 2 := by simp_rw [ENNReal.rpow_two]
  rw [setLAverage_eq, ENNReal.div_eq_inv_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  calc V⁻¹ * ∫⁻ z in K, g z
      ≤ V⁻¹ * ((∫⁻ z in K, g z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * V ^ (1 / 2 : ℝ)) := by gcongr
    _ = (V⁻¹) ^ (1 / 2 : ℝ) * ((V⁻¹) ^ (1 / 2 : ℝ) * V ^ (1 / 2 : ℝ)) *
        (∫⁻ z in K, g z ^ 2) ^ (1 / 2 : ℝ) := by conv_lhs => rw [hV, hg2]
                                                 ring
    _ = _ := by rw [hV1, mul_one]

theorem enorm_avgTaylorPoly_le [CompleteSpace G] {K U : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hK0 : volume K ≠ 0) (hU : IsOpen U) (hKU : K ⊆ U) {m : ℕ} {f : (Fin n → ℝ) → G}
    (hf : ContDiffOn ℝ m f U) {d : ℝ} (hd : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ d) {x : Fin n → ℝ}
    (hx : x ∈ K) :
    ‖avgTaylorPoly K f m x‖ₑ ≤ ∑ i ∈ Finset.range m, ENNReal.ofReal (d ^ i / i.factorial) *
      (⨍⁻ z in K, ‖iteratedFDeriv ℝ i f z‖ₑ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hKt : volume K ≠ ∞ := hK.measure_lt_top.ne
  have hd0 : 0 ≤ d := by simpa using hd x hx x hx
  have hc : ∀ i ∈ Finset.range m, ContinuousOn (iteratedFDeriv ℝ i f) K := fun i hi =>
    (continuousOn_iteratedFDeriv_of_isOpen hU hf
      (by exact_mod_cast (Finset.mem_range.1 hi).le)).mono hKU
  set T : (Fin n → ℝ) → G := fun y => taylorPoly f y m x
  have hTc : ContinuousOn T K := by
    refine continuousOn_finsetSum _ fun i hi => ContinuousOn.const_smul ?_ _
    exact continuous_eval.comp_continuousOn ((hc i hi).prodMk (by fun_prop))
  have h1 : ‖avgTaylorPoly K f m x‖ₑ ≤ (volume K)⁻¹ * ∫⁻ y in K, ‖T y‖ₑ := by
    have hr : volume.real K ≠ 0 := by
      rw [measureReal_def]; exact ENNReal.toReal_ne_zero.2 ⟨hK0, hKt⟩
    rw [avgTaylorPoly, setAverage_eq, enorm_smul]
    gcongr
    · rw [Real.enorm_eq_ofReal (inv_nonneg.2 measureReal_nonneg), ENNReal.ofReal_inv_of_pos
        (lt_of_le_of_ne measureReal_nonneg (Ne.symm hr)), measureReal_def,
        ENNReal.ofReal_toReal hKt]
    · exact enorm_integral_le_lintegral_enorm _
  have h2 : ∀ y ∈ K, ‖T y‖ₑ ≤ ∑ i ∈ Finset.range m,
      ENNReal.ofReal (d ^ i / i.factorial) * ‖iteratedFDeriv ℝ i f y‖ₑ := by
    intro y hy
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have hL := (iteratedFDeriv ℝ i f y).le_opNorm (fun _ => x - y)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hL
    have hxy : ‖x - y‖ ^ i ≤ d ^ i := pow_le_pow_left₀ (norm_nonneg _) (hd x hx y hy) i
    calc (i.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ i f y (fun _ => x - y)‖
        ≤ (i.factorial : ℝ)⁻¹ * (‖iteratedFDeriv ℝ i f y‖ * d ^ i) := by
          gcongr
          exact hL.trans (mul_le_mul_of_nonneg_left hxy (norm_nonneg _))
      _ = _ := by ring
  have hm : ∀ i ∈ Finset.range m,
      AEMeasurable (fun z => ‖iteratedFDeriv ℝ i f z‖ₑ) (volume.restrict K) := fun i hi =>
    (continuous_enorm.comp_continuousOn (hc i hi)).aemeasurable hKm
  calc ‖avgTaylorPoly K f m x‖ₑ ≤ (volume K)⁻¹ * ∫⁻ y in K, ‖T y‖ₑ := h1
    _ ≤ (volume K)⁻¹ * ∫⁻ y in K, ∑ i ∈ Finset.range m,
          ENNReal.ofReal (d ^ i / i.factorial) * ‖iteratedFDeriv ℝ i f y‖ₑ := by
        exact mul_le_mul_right (setLIntegral_mono' hKm h2) _
    _ = ∑ i ∈ Finset.range m, ENNReal.ofReal (d ^ i / i.factorial) *
          ((volume K)⁻¹ * ∫⁻ y in K, ‖iteratedFDeriv ℝ i f y‖ₑ) := by
        rw [lintegral_finsetSum' _ fun i hi => (hm i hi).const_mul _, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]; ring
    _ ≤ _ := Finset.sum_le_sum fun i hi => by
        gcongr; exact inv_mul_setLIntegral_le_sqrt hK0 hKt (hm i hi)

theorem enorm_le_L2 [CompleteSpace G] (hn : 0 < n) {K U : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKc : Convex ℝ K) (hK0 : volume K ≠ 0) (hU : IsOpen U) (hKU : K ⊆ U)
    {k : ℕ} (hnk : n < 2 * (k + 1)) {f : (Fin n → ℝ) → G} (hf : ContDiffOn ℝ (k + 1) f U)
    {d : ℝ} (hd : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ d) {x : Fin n → ℝ} (hx : x ∈ K) :
    ‖f x‖ₑ ≤ ∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (d ^ i / i.factorial) *
        (⨍⁻ z in K, ‖iteratedFDeriv ℝ i f z‖ₑ ^ 2 ∂volume) ^ (1 / 2 : ℝ) +
      avgTaylorConst n k d K * rieszConst n (2 * (k + 1)) (2 * n) d ^ (1 / 2 : ℝ) *
        (∫⁻ z in K, ‖iteratedFDeriv ℝ (k + 1) f z‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  calc ‖f x‖ₑ = ‖avgTaylorPoly K f (k + 1) x + (f x - avgTaylorPoly K f (k + 1) x)‖ₑ := by
        rw [add_sub_cancel]
    _ ≤ _ := (enorm_add_le _ _).trans (add_le_add (enorm_avgTaylorPoly_le hK hK0 hU hKU hf hd hx)
        (enorm_sub_avgTaylorPoly_le_L2 hn hK hKc hK0 hU hKU hnk hf hd hx))

end ConvexSet

/-! ### The reference simplex: interpolation error in `L²` -/

section RefSimplex

open Feec.Mesh

theorem setLIntegral_enorm_sq_lt_top {E : Type*} [NormedAddCommGroup E] {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) {g : (Fin n → ℝ) → E} (hg : ContinuousOn g K) :
    ∫⁻ x in K, ‖g x‖ₑ ^ 2 < ∞ := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hg
  calc ∫⁻ x in K, ‖g x‖ₑ ^ 2 ≤ ∫⁻ _x in K, ENNReal.ofReal M ^ 2 :=
        setLIntegral_mono' hK.isClosed.measurableSet fun x hx => pow_le_pow_left₀ zero_le
          (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hM x hx)) 2
    _ = ENNReal.ofReal M ^ 2 * volume K := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hK.measure_lt_top

theorem volume_closedInterior_ne_zero (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    volume T.closedInterior ≠ 0 :=
  (isOpen_interior.measure_pos volume (interior_closedInterior_nonempty T)).ne'.symm ∘
    fun h => le_antisymm ((measure_mono interior_subset).trans h.le) zero_le |>.symm

/-- The constant `|T̂| (1 + C)² (avgTaylorConst)² C₂` of the reference `L²` estimate. -/
def refL2Const (n s : ℕ) (C : ℝ) : ℝ≥0∞ :=
  volume (Feec.Mesh.refSimplex n).closedInterior * ENNReal.ofReal (1 + C) ^ 2 *
    (avgTaylorConst n s 1 (Feec.Mesh.refSimplex n).closedInterior ^ 2 *
      rieszConst n (2 * (s + 1)) (2 * n) 1)

theorem refL2Const_ne_top (n s : ℕ) (C : ℝ) : refL2Const n s C ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (Feec.Mesh.refSimplex n).isCompact_closedInterior.measure_lt_top.ne
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (avgTaylorConst_ne_top (volume_closedInterior_ne_zero _)))
      (rieszConst_ne_top _ _ _ _))

/-- If `2(s + 1) > n`, a reference interpolant stable in `C⁰(T̂)` and reproducing `P_s` satisfies
`∫_{T̂} ‖f - I f‖² ≤ K ∫_{T̂} ‖D^{s+1} f‖²` ([Ciarlet2002], Thm 3.1.4, Sobolev form). -/
theorem IsRefInterpolant.lintegral_sub_sq_le_L2 [CompleteSpace G] (hn : 0 < n) {s : ℕ}
    (hns : n < 2 * (s + 1)) {I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G} {C : ℝ} (hC : 0 ≤ C)
    (hI : IsRefInterpolant n s 0 G I C) {f : (Fin n → ℝ) → G} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hTU : (Feec.Mesh.refSimplex n).closedInterior ⊆ U)
    (hf : ContDiffOn ℝ (s + 1) f U) :
    ∫⁻ x in (Feec.Mesh.refSimplex n).closedInterior, ‖f x - I f x‖ₑ ^ 2 ≤
      refL2Const n s C * ∫⁻ x in (Feec.Mesh.refSimplex n).closedInterior,
        ‖iteratedFDeriv ℝ (s + 1) f x‖ₑ ^ 2 := by
  set K := (Feec.Mesh.refSimplex n).closedInterior with hK_def
  have hK : IsCompact K := (Feec.Mesh.refSimplex n).isCompact_closedInterior
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hK0 : volume K ≠ 0 := volume_closedInterior_ne_zero _
  have hd : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ 1 := fun x hx y hy =>
    norm_sub_le_one_of_mem_refSimplex hx hy
  set p := avgTaylorPoly K f (s + 1) with hp_def
  have hp : p ∈ polyFunctions n s G :=
    avgTaylorPoly_mem_polyFunctions hK hU hTU (hf.of_le (by exact_mod_cast Nat.le_succ s))
  have hpc : ContDiffOn ℝ (s + 1) p U := (contDiff_of_mem_polyFunctions hp).contDiffOn
  set J := ∫⁻ x in K, ‖iteratedFDeriv ℝ (s + 1) f x‖ₑ ^ 2
  have hJ : J ≠ ∞ := (setLIntegral_enorm_sq_lt_top hK
    ((continuousOn_iteratedFDeriv_of_isOpen hU (N := s + 1) (by exact_mod_cast hf)
      le_rfl).mono hTU)).ne
  set A := avgTaylorConst n s 1 K
  set B := rieszConst n (2 * (s + 1)) (2 * n) 1
  set S := A * B ^ (1 / 2 : ℝ) * J ^ (1 / 2 : ℝ)
  have hS : S ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (avgTaylorConst_ne_top hK0)
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (rieszConst_ne_top _ _ _ _)))
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hJ)
  have hsob : ∀ y ∈ K, ‖f y - p y‖ ≤ S.toReal := fun y hy => by
    have h := enorm_sub_avgTaylorPoly_le_L2 hn hK (convex_closedInterior _) hK0 hU hTU hns hf hd hy
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_le_iff_le_toReal hS).1 h
  have hpt : ∀ x ∈ K, ‖f x - I f x‖ ≤ (1 + C) * S.toReal := by
    intro x hx
    have hsub := hI.map_sub U hU hTU f p hf hpc x hx
    rw [hI.apply_eq p hp x hx] at hsub
    have hstab := hI.norm_le U hU hTU (f - p) (hf.sub hpc) (fun _ => S.toReal)
      (fun j hj y hy => by
        obtain rfl : j = 0 := Nat.le_zero.1 hj
        rw [norm_iteratedFDeriv_zero]; exact hsob y hy) x hx
    rw [Finset.sum_range_one] at hstab
    have : f x - I f x = (f x - p x) - I (f - p) x := by rw [hsub]; abel
    rw [this]
    calc ‖f x - p x - I (f - p) x‖ ≤ ‖f x - p x‖ + ‖I (f - p) x‖ := _root_.norm_sub_le _ _
      _ ≤ S.toReal + C * S.toReal := add_le_add (hsob x hx) hstab
      _ = (1 + C) * S.toReal := by ring
  calc ∫⁻ x in K, ‖f x - I f x‖ₑ ^ 2 ≤ ∫⁻ _x in K, ENNReal.ofReal ((1 + C) * S.toReal) ^ 2 :=
        setLIntegral_mono' hKm fun x hx => pow_le_pow_left₀ zero_le
          (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hpt x hx)) 2
    _ = volume K * ENNReal.ofReal (1 + C) ^ 2 * S ^ 2 := by
        rw [setLIntegral_const, ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_toReal hS]
        ring
    _ = refL2Const n s C * J := by
        have hS2 : S ^ 2 = A ^ 2 * B * J := by
          simp only [S, mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
        rw [hS2, refL2Const]
        ring

end RefSimplex

/-! ### Transport to a physical simplex -/

section Transport

open Feec.Mesh

theorem lintegral_sub_transportInterp_sq_le_L2 [CompleteSpace G] (hn : 0 < n) {s : ℕ}
    (hns : n < 2 * (s + 1)) {I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G} {C : ℝ} (hC : 0 ≤ C)
    (hI : IsRefInterpolant n s 0 G I C) (T : Affine.Simplex ℝ (Fin n → ℝ) n) (Φ : G ≃L[ℝ] G)
    {u : (Fin n → ℝ) → G} {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hTU : T.closedInterior ⊆ U)
    (hu : ContDiffOn ℝ (s + 1) u U) :
    ∫⁻ x in T.closedInterior, ‖u x - transportInterp T Φ I u x‖ₑ ^ 2 ≤
      ENNReal.ofReal ((‖(Φ.symm : G →L[ℝ] G)‖ * (‖(Φ : G →L[ℝ] G)‖ *
        ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (s + 1))) ^ 2) * refL2Const n s C *
        ∫⁻ x in T.closedInterior, ‖iteratedFDeriv ℝ (s + 1) u x‖ₑ ^ 2 := by
  set a := ‖(Φ.symm : G →L[ℝ] G)‖
  set b := ‖(Φ : G →L[ℝ] G)‖ * ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (s + 1)
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := by positivity
  set û := refPullback T Φ u
  have hmem : ∀ y ∈ (Feec.Mesh.refSimplex n).closedInterior, T.refMap y ∈ T.closedInterior :=
    fun y hy => by rw [T.closedInterior_eq_image_refMap]; exact mem_image_of_mem _ hy
  have hTU' : (Feec.Mesh.refSimplex n).closedInterior ⊆ T.refMap ⁻¹' U := fun y hy =>
    hTU (hmem y hy)
  have hU' : IsOpen (T.refMap ⁻¹' U) := hU.preimage (contDiff_refMap T (N := 0)).continuous
  have href := hI.lintegral_sub_sq_le_L2 hn hns hC hU' hTU' (contDiffOn_refPullback T Φ hu)
  have hpt : ∀ y, ‖u (T.refMap y) - transportInterp T Φ I u (T.refMap y)‖ₑ ^ 2 ≤
      ENNReal.ofReal (a ^ 2) * ‖û y - I û y‖ₑ ^ 2 := by
    intro y
    have he : u (T.refMap y) - transportInterp T Φ I u (T.refMap y) = Φ.symm (û y - I û y) := by
      simp [transportInterp, û, refPullback, map_sub]
    rw [he, ENNReal.ofReal_pow ha, ← mul_pow]
    refine pow_le_pow_left₀ zero_le ?_ 2
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul ha]
    exact ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm (Φ.symm : G →L[ℝ] G) _)
  have hD : ∀ y, ‖iteratedFDeriv ℝ (s + 1) û y‖ₑ ^ 2 ≤
      ENNReal.ofReal (b ^ 2) * ‖iteratedFDeriv ℝ (s + 1) u (T.refMap y)‖ₑ ^ 2 := by
    intro y
    rw [ENNReal.ofReal_pow hb, ← mul_pow]
    refine pow_le_pow_left₀ zero_le ?_ 2
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hb]
    exact ENNReal.ofReal_le_ofReal (norm_iteratedFDeriv_refPullback_le T Φ u _ y)
  set D := ENNReal.ofReal |LinearMap.det T.linearPart|
  calc ∫⁻ x in T.closedInterior, ‖u x - transportInterp T Φ I u x‖ₑ ^ 2
      = D * ∫⁻ y in (Feec.Mesh.refSimplex n).closedInterior,
          ‖u (T.refMap y) - transportInterp T Φ I u (T.refMap y)‖ₑ ^ 2 :=
        lintegral_closedInterior_eq T _
    _ ≤ D * ∫⁻ y in (Feec.Mesh.refSimplex n).closedInterior,
          ENNReal.ofReal (a ^ 2) * ‖û y - I û y‖ₑ ^ 2 := by
        gcongr with y; exact hpt y
    _ = D * (ENNReal.ofReal (a ^ 2) * ∫⁻ y in (Feec.Mesh.refSimplex n).closedInterior,
          ‖û y - I û y‖ₑ ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ D * (ENNReal.ofReal (a ^ 2) * (refL2Const n s C *
          ∫⁻ y in (Feec.Mesh.refSimplex n).closedInterior,
            ‖iteratedFDeriv ℝ (s + 1) û y‖ₑ ^ 2)) := by
        gcongr
    _ ≤ D * (ENNReal.ofReal (a ^ 2) * (refL2Const n s C *
          ∫⁻ y in (Feec.Mesh.refSimplex n).closedInterior,
            ENNReal.ofReal (b ^ 2) * ‖iteratedFDeriv ℝ (s + 1) u (T.refMap y)‖ₑ ^ 2)) := by
        gcongr with y; exact hD y
    _ = ENNReal.ofReal ((a * b) ^ 2) * refL2Const n s C * (D *
          ∫⁻ y in (Feec.Mesh.refSimplex n).closedInterior,
            ‖iteratedFDeriv ℝ (s + 1) u (T.refMap y)‖ₑ ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_pow a b 2,
          ENNReal.ofReal_mul (sq_nonneg a)]
        ring
    _ = _ := by
        rw [lintegral_closedInterior_eq T (fun x => ‖iteratedFDeriv ℝ (s + 1) u x‖ₑ ^ 2)]

theorem lintegral_sub_transportInterp_sq_le_L2_of_isShapeRegular [CompleteSpace G] (hn : 0 < n)
    {s : ℕ} (hns : n < 2 * (s + 1)) {I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G} {C : ℝ}
    (hC : 0 ≤ C) (hI : IsRefInterpolant n s 0 G I C) {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}
    {C₀ c : ℝ} (hS : IsShapeRegular S C₀ c) {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ S)
    (Φ : G ≃L[ℝ] G) {A : ℝ} {k : ℕ}
    (hΦ : ‖(Φ : G →L[ℝ] G)‖ ≤ A * ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ k)
    (hΦs : ‖(Φ.symm : G →L[ℝ] G)‖ ≤
      A * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ k)
    {u : (Fin n → ℝ) → G} {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hTU : T.closedInterior ⊆ U)
    (hu : ContDiffOn ℝ (s + 1) u U) :
    ∫⁻ x in T.closedInterior, ‖u x - transportInterp T Φ I u x‖ₑ ^ 2 ≤
      ENNReal.ofReal ((A ^ 2 * C₀ ^ (2 * k) * (C₀ * diam T) ^ (s + 1)) ^ 2) * refL2Const n s C *
        ∫⁻ x in T.closedInterior, ‖iteratedFDeriv ℝ (s + 1) u x‖ₑ ^ 2 := by
  refine (lintegral_sub_transportInterp_sq_le_L2 hn hns hC hI T Φ hU hTU hu).trans ?_
  refine mul_le_mul_left (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _) _
  obtain ⟨hB, -, -⟩ := hS T hT
  have hΦΦ := norm_symm_mul_norm_le_of_isShapeRegular hS hT Φ hΦ hΦs
  have h0 : 0 ≤ ‖(Φ.symm : G →L[ℝ] G)‖ * (‖(Φ : G →L[ℝ] G)‖ *
      ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (s + 1)) := by positivity
  refine pow_le_pow_left₀ h0 ?_ 2
  rw [← mul_assoc]
  exact mul_le_mul hΦΦ (pow_le_pow_left₀ (norm_nonneg _) hB _) (by positivity)
    ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hΦΦ)

end Transport

/-! ### Differential forms on homothetic simplices -/

section Forms

open Feec.Mesh ExteriorFibre

variable {r k : ℕ}

theorem formL2Sq_le_card_mul_lintegral {S : Set (Fin n → ℝ)} {u : FormField n}
    (hfin : ∫⁻ x in S, ‖u x‖ₑ ^ 2 ≠ ∞) :
    formL2Sq S u ≤ Fintype.card (Finset (Fin n)) * (∫⁻ x in S, ‖u x‖ₑ ^ 2).toReal := by
  have h1 : ∀ t : Finset (Fin n), ∫ x in S, (u x t) ^ 2 ≤ (∫⁻ x in S, ‖u x‖ₑ ^ 2).toReal := by
    intro t
    by_cases hi : Integrable (fun x => (u x t) ^ 2) (volume.restrict S)
    · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
        hi.aestronglyMeasurable]
      refine ENNReal.toReal_mono hfin (lintegral_mono fun x => ?_)
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hle : |u x t| ≤ ‖u x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm (u x) t
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    · rw [integral_undef hi]; exact ENNReal.toReal_nonneg
  calc formL2Sq S u = ∑ t, ∫ x in S, (u x t) ^ 2 := rfl
    _ ≤ ∑ _t : Finset (Fin n), (∫⁻ x in S, ‖u x‖ₑ ^ 2).toReal := Finset.sum_le_sum fun t _ => h1 t
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem integral_norm_sq_eq_toReal_lintegral {E : Type*} [NormedAddCommGroup E]
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) {g : (Fin n → ℝ) → E} (hg : ContinuousOn g S) :
    ∫ x in S, ‖g x‖ ^ 2 = (∫⁻ x in S, ‖g x‖ₑ ^ 2).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
    ((hg.norm.pow 2).aestronglyMeasurable hS)]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The constant `(‖Φ_K⁻¹‖ ‖Φ_K‖ ‖B_K‖^{s+1})²` of `K` with the fibre map `Φ_K = B_K^*`. -/
def formTransportConst (K : Affine.Simplex ℝ (Fin n → ℝ) n) (s : ℕ) : ℝ :=
  (‖((fibrePullbackEquiv K.points (isUnit_det_edgeMatrix K)).symm :
      (Finset (Fin n) → ℝ) →L[ℝ] (Finset (Fin n) → ℝ))‖ *
    (‖(fibrePullbackEquiv K.points (isUnit_det_edgeMatrix K) :
      (Finset (Fin n) → ℝ) →L[ℝ] (Finset (Fin n) → ℝ))‖ *
      ‖(K.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (s + 1))) ^ 2

theorem formL2Sq_sub_le_of_transportInterp_eq (K : Affine.Simplex ℝ (Fin n → ℝ) n) (hn : 0 < n)
    {s : ℕ} (hns : n < 2 * (s + 1)) {I : FormField n → FormField n} {CI : ℝ} (hCI : 0 ≤ CI)
    (hI : IsRefInterpolant n s 0 (Finset (Fin n) → ℝ) I CI) {h : ℝ} (hh : 0 < h)
    (t : Fin n → ℝ) {w P : FormField n} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hTU : (mapEquiv (boxMap t h hh.ne') K).closedInterior ⊆ U) (hw : ContDiffOn ℝ (s + 1) w U)
    (hP : ∀ x, transportInterp (mapEquiv (boxMap t h hh.ne') K)
      (fibrePullbackEquiv K.points (isUnit_det_edgeMatrix K)) I w x = P x) :
    formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior (w - P) ≤
      Fintype.card (Finset (Fin n)) * formTransportConst K s * (refL2Const n s CI).toReal *
        h ^ (2 * (s + 1)) * ∫ y in (mapEquiv (boxMap t h hh.ne') K).closedInterior,
          ‖iteratedFDeriv ℝ (s + 1) w y‖ ^ 2 := by
  set T := mapEquiv (boxMap t h hh.ne') K
  set Φ := fibrePullbackEquiv K.points (isUnit_det_edgeMatrix K)
  have hL := lintegral_sub_transportInterp_sq_le_L2 hn hns hCI hI T Φ hU hTU hw
  rw [norm_linearEquiv_mapEquiv_boxMap K t hh] at hL
  simp_rw [hP] at hL
  have hTc : IsCompact T.closedInterior := T.isCompact_closedInterior
  have hTm : MeasurableSet T.closedInterior := hTc.isClosed.measurableSet
  have hDc : ContinuousOn (iteratedFDeriv ℝ (s + 1) w) T.closedInterior :=
    (continuousOn_iteratedFDeriv_of_isOpen hU (N := s + 1) (by exact_mod_cast hw) le_rfl).mono hTU
  have hJ := (setLIntegral_enorm_sq_lt_top hTc hDc).ne
  have hc : (‖(Φ.symm : (Finset (Fin n) → ℝ) →L[ℝ] (Finset (Fin n) → ℝ))‖ *
      (‖(Φ : (Finset (Fin n) → ℝ) →L[ℝ] (Finset (Fin n) → ℝ))‖ *
        (h * ‖(K.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖) ^ (s + 1))) ^ 2 =
      formTransportConst K s * h ^ (2 * (s + 1)) := by
    simp only [formTransportConst, Φ]; ring
  rw [hc] at hL
  have hfin : ∫⁻ x in T.closedInterior, ‖(w - P) x‖ₑ ^ 2 ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (refL2Const_ne_top _ _ _)) hJ) (by simpa only [Pi.sub_apply] using hL)
  have hnn : 0 ≤ formTransportConst K s * h ^ (2 * (s + 1)) := by
    unfold formTransportConst; positivity
  calc formL2Sq T.closedInterior (w - P)
      ≤ Fintype.card (Finset (Fin n)) * (∫⁻ x in T.closedInterior, ‖(w - P) x‖ₑ ^ 2).toReal :=
        formL2Sq_le_card_mul_lintegral hfin
    _ ≤ Fintype.card (Finset (Fin n)) * (ENNReal.ofReal (formTransportConst K s *
          h ^ (2 * (s + 1))) * refL2Const n s CI * ∫⁻ x in T.closedInterior,
            ‖iteratedFDeriv ℝ (s + 1) w x‖ₑ ^ 2).toReal := by
        gcongr
        · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (refL2Const_ne_top _ _ _)) hJ
        · simpa only [Pi.sub_apply] using hL
    _ = _ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn,
          ← integral_norm_sq_eq_toReal_lintegral hTm hDc]
        ring

/-- The `L²(T)` error of `Π_T` for `P_rΛᵏ` on `T = t + h K`, `s ≤ r`, `2(s + 1) > n`:
`‖w - Π_T w‖²_{L²(T)} ≤ C h^{2(s+1)} ∫_T ‖D^{s+1} w‖²`, `C` independent of `h`, `t`, `w`. -/
theorem exists_formL2Sq_sub_polyInterp_le_L2 (K : Affine.Simplex ℝ (Fin n → ℝ) n) (hn : 0 < n)
    (hr : 1 ≤ r) (hk : k ≤ n) {s : ℕ} (hs : s ≤ r) (hns : n < 2 * (s + 1)) :
    ∃ C, 0 ≤ C ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {w : FormField n} (hwc : Continuous w)
      (hwk : ∀ x, IsDeg k (w x)) {U : Set (Fin n → ℝ)}, IsOpen U →
      (mapEquiv (boxMap t h hh.ne') K).closedInterior ⊆ U → ContDiffOn ℝ (s + 1) w U →
      formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior
        (w - (polyInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) hr hk
          ⟨w, mem_contDegForms hwc hwk⟩ : FormField n)) ≤
        C * h ^ (2 * (s + 1)) * ∫ y in (mapEquiv (boxMap t h hh.ne') K).closedInterior,
          ‖iteratedFDeriv ℝ (s + 1) w y‖ ^ 2 := by
  obtain ⟨CI, hCI0, hI⟩ := exists_isRefInterpolant_polyRefInterp (n := n) hr hs
  refine ⟨Fintype.card (Finset (Fin n)) * formTransportConst K s * (refL2Const n s CI).toReal,
    by unfold formTransportConst; positivity, fun {h} hh t w hwc hwk U hU hTU hw => ?_⟩
  exact formL2Sq_sub_le_of_transportInterp_eq K hn hns hCI0 hI hh t hU hTU hw
    (transportInterp_polyRefInterp_eq K hr hk hh t hwc hwk)

/-- The `L²(T)` error of `Π_T` for `P_r⁻Λᵏ` on `T = t + h K`, `s + 1 ≤ r`, `2(s + 1) > n`:
`‖w - Π_T w‖²_{L²(T)} ≤ C h^{2(s+1)} ∫_T ‖D^{s+1} w‖²`, `C` independent of `h`, `t`, `w`. -/
theorem exists_formL2Sq_sub_polyMinusInterp_le_L2 (K : Affine.Simplex ℝ (Fin n → ℝ) n)
    (hn : 0 < n) (hr : 1 ≤ r) (hk : k ≤ n) {s : ℕ} (hs : s + 1 ≤ r) (hns : n < 2 * (s + 1)) :
    ∃ C, 0 ≤ C ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {w : FormField n} (hwc : Continuous w)
      (hwk : ∀ x, IsDeg k (w x)) {U : Set (Fin n → ℝ)}, IsOpen U →
      (mapEquiv (boxMap t h hh.ne') K).closedInterior ⊆ U → ContDiffOn ℝ (s + 1) w U →
      formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior
        (w - (polyMinusInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) hr hk
          ⟨w, mem_contDegForms hwc hwk⟩ : FormField n)) ≤
        C * h ^ (2 * (s + 1)) * ∫ y in (mapEquiv (boxMap t h hh.ne') K).closedInterior,
          ‖iteratedFDeriv ℝ (s + 1) w y‖ ^ 2 := by
  obtain ⟨CI, hCI0, hI⟩ := exists_isRefInterpolant_polyMinusRefInterp (n := n) hr hs
  refine ⟨Fintype.card (Finset (Fin n)) * formTransportConst K s * (refL2Const n s CI).toReal,
    by unfold formTransportConst; positivity, fun {h} hh t w hwc hwk U hU hTU hw => ?_⟩
  exact formL2Sq_sub_le_of_transportInterp_eq K hn hns hCI0 hI hh t hU hTU hw
    (transportInterp_polyMinusRefInterp_eq K hr hk hh t hwc hwk)

end Forms

end Feec.FiniteElement
