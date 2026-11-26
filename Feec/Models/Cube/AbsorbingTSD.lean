module

public import Feec.Models.Cube.Absorbing

/-!
# The TSD constraint under absorbing boundary conditions on the cube

Under the absorbing boundary condition, the TSD constraint `K = L²(TSD) × L²(TSD)` propagates on the
domain of dependence but is not invariant.

## Main results

* `absorbingSemigroup_symTF_depDomain`: for TSD data, `S(t) u₀` is symmetric and trace-free a.e.
  on `depDomain Q t`.
* `not_invariant_tsdPair`: `K` is not invariant under the absorbing semigroup.
* `exists_inner_absorbing_neg`: some `u ∈ D(A)` has `⟪A u, u⟫ < 0`.
-/

open scoped InnerProductSpace ContDiff
open Set MeasureTheory Filter Topology Feec.Domain Feec.Models.BoundedDomain

@[expose] public noncomputable section

namespace Feec.Models.Cube.Absorbing

open Geometry

/-! ### Test pairs and the interior equations -/

/-- The triple of a test field, as an element of the energy space (zero boundary trace). -/
def testTriple {Φ : Ix → R3 → ℝ} (hΦ : IsTestField (Q (Fin 3)) Φ) : EnergySpace :=
  ⟨_, triple_mem_energySpace (C1Field.ofTest hΦ)⟩

@[simp] theorem fieldMap_testTriple {Φ : Ix → R3 → ℝ} (hΦ : IsTestField (Q (Fin 3)) Φ) :
    fieldMap (testTriple hΦ) = testField hΦ := rfl

@[simp] theorem curlMap_testTriple {Φ : Ix → R3 → ℝ} (hΦ : IsTestField (Q (Fin 3)) Φ) :
    curlMap (testTriple hΦ) = (C1Field.ofTest hΦ).curlL2 := rfl

@[simp] theorem traceMap_testTriple {Φ : Ix → R3 → ℝ} (hΦ : IsTestField (Q (Fin 3)) Φ) :
    traceMap (testTriple hΦ) = 0 := C1Field.ofTest_tan hΦ

theorem inner_absorbing_fst (u : absorbing.domain) {Φ : Ix → R3 → ℝ}
    (hΦ : IsTestField (Q (Fin 3)) Φ) :
    ⟪(absorbing u).fst, testField hΦ⟫_ℝ =
      -⟪(u : State).snd, (C1Field.ofTest hΦ).curlL2⟫_ℝ := by
  have h := impedanceTriple.isWeak_witness u (testTriple hΦ)
  change ⟪(absorbing u).fst, fieldMap (testTriple hΦ)⟫_ℝ = _ at h
  rw [fieldMap_testTriple] at h
  rw [h]
  change -⟪(u : State).snd, curlMap (testTriple hΦ)⟫_ℝ -
    ⟪impedanceTriple.γ (impedanceTriple.witness u), traceMap (testTriple hΦ)⟫_ℝ = _
  rw [traceMap_testTriple, inner_zero_right, sub_zero, curlMap_testTriple]

theorem inner_absorbing_snd (u : absorbing.domain) {Φ : Ix → R3 → ℝ}
    (hΦ : IsTestField (Q (Fin 3)) Φ) :
    ⟪(absorbing u).snd, testField hΦ⟫_ℝ = ⟪(u : State).fst, (C1Field.ofTest hΦ).curlL2⟫_ℝ := by
  have hc : (absorbing u).snd = curlMap (impedanceTriple.witness u) :=
    (impedanceTriple.c_witness u).symm
  have hι : (u : State).fst = fieldMap (impedanceTriple.witness u) :=
    (impedanceTriple.ι_witness u).symm
  rw [hc, inner_curlMap_testField, hι]

theorem generator_absorbingSemigroup : absorbingSemigroup.generator = absorbing :=
  isMDissipative_absorbing.generator_semigroup

theorem integral_mem_domain (u₀ : State) {t : ℝ} (ht : 0 ≤ t) :
    ∃ h : (∫ s in (0 : ℝ)..t, absorbingSemigroup.S s u₀) ∈ absorbing.domain,
      absorbing ⟨_, h⟩ = absorbingSemigroup.S t u₀ - u₀ := by
  have hg := absorbingSemigroup.integral_mem_graph_S ht u₀
  rw [generator_absorbingSemigroup] at hg
  exact LinearPMap.mem_graph_iff_exists.1 hg

theorem intervalIntegrable_S (u₀ : State) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => absorbingSemigroup.S s u₀) volume 0 t :=
  ((absorbingSemigroup.strongCont u₀).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht

theorem inner_integral_eq (u₀ : State) {t : ℝ} (ht : 0 ≤ t) (L : State →L[ℝ] ℝ) :
    L (∫ s in (0 : ℝ)..t, absorbingSemigroup.S s u₀) =
      ∫ s in (0 : ℝ)..t, L (absorbingSemigroup.S s u₀) :=
  (L.intervalIntegral_comp_comm (intervalIntegrable_S u₀ ht)).symm

theorem inner_fst_absorbingSemigroup (u₀ : State) {Φ : Ix → R3 → ℝ}
    (hΦ : IsTestField (Q (Fin 3)) Φ) {t : ℝ} (ht : 0 ≤ t) :
    ⟪(absorbingSemigroup.S t u₀).fst, testField hΦ⟫_ℝ = ⟪u₀.fst, testField hΦ⟫_ℝ -
      ∫ s in (0 : ℝ)..t, ⟪(absorbingSemigroup.S s u₀).snd, (C1Field.ofTest hΦ).curlL2⟫_ℝ := by
  obtain ⟨hdom, hval⟩ := integral_mem_domain u₀ ht
  have h := inner_absorbing_fst ⟨_, hdom⟩ hΦ
  rw [hval] at h
  have e := inner_integral_eq u₀ ht
    ((innerSL ℝ (C1Field.ofTest hΦ).curlL2).comp (WithLp.sndL 2 ℝ MQ MQ))
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, WithLp.sndL_apply] at e
  have e' : ⟪(∫ s in (0 : ℝ)..t, absorbingSemigroup.S s u₀).snd, (C1Field.ofTest hΦ).curlL2⟫_ℝ =
      ∫ s in (0 : ℝ)..t, ⟪(absorbingSemigroup.S s u₀).snd, (C1Field.ofTest hΦ).curlL2⟫_ℝ := by
    rw [real_inner_comm, e]
    exact intervalIntegral.integral_congr fun s _ => real_inner_comm _ _
  have hs : (absorbingSemigroup.S t u₀ - u₀).fst = (absorbingSemigroup.S t u₀).fst - u₀.fst := rfl
  rw [hs, inner_sub_left] at h
  change _ = -⟪(∫ s in (0 : ℝ)..t, absorbingSemigroup.S s u₀).snd, _⟫_ℝ at h
  linarith

theorem inner_snd_absorbingSemigroup (u₀ : State) {Φ : Ix → R3 → ℝ}
    (hΦ : IsTestField (Q (Fin 3)) Φ) {t : ℝ} (ht : 0 ≤ t) :
    ⟪(absorbingSemigroup.S t u₀).snd, testField hΦ⟫_ℝ = ⟪u₀.snd, testField hΦ⟫_ℝ +
      ∫ s in (0 : ℝ)..t, ⟪(absorbingSemigroup.S s u₀).fst, (C1Field.ofTest hΦ).curlL2⟫_ℝ := by
  obtain ⟨hdom, hval⟩ := integral_mem_domain u₀ ht
  have h := inner_absorbing_snd ⟨_, hdom⟩ hΦ
  rw [hval] at h
  have e := inner_integral_eq u₀ ht
    ((innerSL ℝ (C1Field.ofTest hΦ).curlL2).comp (WithLp.fstL 2 ℝ MQ MQ))
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, WithLp.fstL_apply] at e
  have e' : ⟪(∫ s in (0 : ℝ)..t, absorbingSemigroup.S s u₀).fst, (C1Field.ofTest hΦ).curlL2⟫_ℝ =
      ∫ s in (0 : ℝ)..t, ⟪(absorbingSemigroup.S s u₀).fst, (C1Field.ofTest hΦ).curlL2⟫_ℝ := by
    rw [real_inner_comm, e]
    exact intervalIntegral.integral_congr fun s _ => real_inner_comm _ _
  have hs : (absorbingSemigroup.S t u₀ - u₀).snd = (absorbingSemigroup.S t u₀).snd - u₀.snd := rfl
  rw [hs, inner_sub_left] at h
  change _ = ⟪(∫ s in (0 : ℝ)..t, absorbingSemigroup.S s u₀).fst, _⟫_ℝ at h
  linarith

/-! ### Integral forms of the pairings -/

theorem inner_l2_eq (u : MQ) (Ψ : C1Field) :
    ⟪u, Ψ.l2⟫_ℝ = ∑ ij, ∫ x in Q (Fin 3), u ij x * Ψ.1 ij x := by
  rw [L2F.inner_def]
  exact Finset.sum_congr rfl fun ij _ =>
    inner_cL2_right measurableSet_Q isBounded_Q _ (Ψ.continuous ij)

theorem inner_curlL2_eq (u : MQ) (Ψ : C1Field) :
    ⟪u, Ψ.curlL2⟫_ℝ = ∑ ij, ∫ x in Q (Fin 3), u ij x * curlM Ψ.1 ij x := by
  rw [L2F.inner_def]
  exact Finset.sum_congr rfl fun ij _ =>
    inner_cL2_right measurableSet_Q isBounded_Q _ (continuous_curlM Ψ.2 ij)

theorem inner_testField_eq_sum (u : MQ) {Φ : Ix → R3 → ℝ} (hΦ : IsTestField (Q (Fin 3)) Φ) :
    ⟪u, testField hΦ⟫_ℝ = ∑ ij, ∫ x in Q (Fin 3), u ij x * Φ ij x := by
  rw [inner_testField]; simp

theorem memLp_Q {f : R3 → ℝ} (hf : Continuous f) : MemLp f 2 (volume.restrict (Q (Fin 3))) :=
  memLp_of_continuous measurableSet_Q isBounded_Q hf

/-! ### The skew test field `Ψ_f = skewOf (f e₀)` and the normal–normal functional -/

/-- `Ψ_f = skewOf (f, 0, 0)`: `Ψ_{2,1} = f`, `Ψ_{1,2} = -f`. -/
def skewE0 (f : R3 → ℝ) : Ix → R3 → ℝ := skewOf fun i => if i = 0 then f else 0

theorem contDiff_skewE0 {n : WithTop ℕ∞} {f : R3 → ℝ} (hf : ContDiff ℝ n f) (jk : Ix) :
    ContDiff ℝ n (skewE0 f jk) :=
  contDiff_skewOf (fun i => by split_ifs; exacts [hf, contDiff_const]) jk

theorem isTestField_skewE0 {f : R3 → ℝ} (hf : IsTest (Q (Fin 3)) f) :
    IsTestField (Q (Fin 3)) (skewE0 f) :=
  isTestField_skewOf fun i => by split_ifs; exacts [hf, IsTest.zero]

theorem curlM_skewE0 {f : R3 → ℝ} (hf : Differentiable ℝ f) (jk : Ix) (x : R3) :
    curlM (skewE0 f) jk x =
      (if jk.1 = jk.2 then partialDeriv 0 f x else 0) -
        (if jk.2 = 0 then partialDeriv jk.1 f x else 0) := by
  rw [skewE0, curlM_skewOf (fun i => by split_ifs; exacts [hf, differentiable_const 0])]
  simp [pd_ite_zero]

/-- **The normal–normal functional** `λ_f(E) = Σⱼ ∫_Q E_{0j} ∂ⱼ f = ⟪E₀, ∇f⟫`. -/
def normalNormalFun (f : R3 → ℝ) (E : MQ) : ℝ :=
  ∑ j : Fin 3, ∫ x in Q (Fin 3), E (0, j) x * partialDeriv j f x

theorem normalNormalFun_eq_neg_inner_curl {E : MQ} (hsym : ∀ i j, E (i, j) = E (j, i))
    (htr : ∑ i, E (i, i) = 0) {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) :
    normalNormalFun f E =
      -∑ jk, ∫ x in Q (Fin 3), E jk x * curlM (skewE0 f) jk x := by
  have hd := hf.differentiable one_ne_zero
  have hp : ∀ j, Continuous (partialDeriv j f) := fun j => hf.continuous_partialDeriv j
  have hint : ∀ jk (g : R3 → ℝ), Continuous g →
      Integrable (fun x => E jk x * g x) (volume.restrict (Q (Fin 3))) :=
    fun jk g hg => integrable_mul _ (memLp_Q hg)
  simp only [curlM_skewE0 hd, mul_sub]
  rw [Finset.sum_congr rfl fun jk _ => integral_sub (hint jk _ (by
      split_ifs; exacts [hp 0, continuous_const])) (hint jk _ (by
      split_ifs; exacts [hp _, continuous_const]))]
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ jk : Ix, ∫ x in Q (Fin 3),
      E jk x * (if jk.1 = jk.2 then partialDeriv 0 f x else 0) = 0 := by
    simp only [mul_ite, mul_zero, integral_ite_zero, Fintype.sum_prod_type, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    simp only [fun u : L2 ℝ (Q (Fin 3)) => integral_mul_eq_inner u (memLp_Q (hp 0)), ← sum_inner,
      htr, inner_zero_left]
  have h2 : ∑ jk : Ix, ∫ x in Q (Fin 3), E jk x * (if jk.2 = 0 then partialDeriv jk.1 f x else 0) =
      normalNormalFun f E := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (0 : Fin 3) (fun b _ hb => by simp [hb]) (by simp)]
    simp only [ite_true]
    rw [hsym a 0]
  rw [h1, h2, zero_sub, neg_neg]

theorem curlMap_two_one {v : EnergySpace} (hv : fieldMap v ∈ tsd (Q (Fin 3))) :
    curlMap v (2, 1) = curlMap v (1, 2) := by
  rw [← sub_eq_zero]
  refine L2.eq_zero_of_forall_inner_toL2 isOpen_Q _ fun χ hχ => ?_
  have hψ : IsTestField (Q (Fin 3)) fun i : Fin 3 => if i = 0 then χ else 0 :=
    fun i => by dsimp only; split_ifs; exacts [hχ, IsTest.zero]
  have hΨ := isTestField_skewE0 hχ
  have h0 := sum_integral_mul_curlM_skewOf_eq_zero hv hψ
  have e1 : ⟪curlMap v, testField hΨ⟫_ℝ =
      ∑ ij, ∫ x in Q (Fin 3), fieldMap v ij x * curlM (skewE0 χ) ij x := by
    rw [inner_curlMap_testField, inner_curlL2_eq]; rfl
  have e2 : ∑ jk, ∫ x in Q (Fin 3), fieldMap v jk x * curlM (skewE0 χ) jk x = 0 := h0
  rw [e2, inner_testField_eq_sum] at e1
  rw [inner_sub_left, inner_toL2, inner_toL2]
  simp only [RCLike.conj_to_real]
  have : ∑ ij : Ix, ∫ x in Q (Fin 3), curlMap v ij x * skewE0 χ ij x =
      (∫ x in Q (Fin 3), curlMap v (2, 1) x * χ x) -
        ∫ x in Q (Fin 3), curlMap v (1, 2) x * χ x := by
    simp only [skewE0, skewOf, Fintype.sum_prod_type, Fin.sum_univ_three]
    simp
    rw [integral_neg]; ring
  rw [← this]
  exact e1

theorem inner_curlMap_skewE0 {v : EnergySpace} (hv : fieldMap v ∈ tsd (Q (Fin 3))) {f : R3 → ℝ}
    (hf : ContDiff ℝ 1 f) :
    ⟪curlMap v, C1Field.l2 ⟨skewE0 f, contDiff_skewE0 hf⟩⟫_ℝ = 0 := by
  rw [inner_l2_eq]
  have h21 : (v : Amb).snd.fst (2, 1) = (v : Amb).snd.fst (1, 2) := curlMap_two_one hv
  simp only [skewE0, skewOf, Fintype.sum_prod_type, Fin.sum_univ_three]
  simp
  rw [h21, integral_neg]; ring

/-! ### The diagonal test field `Θ_f = f (e₁ ⊗ e₁ + e₂ ⊗ e₂)` -/

/-- `Θ_f`: `Θ₁₁ = Θ₂₂ = f`, other entries `0`. -/
def diagPair (f : R3 → ℝ) (ij : Ix) : R3 → ℝ := if ij = (1, 1) ∨ ij = (2, 2) then f else 0

theorem contDiff_diagPair {n : WithTop ℕ∞} {f : R3 → ℝ} (hf : ContDiff ℝ n f) (ij : Ix) :
    ContDiff ℝ n (diagPair f ij) := by
  unfold diagPair; split_ifs; exacts [hf, contDiff_const]

theorem isTestField_diagPair {f : R3 → ℝ} (hf : IsTest (Q (Fin 3)) f) :
    IsTestField (Q (Fin 3)) (diagPair f) := fun ij => by
  unfold diagPair; split_ifs; exacts [hf, IsTest.zero]

theorem curlM_diagPair (f : R3 → ℝ) (jk : Ix) (x : R3) :
    curlM (diagPair f) jk x =
      if jk = (1, 0) then -partialDeriv 2 f x else if jk = (1, 2) then partialDeriv 0 f x else
      if jk = (2, 0) then partialDeriv 1 f x else
      if jk = (2, 1) then -partialDeriv 0 f x else 0 := by
  obtain ⟨j, k⟩ := jk
  simp only [curlM, diagPair, pd_ite_zero]
  fin_cases j <;> fin_cases k <;> simp

theorem sum_integral_curlM_diagPair {B : MQ} (hB : B (1, 2) = B (2, 1)) {f : R3 → ℝ}
    (hf : ContDiff ℝ 1 f) :
    ∑ jk, ∫ x in Q (Fin 3), B jk x * curlM (diagPair f) jk x =
      -(∫ x in Q (Fin 3), B (1, 0) x * partialDeriv 2 f x) + ∫ x in Q (Fin 3),
        B (2, 0) x * partialDeriv 1 f x := by
  have hp : ∀ j, Continuous (partialDeriv j f) := fun j => hf.continuous_partialDeriv j
  simp only [curlM_diagPair, Fintype.sum_prod_type, Fin.sum_univ_three]
  simp only [Prod.mk.injEq, mul_ite, mul_zero, mul_neg]
  simp
  rw [hB, integral_neg, integral_neg]
  ring

/-! ### The weak equation of the absorbing condition on symmetric `B` -/

/-- A smooth cutoff `ρ_k` with values in `[0, 1]`, supported in `[1/(k+4), ½ - 1/(k+4)]`. -/
def cutoff (k : ℕ) (t : ℝ) : ℝ :=
  Real.smoothTransition ((k + 4) * t - 1) * Real.smoothTransition ((k + 4) * (1 / 2 - t) - 1)

theorem contDiff_cutoff (k : ℕ) : ContDiff ℝ ∞ (cutoff k) := by
  unfold cutoff
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem cutoff_nonneg (k : ℕ) (t : ℝ) : 0 ≤ cutoff k t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem cutoff_le_one (k : ℕ) (t : ℝ) : cutoff k t ≤ 1 := by
  unfold cutoff
  calc _ ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
        (Real.smoothTransition.nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem cutoff_eq_zero_of_le (k : ℕ) {t : ℝ} (h : t ≤ 1 / (k + 4) ∨ 1 / 2 - 1 / (k + 4) ≤ t) :
    cutoff k t = 0 := by
  have hk : (0 : ℝ) < k + 4 := by positivity
  unfold cutoff
  rcases h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
    rw [le_div_iff₀ hk] at h; linarith
  · rw [Real.smoothTransition.zero_of_nonpos (x := (k + 4) * (1 / 2 - t) - 1), mul_zero]
    have : 1 / 2 - t ≤ 1 / (k + 4) := by linarith
    rw [le_div_iff₀ hk] at this; linarith

theorem tendsto_cutoff {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) :
    Tendsto (fun k : ℕ => cutoff k t) atTop (𝓝 1) := by
  have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 4) * t - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((tendsto_natCast_atTop_atTop.atTop_add
      tendsto_const_nhds).atTop_mul_const ht.1)
  have h2 : Tendsto (fun k : ℕ => ((k : ℝ) + 4) * (1 / 2 - t) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((tendsto_natCast_atTop_atTop.atTop_add
      tendsto_const_nhds).atTop_mul_const (by linarith [ht.2]))
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [h1.eventually_ge_atTop 1, h2.eventually_ge_atTop 1] with k hk1 hk2
  rw [cutoff, Real.smoothTransition.one_of_one_le hk1, Real.smoothTransition.one_of_one_le hk2,
    mul_one]

/-! ### Test fields localized at the face `{x₀ = ½}` -/

/-- `φ_ψ = faceExt 0 true ψ`: `ψ(x₁, x₂) · 2 x₀`, equal to `ψ` on `{x₀ = ½}`. -/
abbrev faceFun (ψ : (Fin 2 → ℝ) → ℝ) : R3 → ℝ := faceExt 0 true ψ

theorem contDiff_faceFun {ψ : (Fin 2 → ℝ) → ℝ} (hψ : IsTest Sq ψ) : ContDiff ℝ ∞ (faceFun ψ) :=
  contDiff_faceExt 0 true hψ.contDiff

theorem faceFun_faceMap_of_ne {ψ : (Fin 2 → ℝ) → ℝ} (hψ : IsTest Sq ψ) {f : Face}
    (hf : f ≠ (0, true)) (y : Fin 2 → ℝ) : faceFun ψ (faceMap f y) = 0 := by
  rw [faceFun, faceExt_faceMap 0 true (φ := ψ) (fun y hy => hψ.eq_zero_of_notMem hy) f y,
    ite_eq_right hf]

theorem faceFun_faceMap_self {ψ : (Fin 2 → ℝ) → ℝ} (hψ : IsTest Sq ψ) (y : Fin 2 → ℝ) :
    faceFun ψ (faceMap (0, true) y) = ψ y := by
  rw [faceFun, faceExt_faceMap 0 true (φ := ψ) (fun y hy => hψ.eq_zero_of_notMem hy) _ y,
    ite_eq_left rfl]

/-- `φ_ψ` cut off near the faces `{x₀ = 0}`, `{x₀ = ½}`: for `ψ` a test function on `Sq`, a test
function on `Q`. -/
def faceFunCut (ψ : (Fin 2 → ℝ) → ℝ) (k : ℕ) (x : R3) : ℝ := faceFun ψ x * cutoff k (x 0)

theorem contDiff_faceFunCut {ψ : (Fin 2 → ℝ) → ℝ} (hψ : IsTest Sq ψ) (k : ℕ) :
    ContDiff ℝ ∞ (faceFunCut ψ k) :=
  (contDiff_faceFun hψ).mul ((contDiff_cutoff k).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).contDiff)

theorem isTest_faceFunCut {ψ : (Fin 2 → ℝ) → ℝ} (hψ : IsTest Sq ψ) (k : ℕ) :
    IsTest (Q (Fin 3)) (faceFunCut ψ k) := by
  set a : ℝ := 1 / (k + 4)
  set b : ℝ := 1 / 2 - 1 / (k + 4)
  have hk : (0 : ℝ) < k + 4 := by positivity
  have ha : 0 < a := by positivity
  have hb : b < 1 / 2 := by
    have : 0 < 1 / ((k : ℝ) + 4) := by positivity
    simp only [b]; linarith
  set S : Set R3 := (fun p : ℝ × (Fin 2 → ℝ) => Fin.insertNth 0 p.1 p.2) ''
    (Icc a b ×ˢ tsupport ψ)
  have hS : IsCompact S := (isCompact_Icc.prod hψ.hasCompactSupport.isCompact).image
    (Continuous.finInsertNth 0 continuous_fst continuous_snd)
  have hsupp : Function.support (faceFunCut ψ k) ⊆ S := by
    intro x hx
    have h1 : ψ (Fin.removeNth 0 x) ≠ 0 := fun h => hx (by
      simp only [faceFunCut, faceFun, faceExt, h, zero_mul])
    have h2 : cutoff k (x 0) ≠ 0 := fun h => hx (by simp only [faceFunCut, h, mul_zero])
    refine ⟨(x 0, Fin.removeNth 0 x), ⟨⟨?_, ?_⟩, subset_tsupport _ h1⟩, ?_⟩
    · by_contra h; exact h2 (cutoff_eq_zero_of_le k (Or.inl (le_of_lt (not_le.1 h))))
    · by_contra h; exact h2 (cutoff_eq_zero_of_le k (Or.inr (le_of_lt (not_le.1 h))))
    · simp
  have hts : tsupport (faceFunCut ψ k) ⊆ S := closure_minimal hsupp hS.isClosed
  refine ⟨contDiff_faceFunCut hψ k, hS.of_isClosed_subset isClosed_closure hts, hts.trans ?_⟩
  rintro _ ⟨⟨t, y⟩, ⟨ht, hy⟩, rfl⟩
  rw [mem_Q]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.insertNth_apply_same]
    exact ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  · show Fin.insertNth (α := fun _ : Fin 3 => ℝ) 0 t y ((0 : Fin 3).succAbove j) ∈ _
    rw [Fin.insertNth_apply_succAbove]
    exact mem_Q.1 (hψ.tsupport_subset hy) j

theorem pd_faceFunCut {ψ : (Fin 2 → ℝ) → ℝ} (hψ : IsTest Sq ψ) (k : ℕ) {j : Fin 3} (hj : j ≠ 0)
    (x : R3) : partialDeriv j (faceFunCut ψ k) x =
      partialDeriv j (faceFun ψ) x * cutoff k (x 0) := by
  have hc : Differentiable ℝ fun x : R3 => cutoff k (x 0) :=
    ((contDiff_cutoff k).differentiable (by simp)).comp (differentiable_apply 0)
  have hpc : partialDeriv j (fun x : R3 => cutoff k (x 0)) x = 0 := by
    have h1 : HasFDerivAt (cutoff k)
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv (cutoff k) (x 0))) (x 0) :=
      (((contDiff_cutoff k).differentiable (by simp)) (x 0)).hasDerivAt.hasFDerivAt
    have hd := h1.comp x (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 x)
    rw [partialDeriv, show (fun x : R3 => cutoff k (x 0)) = cutoff k ∘ (fun f : R3 => f 0) from rfl,
      hd.fderiv]
    simp [hj.symm]
  have h := partialDeriv_mul ((contDiff_faceFun hψ).differentiable (by simp) x) (hc x) j
  unfold faceFunCut
  rw [h, hpc, mul_zero, add_zero]

theorem tendsto_integral_cutoff (g : L2 ℝ (Q (Fin 3))) {h : R3 → ℝ} (hh : Continuous h) :
    Tendsto (fun k : ℕ => ∫ x in Q (Fin 3), g x * (h x * cutoff k (x 0))) atTop
      (𝓝 (∫ x in Q (Fin 3), g x * h x)) := by
  have hint := integrable_mul g (memLp_Q hh)
  refine tendsto_integral_of_dominated_convergence (fun x => ‖g x * h x‖) (fun k => ?_)
    hint.norm (fun k => Eventually.of_forall fun x => ?_) ?_
  · exact (Lp.aestronglyMeasurable g).mul ((hh.mul (((contDiff_cutoff k).continuous).comp
      (continuous_apply 0))).aestronglyMeasurable)
  · rw [norm_mul, norm_mul, norm_mul, ← mul_assoc]
    refine mul_le_of_le_one_right (by positivity) ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _ _)]
    exact cutoff_le_one _ _
  · filter_upwards [ae_restrict_mem measurableSet_Q] with x hx
    have := (tendsto_cutoff (mem_Q.1 hx 0)).const_mul (g x * h x)
    simp only [mul_one] at this
    exact this.congr fun k => by ring

/-! ### The obstruction -/

/-- **`L²(TSD) × L²(TSD)`**, the TSD constraint for `(E, B)` (no boundary condition). -/
def tsdPair : Submodule ℝ State where
  carrier := {u | u.fst ∈ tsd (Q (Fin 3)) ∧ u.snd ∈ tsd (Q (Fin 3))}
  add_mem' := fun ha hb => ⟨(tsd _).add_mem ha.1 hb.1, (tsd _).add_mem ha.2 hb.2⟩
  zero_mem' := ⟨(tsd _).zero_mem, (tsd _).zero_mem⟩
  smul_mem' := fun c _ h => ⟨(tsd _).smul_mem c h.1, (tsd _).smul_mem c h.2⟩

theorem isClosed_tsdPair : IsClosed (tsdPair : Set State) :=
  (isClosed_tsd.preimage (WithLp.fstL 2 ℝ MQ MQ).continuous).inter
    (isClosed_tsd.preimage (WithLp.sndL 2 ℝ MQ MQ).continuous)

theorem hasDerivWithinAt_of_eq_add_integral {f g : ℝ → ℝ} {T : ℝ} (hg : ContinuousOn g (Ici 0))
    (hf : ∀ s ∈ Icc 0 T, f s = f 0 + ∫ σ in (0 : ℝ)..s, g σ) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt f (g t) (Icc 0 T) t := by
  intro t ht
  set g' : ℝ → ℝ := fun σ => g (max σ 0)
  have hg' : Continuous g' :=
    hg.comp_continuous (continuous_id.max continuous_const) fun σ => le_max_right σ 0
  have hd : HasDerivAt (fun s => f 0 + ∫ σ in (0 : ℝ)..s, g' σ) (g' t) t :=
    ((hg'.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add _
  have he : g' t = g t := by simp [g', max_eq_left ht.1]
  rw [he] at hd
  refine hd.hasDerivWithinAt.congr_of_mem (fun s hs => ?_) ht
  rw [hf s hs]
  congr 1
  refine intervalIntegral.integral_congr fun σ hσ => ?_
  rw [uIcc_of_le hs.1] at hσ
  simp [g', max_eq_left hσ.1]

/-- **The orbits of the absorbing semigroup are weak solutions** in `Q`, for TSD data. -/
theorem weakEB_absorbingSemigroup {u₀ : State} (hu₀ : u₀ ∈ tsdPair) (T : ℝ) :
    WeakEB (Q (Fin 3)) T (fun t => (absorbingSemigroup.S t u₀).fst)
      (fun t => (absorbingSemigroup.S t u₀).snd) := by
  have hc : ContinuousOn (fun t => absorbingSemigroup.S t u₀) (Icc 0 T) :=
    (absorbingSemigroup.strongCont u₀).mono Icc_subset_Ici_self
  have hci : ContinuousOn (fun t => absorbingSemigroup.S t u₀) (Ici 0) :=
    absorbingSemigroup.strongCont u₀
  refine ⟨(WithLp.fstL 2 ℝ MQ MQ).continuous.comp_continuousOn hc,
    (WithLp.sndL 2 ℝ MQ MQ).continuous.comp_continuousOn hc, fun φ hφ => ?_, fun φ hφ => ?_,
    fun t ht Φ hΦ => ?_, fun t ht Φ hΦ => ?_⟩
  · simp only [C0Semigroup.S_zero_apply]
    rw [← inner_grad_testField _ hφ]; exact hu₀.1.2.2 φ hφ
  · simp only [C0Semigroup.S_zero_apply]
    rw [← inner_grad_testField _ hφ]; exact hu₀.2.2.2 φ hφ
  · refine hasDerivWithinAt_of_eq_add_integral
      (g := fun σ => -∑ ij, ∫ x in Q (Fin 3), (absorbingSemigroup.S σ u₀).snd ij x *
        curlM Φ ij x) ?_ (fun s hs => ?_) t ht
    · have : ContinuousOn (fun σ => -⟪(absorbingSemigroup.S σ u₀).snd,
          (C1Field.ofTest hΦ).curlL2⟫_ℝ) (Ici 0) :=
        (((WithLp.sndL 2 ℝ MQ MQ).continuous.comp_continuousOn hci).inner
          continuousOn_const).neg
      refine this.congr fun σ _ => ?_
      simp only [inner_curlL2_eq]; rfl
    · have h := inner_fst_absorbingSemigroup u₀ hΦ hs.1
      simp only [inner_testField_eq_sum, inner_curlL2_eq, C0Semigroup.S_zero_apply] at h ⊢
      rw [h, intervalIntegral.integral_neg, sub_eq_add_neg]
      rfl
  · refine hasDerivWithinAt_of_eq_add_integral
      (g := fun σ => ∑ ij, ∫ x in Q (Fin 3), (absorbingSemigroup.S σ u₀).fst ij x *
        curlM Φ ij x) ?_ (fun s hs => ?_) t ht
    · have : ContinuousOn (fun σ => ⟪(absorbingSemigroup.S σ u₀).fst,
          (C1Field.ofTest hΦ).curlL2⟫_ℝ) (Ici 0) :=
        ((WithLp.fstL 2 ℝ MQ MQ).continuous.comp_continuousOn hci).inner continuousOn_const
      refine this.congr fun σ _ => ?_
      simp only [inner_curlL2_eq]; rfl
    · have h := inner_snd_absorbingSemigroup u₀ hΦ hs.1
      simp only [inner_testField_eq_sum, inner_curlL2_eq, C0Semigroup.S_zero_apply] at h ⊢
      rw [h]
      rfl

theorem absorbingSemigroup_divFree {u₀ : State} (hu₀ : u₀ ∈ tsdPair) {t : ℝ} (ht : 0 ≤ t)
    (φ : Fin 3 → R3 → ℝ) (hφ : IsTestField (Q (Fin 3)) φ) :
    (∑ ij : Ix, ∫ x in Q (Fin 3), (absorbingSemigroup.S t u₀).fst ij x *
      partialDeriv ij.2 (φ ij.1) x = 0) ∧
    ∑ ij : Ix, ∫ x in Q (Fin 3), (absorbingSemigroup.S t u₀).snd ij x *
      partialDeriv ij.2 (φ ij.1) x = 0 :=
  ⟨(weakEB_absorbingSemigroup hu₀ t).divE t ⟨ht, le_rfl⟩ φ hφ,
    (weakEB_absorbingSemigroup hu₀ t).divB t ⟨ht, le_rfl⟩ φ hφ⟩

/-- **TSD propagates in the domain of dependence**: for TSD data, `S(t) u₀` is symmetric and
trace-free a.e. on `depDomain Q t`. -/
theorem absorbingSemigroup_symTF_depDomain {u₀ : State} (hu₀ : u₀ ∈ tsdPair) {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ᵐ y ∂volume.restrict (depDomain (Q (Fin 3)) t),
      SymTF (absorbingSemigroup.S t u₀).fst y ∧ SymTF (absorbingSemigroup.S t u₀).snd y := by
  have h := weakEB_absorbingSemigroup hu₀ t
  have h0 : viol (absorbingSemigroup.S 0 u₀).fst (absorbingSemigroup.S 0 u₀).snd = 0 := by
    simp only [C0Semigroup.S_zero_apply]; exact viol_eq_zero_of_mem_tsd hu₀.1 hu₀.2
  exact h.ae_symTF_depDomain isOpen_Q h0 ⟨ht, le_rfl⟩

/-! ### The absorbing condition on symmetric `B` forces `∮ (E₁₁ + E₂₂) φ = 0` -/

/-- The `C¹` field `Θ_φ` for `φ = φ_ψ`. -/
def diagC1 {ψ : (Fin 2 → ℝ) → ℝ} (hψ : IsTest Sq ψ) : C1Field :=
  ⟨diagPair (faceFun ψ), fun ij => (contDiff_diagPair (contDiff_faceFun hψ) ij).of_le (by simp)⟩

/-- The `C¹` field `Ψ_φ = skewOf (φ, 0, 0)` for `φ = φ_ψ`. -/
def skewC1 {ψ : (Fin 2 → ℝ) → ℝ} (hψ : IsTest Sq ψ) : C1Field :=
  ⟨skewE0 (faceFun ψ), fun ij => (contDiff_skewE0 (contDiff_faceFun hψ) ij).of_le (by simp)⟩

theorem sum_integral_diagPair (w : MQ) (f : R3 → ℝ) :
    ∑ ij, ∫ x in Q (Fin 3), w ij x * diagPair f ij x =
      (∫ x in Q (Fin 3), w (1, 1) x * f x) + ∫ x in Q (Fin 3), w (2, 2) x * f x := by
  simp only [diagPair, Fintype.sum_prod_type, Fin.sum_univ_three]
  simp

theorem inner_trace_diagC1_eq_zero (u : absorbing.domain)
    (hB : (u : State).snd (1, 2) = (u : State).snd (2, 1)) {ψ : (Fin 2 → ℝ) → ℝ}
    (hψ : IsTest Sq ψ) : ⟪impedanceTriple.trace u, (diagC1 hψ).tan⟫_ℝ = 0 := by
  set w := (absorbing u).fst
  set B := (u : State).snd
  set φ := faceFun ψ
  have hφ : ContDiff ℝ 1 φ := (contDiff_faceFun hψ).of_le (by simp)
  have hp1 : Continuous (partialDeriv 1 φ) := hφ.continuous_partialDeriv 1
  have hp2 : Continuous (partialDeriv 2 φ) := hφ.continuous_partialDeriv 2
  -- the identity for the cut-off fields
  have hk : ∀ k : ℕ, (∫ x in Q (Fin 3), w (1, 1) x * (φ x * cutoff k (x 0))) +
      ∫ x in Q (Fin 3), w (2, 2) x * (φ x * cutoff k (x 0)) =
      (∫ x in Q (Fin 3), B (1, 0) x * (partialDeriv 2 φ x * cutoff k (x 0))) -
        ∫ x in Q (Fin 3), B (2, 0) x * (partialDeriv 1 φ x * cutoff k (x 0)) := by
    intro k
    have hfk := isTest_faceFunCut hψ k
    have hfk1 : ContDiff ℝ 1 (faceFunCut ψ k) := (contDiff_faceFunCut hψ k).of_le (by simp)
    have h := inner_absorbing_fst u (isTestField_diagPair hfk)
    rw [inner_testField_eq_sum, inner_curlL2_eq] at h
    change ∑ ij, ∫ x in Q (Fin 3), w ij x * diagPair (faceFunCut ψ k) ij x =
      -∑ ij, ∫ x in Q (Fin 3), B ij x * curlM (diagPair (faceFunCut ψ k)) ij x at h
    rw [sum_integral_diagPair, sum_integral_curlM_diagPair hB hfk1] at h
    simp only [pd_faceFunCut hψ k (by decide : (2 : Fin 3) ≠ 0),
      pd_faceFunCut hψ k (by decide : (1 : Fin 3) ≠ 0)] at h
    simp only [faceFunCut] at h
    linarith
  -- the limit
  have hlim := tendsto_nhds_unique
    (((tendsto_integral_cutoff (w (1, 1)) (contDiff_faceFun hψ).continuous).add
      (tendsto_integral_cutoff (w (2, 2)) (contDiff_faceFun hψ).continuous)).congr fun k =>
        (hk k))
    ((tendsto_integral_cutoff (B (1, 0)) hp2).sub (tendsto_integral_cutoff (B (2, 0)) hp1))
  -- the weak equation for `Θ_φ`
  have hw := impedanceTriple.isWeak_witness u ⟨_, triple_mem_energySpace (diagC1 hψ)⟩
  change ⟪w, (diagC1 hψ).l2⟫_ℝ = -⟪B, (diagC1 hψ).curlL2⟫_ℝ -
    ⟪impedanceTriple.trace u, (diagC1 hψ).tan⟫_ℝ at hw
  rw [inner_l2_eq, inner_curlL2_eq] at hw
  change ∑ ij, ∫ x in Q (Fin 3), w ij x * diagPair φ ij x =
    (-∑ ij, ∫ x in Q (Fin 3), B ij x * curlM (diagPair φ) ij x) -
      ⟪impedanceTriple.trace u, (diagC1 hψ).tan⟫_ℝ at hw
  rw [sum_integral_diagPair, sum_integral_curlM_diagPair hB hφ] at hw
  linarith

theorem flux_skewC1 {ψ : (Fin 2 → ℝ) → ℝ} (hψ : IsTest Sq ψ) :
    (skewC1 hψ).flux = -(diagC1 hψ).tan := by
  ext1 b
  rw [C1Field.flux, C1Field.tan, fluxTrace_apply, PiLp.neg_apply, tanTrace_apply]
  have hfun : fluxFun (skewE0 (faceFun ψ)) b = fun y => -tanFun (diagPair (faceFun ψ)) b y := by
    funext y
    obtain ⟨⟨m, s⟩, i, j'⟩ := b
    by_cases hf : (m, s) = (0, true)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hf
      simp only [fluxFun, tanFun, fluxVal, tanDir, faceSign, skewE0, skewOf, diagPair]
      fin_cases i <;> fin_cases j' <;> simp [Fin.succAbove]
    · have h0 := faceFun_faceMap_of_ne hψ hf y
      simp only [fluxFun, tanFun, fluxVal, skewE0, skewOf, diagPair]
      split_ifs <;> simp [h0]
  rw [show cL2 measurableSet_Q isBounded_Q (continuous_fluxFun (skewC1 hψ).continuous b) =
      cL2 measurableSet_Q isBounded_Q
        ((continuous_tanFun (diagC1 hψ).continuous b).neg) from by
    unfold cL2; congr 1]
  exact MemLp.toLp_neg _

/-- **The normal–normal component of `E` vanishes on `{x₀ = ½}`** for TSD states of `D(A)`. -/
theorem normalNormal_eq_zero (u : absorbing.domain) (hu : (u : State) ∈ tsdPair)
    {ψ : (Fin 2 → ℝ) → ℝ} (hψ : IsTest Sq ψ) :
    normalNormalFun (faceFun ψ) (u : State).fst = 0 := by
  set v := impedanceTriple.witness u
  have hE : fieldMap v = (u : State).fst := impedanceTriple.ι_witness u
  have hEt : fieldMap v ∈ tsd (Q (Fin 3)) := hE ▸ hu.1
  obtain ⟨hsym, htr, -⟩ := hu.1
  have hφ : ContDiff ℝ 1 (faceFun ψ) := (contDiff_faceFun hψ).of_le (by simp)
  rw [normalNormalFun_eq_neg_inner_curl hsym htr hφ]
  have hg := green_energySpace v (skewC1 hψ)
  rw [show (skewC1 hψ) = ⟨skewE0 (faceFun ψ), contDiff_skewE0 hφ⟩ from rfl,
    inner_curlMap_skewE0 hEt hφ, ← show (skewC1 hψ) = ⟨skewE0 (faceFun ψ), contDiff_skewE0 hφ⟩
      from rfl, zero_sub, inner_curlL2_eq, hE] at hg
  change -(∑ jk, ∫ x in Q (Fin 3), (u : State).fst jk x * curlM (skewE0 (faceFun ψ)) jk x) =
    ⟪impedanceTriple.trace u, (skewC1 hψ).flux⟫_ℝ at hg
  rw [hg, flux_skewC1, inner_neg_right, inner_trace_diagC1_eq_zero u
    (hu.2.1 1 2) hψ, neg_zero]

/-! ### A TSD state with nonzero normal–normal component -/

/-- The diagonal of `diag(1, -½, -½)`. -/
def constTSDCoeff (ij : Ix) : ℝ :=
  if ij = (0, 0) then 1 else if ij = (1, 1) ∨ ij = (2, 2) then -1 / 2 else 0

/-- The constant TSD field `diag(1, -½, -½)` on `Q`. -/
def constTSD : MQ := cField (Φ := fun ij _ => constTSDCoeff ij) fun _ => continuous_const

theorem coeFn_cL2 {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) :
    (cL2 hΩ hb hf : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict Ω] f :=
  MemLp.coeFn_toLp _

theorem integral_constTSD_mul (ij : Ix) (g : R3 → ℝ) :
    ∫ x in Q (Fin 3), constTSD ij x * g x = constTSDCoeff ij * ∫ x in Q (Fin 3), g x := by
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_cL2 measurableSet_Q isBounded_Q (continuous_const (y := constTSDCoeff ij))]
    with x hx
  simp only [constTSD, cField_apply]
  rw [hx]

theorem integral_pd_eq_zero {g : R3 → ℝ} (hg : IsTest (Q (Fin 3)) g) (i : Fin 3) :
    ∫ x in Q (Fin 3), partialDeriv i g x = 0 := by
  have hF : ∀ m, ContDiff ℝ 1 (if m = i then g else 0) := fun m => by
    split_ifs; exacts [hg.contDiff.of_le (by simp), contDiff_const]
  have h := integral_sum_pd_eq_faces hF
  have hz : ∀ f : Face, ∀ y, g (faceMap f y) = 0 := fun f y =>
    hg.eq_zero_of_notMem (faceMap_notMem_Q f y)
  simp only [pd_ite_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [h]
  refine Finset.sum_eq_zero fun m _ => ?_
  split_ifs <;> simp [hz]

theorem constTSD_mem_tsd : constTSD ∈ tsd (Q (Fin 3)) := by
  refine ⟨fun i j => ?_, ?_, fun φ hφ => ?_⟩
  · simp only [constTSD, cField_apply]
    congr 1
    funext x
    simp only [constTSDCoeff, Prod.mk.injEq]
    fin_cases i <;> fin_cases j <;> simp
  · simp only [constTSD, cField_apply, Fin.sum_univ_three]
    unfold cL2
    rw [← MemLp.toLp_add, ← MemLp.toLp_add, MemLp.toLp_congr _ MemLp.zero
      (Eventually.of_forall fun x => by simp [constTSDCoeff]; norm_num), MemLp.toLp_zero]
  · rw [inner_grad_testField _ hφ]
    simp only [integral_constTSD_mul, integral_pd_eq_zero (hφ _)]
    simp

theorem normalNormalFun_constTSD {ψ : (Fin 2 → ℝ) → ℝ} (hψ : IsTest Sq ψ) :
    normalNormalFun (faceFun ψ) constTSD = ∫ y in Sq, ψ y := by
  simp only [normalNormalFun, integral_constTSD_mul, Fin.sum_univ_three]
  simp [constTSDCoeff]
  have hF : ∀ m, ContDiff ℝ 1 (if m = (0 : Fin 3) then faceFun ψ else 0) := fun m => by
    split_ifs; exacts [(contDiff_faceFun hψ).of_le (by simp), contDiff_const]
  have h := integral_sum_pd_eq_faces hF
  simp only [pd_ite_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [h, Fin.sum_univ_three]
  simp only [ite_true, show ((1 : Fin 3) = 0) = False from by decide,
    show ((2 : Fin 3) = 0) = False from by decide, ite_false]
  simp only [faceFun_faceMap_self hψ, faceFun_faceMap_of_ne hψ (by decide : ((0 : Fin 3), false) ≠
    (0, true)), integral_zero, sub_zero]
  simp

/-- A nonnegative test function of the square with positive integral. -/
def sqBump : ContDiffBump (fun _ : Fin 2 => (1 / 4 : ℝ)) :=
  ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩

theorem isTest_sqBump : IsTest Sq (sqBump : (Fin 2 → ℝ) → ℝ) := by
  refine ⟨sqBump.contDiff, sqBump.hasCompactSupport, ?_⟩
  rw [sqBump.tsupport_eq]
  intro y hy
  rw [mem_Q]
  intro i
  have := (dist_le_pi_dist y (fun _ => 1 / 4) i).trans (Metric.mem_closedBall.1 hy)
  rw [Real.dist_eq, abs_le] at this
  simp only [sqBump] at this
  constructor <;> linarith [this.1, this.2]

theorem integral_sqBump_pos : 0 < ∫ y in Sq, (sqBump : (Fin 2 → ℝ) → ℝ) y := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy =>
    isTest_sqBump.eq_zero_of_notMem hy]
  exact sqBump.integral_pos

/-! ### The theorem -/

theorem normalNormalFun_eq_inner {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (E : MQ) :
    normalNormalFun f E = ∑ j : Fin 3, ⟪E (0, j), cL2 measurableSet_Q isBounded_Q
      (hf.continuous_partialDeriv j)⟫_ℝ :=
  Finset.sum_congr rfl fun _ _ => (inner_cL2_right _ _ _ _).symm

theorem continuous_normalNormalFun {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous fun u : State => normalNormalFun f u.fst := by
  simp only [normalNormalFun_eq_inner hf]
  exact continuous_finsetSum _ fun j _ =>
    ((L2F.continuous_apply (0, j)).comp (WithLp.fstL 2 ℝ MQ MQ).continuous).inner
      continuous_const

/-- **The TSD constraint is not invariant under the absorbing semigroup.** -/
theorem not_invariant_tsdPair :
    ¬ ∀ t, 0 ≤ t → ∀ x ∈ tsdPair, absorbingSemigroup.S t x ∈ tsdPair := by
  intro hinv
  have hcl := isMDissipative_absorbing.closure_domain_inter_of_invariant isClosed_tsdPair hinv
  set ψ := (sqBump : (Fin 2 → ℝ) → ℝ)
  have hψ := isTest_sqBump
  have hφ : ContDiff ℝ 1 (faceFun ψ) := (contDiff_faceFun hψ).of_le (by simp)
  set k₀ : State := WithLp.toLp 2 (constTSD, 0)
  have hk₀ : k₀ ∈ tsdPair := ⟨constTSD_mem_tsd, (tsd _).zero_mem⟩
  have hzero : ∀ y ∈ (absorbing.domain : Set State) ∩ tsdPair,
      normalNormalFun (faceFun ψ) y.fst = 0 := fun y hy =>
    normalNormal_eq_zero ⟨y, hy.1⟩ hy.2 hψ
  have hk := hcl k₀ hk₀
  have hclosed : IsClosed {y : State | normalNormalFun (faceFun ψ) y.fst = 0} :=
    isClosed_eq (continuous_normalNormalFun hφ) continuous_const
  have h0 : normalNormalFun (faceFun ψ) k₀.fst = 0 :=
    closure_minimal (fun y hy => hzero y hy) hclosed hk
  have hpos : 0 < normalNormalFun (faceFun ψ) k₀.fst := by
    change 0 < normalNormalFun (faceFun ψ) constTSD
    rw [normalNormalFun_constTSD hψ]
    exact integral_sqBump_pos
  linarith

/-! ### A radiating state -/

/-- The field `φ_ψ e₀ ⊗ e₁` (entry `(0, 1)`). -/
def witnessE : C1Field :=
  ⟨fun ij => if ij = (0, 1) then faceFun sqBump else 0, fun ij => by
    dsimp only; split_ifs
    exacts [(contDiff_faceFun isTest_sqBump).of_le (by simp), contDiff_const]⟩

/-- The field `-φ_ψ e₀ ⊗ e₂` (entry `(0, 2)`). -/
def witnessB : C1Field :=
  ⟨fun ij => if ij = (0, 2) then -faceFun sqBump else 0, fun ij => by
    dsimp only; split_ifs
    exacts [((contDiff_faceFun isTest_sqBump).of_le (by simp)).neg, contDiff_const]⟩

theorem witness_bc : witnessE.tan + witnessB.flux = 0 := by
  ext1 b
  rw [PiLp.add_apply, C1Field.tan, C1Field.flux, tanTrace_apply, fluxTrace_apply, PiLp.zero_apply]
  unfold cL2
  rw [← MemLp.toLp_add]
  refine (MemLp.toLp_congr _ MemLp.zero (Eventually.of_forall fun y => ?_)).trans
    (MemLp.toLp_zero _)
  obtain ⟨⟨m, s⟩, i, j'⟩ := b
  simp only [Pi.add_apply, Pi.zero_apply, tanFun, fluxFun, fluxVal, witnessE, witnessB]
  by_cases hf : (m, s) = (0, true)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hf
    fin_cases i <;> fin_cases j' <;> simp [tanDir, faceSign, Fin.succAbove]
  · have h0 := faceFun_faceMap_of_ne isTest_sqBump hf y
    split_ifs <;> simp [h0]

/-- **A radiating state**: some `u ∈ D(A)` has `⟪A u, u⟫ < 0`. -/
theorem exists_inner_absorbing_neg :
    ∃ u : absorbing.domain, ⟪absorbing u, (u : State)⟫_ℝ < 0 := by
  obtain ⟨hdom, -, htr⟩ := mem_domain_of_smooth witnessE witnessB witness_bc
  refine ⟨⟨_, hdom⟩, ?_⟩
  rw [inner_absorbing]
  change -‖impedanceTriple.trace (⟨_, hdom⟩ : impedanceTriple.op.domain)‖ ^ 2 < 0
  rw [htr, neg_lt_zero]
  refine pow_pos (norm_pos_iff.2 fun h => ?_) 2
  -- the slot `((0, ½), row 0, direction 1)` of the trace is `ψ`
  have h1 := congrArg (fun β : Bdry => β (((0 : Fin 3), true), (0 : Fin 3), (0 : Fin 2))) h
  simp only [C1Field.tan, tanTrace_apply, PiLp.zero_apply] at h1
  have h2 : ∫ y in Sq, (cL2 measurableSet_Q isBounded_Q
      (continuous_tanFun witnessE.continuous (((0 : Fin 3), true), (0 : Fin 3), (0 : Fin 2))) :
        (Fin 2 → ℝ) → ℝ) y * 1 = ∫ y in Sq, (sqBump : (Fin 2 → ℝ) → ℝ) y := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_cL2 measurableSet_Q isBounded_Q
      (continuous_tanFun witnessE.continuous (((0 : Fin 3), true), (0 : Fin 3), (0 : Fin 2)))]
      with y hy
    rw [hy, mul_one]
    simp only [tanFun, witnessE, tanDir]
    rw [ite_eq_left (by decide), faceFun_faceMap_self isTest_sqBump]
  rw [h1] at h2
  have := integral_sqBump_pos
  have h3 : ∫ y in Sq, ((0 : L2 ℝ Sq) : (Fin 2 → ℝ) → ℝ) y * 1 = 0 := by
    rw [integral_congr_ae ((Lp.coeFn_zero ℝ 2 (volume.restrict Sq)).mono fun y hy => by
      rw [hy])]
    simp
  linarith

end Feec.Models.Cube.Absorbing
