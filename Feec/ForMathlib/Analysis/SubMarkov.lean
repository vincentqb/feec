module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Feec.ForMathlib.Analysis.ExpFlow

/-!
# Sub-Markov generators: positive contraction semigroups in the maximum norm

On `ℝ^ι` with the maximum norm, a sub-Markov generator `L` (`L + c` positive for some `c ≥ 0`,
`L 𝟙 ≤ 0`) generates a positive contraction semigroup `e^{tL}`, `t ≥ 0`; when `L 𝟙 = 0`, barrier
estimates hold for the flow and for backward Euler.
-/

open NormedSpace Set

@[expose] public noncomputable section

theorem NormedSpace.norm_exp_le_exp_norm {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (h1 : ‖(1 : 𝔸)‖ ≤ 1) (x : 𝔸) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  have hpow : ∀ n : ℕ, ‖x ^ n‖ ≤ ‖x‖ ^ n := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using h1
    · exact norm_pow_le' x hn
  rw [exp_eq_tsum ℝ, Real.exp_eq_exp_ℝ, exp_eq_tsum ℝ]
  refine (norm_tsum_le_tsum_norm (norm_expSeries_summable' x)).trans ?_
  refine Summable.tsum_le_tsum (fun n => ?_) (norm_expSeries_summable' x)
    ((norm_expSeries_summable' ‖x‖).of_norm)
  rw [norm_smul, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (hpow n) (by positivity)

namespace ContinuousLinearMap

variable {ι : Type*}

theorem abs_apply_le_of_nonneg {P : (ι → ℝ) →L[ℝ] (ι → ℝ)} (hP : ∀ v, 0 ≤ v → 0 ≤ P v)
    (v : ι → ℝ) (i : ι) : |P v i| ≤ P |v| i := by
  have h1 := hP (|v| - v) fun j => by simp [le_abs_self]
  have h2 := hP (|v| + v) fun j => by
    simp only [Pi.add_apply, Pi.abs_apply, Pi.zero_apply]; linarith [neg_abs_le (v j)]
  rw [map_sub] at h1
  rw [map_add] at h2
  have a1 := h1 i
  have a2 := h2 i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at a1 a2
  exact abs_le.2 ⟨by linarith, by linarith⟩

variable [Fintype ι]

theorem norm_le_of_nonneg_of_apply_one_le {P : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hP : ∀ v, 0 ≤ v → 0 ≤ P v) {c : ℝ} (hc : 0 ≤ c) (h1 : ∀ i, P (fun _ => 1) i ≤ c) :
    ‖P‖ ≤ c := by
  refine opNorm_le_bound _ hc fun v => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have hb : |v| ≤ ‖v‖ • (fun _ => (1 : ℝ)) := fun j => by
    simpa using norm_le_pi_norm v j
  have h2 := hP _ (sub_nonneg.2 hb)
  rw [map_sub, map_smul, sub_nonneg] at h2
  rw [Real.norm_eq_abs]
  calc |P v i| ≤ P |v| i := abs_apply_le_of_nonneg hP v i
    _ ≤ ‖v‖ * P (fun _ => 1) i := h2 i
    _ ≤ ‖v‖ * c := mul_le_mul_of_nonneg_left (h1 i) (norm_nonneg v)
    _ = c * ‖v‖ := mul_comm _ _

theorem exp_smul_apply_nonneg {P : (ι → ℝ) →L[ℝ] (ι → ℝ)} (hP : ∀ v, 0 ≤ v → 0 ≤ P v)
    {t : ℝ} (ht : 0 ≤ t) {v : ι → ℝ} (hv : 0 ≤ v) : 0 ≤ exp (t • P) v := by
  have hpow : ∀ k : ℕ, 0 ≤ (P ^ k) v := fun k => by
    induction k with
    | zero => simpa using hv
    | succ k ih => rw [pow_succ']; exact hP _ ih
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℝ) (t • P)
  have e := (ContinuousLinearMap.apply ℝ (ι → ℝ) v).map_tsum hs
  simp only [ContinuousLinearMap.apply_apply] at e
  rw [exp_eq_tsum ℝ]
  dsimp only
  rw [e]
  refine tsum_nonneg fun k => ?_
  rw [smul_pow, smul_smul, _root_.smul_apply]
  exact smul_nonneg (by positivity) (hpow k)

end ContinuousLinearMap

variable {ι : Type*} [Fintype ι]

/-- `L` is a sub-Markov generator: `L + c` is positive for some `c ≥ 0`, and `L 𝟙 ≤ 0`. -/
structure IsSubMarkovGenerator (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) : Prop where
  exists_shift : ∃ c : ℝ, 0 ≤ c ∧ ∀ v, 0 ≤ v → 0 ≤ L v + c • v
  apply_one_nonpos : ∀ i, L (fun _ => 1) i ≤ 0

namespace IsSubMarkovGenerator

/-- `ℚ`-algebra structure on operators, for `NormedSpace.exp_add_of_commute`. -/
local instance instNormedAlgebraRat : NormedAlgebra ℚ ((ι → ℝ) →L[ℝ] (ι → ℝ)) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

theorem _root_.ContinuousLinearMap.exp_smul_eq_smul_exp_smul_add (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) (c t : ℝ) :
    exp (t • L) = Real.exp (-(t * c)) • exp (t • (L + c • 1)) := by
  have e : t • L = t • (L + c • 1) + algebraMap ℝ ((ι → ℝ) →L[ℝ] (ι → ℝ)) (-(t * c)) := by
    rw [Algebra.algebraMap_eq_smul_one, smul_add, smul_smul]; module
  rw [e, exp_add_of_commute (Algebra.commutes _ _).symm, ← algebraMap_exp_comm,
    ← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]

variable {L : (ι → ℝ) →L[ℝ] (ι → ℝ)} (hL : IsSubMarkovGenerator L)
include hL

theorem exp_smul_apply_nonneg {t : ℝ} (ht : 0 ≤ t) {v : ι → ℝ} (hv : 0 ≤ v) :
    0 ≤ exp (t • L) v := by
  obtain ⟨c, -, hc⟩ := hL.exists_shift
  rw [L.exp_smul_eq_smul_exp_smul_add c t, _root_.smul_apply]
  exact smul_nonneg (Real.exp_pos _).le
    (ContinuousLinearMap.exp_smul_apply_nonneg (fun w hw => by simpa using hc w hw) ht hv)

theorem norm_exp_smul_le_one {t : ℝ} (ht : 0 ≤ t) : ‖exp (t • L)‖ ≤ 1 := by
  obtain ⟨c, hc0, hc⟩ := hL.exists_shift
  have hP : ∀ v, 0 ≤ v → 0 ≤ (L + c • 1) v := fun v hv => by simpa using hc v hv
  have hn : ‖L + c • 1‖ ≤ c :=
    ContinuousLinearMap.norm_le_of_nonneg_of_apply_one_le hP hc0 fun i => by
      simpa using hL.apply_one_nonpos i
  rw [L.exp_smul_eq_smul_exp_smul_add c t, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-(t * c)) * ‖exp (t • (L + c • 1))‖
      ≤ Real.exp (-(t * c)) * Real.exp (t * c) := by
        gcongr
        refine (NormedSpace.norm_exp_le_exp_norm ContinuousLinearMap.norm_id_le _).trans ?_
        gcongr
        rw [norm_smul, Real.norm_of_nonneg ht]
        exact mul_le_mul_of_nonneg_left hn ht
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

theorem exp_smul_apply_le {t : ℝ} (ht : 0 ≤ t) {a : ℝ} (ha : 0 ≤ a) {v : ι → ℝ}
    (hv : v ≤ fun _ => a) : exp (t • L) v ≤ fun _ => a := by
  have h1 := hL.exp_smul_apply_nonneg ht (sub_nonneg.2 hv)
  rw [map_sub, sub_nonneg] at h1
  refine fun i => (h1 i).trans ?_
  have := (norm_le_pi_norm (exp (t • L) fun _ => a) i).trans
    (((exp (t • L)).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _)
      (hL.norm_exp_smul_le_one ht)))
  rw [Real.norm_eq_abs] at this
  refine (le_abs_self _).trans (this.trans ?_)
  exact (pi_norm_le_iff_of_nonneg ha).2 fun _ => by rw [Real.norm_of_nonneg ha]

theorem le_exp_smul_apply {t : ℝ} (ht : 0 ≤ t) {a : ℝ} (ha : 0 ≤ a) {v : ι → ℝ}
    (hv : (fun _ => -a) ≤ v) : (fun _ => -a) ≤ exp (t • L) v := by
  have := hL.exp_smul_apply_le ht ha (v := -v) fun i => by simpa using neg_le.1 (hv i)
  intro i
  have h := this i
  simp only [map_neg, Pi.neg_apply] at h
  exact neg_le.1 h

theorem nonneg_of_hasDerivAt {Z Z' : ℝ → ι → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hZ : ∀ r ∈ Icc 0 t, HasDerivAt Z (Z' r) r)
    (hZ' : ∀ r ∈ Icc 0 t, 0 ≤ Z' r - L (Z r)) (h0 : 0 ≤ Z 0) : 0 ≤ Z t := by
  set f : ℝ → ι → ℝ := fun r => exp ((t - r) • L) (Z r)
  have hf : ∀ r ∈ Icc 0 t, HasDerivAt f (exp ((t - r) • L) (Z' r - L (Z r))) r :=
    fun r hr => by
      simpa using L.hasDerivAt_exp_sub_smul_apply (𝕜 := ℝ) t (hZ r hr)
  intro i
  have hmono : MonotoneOn (fun r => f r i) (Icc 0 t) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t)
      (fun r hr => ((hasDerivAt_pi.1 (hf r hr) i).continuousAt).continuousWithinAt)
      (fun r hr => (hasDerivAt_pi.1 (hf r (interior_subset hr)) i).hasDerivWithinAt)
      fun r hr => ?_
    have hr' := interior_subset hr
    exact hL.exp_smul_apply_nonneg (sub_nonneg.2 hr'.2) (hZ' r hr') i
  have h := hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  simp only [f, sub_self, zero_smul, exp_zero, one_apply_eq_self, sub_zero] at h
  exact (hL.exp_smul_apply_nonneg ht h0 i).trans h

theorem abs_apply_le_of_barrier (h1 : L (fun _ => 1) = 0) {E E' : ℝ → ι → ℝ} {t A : ℝ} (ht : 0 ≤ t)
    (hE : ∀ r ∈ Icc 0 t, HasDerivAt E (E' r) r) {ψ : ι → ℝ} (hψ : 0 ≤ ψ)
    (hτ : ∀ r ∈ Icc 0 t, ∀ i, |(E' r - L (E r)) i| ≤ A - L ψ i) (i : ι) :
    |E t i| ≤ ‖E 0‖ + ψ i + t * A := by
  have key : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ε * E t i ≤ ‖E 0‖ + ψ i + t * A := fun ε hε => by
    set Z : ℝ → ι → ℝ := fun r => (‖E 0‖ + r * A) • (fun _ => (1 : ℝ)) + ψ - ε • E r
    have hZ : ∀ r ∈ Icc 0 t, HasDerivAt Z (A • (fun _ => (1 : ℝ)) - ε • E' r) r := fun r hr => by
      refine hasDerivAt_pi.2 fun j => ?_
      have := ((((hasDerivAt_id r).mul_const A).const_add ‖E 0‖).add_const (ψ j)).sub
        ((hasDerivAt_pi.1 (hE r hr) j).const_mul ε)
      convert this using 1 <;> first | (funext x; simp [Z]) | simp
    have hL1 : ∀ c : ℝ, L (c • fun _ => (1 : ℝ)) = 0 := fun c => by rw [map_smul, h1, smul_zero]
    have h := hL.nonneg_of_hasDerivAt ht hZ (fun r hr j => by
      have hb := hτ r hr j
      simp only [Z, map_sub, map_add, hL1, zero_add, map_smul, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, Pi.zero_apply, mul_one]
      rcases hε with rfl | rfl
      · have := (abs_le.1 hb).2; simp only [Pi.sub_apply] at this; linarith
      · have := (abs_le.1 hb).1; simp only [Pi.sub_apply] at this; linarith) (fun j => by
      simp only [Z, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero,
        mul_one, Pi.zero_apply]
      have := norm_le_pi_norm (E 0) j
      rw [Real.norm_eq_abs] at this
      have hψj : 0 ≤ ψ j := hψ j
      rcases hε with rfl | rfl
      · linarith [le_abs_self (E 0 j)]
      · linarith [neg_abs_le (E 0 j)]) i
    simp only [Z, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one,
      Pi.zero_apply] at h
    linarith
  rcases abs_cases (E t i) with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; simpa using key 1 (Or.inl rfl)
  · rw [h]; simpa using key (-1) (Or.inr rfl)

theorem nonneg_of_sub_smul_apply_nonneg {τ : ℝ} (hτ : 0 ≤ τ) {x : ι → ℝ}
    (h : 0 ≤ x - τ • L x) : 0 ≤ x := by
  intro i
  by_contra hi
  obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ x ⟨i, Finset.mem_univ i⟩
  obtain ⟨c, -, hc⟩ := hL.exists_shift
  have hm : x j < 0 := (hj i (Finset.mem_univ i)).trans_lt (not_le.1 hi)
  have h1 := hc (x - x j • fun _ => 1) (fun k => by simpa using hj k (Finset.mem_univ k)) j
  have h2 := hL.apply_one_nonpos j
  have h3 := h j
  simp only [map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one,
    sub_self, mul_zero, add_zero, Pi.zero_apply] at h1 h3
  nlinarith [mul_nonneg hτ (by nlinarith : 0 ≤ L x j)]

theorem abs_apply_le_of_barrier_step (h1 : L (fun _ => 1) = 0) {E δ : ℕ → ι → ℝ} {τ A : ℝ}
    (hτ : 0 ≤ τ) {n : ℕ} (hE : ∀ k < n, E (k + 1) - τ • L (E (k + 1)) = E k + τ • δ k)
    {ψ : ι → ℝ} (hψ : 0 ≤ ψ) (hδ : ∀ k < n, ∀ i, |δ k i| ≤ A - L ψ i) (i : ι) :
    |E n i| ≤ ‖E 0‖ + ψ i + n * τ * A := by
  have hL1 : ∀ c : ℝ, L (c • fun _ => (1 : ℝ)) = 0 := fun c => by rw [map_smul, h1, smul_zero]
  have key : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ k ≤ n,
      0 ≤ (‖E 0‖ + k * τ * A) • (fun _ => (1 : ℝ)) + ψ - ε • E k := fun ε hε k => by
    induction k with
    | zero =>
      intro _ j
      have := norm_le_pi_norm (E 0) j
      rw [Real.norm_eq_abs] at this
      have : 0 ≤ ψ j := hψ j
      rcases hε with rfl | rfl <;> simp <;> linarith [le_abs_self (E 0 j), neg_abs_le (E 0 j)]
    | succ k ih =>
      intro hk
      have hk' : k < n := hk
      refine hL.nonneg_of_sub_smul_apply_nonneg hτ fun j => ?_
      have e := congrFun (hE k hk') j
      have hz := ih hk'.le j
      have hb := hδ k hk' j
      simp only [map_sub, map_add, hL1, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, mul_one, Pi.zero_apply, zero_add] at e hz ⊢
      push_cast
      rcases hε with rfl | rfl
      · nlinarith [mul_nonneg hτ (by linarith [(abs_le.1 hb).2] : 0 ≤ A - L ψ j - δ k j)]
      · nlinarith [mul_nonneg hτ (by linarith [(abs_le.1 hb).1] : 0 ≤ A - L ψ j + δ k j)]
  have hp := key 1 (Or.inl rfl) n le_rfl i
  have hm := key (-1) (Or.inr rfl) n le_rfl i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one, one_mul,
    neg_mul, Pi.zero_apply] at hp hm
  exact abs_le.2 ⟨by linarith, by linarith⟩

end IsSubMarkovGenerator
