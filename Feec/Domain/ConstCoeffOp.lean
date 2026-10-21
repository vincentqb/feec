module

public import Feec.Domain.L2Field
public import Feec.ForMathlib.LinearPMap.GraphSpace

/-!
# Constant-coefficient differential operators and their `L²` realizations

Let `E` be a finite-dimensional real normed space with an additive Haar measure (`ℝⁿ`), `Ω ⊆ E`
open, and `𝕜 = ℝ` or `ℂ`. A **constant-coefficient differential operator** from `𝕜^ι`-valued to
`𝕜^κ`-valued fields is a matrix of finite sums of constant multiples of iterated directional
derivatives,

  `(A f)ⱼ = Σᵢ Σ_{(v₁ ⋯ v_k, c) ∈ coeff j i} c · ∂_{v₁} ⋯ ∂_{v_k} fᵢ`

(`Feec.Domain.ConstCoeffOp`); grad, curl, div, sym grad, Hessian, inc, div div, the exterior
derivative on `k`-forms, … are instances, of any order and in any dimension. Its **formal
adjoint** `A.formalAdj` has entries `(-1)^k conj c · ∂_{v_k} ⋯ ∂_{v₁}`, and
`A.formalAdj.formalAdj = A` holds exactly.

## Main results

* `integral_conj_iterDeriv_mul`, `ConstCoeffOp.green`: integration by parts against a test
  field, with **no boundary condition** on the other factor (any smooth field on `E`):
  `Σⱼ ∫ conj (A φ)ⱼ ψⱼ = Σᵢ ∫ conj φᵢ (Aᵗ ψ)ᵢ`.
* `ConstCoeffOp.minimal A Ω`: the **minimal realization**, the closure in `L²(Ω)` of `A` on
  `C_c^∞(Ω; 𝕜^ι)` (the "`H̊`" boundary condition); closed (`isClosed_minimal`) and densely
  defined (`dense_minimal_domain`), equal to `A` on test fields (`minimal_testField`). Its
  graph-closure identity `minimal_green` tests against smooth fields with no boundary condition.
* `ConstCoeffOp.maximal A Ω`: the **maximal (weak) realization**: `u ∈ D(A_max)` iff
  `A u ∈ L²(Ω)` in the sense of distributions on `Ω` (`mem_maximal_domain_iff`), with no
  boundary condition; closed and densely defined, `A_min ≤ A_max`
  (`minimal_le_maximal`), and smooth fields with `ψ, A ψ ∈ L²(Ω)` lie in `D(A_max)`
  (`smooth_mem_maximal_domain`).
* **Duality** `adjoint_minimal : (A_min)† = (Aᵗ)_max` and
  `adjoint_maximal : (A_max)† = (Aᵗ)_min`. These subsume the hand-built graph closures of the
  bounded-domain models (`curl`, `grad`, `curl` on symmetric fields, `hess`, …) and their
  `mem_adjoint_*_iff` lemmas.

## References

* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.1
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], §6.2 (`H̊` and `H` realizations)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (the complexes on bounded domains)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff ENNReal ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Domain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Iterated directional derivatives -/

section IterDeriv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The iterated directional derivative `∂_{v₁} ∂_{v₂} ⋯ ∂_{v_k} f` for `vs = [v₁, …, v_k]`. -/
def iterDeriv : List E → (E → F) → E → F
  | [], f => f
  | v :: vs, f => fun x => fderiv ℝ (iterDeriv vs f) x v

@[simp] theorem iterDeriv_nil (f : E → F) : iterDeriv [] f = f := rfl

theorem iterDeriv_cons (v : E) (vs : List E) (f : E → F) :
    iterDeriv (v :: vs) f = fun x => fderiv ℝ (iterDeriv vs f) x v := rfl

theorem iterDeriv_singleton (v : E) (f : E → F) :
    iterDeriv [v] f = fun x => fderiv ℝ f x v := rfl

theorem iterDeriv_append (l₁ l₂ : List E) (f : E → F) :
    iterDeriv (l₁ ++ l₂) f = iterDeriv l₁ (iterDeriv l₂ f) := by
  induction l₁ with
  | nil => rfl
  | cons v l ih => simp only [List.cons_append, iterDeriv_cons, ih]

theorem contDiff_iterDeriv {f : E → F} (hf : ContDiff ℝ ∞ f) (vs : List E) :
    ContDiff ℝ ∞ (iterDeriv vs f) := by
  induction vs with
  | nil => exact hf
  | cons v vs ih => exact (ih.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- `∂^{vs} f ∈ C^M` for `f ∈ C^N`, `#vs + M ≤ N`. -/
theorem contDiff_iterDeriv_of_le {N M : ℕ} {f : E → F} (hf : ContDiff ℝ N f) (vs : List E)
    (h : vs.length + M ≤ N) : ContDiff ℝ M (iterDeriv vs f) := by
  induction vs generalizing M with
  | nil => exact hf.of_le (by simpa using h)
  | cons v vs ih =>
    rw [List.length_cons] at h
    exact ((ih (M := M + 1) (by omega)).fderiv_right (m := M) (by push_cast; exact le_rfl)).clm_apply
      contDiff_const

theorem IsTest.iterDeriv {Ω : Set E} {f : E → F} (hf : IsTest Ω f) (vs : List E) :
    IsTest Ω (iterDeriv vs f) := by
  induction vs with
  | nil => exact hf
  | cons v vs ih => exact ih.fderiv_apply v

theorem iterDeriv_add {f g : E → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (vs : List E) :
    iterDeriv vs (f + g) = iterDeriv vs f + iterDeriv vs g := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    change fderiv ℝ (iterDeriv vs (f + g)) x v =
      fderiv ℝ (iterDeriv vs f) x v + fderiv ℝ (iterDeriv vs g) x v
    rw [ih, fderiv_add ((contDiff_iterDeriv hf vs).differentiable (by simp) x)
      ((contDiff_iterDeriv hg vs).differentiable (by simp) x)]
    rfl

theorem iterDeriv_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F]
    (c : 𝕜) {f : E → F} (hf : ContDiff ℝ ∞ f) (vs : List E) :
    iterDeriv vs (c • f) = c • iterDeriv vs f := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    change fderiv ℝ (iterDeriv vs (c • f)) x v = c • fderiv ℝ (iterDeriv vs f) x v
    rw [ih, fderiv_const_smul ((contDiff_iterDeriv hf vs).differentiable (by simp) x)]
    rfl

theorem iterDeriv_zero (vs : List E) : iterDeriv vs (0 : E → F) = 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    rw [iterDeriv_cons, ih]
    simp

theorem iterDeriv_sum {α : Type*} (s : Finset α) {f : α → E → F}
    (hf : ∀ a ∈ s, ContDiff ℝ ∞ (f a)) (vs : List E) :
    iterDeriv vs (fun x => ∑ a ∈ s, f a x) = fun x => ∑ a ∈ s, iterDeriv vs (f a) x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact iterDeriv_zero (F := F) vs
  | insert a s ha ih =>
    have hs : ContDiff ℝ ∞ (fun x => ∑ b ∈ s, f b x) :=
      ContDiff.sum fun b hb => hf b (Finset.mem_insert_of_mem hb)
    simp only [Finset.sum_insert ha]
    have := iterDeriv_add (hf a (Finset.mem_insert_self a s)) hs vs
    rw [show (fun x => f a x + ∑ b ∈ s, f b x) = f a + fun x => ∑ b ∈ s, f b x from rfl, this,
      ih fun b hb => hf b (Finset.mem_insert_of_mem hb)]
    rfl

theorem iterDeriv_comp_clm (L : F →L[ℝ] G) {f : E → F} (hf : ContDiff ℝ ∞ f) (vs : List E) :
    iterDeriv vs (fun x => L (f x)) = fun x => L (iterDeriv vs f x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    change fderiv ℝ (iterDeriv vs fun x => L (f x)) x v = L (fderiv ℝ (iterDeriv vs f) x v)
    rw [ih]
    have hd := (contDiff_iterDeriv hf vs).differentiable (by simp) x
    rw [show (fun y => L (iterDeriv vs f y)) = L ∘ iterDeriv vs f from rfl,
      (L.hasFDerivAt.comp x hd.hasFDerivAt).fderiv]
    rfl

end IterDeriv

/-! ## Integration by parts -/

section IBP

variable [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] {𝕜 : Type*} [RCLike 𝕜]

/-- One integration by parts: `∫ conj (∂_v f) g = -∫ conj f ∂_v g` for a test function `f` and a
`C¹` function `g` (no boundary condition on `g`). -/
theorem integral_conj_fderiv_mul {Ω : Set E} {f g : E → 𝕜} (hf : IsTest Ω f)
    (hg : ContDiff ℝ 1 g) (v : E) :
    ∫ x, conj (fderiv ℝ f x v) * g x = -∫ x, conj (f x) * fderiv ℝ g x v := by
  have hc := hf.conjugate
  have hcd : ∀ x, fderiv ℝ (fun y => conj (f y)) x v = conj (fderiv ℝ f x v) := by
    intro x
    have := iterDeriv_comp_clm (RCLike.conjCLE (K := 𝕜)).toContinuousLinearMap hf.contDiff [v]
    exact congrFun this x
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hcg : Continuous fun x => fderiv ℝ g x v :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun y => conj (f y)) (g := g) (v := v)
    (((hc.fderiv_apply v).continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (hc.fderiv_apply v).hasCompactSupport.mul_right)
    ((hc.continuous.mul hcg).integrable_of_hasCompactSupport hc.hasCompactSupport.mul_right)
    ((hc.continuous.mul hg.continuous).integrable_of_hasCompactSupport
      hc.hasCompactSupport.mul_right)
    (fun x _ => hc.differentiable x) (fun x _ => hgd x)
  simp only [hcd] at h
  rw [h, neg_neg]

/-- **Iterated integration by parts**: `∫ conj (∂^{vs} f) g = (-1)^k ∫ conj f ∂^{rev vs} g` for a
test function `f` and a `C^k` function `g` (no boundary condition on `g`), `k = #vs`. -/
theorem integral_conj_iterDeriv_mul {Ω : Set E} {f g : E → 𝕜} (hf : IsTest Ω f) (vs : List E)
    (hg : ContDiff ℝ vs.length g) :
    ∫ x, conj (iterDeriv vs f x) * g x =
      (-1) ^ vs.length * ∫ x, conj (f x) * iterDeriv vs.reverse g x := by
  induction vs generalizing g with
  | nil => simp
  | cons v vs ih =>
    change ∫ x, conj (fderiv ℝ (iterDeriv vs f) x v) * g x = _
    rw [List.length_cons] at hg
    rw [integral_conj_fderiv_mul (hf.iterDeriv vs) (hg.of_le (by simp)) v]
    have hg' : ContDiff ℝ vs.length (fun x => fderiv ℝ g x v) :=
      (hg.fderiv_right (m := vs.length) (by push_cast; exact le_rfl)).clm_apply contDiff_const
    have e := ih hg'
    rw [show (fun x => fderiv ℝ g x v) = iterDeriv [v] g from rfl, ← iterDeriv_append] at e
    have e' : ∫ x, conj (iterDeriv vs f x) * fderiv ℝ g x v =
        (-1) ^ vs.length * ∫ x, conj (f x) * iterDeriv (vs.reverse ++ [v]) g x := e
    rw [e', List.reverse_cons, List.length_cons, pow_succ]
    ring

end IBP

/-! ## Constant-coefficient operators -/

variable (E) in
/-- A constant-coefficient differential operator from `𝕜^ι`-valued to `𝕜^κ`-valued fields on
`E`: `(A f)ⱼ = Σᵢ Σ_{(vs, c) ∈ coeff j i} c · ∂^{vs} fᵢ`. -/
structure ConstCoeffOp (𝕜 : Type*) [RCLike 𝕜] (ι κ : Type*) where
  /-- the entries: lists of (directions, coefficient) -/
  coeff : κ → ι → List (List E × 𝕜)

namespace ConstCoeffOp

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*}

/-- A scalar entry `Σ c · ∂^{vs}` applied to a function. -/
def applyEntry (P : List (List E × 𝕜)) (f : E → 𝕜) (x : E) : 𝕜 :=
  (P.map fun t => t.2 * iterDeriv t.1 f x).sum

/-- The formal adjoint of a scalar entry: `Σ (-1)^k conj c · ∂^{rev vs}`. -/
def adjEntry (P : List (List E × 𝕜)) : List (List E × 𝕜) :=
  P.map fun t => (t.1.reverse, (-1) ^ t.1.length * conj t.2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem adjEntry_adjEntry (P : List (List E × 𝕜)) : adjEntry (adjEntry P) = P := by
  simp only [adjEntry, List.map_map]
  conv_rhs => rw [← List.map_id P]
  refine List.map_congr_left fun t _ => ?_
  obtain ⟨vs, c⟩ := t
  simp only [Function.comp_apply, List.reverse_reverse, List.length_reverse, map_mul, map_pow,
    RCLike.conj_conj, id_eq, Prod.mk.injEq, true_and]
  rw [show conj (-1 : 𝕜) = -1 by simp, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow,
    one_mul]

@[simp] theorem applyEntry_nil (f : E → 𝕜) : applyEntry ([] : List (List E × 𝕜)) f = 0 := by
  funext x; simp [applyEntry]

theorem applyEntry_cons (t : List E × 𝕜) (P : List (List E × 𝕜)) (f : E → 𝕜) :
    applyEntry (t :: P) f = fun x => t.2 * iterDeriv t.1 f x + applyEntry P f x := by
  funext x; simp [applyEntry]

/-- The action on a field `f : ι → E → 𝕜`. -/
def apply [Fintype ι] (A : ConstCoeffOp E 𝕜 ι κ) (f : ι → E → 𝕜) : κ → E → 𝕜 :=
  fun j x => ∑ i, applyEntry (A.coeff j i) (f i) x

/-- The formal adjoint `Aᵗ`, with `∫ conj (A φ) · ψ = ∫ conj φ · Aᵗ ψ`. -/
def formalAdj (A : ConstCoeffOp E 𝕜 ι κ) : ConstCoeffOp E 𝕜 κ ι where
  coeff i j := adjEntry (A.coeff j i)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem formalAdj_formalAdj (A : ConstCoeffOp E 𝕜 ι κ) : A.formalAdj.formalAdj = A := by
  cases A
  simp only [formalAdj, adjEntry_adjEntry]

/-- All entries of `A` have order at most `N`. -/
def IsOrderLE (A : ConstCoeffOp E 𝕜 ι κ) (N : ℕ) : Prop :=
  ∀ j i, ∀ t ∈ A.coeff j i, t.1.length ≤ N

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem IsOrderLE.formalAdj {A : ConstCoeffOp E 𝕜 ι κ} {N : ℕ} (h : A.IsOrderLE N) :
    A.formalAdj.IsOrderLE N := by
  intro i j t ht
  change t ∈ adjEntry (A.coeff j i) at ht
  simp only [adjEntry, List.mem_map] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  simpa using h j i t' ht'

/-- A bound for the order of `A` (the total length of all its direction lists). -/
def order [Fintype ι] [Fintype κ] (A : ConstCoeffOp E 𝕜 ι κ) : ℕ :=
  ∑ j, ∑ i, ((A.coeff j i).map fun t => t.1.length).sum

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem isOrderLE_order [Fintype ι] [Fintype κ] (A : ConstCoeffOp E 𝕜 ι κ) :
    A.IsOrderLE A.order := by
  intro j i t ht
  calc t.1.length ≤ ((A.coeff j i).map fun t => t.1.length).sum :=
        List.le_sum_of_mem (List.mem_map_of_mem ht)
    _ ≤ ∑ i, ((A.coeff j i).map fun t => t.1.length).sum :=
        Finset.single_le_sum (f := fun i => ((A.coeff j i).map fun t => t.1.length).sum)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ ≤ A.order :=
        Finset.single_le_sum (f := fun j => ∑ i, ((A.coeff j i).map fun t => t.1.length).sum)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

section Smooth

theorem continuous_applyEntry {N : ℕ} (P : List (List E × 𝕜)) (hP : ∀ t ∈ P, t.1.length ≤ N)
    {f : E → 𝕜} (hf : ContDiff ℝ N f) : Continuous (applyEntry P f) := by
  induction P with
  | nil => rw [applyEntry_nil]; exact continuous_const
  | cons t P ih =>
    rw [applyEntry_cons]
    exact (continuous_const.mul (contDiff_iterDeriv_of_le hf t.1
      (M := 0) (by simpa using hP t (List.mem_cons_self))).continuous).add
      (ih fun t' ht' => hP t' (List.mem_cons_of_mem _ ht'))

theorem continuous_apply [Fintype ι] {N : ℕ} (A : ConstCoeffOp E 𝕜 ι κ) (hA : A.IsOrderLE N)
    {f : ι → E → 𝕜} (hf : ∀ i, ContDiff ℝ N (f i)) (j : κ) : Continuous (A.apply f j) :=
  continuous_finsetSum _ fun i _ => continuous_applyEntry _ (hA j i) (hf i)

theorem contDiff_applyEntry (P : List (List E × 𝕜)) {f : E → 𝕜} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (applyEntry P f) := by
  induction P with
  | nil => rw [applyEntry_nil]; exact contDiff_const
  | cons t P ih =>
    rw [applyEntry_cons]
    exact (contDiff_const.mul (contDiff_iterDeriv hf t.1)).add ih

theorem _root_.Feec.Domain.IsTest.applyEntry {Ω : Set E} (P : List (List E × 𝕜)) {f : E → 𝕜} (hf : IsTest Ω f) :
    IsTest Ω (ConstCoeffOp.applyEntry P f) := by
  induction P with
  | nil => rw [applyEntry_nil]; exact IsTest.zero
  | cons t P ih =>
    rw [applyEntry_cons]
    exact ((hf.iterDeriv t.1).const_mul t.2).add ih

theorem contDiff_apply [Fintype ι] (A : ConstCoeffOp E 𝕜 ι κ) {f : ι → E → 𝕜}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (j : κ) : ContDiff ℝ ∞ (A.apply f j) :=
  ContDiff.sum fun i _ => contDiff_applyEntry _ (hf i)

theorem isTestField_apply [Fintype ι] (A : ConstCoeffOp E 𝕜 ι κ) {Ω : Set E} {φ : ι → E → 𝕜}
    (hφ : IsTestField Ω φ) : IsTestField Ω (A.apply φ) := fun _ =>
  IsTest.sum _ fun i _ => IsTest.applyEntry _ (hφ i)

theorem applyEntry_zero (P : List (List E × 𝕜)) : applyEntry P (0 : E → 𝕜) = 0 := by
  induction P with
  | nil => exact applyEntry_nil _
  | cons t P ih =>
    rw [applyEntry_cons, ih, iterDeriv_zero]
    funext x
    simp

theorem applyEntry_add (P : List (List E × 𝕜)) {f g : E → 𝕜} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) : applyEntry P (f + g) = applyEntry P f + applyEntry P g := by
  funext x
  induction P with
  | nil => simp [applyEntry]
  | cons t P ih =>
    simp only [applyEntry, List.map_cons, List.sum_cons, Pi.add_apply] at ih ⊢
    rw [ih, iterDeriv_add hf hg]
    simp only [Pi.add_apply]
    ring

theorem applyEntry_smul (P : List (List E × 𝕜)) (c : 𝕜) {f : E → 𝕜} (hf : ContDiff ℝ ∞ f) :
    applyEntry P (c • f) = c • applyEntry P f := by
  funext x
  induction P with
  | nil => simp [applyEntry]
  | cons t P ih =>
    simp only [applyEntry, List.map_cons, List.sum_cons, Pi.smul_apply, smul_eq_mul] at ih ⊢
    rw [ih, iterDeriv_smul c hf]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem apply_add [Fintype ι] (A : ConstCoeffOp E 𝕜 ι κ) {f g : ι → E → 𝕜} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) : A.apply (f + g) = A.apply f + A.apply g := by
  funext j x
  simp only [apply, Pi.add_apply, applyEntry_add _ (hf _) (hg _), ← Finset.sum_add_distrib]

theorem apply_smul [Fintype ι] (A : ConstCoeffOp E 𝕜 ι κ) (c : 𝕜) {f : ι → E → 𝕜}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) : A.apply (c • f) = c • A.apply f := by
  funext j x
  simp only [apply, Pi.smul_apply, applyEntry_smul _ c (hf _), smul_eq_mul, Finset.mul_sum]

theorem apply_zero [Fintype ι] (A : ConstCoeffOp E 𝕜 ι κ) : A.apply 0 = 0 := by
  have := A.apply_smul 0 (f := 0) fun _ => contDiff_const
  simpa using this

end Smooth

/-! ### Green's formula -/

section Green

variable [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] in
theorem _root_.Feec.Domain.IsTest.integrable_conj_mul {Ω : Set E} {f g : E → 𝕜}
    (hf : IsTest Ω f) (hg : Continuous g) : Integrable (fun x => conj (f x) * g x) :=
  (hf.conjugate.continuous.mul hg).integrable_of_hasCompactSupport
    hf.conjugate.hasCompactSupport.mul_right

/-- Green's formula for a scalar entry of order `≤ N`, against a `C^N` function with no
boundary condition. -/
theorem integral_conj_applyEntry_mul {N : ℕ} (P : List (List E × 𝕜))
    (hP : ∀ t ∈ P, t.1.length ≤ N) {Ω : Set E} {f g : E → 𝕜} (hf : IsTest Ω f)
    (hg : ContDiff ℝ N g) :
    ∫ x, conj (applyEntry P f x) * g x = ∫ x, conj (f x) * applyEntry (adjEntry P) g x := by
  induction P with
  | nil => simp [adjEntry]
  | cons t P ih =>
    obtain ⟨vs, c⟩ := t
    have hvs : vs.length ≤ N := hP _ List.mem_cons_self
    have hP' : ∀ t ∈ P, t.1.length ≤ N := fun t ht => hP t (List.mem_cons_of_mem _ ht)
    have hPadj : ∀ t ∈ adjEntry P, t.1.length ≤ N := by
      intro t ht
      simp only [adjEntry, List.mem_map] at ht
      obtain ⟨t', ht', rfl⟩ := ht
      simpa using hP' t' ht'
    have e1 : (fun x => conj (applyEntry ((vs, c) :: P) f x) * g x) = fun x =>
        conj c * (conj (iterDeriv vs f x) * g x) + conj (applyEntry P f x) * g x := by
      funext x; rw [applyEntry_cons]; simp only [_root_.map_add, _root_.map_mul]; ring
    have e2 : (fun x => conj (f x) * applyEntry (adjEntry ((vs, c) :: P)) g x) = fun x =>
        (-1) ^ vs.length * conj c * (conj (f x) * iterDeriv vs.reverse g x) +
          conj (f x) * applyEntry (adjEntry P) g x := by
      funext x; simp only [adjEntry, List.map_cons]; rw [applyEntry_cons]; ring
    rw [e1, e2, integral_add, integral_add, integral_const_mul, integral_const_mul,
      integral_conj_iterDeriv_mul hf vs (hg.of_le (by exact_mod_cast hvs)), ih hP']
    · ring
    · exact (hf.integrable_conj_mul (contDiff_iterDeriv_of_le hg vs.reverse (M := 0)
        (by simpa using hvs)).continuous).const_mul _
    · exact hf.integrable_conj_mul (continuous_applyEntry _ hPadj hg)
    · exact ((hf.iterDeriv vs).integrable_conj_mul hg.continuous).const_mul _
    · exact (hf.applyEntry P).integrable_conj_mul hg.continuous

variable [Fintype ι] [Fintype κ]

/-- **Green's formula** for a constant-coefficient operator of order `≤ N`, against a `C^N`
field `ψ` on `E` with **no boundary condition**:
`Σⱼ ∫ conj (A φ)ⱼ ψⱼ = Σᵢ ∫ conj φᵢ (Aᵗ ψ)ᵢ` for `φ ∈ C_c^∞`. -/
theorem green (A : ConstCoeffOp E 𝕜 ι κ) {N : ℕ} (hA : A.IsOrderLE N) {Ω : Set E}
    {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) {ψ : κ → E → 𝕜} (hψ : ∀ j, ContDiff ℝ N (ψ j)) :
    ∑ j, ∫ x, conj (A.apply φ j x) * ψ j x =
      ∑ i, ∫ x, conj (φ i x) * A.formalAdj.apply ψ i x := by
  have hL : ∀ j, ∫ x, conj (A.apply φ j x) * ψ j x =
      ∑ i, ∫ x, conj (applyEntry (A.coeff j i) (φ i) x) * ψ j x := by
    intro j
    rw [← integral_finsetSum _ fun i _ =>
      (IsTest.applyEntry _ (hφ i)).integrable_conj_mul (hψ j).continuous]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [apply, map_sum, Finset.sum_mul]
  have hR : ∀ i, ∫ x, conj (φ i x) * A.formalAdj.apply ψ i x =
      ∑ j, ∫ x, conj (φ i x) * applyEntry (adjEntry (A.coeff j i)) (ψ j) x := by
    intro i
    rw [← integral_finsetSum _ fun j _ =>
      (hφ i).integrable_conj_mul
        (continuous_applyEntry (adjEntry (A.coeff j i)) (hA.formalAdj i j) (hψ j))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [apply, formalAdj, Finset.mul_sum]
  simp only [hL, hR]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    integral_conj_applyEntry_mul _ (hA j i) (hφ i) (hψ j)

/-- Green's formula against a smooth field `ψ` on `E` (no boundary condition). -/
theorem green_smooth (A : ConstCoeffOp E 𝕜 ι κ) {Ω : Set E} {φ : ι → E → 𝕜}
    (hφ : IsTestField Ω φ) {ψ : κ → E → 𝕜} (hψ : ∀ j, ContDiff ℝ ∞ (ψ j)) :
    ∑ j, ∫ x, conj (A.apply φ j x) * ψ j x =
      ∑ i, ∫ x, conj (φ i x) * A.formalAdj.apply ψ i x :=
  A.green A.isOrderLE_order hφ fun j => (hψ j).of_le (by exact_mod_cast le_top)

end Green

/-! ### The minimal and maximal realizations in `L²(Ω)` -/

section Realization

variable [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] [Fintype ι] [Fintype κ] {Ω : Set E}

/-- A smooth field with `L²(Ω)` components, as an element of `L²(Ω; 𝕜^ι)`. -/
def _root_.Feec.Domain.toL2F {ψ : ι → E → 𝕜} (hψ : ∀ i, MemLp (ψ i) 2 (volume.restrict Ω)) :
    L2F 𝕜 Ω ι :=
  WithLp.toLp 2 fun i => (hψ i).toLp (ψ i)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem _root_.Feec.Domain.inner_toL2F (u : L2F 𝕜 Ω ι) {ψ : ι → E → 𝕜}
    (hψ : ∀ i, MemLp (ψ i) 2 (volume.restrict Ω)) :
    ⟪u, toL2F hψ⟫_𝕜 = ∑ i, ∫ x, conj (u i x) * ψ i x ∂volume.restrict Ω := by
  rw [L2F.inner_def]
  exact Finset.sum_congr rfl fun i _ => inner_toLp _ (hψ i)

omit [FiniteDimensional ℝ E] [Fintype ι] in
theorem _root_.Feec.Domain.testField_eq_toL2F {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) :
    testField hφ = toL2F fun i => (hφ i).memLp := rfl

omit [FiniteDimensional ℝ E] in
/-- `⟪φ, ψ⟫_{L²(Ω)} = Σᵢ ∫_E conj φᵢ ψᵢ` for a test field `φ` (the integrand vanishes off `Ω`). -/
theorem _root_.Feec.Domain.inner_testField_toL2F {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ)
    {ψ : ι → E → 𝕜} (hψ : ∀ i, MemLp (ψ i) 2 (volume.restrict Ω)) :
    ⟪testField hφ, toL2F hψ⟫_𝕜 = ∑ i, ∫ x, conj (φ i x) * ψ i x := by
  rw [inner_toL2F]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_restrict_of_eq_zero (Ω := Ω) fun x hx => by
    rw [(hφ i).eq_zero_of_notMem hx, map_zero, zero_mul]]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_testField hφ i] with x hx
  rw [hx]

omit [FiniteDimensional ℝ E] [Fintype ι] in
theorem _root_.Feec.Domain.testField_congr {φ φ' : ι → E → 𝕜} (hφ : IsTestField Ω φ)
    (hφ' : IsTestField Ω φ') (h : φ = φ') : testField hφ = testField hφ' := by
  subst h; rfl

variable (A : ConstCoeffOp E 𝕜 ι κ)

variable (Ω) in
/-- The graph `{(φ, A φ) : φ ∈ C_c^∞(Ω; 𝕜^ι)}` in `L²(Ω; 𝕜^ι) × L²(Ω; 𝕜^κ)`. -/
def testGraph : Submodule 𝕜 (L2F 𝕜 Ω ι × L2F 𝕜 Ω κ) where
  carrier := {p | ∃ φ : ι → E → 𝕜, ∃ hφ : IsTestField Ω φ,
    p = (testField hφ, testField (A.isTestField_apply hφ))}
  zero_mem' := ⟨0, IsTestField.zero, by
    rw [testField_zero, testField_congr _ IsTestField.zero A.apply_zero, testField_zero]; rfl⟩
  add_mem' := by
    rintro _ _ ⟨φ, hφ, rfl⟩ ⟨ψ, hψ, rfl⟩
    refine ⟨φ + ψ, hφ.add hψ, ?_⟩
    rw [testField_add, testField_congr _ ((A.isTestField_apply hφ).add (A.isTestField_apply hψ))
      (A.apply_add (fun i => (hφ i).contDiff) fun i => (hψ i).contDiff), testField_add]
    rfl
  smul_mem' := by
    rintro c _ ⟨φ, hφ, rfl⟩
    refine ⟨c • φ, hφ.smul c, ?_⟩
    rw [testField_smul, testField_congr _ ((A.isTestField_apply hφ).smul c)
      (A.apply_smul c fun i => (hφ i).contDiff), testField_smul]
    rfl

/-- Green's formula in `L²(Ω)` for test fields against smooth `L²(Ω)` fields. -/
theorem inner_testField_apply {N : ℕ} (hA : A.IsOrderLE N) {φ : ι → E → 𝕜}
    (hφ : IsTestField Ω φ) {ψ : κ → E → 𝕜}
    (hψs : ∀ j, ContDiff ℝ N (ψ j)) (hψ : ∀ j, MemLp (ψ j) 2 (volume.restrict Ω))
    (hAψ : ∀ i, MemLp (A.formalAdj.apply ψ i) 2 (volume.restrict Ω)) :
    ⟪testField (A.isTestField_apply hφ), toL2F hψ⟫_𝕜 = ⟪testField hφ, toL2F hAψ⟫_𝕜 := by
  rw [inner_testField_toL2F, inner_testField_toL2F]
  exact A.green hA hφ hψs

/-- Green's formula in `L²(Ω)` between test fields: `⟪A φ, ψ⟫ = ⟪φ, Aᵗ ψ⟫`. -/
theorem inner_testField_apply_testField {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ)
    {ψ : κ → E → 𝕜} (hψ : IsTestField Ω ψ) :
    ⟪testField (A.isTestField_apply hφ), testField hψ⟫_𝕜 =
      ⟪testField hφ, testField (A.formalAdj.isTestField_apply hψ)⟫_𝕜 :=
  A.inner_testField_apply A.isOrderLE_order hφ
    (fun j => (hψ j).contDiff.of_le (by exact_mod_cast le_top)) _ _

/-- The graph-closure identity: for `(u, w)` in the closure of the test graph and a `C^N` field
`ψ` on `E` (`N ≥` the order of `A`) with `ψ, Aᵗ ψ ∈ L²(Ω)` (no boundary condition),
`⟪w, ψ⟫ = ⟪u, Aᵗ ψ⟫`. -/
theorem closure_testGraph_inner {N : ℕ} (hA : A.IsOrderLE N) {u : L2F 𝕜 Ω ι} {w : L2F 𝕜 Ω κ}
    (h : (u, w) ∈ (A.testGraph Ω).topologicalClosure) {ψ : κ → E → 𝕜}
    (hψs : ∀ j, ContDiff ℝ N (ψ j)) (hψ : ∀ j, MemLp (ψ j) 2 (volume.restrict Ω))
    (hAψ : ∀ i, MemLp (A.formalAdj.apply ψ i) 2 (volume.restrict Ω)) :
    ⟪w, toL2F hψ⟫_𝕜 = ⟪u, toL2F hAψ⟫_𝕜 := by
  let S : Set (L2F 𝕜 Ω ι × L2F 𝕜 Ω κ) :=
    {p | ⟪p.2, toL2F hψ⟫_𝕜 = ⟪p.1, toL2F hAψ⟫_𝕜}
  have hS : IsClosed S := isClosed_eq (continuous_snd.inner continuous_const)
    (continuous_fst.inner continuous_const)
  have hsub : (A.testGraph Ω : Set _) ⊆ S := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact A.inner_testField_apply hA hφ hψs hψ hAψ
  exact closure_minimal hsub hS h

/-- The graph-closure identity against test fields. -/
theorem closure_testGraph_inner_testField {u : L2F 𝕜 Ω ι} {w : L2F 𝕜 Ω κ}
    (h : (u, w) ∈ (A.testGraph Ω).topologicalClosure) {φ : κ → E → 𝕜} (hφ : IsTestField Ω φ) :
    ⟪w, testField hφ⟫_𝕜 = ⟪u, testField (A.formalAdj.isTestField_apply hφ)⟫_𝕜 :=
  A.closure_testGraph_inner A.isOrderLE_order h
    (fun j => (hφ j).contDiff.of_le (by exact_mod_cast le_top)) _ _

/-- `A` on `C_c^∞(Ω)` is closable. -/
theorem testGraph_closable (hΩ : IsOpen Ω) :
    ∀ x ∈ (A.testGraph Ω).topologicalClosure, x.1 = 0 → x.2 = 0 := by
  rintro ⟨u, w⟩ hx (h0 : u = 0)
  subst h0
  refine L2F.eq_zero_of_forall_inner_testField hΩ w fun φ hφ => ?_
  rw [A.closure_testGraph_inner_testField hx hφ, inner_zero_left]

variable (Ω) in
/-- The **minimal realization** `A_min` of `A` in `L²(Ω)`: the closure of `A` on `C_c^∞(Ω)`
(the `H̊` boundary condition). -/
def minimal : L2F 𝕜 Ω ι →ₗ.[𝕜] L2F 𝕜 Ω κ := (A.testGraph Ω).topologicalClosure.toLinearPMap

theorem minimal_graph (hΩ : IsOpen Ω) :
    (A.minimal Ω).graph = (A.testGraph Ω).topologicalClosure :=
  Submodule.toLinearPMap_graph_eq _ (A.testGraph_closable hΩ)

theorem mem_closure_minimal (hΩ : IsOpen Ω) (u : (A.minimal Ω).domain) :
    ((u : L2F 𝕜 Ω ι), A.minimal Ω u) ∈ (A.testGraph Ω).topologicalClosure :=
  Submodule.mem_graph_toLinearPMap (A.testGraph_closable hΩ) u

theorem isClosed_minimal (hΩ : IsOpen Ω) : (A.minimal Ω).IsClosed := by
  rw [LinearPMap.IsClosed, A.minimal_graph hΩ]
  exact Submodule.isClosed_topologicalClosure _

theorem testField_mem_graph_minimal (hΩ : IsOpen Ω) {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) :
    (testField hφ, testField (A.isTestField_apply hφ)) ∈ (A.minimal Ω).graph := by
  rw [A.minimal_graph hΩ]
  exact Submodule.le_topologicalClosure _ ⟨φ, hφ, rfl⟩

theorem testField_mem_minimal_domain (hΩ : IsOpen Ω) {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) :
    testField hφ ∈ (A.minimal Ω).domain :=
  LinearPMap.mem_domain_of_mem_graph (A.testField_mem_graph_minimal hΩ hφ)

/-- On test fields the minimal realization is the classical operator. -/
theorem minimal_testField (hΩ : IsOpen Ω) {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) :
    A.minimal Ω ⟨testField hφ, A.testField_mem_minimal_domain hΩ hφ⟩ =
      testField (A.isTestField_apply hφ) :=
  ((LinearPMap.image_iff _).2 (A.testField_mem_graph_minimal hΩ hφ)).symm

theorem testFieldSub_le_minimal_domain (hΩ : IsOpen Ω) :
    testFieldSub 𝕜 Ω ι ≤ (A.minimal Ω).domain := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact A.testField_mem_minimal_domain hΩ hφ

theorem dense_minimal_domain (hΩ : IsOpen Ω) :
    Dense ((A.minimal Ω).domain : Set (L2F 𝕜 Ω ι)) :=
  (dense_testFieldSub hΩ ι).mono (A.testFieldSub_le_minimal_domain hΩ)

/-- Green's formula on `D(A_min)` against smooth fields with **no boundary condition**:
`⟪A_min u, ψ⟫ = ⟪u, Aᵗ ψ⟫` whenever `ψ, Aᵗ ψ ∈ L²(Ω)` (e.g. `Ω` bounded). This is the boundary
term `∫_{∂Ω}` vanishing for the `H̊` boundary condition. -/
theorem minimal_green (hΩ : IsOpen Ω) {N : ℕ} (hA : A.IsOrderLE N) (u : (A.minimal Ω).domain)
    {ψ : κ → E → 𝕜} (hψs : ∀ j, ContDiff ℝ N (ψ j)) (hψ : ∀ j, MemLp (ψ j) 2 (volume.restrict Ω))
    (hAψ : ∀ i, MemLp (A.formalAdj.apply ψ i) 2 (volume.restrict Ω)) :
    ⟪A.minimal Ω u, toL2F hψ⟫_𝕜 = ⟪(u : L2F 𝕜 Ω ι), toL2F hAψ⟫_𝕜 :=
  A.closure_testGraph_inner hA (A.mem_closure_minimal hΩ u) hψs hψ hAψ

/-- An identity tested on `C_c^∞` extends to `D(A_min)`. -/
theorem inner_minimal_of_forall_testField (hΩ : IsOpen Ω) {w : L2F 𝕜 Ω ι} {u : L2F 𝕜 Ω κ}
    (h : ∀ φ : ι → E → 𝕜, ∀ hφ : IsTestField Ω φ,
      ⟪w, testField hφ⟫_𝕜 = ⟪u, testField (A.isTestField_apply hφ)⟫_𝕜)
    (x : (A.minimal Ω).domain) : ⟪w, (x : L2F 𝕜 Ω ι)⟫_𝕜 = ⟪u, A.minimal Ω x⟫_𝕜 := by
  let S : Set (L2F 𝕜 Ω ι × L2F 𝕜 Ω κ) := {p | ⟪w, p.1⟫_𝕜 = ⟪u, p.2⟫_𝕜}
  have hS : IsClosed S := isClosed_eq (continuous_const.inner continuous_fst)
    (continuous_const.inner continuous_snd)
  have hsub : (A.testGraph Ω : Set _) ⊆ S := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact h φ hφ
  exact closure_minimal hsub hS (A.mem_closure_minimal hΩ x)

variable (Ω) in
/-- The **maximal (weak) realization** `A_max = ((Aᵗ)_min)†` of `A` in `L²(Ω)`: `u ∈ D(A_max)`
iff `A u ∈ L²(Ω)` in the sense of distributions on `Ω`, with no boundary condition
(`mem_maximal_domain_iff`). -/
def maximal : L2F 𝕜 Ω ι →ₗ.[𝕜] L2F 𝕜 Ω κ := (A.formalAdj.minimal Ω)†

/-- **`D(A_max)` is the weak domain**: `u ∈ D(A_max)` iff there is `w ∈ L²(Ω)` with
`⟪w, φ⟫ = ⟪u, Aᵗ φ⟫` for all `φ ∈ C_c^∞(Ω)`; then `A_max u = w`. -/
theorem mem_maximal_domain_iff (hΩ : IsOpen Ω) {u : L2F 𝕜 Ω ι} :
    u ∈ (A.maximal Ω).domain ↔ ∃ w : L2F 𝕜 Ω κ, ∀ φ : κ → E → 𝕜, ∀ hφ : IsTestField Ω φ,
      ⟪w, testField hφ⟫_𝕜 = ⟪u, testField (A.formalAdj.isTestField_apply hφ)⟫_𝕜 := by
  constructor
  · intro hu
    refine ⟨A.maximal Ω ⟨u, hu⟩, fun φ hφ => ?_⟩
    have := LinearPMap.adjoint_isFormalAdjoint (A.formalAdj.dense_minimal_domain hΩ) ⟨u, hu⟩
      ⟨_, A.formalAdj.testField_mem_minimal_domain hΩ hφ⟩
    rw [A.formalAdj.minimal_testField hΩ hφ] at this
    exact this
  · rintro ⟨w, hw⟩
    exact LinearPMap.mem_adjoint_domain_of_exists _
      ⟨w, A.formalAdj.inner_minimal_of_forall_testField hΩ hw⟩

/-- The value of `A_max` is the weak `A`. -/
theorem maximal_apply_eq (hΩ : IsOpen Ω) (u : (A.maximal Ω).domain) {w : L2F 𝕜 Ω κ}
    (hw : ∀ φ : κ → E → 𝕜, ∀ hφ : IsTestField Ω φ,
      ⟪w, testField hφ⟫_𝕜 = ⟪(u : L2F 𝕜 Ω ι), testField (A.formalAdj.isTestField_apply hφ)⟫_𝕜) :
    A.maximal Ω u = w :=
  LinearPMap.adjoint_apply_eq (A.formalAdj.dense_minimal_domain hΩ) u
    (A.formalAdj.inner_minimal_of_forall_testField hΩ hw)

/-- The defining identity of `A_max` against test fields. -/
theorem maximal_inner_testField (hΩ : IsOpen Ω) (u : (A.maximal Ω).domain) {φ : κ → E → 𝕜}
    (hφ : IsTestField Ω φ) :
    ⟪A.maximal Ω u, testField hφ⟫_𝕜 =
      ⟪(u : L2F 𝕜 Ω ι), testField (A.formalAdj.isTestField_apply hφ)⟫_𝕜 := by
  have := LinearPMap.adjoint_isFormalAdjoint (A.formalAdj.dense_minimal_domain hΩ) u
    ⟨_, A.formalAdj.testField_mem_minimal_domain hΩ hφ⟩
  rw [A.formalAdj.minimal_testField hΩ hφ] at this
  exact this

theorem isClosed_maximal (hΩ : IsOpen Ω) : (A.maximal Ω).IsClosed :=
  LinearPMap.adjoint_isClosed (A.formalAdj.dense_minimal_domain hΩ)

/-- `(Aᵗ)_min` and `A_min` are formal adjoints. -/
theorem isFormalAdjoint_minimal (hΩ : IsOpen Ω) :
    (A.formalAdj.minimal Ω).IsFormalAdjoint (A.minimal Ω) := by
  intro x y
  have h := A.formalAdj.inner_minimal_of_forall_testField hΩ (w := A.minimal Ω y)
    (u := (y : L2F 𝕜 Ω ι)) (fun φ hφ => A.closure_testGraph_inner_testField
      (A.mem_closure_minimal hΩ y) hφ) x
  rw [← inner_conj_symm, ← h, inner_conj_symm]

/-- `A_min ≤ A_max`. -/
theorem minimal_le_maximal (hΩ : IsOpen Ω) : A.minimal Ω ≤ A.maximal Ω :=
  (A.isFormalAdjoint_minimal hΩ).le_adjoint (A.formalAdj.dense_minimal_domain hΩ)

theorem dense_maximal_domain (hΩ : IsOpen Ω) :
    Dense ((A.maximal Ω).domain : Set (L2F 𝕜 Ω ι)) :=
  (A.dense_minimal_domain hΩ).mono (A.minimal_le_maximal hΩ).1

omit [FiniteDimensional ℝ E] in
/-- **`(A_min)† = (Aᵗ)_max`.** -/
theorem adjoint_minimal : (A.minimal Ω)† = A.formalAdj.maximal Ω := by
  rw [maximal, formalAdj_formalAdj]

/-- **`(A_max)† = (Aᵗ)_min`** (von Neumann). -/
theorem adjoint_maximal (hΩ : IsOpen Ω) : (A.maximal Ω)† = A.formalAdj.minimal Ω :=
  LinearPMap.adjoint_adjoint _ (A.formalAdj.dense_minimal_domain hΩ)
    (A.formalAdj.isClosed_minimal hΩ)

omit [FiniteDimensional ℝ E] [Fintype κ] in
theorem testField_formalAdj_formalAdj {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) :
    testField (A.formalAdj.formalAdj.isTestField_apply hφ) = testField (A.isTestField_apply hφ) :=
  testField_congr _ _ (by rw [formalAdj_formalAdj])

/-- **`D((A_min)†)` is the weak domain of `Aᵗ`**: `v ∈ D((A_min)†)` iff there is `w` with
`⟪w, φ⟫ = ⟪v, A φ⟫` for all `φ ∈ C_c^∞(Ω)` (no boundary condition on `v`). -/
theorem mem_adjoint_minimal_domain_iff (hΩ : IsOpen Ω) {v : L2F 𝕜 Ω κ} :
    v ∈ (A.minimal Ω)†.domain ↔ ∃ w : L2F 𝕜 Ω ι, ∀ φ : ι → E → 𝕜, ∀ hφ : IsTestField Ω φ,
      ⟪w, testField hφ⟫_𝕜 = ⟪v, testField (A.isTestField_apply hφ)⟫_𝕜 := by
  rw [A.adjoint_minimal, A.formalAdj.mem_maximal_domain_iff hΩ]
  refine exists_congr fun w => forall_congr' fun φ => forall_congr' fun hφ => ?_
  rw [A.testField_formalAdj_formalAdj hφ]

/-- The value of `(A_min)†` is the weak `Aᵗ`. -/
theorem adjoint_minimal_apply_eq (hΩ : IsOpen Ω) (v : (A.minimal Ω)†.domain) {w : L2F 𝕜 Ω ι}
    (hw : ∀ φ : ι → E → 𝕜, ∀ hφ : IsTestField Ω φ,
      ⟪w, testField hφ⟫_𝕜 = ⟪(v : L2F 𝕜 Ω κ), testField (A.isTestField_apply hφ)⟫_𝕜) :
    (A.minimal Ω)† v = w :=
  LinearPMap.adjoint_apply_eq (A.dense_minimal_domain hΩ) v (A.inner_minimal_of_forall_testField hΩ hw)

/-- The defining identity of `(A_min)†` against test fields. -/
theorem adjoint_minimal_inner_testField (hΩ : IsOpen Ω) (v : (A.minimal Ω)†.domain)
    {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) :
    ⟪(A.minimal Ω)† v, testField hφ⟫_𝕜 = ⟪(v : L2F 𝕜 Ω κ), testField (A.isTestField_apply hφ)⟫_𝕜 := by
  have := LinearPMap.adjoint_isFormalAdjoint (A.dense_minimal_domain hΩ) v
    ⟨_, A.testField_mem_minimal_domain hΩ hφ⟩
  rw [A.minimal_testField hΩ hφ] at this
  exact this

/-- `C^N` fields (`N ≥` the order of `A`) with `ψ, A ψ ∈ L²(Ω)` lie in `D(A_max)` (no boundary condition), and
`A_max ψ = A ψ`. -/
theorem smooth_mem_maximal_domain (hΩ : IsOpen Ω) {N : ℕ} (hA : A.IsOrderLE N)
    {ψ : ι → E → 𝕜} (hψs : ∀ i, ContDiff ℝ N (ψ i)) (hψ : ∀ i, MemLp (ψ i) 2 (volume.restrict Ω))
    (hAψ : ∀ j, MemLp (A.apply ψ j) 2 (volume.restrict Ω)) :
    ∃ h : toL2F hψ ∈ (A.maximal Ω).domain, A.maximal Ω ⟨_, h⟩ = toL2F hAψ := by
  have key : ∀ φ : κ → E → 𝕜, ∀ hφ : IsTestField Ω φ, ⟪toL2F hAψ, testField hφ⟫_𝕜 =
      ⟪toL2F hψ, testField (A.formalAdj.isTestField_apply hφ)⟫_𝕜 := by
    intro φ hφ
    have hAψ' : ∀ j, MemLp (A.formalAdj.formalAdj.apply ψ j) 2 (volume.restrict Ω) := by
      simpa using hAψ
    have e := A.formalAdj.inner_testField_apply hA.formalAdj hφ hψs hψ hAψ'
    rw [← inner_conj_symm, ← inner_conj_symm (toL2F hψ), e]
    congr 2
    exact (WithLp.ext_iff 2).2 (funext fun j => by simp [toL2F])
  have hmem := (A.mem_maximal_domain_iff hΩ).2 ⟨_, key⟩
  exact ⟨hmem, A.maximal_apply_eq hΩ ⟨_, hmem⟩ key⟩

end Realization

end ConstCoeffOp

end Feec.Domain
