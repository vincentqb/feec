module

public import Feec.FiniteElement.LocalSpace
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Degrees of freedom of `P_rΛᵏ(T)` and `P_r⁻Λᵏ(T)`: unisolvence and commuting interpolants

For an `n`-simplex `T` in `ℝⁿ` (vertices `p`, invertible edge matrix) the degrees of freedom of
the FEEC spaces are the moments

  `ω ↦ ∫_f tr_f ω ∧ η`,

over the faces `f` of `T` of dimension `m ≥ k`, with `η` in a basis of the test space
`P⁻_{r+k-m}Λ^{m-k}(f)` for `P_rΛᵏ(T)` and `P_{r+k-m-1}Λ^{m-k}(f)` for `P_r⁻Λᵏ(T)` (zero unless
`m < r + k`). Here `f = p ∘ e` with its vertices in increasing order, `tr_f` is the pullback
along the parametrization `F_f : T̂_m → f`, and `∫_f` is the integral over `T̂_m`
([AFW2006], §4.5–4.6, §4.9; [AFW2010], §5.2; [Arnold2018], Ch. 7).

## Main definitions

* `Feec.FiniteElement.Face n`: faces of an `n`-simplex (dimension and vertex set);
* `Feec.FiniteElement.testSpace r k m`, `testSpaceMinus r k m`: the test forms on `m`-faces;
* `Feec.FiniteElement.faceMoment p e η ω = ∫_{T̂_m} tr_{p ∘ e} ω ∧ η`;
* `Feec.FiniteElement.localDof p r k`, `localDofMinus p r k`: the degrees of freedom of
  `P_rΛᵏ(T)` and `P_r⁻Λᵏ(T)`;
* `Feec.FiniteElement.SimplexElement p`: a local finite element (shape functions, degrees of
  freedom attached to faces, unisolvence, trace determination), and its instances
  `polySimplexElement`, `polyMinusSimplexElement`;
* `Feec.FiniteElement.polyInterp`, `polyMinusInterp`: the canonical interpolants on continuous
  `k`-forms.

## Main results

* `card_dofIndex`, `card_dofIndexMinus`: **the number of degrees of freedom is the dimension**
  ([AFW2006], Thms 4.9, 4.13), via `sum_choose_mul_choose_eq` (Vandermonde);
* `eq_zero_of_faceMoment_eq_zero`, `eq_zero_of_faceMoment_eq_zero_minus`: vanishing degrees of
  freedom force `ω = 0` on `T̂` ([AFW2006], Thms 4.8, 4.12; induction on the dimension of the
  faces, with [AFW2006], Lemmas 4.7, 4.11 for the bubbles), and their versions on `T`;
* `isUnisolvent_localDof`, `isUnisolvent_localDofMinus`: **unisolvence for all `r ≥ 1`,
  `0 ≤ k ≤ n`** ([AFW2006], Thms 4.10, 4.14; [AFW2010], Thm 5.5);
* `faceTrace_eq_of_localDof_eq`, `faceTrace_eq_of_localDofMinus_eq`: **the degrees of freedom on
  a face and its subfaces determine the trace on that face**;
* `finrank_bubbleSpace_polySpace`, `finrank_bubbleSpace_polyMinusSpace`: `dim P̊_rΛᵏ(T̂)` and
  `dim P̊_r⁻Λᵏ(T̂)` are the dimensions of the top-face test spaces ([AFW2010], Lemma 5.6);
* `faceMoment_extDeriv`: Stokes' formula for moments, from the Leibniz rule
  `extDeriv_wedgeField_apply` and `Feec.FiniteElement.setIntegral_refSimplex_extDeriv`;
* `polyInterp_extDeriv`, `polyMinusInterp_extDeriv`: **the commuting property**
  `Π_T dω = d Π_T ω` for `C¹` `k`-forms, `P_{r+1}Λᵏ(T) → P_rΛ^{k+1}(T)` and
  `P_r⁻Λᵏ(T) → P_r⁻Λ^{k+1}(T)` ([AFW2006], §4.9, Lemma 4.24), from
  `Feec.FiniteElement.interp_comp_eq`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §4.5–4.6 (Thms 4.8–4.14), §4.9 (Lemma 4.24)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.2 (Thm 5.5, Lemma 5.6)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MeasureTheory MvPolynomial

@[expose] public noncomputable section

namespace Feec.FiniteElement

open ExteriorFibre

variable {n : ℕ}

/-! ### Faces -/

/-- A face of an `n`-simplex: its dimension `m ≤ n` and its `m + 1` vertices. -/
abbrev Face (n : ℕ) := Σ m : Fin (n + 1), {f : Finset (Fin (n + 1)) // #f = m + 1}

/-- The dimension of a face. -/
abbrev Face.dim (f : Face n) : ℕ := f.1

/-- The vertices of a face, in increasing order. -/
def Face.emb (f : Face n) : Fin (f.dim + 1) ↪o Fin (n + 1) := f.2.1.orderEmbOfFin f.2.2

/-- The face spanned by the vertices `e(0) < ⋯ < e(m)`. -/
abbrev Face.ofEmb {m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1)) : Face n :=
  ⟨⟨m, by have := Fintype.card_le_of_injective e e.injective; simp at this; omega⟩,
    ⟨univ.map e.toEmbedding, by simp⟩⟩

@[simp] theorem Face.dim_ofEmb {m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1)) :
    (Face.ofEmb e).dim = m := rfl

theorem Face.emb_ofEmb {m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1)) : (Face.ofEmb e).emb = e := by
  refine DFunLike.ext' (orderEmbOfFin_unique _ (fun x => ?_) e.strictMono).symm
  simp

/-- `Σ_f g(dim f) = Σ_m (n+1 choose m+1) g(m)`. -/
theorem sum_face_eq {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ f : Face n, g f.dim = ∑ m ∈ range (n + 1), (n + 1).choose (m + 1) • g m := by
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun m _ => ?_
  change ∑ _y : {f : Finset (Fin (n + 1)) // #f = m + 1}, g m = _
  rw [sum_const, card_univ, Fintype.card_finset_len, Fintype.card_fin]

/-- The binomial identity behind the dimension count of the degrees of freedom ([AFW2006],
Thm 4.9): `Σ_{m=k}^{n} (n+1 choose m+1) (r-1 choose m-k) = (n + r choose n - k)`. -/
theorem sum_choose_mul_choose_eq {n r k : ℕ} (hk : k ≤ n) (hr : 1 ≤ r) :
    ∑ m ∈ range (n + 1), (n + 1).choose (m + 1) *
      (if k ≤ m ∧ m < r + k then (r - 1).choose (m - k) else 0) = (n + r).choose (n - k) := by
  have h1 : ∀ m ∈ range (n + 1), (n + 1).choose (m + 1) *
      (if k ≤ m ∧ m < r + k then (r - 1).choose (m - k) else 0) =
      if k ≤ m then (n + 1).choose (m + 1) * (r - 1).choose (m - k) else 0 := by
    intro m _
    by_cases hkm : k ≤ m
    · by_cases hmr : m < r + k
      · simp [hkm, hmr]
      · simp [hkm, hmr, Nat.choose_eq_zero_of_lt (show r - 1 < m - k by omega)]
    · simp [hkm]
  rw [sum_congr rfl h1, ← sum_filter, show (range (n + 1)).filter (fun m => k ≤ m) = Ico k (n + 1)
    by ext m; simp; omega, sum_Ico_eq_sum_range,
    show n + r = (r - 1) + (n + 1) by omega, Nat.add_choose_eq,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, show n + 1 - k = (n - k).succ by omega]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n - k := by simp at hi; omega
  rw [mul_comm, show k + i - k = i by omega]
  congr 1
  exact Nat.choose_symm_of_eq_add (by omega)

/-! ### Dimensions of the polynomial form fields -/

theorem finrank_polySpace (m s j : ℕ) :
    Module.finrank ℝ (polySpace m s j) = (s + m).choose (s + j) * (s + j).choose j := by
  rw [polySpace, Koszul.finrank_map_of_injOn _ _ fun x _ hx =>
      evalForm_injective (by rw [hx, map_zero]),
    Koszul.finrank_polyForm, Fintype.card_fin]

theorem finrank_polyMinusSpace (m : ℕ) {s : ℕ} (hs : 1 ≤ s) (j : ℕ) :
    Module.finrank ℝ (polyMinusSpace m s j) = (s + m).choose (s + j) * (s + j - 1).choose j := by
  rw [polyMinusSpace, Koszul.finrank_map_of_injOn _ _ fun x _ hx => evalForm_injective
    (by rw [hx, map_zero]), Koszul.finrank_polyFormMinus hs, Fintype.card_fin]

instance (m s j : ℕ) : FiniteDimensional ℝ (polySpace m s j) := by
  unfold polySpace; infer_instance

instance (m s j : ℕ) : FiniteDimensional ℝ (polyMinusSpace m s j) := by
  unfold polyMinusSpace; infer_instance

theorem contDiff_of_mem_polyMinusSpace {m s j : ℕ} {η : FormField m}
    (h : η ∈ polyMinusSpace m s j) : ContDiff ℝ ⊤ η := by
  obtain ⟨Ω, -, rfl⟩ := h
  exact contDiff_evalForm Ω

/-! ### The spaces of test forms -/

/-- The test forms of the degrees of freedom of `P_rΛᵏ(T)` on an `m`-face:
`P⁻_{r+k-m}Λ^{m-k}(ℝᵐ)` (zero unless `k ≤ m < r + k`). -/
def testSpace (r k m : ℕ) : Submodule ℝ (FormField m) :=
  if k ≤ m ∧ m < r + k then polyMinusSpace m (r + k - m) (m - k) else ⊥

/-- The test forms of the degrees of freedom of `P_r⁻Λᵏ(T)` on an `m`-face:
`P_{r+k-m-1}Λ^{m-k}(ℝᵐ)` (zero unless `k ≤ m < r + k`). -/
def testSpaceMinus (r k m : ℕ) : Submodule ℝ (FormField m) :=
  if k ≤ m ∧ m < r + k then polySpace m (r + k - m - 1) (m - k) else ⊥

theorem testSpace_eq {r k m : ℕ} (h : k ≤ m ∧ m < r + k) :
    testSpace r k m = polyMinusSpace m (r + k - m) (m - k) := by
  simp only [testSpace, h.1, h.2, and_self, ↓reduceIte]

theorem testSpace_eq_bot {r k m : ℕ} (h : ¬(k ≤ m ∧ m < r + k)) : testSpace r k m = ⊥ := by
  simp only [testSpace, h, ↓reduceIte]

theorem testSpaceMinus_eq {r k m : ℕ} (h : k ≤ m ∧ m < r + k) :
    testSpaceMinus r k m = polySpace m (r + k - m - 1) (m - k) := by
  simp only [testSpaceMinus, h.1, h.2, and_self, ↓reduceIte]

theorem testSpaceMinus_eq_bot {r k m : ℕ} (h : ¬(k ≤ m ∧ m < r + k)) :
    testSpaceMinus r k m = ⊥ := by
  simp only [testSpaceMinus, h, ↓reduceIte]

instance (r k m : ℕ) : FiniteDimensional ℝ (testSpace r k m) := by
  by_cases h : k ≤ m ∧ m < r + k
  · rw [testSpace_eq h]; infer_instance
  · rw [testSpace_eq_bot h]; infer_instance

instance (r k m : ℕ) : FiniteDimensional ℝ (testSpaceMinus r k m) := by
  by_cases h : k ≤ m ∧ m < r + k
  · rw [testSpaceMinus_eq h]; infer_instance
  · rw [testSpaceMinus_eq_bot h]; infer_instance

theorem contDiff_of_mem_testSpace {r k m : ℕ} {η : FormField m} (h : η ∈ testSpace r k m) :
    ContDiff ℝ ⊤ η := by
  by_cases hc : k ≤ m ∧ m < r + k
  · rw [testSpace_eq hc] at h; exact contDiff_of_mem_polyMinusSpace h
  · rw [testSpace_eq_bot hc, Submodule.mem_bot] at h; subst h; exact contDiff_const

theorem contDiff_of_mem_testSpaceMinus {r k m : ℕ} {η : FormField m}
    (h : η ∈ testSpaceMinus r k m) : ContDiff ℝ ⊤ η := by
  by_cases hc : k ≤ m ∧ m < r + k
  · rw [testSpaceMinus_eq hc] at h; exact polySpace_le_c1 h
  · rw [testSpaceMinus_eq_bot hc, Submodule.mem_bot] at h; subst h; exact contDiff_const

theorem finrank_testSpace (r k m : ℕ) :
    Module.finrank ℝ (testSpace r k m) =
      (r + k).choose r * if k ≤ m ∧ m < r + k then (r - 1).choose (m - k) else 0 := by
  by_cases h : k ≤ m ∧ m < r + k
  · rw [testSpace_eq h, finrank_polyMinusSpace m (by omega), show r + k - m + m = r + k by omega,
      show r + k - m + (m - k) = r by omega, mul_comm]
    simp only [h.1, h.2, and_self, ↓reduceIte, mul_comm]
  · rw [testSpace_eq_bot h]; simp [h]

theorem finrank_testSpaceMinus {r : ℕ} (hr : 1 ≤ r) (k m : ℕ) :
    Module.finrank ℝ (testSpaceMinus r k m) =
      (r + k - 1).choose (r - 1) * if k ≤ m ∧ m < r + k then (r - 1).choose (m - k) else 0 := by
  by_cases h : k ≤ m ∧ m < r + k
  · rw [testSpaceMinus_eq h, finrank_polySpace, show r + k - m - 1 + m = r + k - 1 by omega,
      show r + k - m - 1 + (m - k) = r - 1 by omega]
    simp only [h.1, h.2, and_self, ↓reduceIte]
  · rw [testSpaceMinus_eq_bot h]; simp [h]

/-! ### Traces of traces and continuity -/

/-- **Traces compose**: the trace on a face `e'` of the reference face of `p ∘ e` is the trace on
the face `p ∘ e ∘ e'`. -/
theorem faceTrace_faceTrace {m m' : ℕ} (p : Fin (n + 1) → Fin n → ℝ)
    (e : Fin (m + 1) → Fin (n + 1)) (e' : Fin (m' + 1) → Fin (m + 1)) (ω : FormField n) :
    faceTrace (refVertex m) e' (faceTrace p e ω) = faceTrace p (e ∘ e') ω := by
  have hq : (p ∘ e ∘ e') = fun i => affine (simplexMatrix (p ∘ e)) (p (e 0))
      ((refVertex m ∘ e') i) := by
    funext i
    exact (simplexMap_refVertex (p ∘ e) (e' i)).symm
  rw [faceTrace_apply, faceTrace_apply, faceTrace_apply, affinePullback_affinePullback]
  congr 1
  · rw [show p ∘ (e ∘ e') = p ∘ e ∘ e' from rfl, hq, simplexMatrix_comp_affine]
  · have := congrFun hq 0
    simp only [Function.comp_apply] at this
    exact this.symm

theorem continuous_affinePullback {m : ℕ} (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ)
    {ω : FormField n} (hω : Continuous ω) : Continuous (affinePullback B b ω) :=
  (contDiff_affinePullback (r := 0) B b (contDiff_zero.2 hω)).continuous

theorem continuous_wedgeField {ω η : FormField n} (hω : Continuous ω) (hη : Continuous η) :
    Continuous (wedgeField ω η) := by
  refine continuous_pi fun u => ?_
  simp only [wedgeField, wedgeForm_apply]
  refine continuous_finsetSum _ fun s _ => ?_
  exact (continuous_const.mul ((continuous_apply s).comp hω)).mul ((continuous_apply _).comp hη)

/-! ### Moments -/

/-- The face trace of a continuous form field is continuous. -/
theorem continuous_faceTrace (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) {ω : FormField n} (hω : Continuous ω) :
    Continuous (faceTrace p e ω) :=
  continuous_affinePullback _ _ hω

/-- The **moment** `ω ↦ ∫_f tr_f ω ∧ η` on the face `f` of `p`, with the test form `η` on the
reference face `T̂_{dim f}` (the face is oriented by its vertex order). -/
def faceMoment (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ} (e : Fin (m + 1) → Fin (n + 1))
    (η : FormField m) (ω : FormField n) : ℝ :=
  simplexIntegral (refVertex m) (wedgeField (faceTrace p e ω) η)

theorem faceMoment_eq_integral (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) (η : FormField m) (ω : FormField n) :
    faceMoment p e η ω = ∫ x in refSimplex m, wedgeField (faceTrace p e ω) η x univ :=
  simplexIntegral_refVertex _

theorem integrableOn_wedgeField {m : ℕ} {ω η : FormField m} (hω : Continuous ω)
    (hη : Continuous η) : IntegrableOn (fun x => wedgeField ω η x univ) (refSimplex m) :=
  ((continuous_apply univ).comp (continuous_wedgeField hω hη)).continuousOn.integrableOn_compact
    (isCompact_refSimplex m)

theorem faceMoment_add_left (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) {η : FormField m} (hη : Continuous η) {ω ω' : FormField n}
    (hω : Continuous ω) (hω' : Continuous ω') :
    faceMoment p e η (ω + ω') = faceMoment p e η ω + faceMoment p e η ω' := by
  simp only [faceMoment_eq_integral]
  rw [← integral_add (integrableOn_wedgeField (continuous_faceTrace p e hω) hη)
    (integrableOn_wedgeField (continuous_faceTrace p e hω') hη)]
  congr 1
  funext x
  simp [wedgeField, wedgeForm_add_left]

theorem faceMoment_smul_left (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) (η : FormField m) (c : ℝ) (ω : FormField n) :
    faceMoment p e η (c • ω) = c • faceMoment p e η ω := by
  simp only [faceMoment_eq_integral, smul_eq_mul, ← integral_const_mul]
  congr 1
  funext x
  simp [wedgeField, wedgeForm_smul_left]

theorem faceMoment_add_right (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) {η η' : FormField m} (hη : Continuous η)
    (hη' : Continuous η') {ω : FormField n} (hω : Continuous ω) :
    faceMoment p e (η + η') ω = faceMoment p e η ω + faceMoment p e η' ω := by
  simp only [faceMoment_eq_integral]
  rw [← integral_add (integrableOn_wedgeField (continuous_faceTrace p e hω) hη)
    (integrableOn_wedgeField (continuous_faceTrace p e hω) hη')]
  congr 1
  funext x
  simp [wedgeField, wedgeForm_add_right]

theorem faceMoment_smul_right (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) (η : FormField m) (c : ℝ) (ω : FormField n) :
    faceMoment p e (c • η) ω = c • faceMoment p e η ω := by
  simp only [faceMoment_eq_integral, smul_eq_mul, ← integral_const_mul]
  congr 1
  funext x
  simp [wedgeField, wedgeForm_smul_right]

/-- The moment as a linear functional on continuous forms. -/
def faceMomentₗ (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ} (e : Fin (m + 1) → Fin (n + 1))
    (η : FormField m) (hη : Continuous η) : contForms n →ₗ[ℝ] ℝ where
  toFun ω := faceMoment p e η ω
  map_add' ω ω' := faceMoment_add_left p e hη ω.2 ω'.2
  map_smul' c ω := faceMoment_smul_left p e η c ω

/-- Moments on the faces of `p` are moments on the faces of `T̂` of `F_T^* ω`. -/
theorem faceMoment_eq_faceMoment_refVertex (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) (η : FormField m) (ω : FormField n) :
    faceMoment p e η ω =
      faceMoment (refVertex n) e η (affinePullback (simplexMatrix p) (p 0) ω) := by
  have := faceTrace_faceTrace p id e ω
  simp only [Function.id_comp] at this
  rw [faceMoment, faceMoment, ← this]
  rfl

/-! ### Unisolvence on the reference simplex ([AFW2006], Thms 4.8, 4.12) -/

theorem faceTrace_refVertex_id (ω : FormField n) : faceTrace (refVertex n) id ω = ω := by
  rw [faceTrace_apply]
  simp only [Function.comp_id, id, refVertex_zero, simplexMatrix_refVertex]
  exact affinePullback_id ω

theorem polySpace_eq_bot_of_lt {r k : ℕ} (h : n < k) : polySpace n r k = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 ?_
  rintro _ ⟨Ω, hΩ, rfl⟩
  have : Ω = 0 := funext fun s => hΩ.1 s fun hs => by
    have := card_le_univ s; simp at this; omega
  rw [this, map_zero]

theorem polyMinusSpace_eq_bot_of_lt {r k : ℕ} (h : n < k) : polyMinusSpace n r k = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 ?_
  rintro _ ⟨Ω, hΩ, rfl⟩
  have hdeg := (Koszul.polyFormMinus_le_polyForm_succ r k hΩ).1
  have : Ω = 0 := funext fun s => hdeg s fun hs => by
    have := card_le_univ s; simp at this; omega
  rw [this, map_zero]

/-- **Vanishing of the degrees of freedom forces `ω = 0` on `P_rΛᵏ(T̂)`** ([AFW2006], Thm 4.8):
if `∫_f tr_f ω ∧ η = 0` for every face `f` of `T̂ₙ` (of any dimension `m`) and every
`η ∈ P⁻_{r+k-m}Λ^{m-k}(f)`, then `ω = 0`. By induction on `n`: the traces on the proper faces
vanish by the induction hypothesis, and [AFW2006], Lemma 4.7 applies to the bubble `ω`. -/
theorem eq_zero_of_faceMoment_eq_zero {r : ℕ} (hr : 1 ≤ r) (k n : ℕ) {ω : FormField n}
    (hω : ω ∈ polySpace n r k)
    (hdof : ∀ (m : ℕ) (e : Fin (m + 1) ↪o Fin (n + 1)), ∀ η ∈ testSpace r k m,
      faceMoment (refVertex n) e η ω = 0) : ω = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hkn : n < k
  · rw [polySpace_eq_bot_of_lt hkn, Submodule.mem_bot] at hω; exact hω
  have hbub : IsBubble (refVertex n) ω := by
    intro m e hm
    refine ih m hm (affinePullback_mem_polySpace _ _ hω) fun m' e' η hη => ?_
    have := hdof m' (e'.trans e) η hη
    rw [faceMoment, faceTrace_faceTrace]
    exact this
  refine eq_zero_of_mem_bubbleSpace_polySpace hr ⟨hω, hbub⟩ fun h η hη => ?_
  have := hdof n (OrderEmbedding.ofStrictMono id strictMono_id) η
    (by rw [testSpace_eq ⟨by omega, h⟩]; exact hη)
  rw [faceMoment] at this
  simpa [faceTrace_refVertex_id] using this

/-- **Vanishing of the degrees of freedom forces `ω = 0` on `P_r⁻Λᵏ(T̂)`** ([AFW2006],
Thm 4.12), with the test forms `η ∈ P_{r+k-m-1}Λ^{m-k}(f)`. -/
theorem eq_zero_of_faceMoment_eq_zero_minus {r : ℕ} (hr : 1 ≤ r) (k n : ℕ) {ω : FormField n}
    (hω : ω ∈ polyMinusSpace n r k)
    (hdof : ∀ (m : ℕ) (e : Fin (m + 1) ↪o Fin (n + 1)), ∀ η ∈ testSpaceMinus r k m,
      faceMoment (refVertex n) e η ω = 0) : ω = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hkn : n < k
  · rw [polyMinusSpace_eq_bot_of_lt hkn, Submodule.mem_bot] at hω; exact hω
  have hbub : IsBubble (refVertex n) ω := by
    intro m e hm
    refine ih m hm (affinePullback_mem_polyMinusSpace _ _ hω) fun m' e' η hη => ?_
    have := hdof m' (e'.trans e) η hη
    rw [faceMoment, faceTrace_faceTrace]
    exact this
  refine eq_zero_of_mem_bubbleSpace_polyMinusSpace hr ⟨hω, hbub⟩ fun h η hη => ?_
  have := hdof n (OrderEmbedding.ofStrictMono id strictMono_id) η
    (by rw [testSpaceMinus_eq ⟨by omega, h⟩]; exact hη)
  rw [faceMoment] at this
  simpa [faceTrace_refVertex_id] using this

/-! ### Moments against a basis of the test space -/

/-- A moment against a combination of test forms is the combination of the moments. -/
theorem faceMoment_sum_smul_right (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) {ι : Type*} (u : Finset ι) (c : ι → ℝ)
    {η : ι → FormField m} (hη : ∀ i, Continuous (η i)) {ω : FormField n} (hω : Continuous ω) :
    faceMoment p e (∑ i ∈ u, c i • η i) ω = ∑ i ∈ u, c i * faceMoment p e (η i) ω := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    simp [faceMoment_eq_integral, wedgeField]
  | insert a u ha ih =>
    have hs : Continuous (∑ i ∈ u, c i • η i) := by
      rw [Finset.sum_fn]; exact continuous_finsetSum _ fun i _ => (hη i).const_smul (c i)
    rw [sum_insert ha, sum_insert ha, faceMoment_add_right p e ((hη a).const_smul (c a)) hs hω,
      faceMoment_smul_right, ih, smul_eq_mul]

/-- If the moments against a basis of a space of continuous test forms vanish, all moments
against the space vanish. -/
theorem faceMoment_eq_zero_of_basis (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) {V : Submodule ℝ (FormField m)} {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ V) (hV : ∀ η ∈ V, Continuous η) {ω : FormField n} (hω : Continuous ω)
    (h : ∀ i, faceMoment p e (b i : FormField m) ω = 0) {η : FormField m} (hη : η ∈ V) :
    faceMoment p e η ω = 0 := by
  have hsum : η = ∑ i, b.repr ⟨η, hη⟩ i • (b i : FormField m) := by
    have := b.sum_repr ⟨η, hη⟩
    rw [Subtype.ext_iff, Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    exact this.symm
  rw [hsum, faceMoment_sum_smul_right p e _ _ (fun i => hV _ (b i).2) hω]
  simp [h]

/-! ### The degrees of freedom of `P_rΛᵏ(T)` and `P_r⁻Λᵏ(T)` -/

/-- A basis of the test forms on `m`-faces. -/
def testBasis (r k m : ℕ) : Module.Basis (Fin (Module.finrank ℝ (testSpace r k m))) ℝ
    (testSpace r k m) := Module.finBasis ℝ _

/-- A basis of the test forms of `P_r⁻Λᵏ` on `m`-faces. -/
def testBasisMinus (r k m : ℕ) : Module.Basis (Fin (Module.finrank ℝ (testSpaceMinus r k m))) ℝ
    (testSpaceMinus r k m) := Module.finBasis ℝ _

/-- The degrees of freedom of `P_rΛᵏ(T)` attached to the face `f`: the moments against a basis
of `P⁻_{r+k-dim f}Λ^{dim f-k}(f)`. -/
abbrev DofIndex (r k : ℕ) (f : Face n) := Fin (Module.finrank ℝ (testSpace r k f.dim))

/-- The degrees of freedom of `P_r⁻Λᵏ(T)` attached to the face `f`. -/
abbrev DofIndexMinus (r k : ℕ) (f : Face n) := Fin (Module.finrank ℝ (testSpaceMinus r k f.dim))

/-- The degree of freedom `ω ↦ ∫_f tr_f ω ∧ ηᵢ` of `P_rΛᵏ(T)`, on continuous forms. -/
def polyDof (p : Fin (n + 1) → Fin n → ℝ) (r k : ℕ) (f : Face n) (i : DofIndex r k f) :
    contForms n →ₗ[ℝ] ℝ :=
  faceMomentₗ p f.emb (testBasis r k f.dim i : FormField f.dim)
    (contDiff_of_mem_testSpace (testBasis r k f.dim i).2).continuous

/-- The degree of freedom `ω ↦ ∫_f tr_f ω ∧ ηᵢ` of `P_r⁻Λᵏ(T)`, on continuous forms. -/
def polyMinusDof (p : Fin (n + 1) → Fin n → ℝ) (r k : ℕ) (f : Face n)
    (i : DofIndexMinus r k f) : contForms n →ₗ[ℝ] ℝ :=
  faceMomentₗ p f.emb (testBasisMinus r k f.dim i : FormField f.dim)
    (contDiff_of_mem_testSpaceMinus (testBasisMinus r k f.dim i).2).continuous

theorem localPolySpace_le_contForms (p : Fin (n + 1) → Fin n → ℝ) (r k : ℕ) :
    localPolySpace p r k ≤ contForms n := by
  rintro _ ⟨ω, hω, rfl⟩
  exact continuous_affinePullback _ _ (polySpace_le_c1 hω).continuous

theorem localPolyMinusSpace_le_contForms (p : Fin (n + 1) → Fin n → ℝ) (r k : ℕ) :
    localPolyMinusSpace p r k ≤ contForms n := by
  rintro _ ⟨ω, hω, rfl⟩
  exact continuous_affinePullback _ _ (contDiff_of_mem_polyMinusSpace hω).continuous

/-- The degrees of freedom of `P_rΛᵏ(T)`, indexed by the faces `f` and a basis of the test
forms on `f`. -/
def localDof (p : Fin (n + 1) → Fin n → ℝ) (r k : ℕ) (i : Σ f : Face n, DofIndex r k f) :
    localPolySpace p r k →ₗ[ℝ] ℝ :=
  polyDof p r k i.1 i.2 ∘ₗ Submodule.inclusion (localPolySpace_le_contForms p r k)

/-- The degrees of freedom of `P_r⁻Λᵏ(T)`. -/
def localDofMinus (p : Fin (n + 1) → Fin n → ℝ) (r k : ℕ)
    (i : Σ f : Face n, DofIndexMinus r k f) : localPolyMinusSpace p r k →ₗ[ℝ] ℝ :=
  polyMinusDof p r k i.1 i.2 ∘ₗ Submodule.inclusion (localPolyMinusSpace_le_contForms p r k)

theorem localDof_apply (p : Fin (n + 1) → Fin n → ℝ) (r k : ℕ)
    (i : Σ f : Face n, DofIndex r k f) (ω : localPolySpace p r k) :
    localDof p r k i ω =
      faceMoment p i.1.emb (testBasis r k i.1.dim i.2 : FormField i.1.dim) ω := rfl

theorem localDofMinus_apply (p : Fin (n + 1) → Fin n → ℝ) (r k : ℕ)
    (i : Σ f : Face n, DofIndexMinus r k f) (ω : localPolyMinusSpace p r k) :
    localDofMinus p r k i ω =
      faceMoment p i.1.emb (testBasisMinus r k i.1.dim i.2 : FormField i.1.dim) ω := rfl

/-! ### Counting the degrees of freedom ([AFW2006], Thms 4.9, 4.13) -/

/-- **`#DOF = dim P_rΛᵏ(T)`** ([AFW2006], Thm 4.9). -/
theorem card_dofIndex {r k : ℕ} (hr : 1 ≤ r) (hk : k ≤ n) :
    Fintype.card (Σ f : Face n, DofIndex r k f) =
      (r + n).choose (r + k) * (r + k).choose k := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, finrank_testSpace]
  rw [sum_face_eq (fun m => (r + k).choose r * if k ≤ m ∧ m < r + k then
    (r - 1).choose (m - k) else 0)]
  simp only [smul_eq_mul, mul_left_comm _ ((r + k).choose r)]
  rw [← mul_sum, sum_choose_mul_choose_eq hk hr, ← @Nat.choose_symm_add r k,
    Nat.choose_symm_of_eq_add (show n + r = (n - k) + (r + k) by omega), add_comm n r, mul_comm]

/-- **`#DOF = dim P_r⁻Λᵏ(T)`** ([AFW2006], Thm 4.13). -/
theorem card_dofIndexMinus {r k : ℕ} (hr : 1 ≤ r) (hk : k ≤ n) :
    Fintype.card (Σ f : Face n, DofIndexMinus r k f) =
      (r + n).choose (r + k) * (r + k - 1).choose k := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, finrank_testSpaceMinus hr]
  rw [sum_face_eq (fun m => (r + k - 1).choose (r - 1) * if k ≤ m ∧ m < r + k then
    (r - 1).choose (m - k) else 0)]
  simp only [smul_eq_mul, mul_left_comm _ ((r + k - 1).choose (r - 1))]
  rw [← mul_sum, sum_choose_mul_choose_eq hk hr,
    Nat.choose_symm_of_eq_add (show r + k - 1 = (r - 1) + k by omega),
    Nat.choose_symm_of_eq_add (show n + r = (n - k) + (r + k) by omega), add_comm n r, mul_comm]

/-! ### Unisolvence ([AFW2006], Thms 4.10, 4.14) -/

instance (p : Fin (n + 1) → Fin n → ℝ) (r k : ℕ) : FiniteDimensional ℝ (localPolySpace p r k) := by
  unfold localPolySpace; infer_instance

instance (p : Fin (n + 1) → Fin n → ℝ) (r k : ℕ) :
    FiniteDimensional ℝ (localPolyMinusSpace p r k) := by
  unfold localPolyMinusSpace; infer_instance

variable {p : Fin (n + 1) → Fin n → ℝ}

theorem faceMoment_sub_left (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) {η : FormField m} (hη : Continuous η) {ω ω' : FormField n}
    (hω : Continuous ω) (hω' : Continuous ω') :
    faceMoment p e η (ω - ω') = faceMoment p e η ω - faceMoment p e η ω' := by
  rw [sub_eq_add_neg, faceMoment_add_left p e hη hω hω'.neg, ← neg_one_smul ℝ ω',
    faceMoment_smul_left]
  simp [sub_eq_add_neg]

/-- `F_T^*` is injective. -/
theorem eq_zero_of_affinePullback_eq_zero (hp : IsUnit (edgeMatrix p).det) {ω : FormField n}
    (h : affinePullback (simplexMatrix p) (p 0) ω = 0) : ω = 0 := by
  rw [← affinePullback_affinePullback_of_comp_eq_id (simplexMatrix p) (p 0) (invMatrix p)
    (invOffset p) (simplexMap_affine_inv hp) ω, h]
  funext x; simp [affinePullback_apply]

/-- **Vanishing of the degrees of freedom on a simplex `T`**: if all the moments
`∫_f tr_f ω ∧ η`, `η ∈ P⁻_{r+k-dim f}Λ^{dim f-k}(f)`, of `ω ∈ P_rΛᵏ(T)` vanish, then `ω = 0`. -/
theorem eq_zero_of_faceMoment_eq_zero_simplex (hp : IsUnit (edgeMatrix p).det) {r : ℕ}
    (hr : 1 ≤ r) (k : ℕ) {ω : FormField n} (hω : ω ∈ polySpace n r k)
    (hdof : ∀ (m : ℕ) (e : Fin (m + 1) ↪o Fin (n + 1)), ∀ η ∈ testSpace r k m,
      faceMoment p e η ω = 0) : ω = 0 :=
  eq_zero_of_affinePullback_eq_zero hp (eq_zero_of_faceMoment_eq_zero hr k n
    (affinePullback_mem_polySpace _ _ hω) fun m e η hη => by
      rw [← faceMoment_eq_faceMoment_refVertex]; exact hdof m e η hη)

/-- **Vanishing of the degrees of freedom on a simplex `T`**, for `P_r⁻Λᵏ(T)`. -/
theorem eq_zero_of_faceMoment_eq_zero_minus_simplex (hp : IsUnit (edgeMatrix p).det) {r : ℕ}
    (hr : 1 ≤ r) (k : ℕ) {ω : FormField n} (hω : ω ∈ polyMinusSpace n r k)
    (hdof : ∀ (m : ℕ) (e : Fin (m + 1) ↪o Fin (n + 1)), ∀ η ∈ testSpaceMinus r k m,
      faceMoment p e η ω = 0) : ω = 0 :=
  eq_zero_of_affinePullback_eq_zero hp (eq_zero_of_faceMoment_eq_zero_minus hr k n
    (affinePullback_mem_polyMinusSpace _ _ hω) fun m e η hη => by
      rw [← faceMoment_eq_faceMoment_refVertex]; exact hdof m e η hη)

/-- **Unisolvence of the degrees of freedom of `P_rΛᵏ(T)`** for every `r ≥ 1`, `0 ≤ k ≤ n`:
the moments `ω ↦ ∫_f tr_f ω ∧ η`, `η ∈ P⁻_{r+k-dim f}Λ^{dim f-k}(f)`, over all faces `f` of `T`.
[AFW2006], Thm 4.10; [AFW2010], Thm 5.5 -/
theorem isUnisolvent_localDof (hp : IsUnit (edgeMatrix p).det) {r k : ℕ} (hr : 1 ≤ r)
    (hk : k ≤ n) : IsUnisolvent (localDof p r k) := by
  rw [isUnisolvent_iff_forall_eq_zero _ (by
    rw [localPolySpace_eq hp, finrank_polySpace, card_dofIndex hr hk])]
  intro ω hω
  refine Subtype.ext (eq_zero_of_faceMoment_eq_zero_simplex hp hr k
    (localPolySpace_eq hp r k ▸ ω.2) fun m e η hη => ?_)
  have := faceMoment_eq_zero_of_basis p (Face.ofEmb e).emb (testBasis r k m)
    (fun η h => (contDiff_of_mem_testSpace h).continuous)
    (localPolySpace_le_contForms p r k ω.2) (fun i => hω ⟨Face.ofEmb e, i⟩) hη
  rwa [Face.emb_ofEmb] at this

/-- **Unisolvence of the degrees of freedom of `P_r⁻Λᵏ(T)`** for every `r ≥ 1`, `0 ≤ k ≤ n`:
the moments `ω ↦ ∫_f tr_f ω ∧ η`, `η ∈ P_{r+k-dim f-1}Λ^{dim f-k}(f)`. [AFW2006], Thm 4.14;
[AFW2010], Thm 5.5 -/
theorem isUnisolvent_localDofMinus (hp : IsUnit (edgeMatrix p).det) {r k : ℕ} (hr : 1 ≤ r)
    (hk : k ≤ n) : IsUnisolvent (localDofMinus p r k) := by
  rw [isUnisolvent_iff_forall_eq_zero _ (by
    rw [localPolyMinusSpace_eq hp, finrank_polyMinusSpace n hr, card_dofIndexMinus hr hk])]
  intro ω hω
  refine Subtype.ext (eq_zero_of_faceMoment_eq_zero_minus_simplex hp hr k
    (localPolyMinusSpace_eq hp r k ▸ ω.2) fun m e η hη => ?_)
  have := faceMoment_eq_zero_of_basis p (Face.ofEmb e).emb (testBasisMinus r k m)
    (fun η h => (contDiff_of_mem_testSpaceMinus h).continuous)
    (localPolyMinusSpace_le_contForms p r k ω.2) (fun i => hω ⟨Face.ofEmb e, i⟩) hη
  rwa [Face.emb_ofEmb] at this

/-! ### The degrees of freedom on a face determine the trace -/

/-- The face of `T` spanned by a face `e'` of the reference face of `f`. -/
theorem Face.ofEmb_trans_subset (f : Face n) {m : ℕ} (e' : Fin (m + 1) ↪o Fin (f.dim + 1)) :
    (Face.ofEmb (e'.trans f.emb)).2.1 ⊆ f.2.1 := by
  intro x hx
  simp only [mem_map, mem_univ, true_and, RelEmbedding.coe_toEmbedding,
    RelEmbedding.coe_trans, Function.comp_apply] at hx
  obtain ⟨y, rfl⟩ := hx
  exact orderEmbOfFin_mem _ _ _

/-- **Trace determination for `P_rΛᵏ(T)`**: the degrees of freedom attached to a face `f` and to
its subfaces determine the trace `tr_f ω`. This is what makes the assembled space conforming
([AFW2006], §5.1; [AFW2010], §5.2). -/
theorem faceTrace_eq_of_localDof_eq (hp : IsUnit (edgeMatrix p).det) {r k : ℕ} (hr : 1 ≤ r)
    (f : Face n) {ω ω' : localPolySpace p r k}
    (h : ∀ g : Face n, g.2.1 ⊆ f.2.1 → ∀ i, localDof p r k ⟨g, i⟩ ω = localDof p r k ⟨g, i⟩ ω') :
    faceTrace p f.emb ω = faceTrace p f.emb ω' := by
  have hc : ∀ ψ : localPolySpace p r k, Continuous (ψ : FormField n) := fun ψ =>
    localPolySpace_le_contForms p r k ψ.2
  have hmem : faceTrace p f.emb ((ω : FormField n) - ω') ∈ polySpace f.dim r k := by
    change affinePullback (simplexMatrix (p ∘ f.emb)) (p (f.emb 0)) ((ω : FormField n) - ω') ∈ _
    refine affinePullback_mem_polySpace _ _ ?_
    rw [← localPolySpace_eq hp r k]
    exact Submodule.sub_mem _ ω.2 ω'.2
  have h0 := eq_zero_of_faceMoment_eq_zero hr k f.dim hmem fun m e' η hη => by
    rw [faceMoment, faceTrace_faceTrace]
    refine faceMoment_eq_zero_of_basis p (e'.trans f.emb) (testBasis r k m)
      (fun η h => (contDiff_of_mem_testSpace h).continuous) ((hc ω).sub (hc ω')) (fun i => ?_) hη
    have := h _ (f.ofEmb_trans_subset e') i
    rw [localDof_apply, localDof_apply, Face.emb_ofEmb] at this
    rw [faceMoment_sub_left _ _ (contDiff_of_mem_testSpace (testBasis r k m i).2).continuous
      (hc ω) (hc ω')]
    exact sub_eq_zero.2 this
  rw [map_sub, sub_eq_zero] at h0
  exact h0

/-- **Trace determination for `P_r⁻Λᵏ(T)`**. -/
theorem faceTrace_eq_of_localDofMinus_eq (hp : IsUnit (edgeMatrix p).det) {r k : ℕ}
    (hr : 1 ≤ r) (f : Face n) {ω ω' : localPolyMinusSpace p r k}
    (h : ∀ g : Face n, g.2.1 ⊆ f.2.1 → ∀ i,
      localDofMinus p r k ⟨g, i⟩ ω = localDofMinus p r k ⟨g, i⟩ ω') :
    faceTrace p f.emb ω = faceTrace p f.emb ω' := by
  have hc : ∀ ψ : localPolyMinusSpace p r k, Continuous (ψ : FormField n) := fun ψ =>
    localPolyMinusSpace_le_contForms p r k ψ.2
  have hmem : faceTrace p f.emb ((ω : FormField n) - ω') ∈ polyMinusSpace f.dim r k := by
    change affinePullback (simplexMatrix (p ∘ f.emb)) (p (f.emb 0)) ((ω : FormField n) - ω') ∈ _
    refine affinePullback_mem_polyMinusSpace _ _ ?_
    rw [← localPolyMinusSpace_eq hp r k]
    exact Submodule.sub_mem _ ω.2 ω'.2
  have h0 := eq_zero_of_faceMoment_eq_zero_minus hr k f.dim hmem fun m e' η hη => by
    rw [faceMoment, faceTrace_faceTrace]
    refine faceMoment_eq_zero_of_basis p (e'.trans f.emb) (testBasisMinus r k m)
      (fun η h => (contDiff_of_mem_testSpaceMinus h).continuous) ((hc ω).sub (hc ω'))
      (fun i => ?_) hη
    have := h _ (f.ofEmb_trans_subset e') i
    rw [localDofMinus_apply, localDofMinus_apply, Face.emb_ofEmb] at this
    rw [faceMoment_sub_left _ _
      (contDiff_of_mem_testSpaceMinus (testBasisMinus r k m i).2).continuous (hc ω) (hc ω')]
    exact sub_eq_zero.2 this
  rw [map_sub, sub_eq_zero] at h0
  exact h0

/-! ### Local finite elements -/

/-- A **local finite element** on the simplex `p`: a space of shape functions (form fields on
`ℝⁿ`), degrees of freedom attached to the faces of `p`, unisolvent, and such that the degrees of
freedom attached to a face and its subfaces determine the trace on that face (the
trace-determination property used for the conformity of the assembled space). -/
structure SimplexElement (p : Fin (n + 1) → Fin n → ℝ) where
  /-- The shape functions. -/
  space : Submodule ℝ (FormField n)
  /-- The degrees of freedom attached to each face. -/
  dofIndex : Face n → Type
  [fintype : ∀ f, Fintype (dofIndex f)]
  /-- The degrees of freedom. -/
  dof : (f : Face n) → dofIndex f → space →ₗ[ℝ] ℝ
  /-- Unisolvence. -/
  isUnisolvent : IsUnisolvent fun i : Σ f, dofIndex f => dof i.1 i.2
  /-- The degrees of freedom on a face and its subfaces determine the trace on the face. -/
  faceTrace_eq : ∀ (f : Face n) (ω ω' : space),
    (∀ g : Face n, g.2.1 ⊆ f.2.1 → ∀ i, dof g i ω = dof g i ω') →
      faceTrace p f.emb ω = faceTrace p f.emb ω'

/-- **The finite element `P_rΛᵏ(T)`** ([AFW2006], §4.5; [AFW2010], §5.2). -/
def polySimplexElement (hp : IsUnit (edgeMatrix p).det) {r k : ℕ} (hr : 1 ≤ r) (hk : k ≤ n) :
    SimplexElement p where
  space := localPolySpace p r k
  dofIndex := DofIndex r k
  dof f i := localDof p r k ⟨f, i⟩
  isUnisolvent := isUnisolvent_localDof hp hr hk
  faceTrace_eq f _ _ h := faceTrace_eq_of_localDof_eq hp hr f h

/-- **The finite element `P_r⁻Λᵏ(T)`** ([AFW2006], §4.6; [AFW2010], §5.2). -/
def polyMinusSimplexElement (hp : IsUnit (edgeMatrix p).det) {r k : ℕ} (hr : 1 ≤ r)
    (hk : k ≤ n) : SimplexElement p where
  space := localPolyMinusSpace p r k
  dofIndex := DofIndexMinus r k
  dof f i := localDofMinus p r k ⟨f, i⟩
  isUnisolvent := isUnisolvent_localDofMinus hp hr hk
  faceTrace_eq f _ _ h := faceTrace_eq_of_localDofMinus_eq hp hr f h

/-! ### Mathlib simplices -/

/-- Unisolvence of the degrees of freedom of `P_rΛᵏ(T)` on a Mathlib `n`-simplex `T`. -/
theorem isUnisolvent_localDof_simplex (T : Affine.Simplex ℝ (Fin n → ℝ) n) {r k : ℕ}
    (hr : 1 ≤ r) (hk : k ≤ n) : IsUnisolvent (localDof T.points r k) :=
  isUnisolvent_localDof (isUnit_det_edgeMatrix T) hr hk

/-- Unisolvence of the degrees of freedom of `P_r⁻Λᵏ(T)` on a Mathlib `n`-simplex `T`. -/
theorem isUnisolvent_localDofMinus_simplex (T : Affine.Simplex ℝ (Fin n → ℝ) n) {r k : ℕ}
    (hr : 1 ≤ r) (hk : k ≤ n) : IsUnisolvent (localDofMinus T.points r k) :=
  isUnisolvent_localDofMinus (isUnit_det_edgeMatrix T) hr hk

/-! ### The Leibniz rule and Stokes' theorem for moments -/

/-- The coefficientwise partial derivative of the exterior product. -/
theorem partialDerivForm_wedgeField {m : ℕ} (j : Fin m) {ω η : FormField m} {x : Fin m → ℝ}
    (hω : DifferentiableAt ℝ ω x) (hη : DifferentiableAt ℝ η x) :
    partialDerivForm j (wedgeField ω η) x =
      wedgeForm (partialDerivForm j ω x) (η x) + wedgeForm (ω x) (partialDerivForm j η x) := by
  funext u
  simp only [partialDerivForm, wedgeField, wedgeForm_apply, Pi.add_apply, ← sum_add_distrib]
  have hω' : ∀ s, DifferentiableAt ℝ (fun y => ω y s) x := fun s => differentiableAt_pi.1 hω s
  have hη' : ∀ s, DifferentiableAt ℝ (fun y => η y s) x := fun s => differentiableAt_pi.1 hη s
  rw [partialDeriv_sum (f := fun s y => shuffleSgn s (u \ s) * ω y s * η y (u \ s)) _
    fun s _ => ((hω' s).const_mul _).mul (hη' _)]
  refine sum_congr rfl fun s _ => ?_
  rw [partialDeriv_mul ((hω' s).const_mul _) (hη' _),
    show (fun y => shuffleSgn s (u \ s) * ω y s) = fun y => (shuffleSgn s (u \ s) : ℝ) • ω y s
      from rfl, partialDeriv_const_smul (hω' s)]
  simp only [smul_eq_mul]

/-- **The Leibniz rule for smooth forms**: `d (ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη` for a
`k`-form `ω`, at every point where `ω` and `η` are differentiable. -/
theorem extDeriv_wedgeField_apply {m k : ℕ} {ω η : FormField m} {x : Fin m → ℝ}
    (hk : ∀ y, IsDeg k (ω y)) (hω : DifferentiableAt ℝ ω x) (hη : DifferentiableAt ℝ η x) :
    extDeriv (wedgeField ω η) x =
      wedgeField (extDeriv ω) η x + (-1 : ℝ) ^ k • wedgeField ω (extDeriv η) x := by
  simp only [wedgeField, extDeriv_eq_sum_wedge, partialDerivForm_wedgeField _ hω hη,
    wedgeForm_sum_left, wedgeForm_sum_right, Finset.smul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [wedge_add, wedge_wedgeForm, wedge_wedgeForm_right _ (hk x)]

theorem contDiff_wedgeField {m : ℕ} {r : WithTop ℕ∞} {ω η : FormField m} (hω : ContDiff ℝ r ω)
    (hη : ContDiff ℝ r η) : ContDiff ℝ r (wedgeField ω η) := by
  refine contDiff_pi.2 fun u => ?_
  simp only [wedgeField, wedgeForm_apply]
  refine ContDiff.sum fun s _ => ?_
  exact (contDiff_const.mul (contDiff_pi.1 hω s)).mul (contDiff_pi.1 hη _)

theorem contDiff_faceTrace (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ} {r : WithTop ℕ∞}
    (e : Fin (m + 1) → Fin (n + 1)) {ω : FormField n} (hω : ContDiff ℝ r ω) :
    ContDiff ℝ r (faceTrace p e ω) :=
  contDiff_affinePullback _ _ hω

theorem IsDeg.faceTrace (p : Fin (n + 1) → Fin n → ℝ) {m k : ℕ} (e : Fin (m + 1) → Fin (n + 1))
    {ω : FormField n} (hk : ∀ y, IsDeg k (ω y)) (y : Fin m → ℝ) :
    IsDeg k (FiniteElement.faceTrace p e ω y) :=
  IsDeg.affinePullback hk _ _ y

/-- **Stokes' formula for moments**: for a `C¹` `k`-form `ω`, a face `p ∘ e` of dimension
`M + 1` and a smooth test form `η` on it,
`∫_f tr_f dω ∧ η = Σᵢ (-1)ⁱ ∫_{∂ᵢ f} tr ω ∧ tr η - (-1)^k ∫_f tr_f ω ∧ dη`. -/
theorem faceMoment_extDeriv (p : Fin (n + 1) → Fin n → ℝ) {M k : ℕ}
    (e : Fin (M + 2) → Fin (n + 1)) {η : FormField (M + 1)} (hη : ContDiff ℝ ⊤ η)
    {ω : FormField n} (hω : ContDiff ℝ 1 ω) (hk : ∀ y, IsDeg k (ω y)) :
    faceMoment p e η (extDeriv ω) =
      ∑ i : Fin (M + 2), (-1) ^ (i : ℕ) * faceMoment p (e ∘ i.succAbove)
        (faceTrace (refVertex (M + 1)) i.succAbove η) ω -
      (-1) ^ k * faceMoment p e (extDeriv η) ω := by
  set ψ := wedgeField (faceTrace p e ω) η
  have hψ : ContDiff ℝ 1 ψ := contDiff_wedgeField (contDiff_faceTrace p e hω) (hη.of_le le_top)
  have hS := setIntegral_refSimplex_extDeriv (m := M) (η := ψ) isOpen_univ (Set.subset_univ _)
    hψ.contDiffOn
  have hface : ∀ i : Fin (M + 2), simplexIntegral (refVertex (M + 1) ∘ i.succAbove) ψ =
      faceMoment p (e ∘ i.succAbove) (faceTrace (refVertex (M + 1)) i.succAbove η) ω := by
    intro i
    have : simplexIntegral (refVertex (M + 1) ∘ i.succAbove) ψ =
        simplexIntegral (refVertex M) (faceTrace (refVertex (M + 1)) i.succAbove ψ) := by
      rw [simplexIntegral_refVertex]; rfl
    rw [this, faceTrace_wedgeField, faceTrace_faceTrace]
    rfl
  simp only [hface] at hS
  have hdiff : ∀ x, extDeriv ψ x univ = wedgeField (faceTrace p e (extDeriv ω)) η x univ +
      (-1) ^ k * wedgeField (faceTrace p e ω) (extDeriv η) x univ := by
    intro x
    rw [extDeriv_wedgeField_apply (IsDeg.faceTrace p e hk)
      ((contDiff_faceTrace p e hω).differentiable one_ne_zero x)
      ((hη.of_le le_top : ContDiff ℝ 1 η).differentiable one_ne_zero x),
      faceTrace_extDeriv p e (hω.differentiable one_ne_zero)]
    rfl
  simp only [hdiff] at hS
  have hc1 : Continuous (faceTrace p e (extDeriv ω)) :=
    continuous_faceTrace p e (continuous_extDeriv hω)
  have hc2 : Continuous (extDeriv η) := continuous_extDeriv (hη.of_le le_top)
  rw [integral_add (integrableOn_wedgeField hc1 hη.continuous)
    ((integrableOn_wedgeField (continuous_faceTrace p e hω.continuous) hc2).const_mul _),
    integral_const_mul] at hS
  rw [faceMoment_eq_integral, faceMoment_eq_integral p e (extDeriv η)]
  linarith

/-! ### Test forms under traces and `d` -/

theorem extDeriv_mem_polySpace {m s j : ℕ} {η : FormField m} (h : η ∈ polySpace m s j) :
    extDeriv η ∈ polySpace m (s - 1) (j + 1) := by
  obtain ⟨H, hH, rfl⟩ := h
  exact ⟨_, Koszul.extDeriv_mem_polyForm hH, (extDeriv_evalForm H).symm⟩

theorem extDeriv_mem_polyMinusSpace {m s j : ℕ} {η : FormField m}
    (h : η ∈ polyMinusSpace m s j) : extDeriv η ∈ polyMinusSpace m s (j + 1) := by
  obtain ⟨H, hH, rfl⟩ := h
  exact ⟨_, Koszul.extDeriv_mem_polyFormMinus_of_mem_polyFormMinus hH,
    (extDeriv_evalForm H).symm⟩

theorem polyMinusSpace_mono {m s : ℕ} (hs : 1 ≤ s) (j : ℕ) :
    polyMinusSpace m s j ≤ polyMinusSpace m (s + 1) j :=
  Submodule.map_mono ((Koszul.polyFormMinus_le_polyForm hs j).trans
    (Koszul.polyForm_le_polyFormMinus (s + 1) j))

theorem extDeriv_zero_field {m : ℕ} : extDeriv (0 : FormField m) = 0 := by
  funext x s; simp [FiniteElement.extDeriv_apply]

/-- Traces of the test forms of `P_rΛ^{k+1}` on an `(M+1)`-face are test forms of
`P_{r+1}Λᵏ` on its facets. -/
theorem faceTrace_mem_testSpace {r k M : ℕ} {η : FormField (M + 1)}
    (h : η ∈ testSpace r (k + 1) (M + 1)) (i : Fin (M + 2)) :
    faceTrace (refVertex (M + 1)) i.succAbove η ∈ testSpace (r + 1) k M := by
  by_cases hc : k + 1 ≤ M + 1 ∧ M + 1 < r + (k + 1)
  · rw [testSpace_eq hc] at h
    rw [testSpace_eq (by omega)]
    have := affinePullback_mem_polyMinusSpace (simplexMatrix (refVertex (M + 1) ∘ i.succAbove))
      (refVertex (M + 1) (i.succAbove 0)) h
    rw [show r + 1 + k - M = r + (k + 1) - (M + 1) + 1 by omega,
      show M - k = M + 1 - (k + 1) by omega]
    exact polyMinusSpace_mono (by omega) _ this
  · rw [testSpace_eq_bot hc, Submodule.mem_bot] at h
    rw [h, map_zero]; exact Submodule.zero_mem _

/-- `d` maps the test forms of `P_rΛ^{k+1}` on an `(M+1)`-face into those of `P_{r+1}Λᵏ`. -/
theorem extDeriv_mem_testSpace {r k M : ℕ} {η : FormField (M + 1)}
    (h : η ∈ testSpace r (k + 1) (M + 1)) : extDeriv η ∈ testSpace (r + 1) k (M + 1) := by
  by_cases hc : k + 1 ≤ M + 1 ∧ M + 1 < r + (k + 1)
  · rw [testSpace_eq hc] at h
    rw [testSpace_eq (by omega)]
    have := extDeriv_mem_polyMinusSpace h
    rwa [show r + 1 + k - (M + 1) = r + (k + 1) - (M + 1) by omega,
      show M + 1 - k = M + 1 - (k + 1) + 1 by omega]
  · rw [testSpace_eq_bot hc, Submodule.mem_bot] at h
    rw [h, extDeriv_zero_field]; exact Submodule.zero_mem _

/-- Traces of the test forms of `P_r⁻Λ^{k+1}` on an `(M+1)`-face are test forms of `P_r⁻Λᵏ` on
its facets. -/
theorem faceTrace_mem_testSpaceMinus {r k M : ℕ} {η : FormField (M + 1)}
    (h : η ∈ testSpaceMinus r (k + 1) (M + 1)) (i : Fin (M + 2)) :
    faceTrace (refVertex (M + 1)) i.succAbove η ∈ testSpaceMinus r k M := by
  by_cases hc : k + 1 ≤ M + 1 ∧ M + 1 < r + (k + 1)
  · rw [testSpaceMinus_eq hc] at h
    rw [testSpaceMinus_eq (by omega)]
    have := affinePullback_mem_polySpace (simplexMatrix (refVertex (M + 1) ∘ i.succAbove))
      (refVertex (M + 1) (i.succAbove 0)) h
    rwa [show r + k - M - 1 = r + (k + 1) - (M + 1) - 1 by omega,
      show M - k = M + 1 - (k + 1) by omega]
  · rw [testSpaceMinus_eq_bot hc, Submodule.mem_bot] at h
    rw [h, map_zero]; exact Submodule.zero_mem _

/-- `d` maps the test forms of `P_r⁻Λ^{k+1}` on an `(M+1)`-face into those of `P_r⁻Λᵏ`. -/
theorem extDeriv_mem_testSpaceMinus {r k M : ℕ} {η : FormField (M + 1)}
    (h : η ∈ testSpaceMinus r (k + 1) (M + 1)) : extDeriv η ∈ testSpaceMinus r k (M + 1) := by
  by_cases hc : k + 1 ≤ M + 1 ∧ M + 1 < r + (k + 1)
  · rw [testSpaceMinus_eq hc] at h
    by_cases hc' : M + 1 < r + k
    · rw [testSpaceMinus_eq (by omega)]
      have := extDeriv_mem_polySpace h
      rwa [show r + (k + 1) - (M + 1) - 1 - 1 = r + k - (M + 1) - 1 by omega,
        show M + 1 - (k + 1) + 1 = M + 1 - k by omega] at this
    · obtain ⟨H, hH, rfl⟩ := h
      rw [show r + (k + 1) - (M + 1) - 1 = 0 by omega] at hH
      rw [extDeriv_evalForm, extDeriv_eq_zero_of_mem_polyForm_zero hH, map_zero]
      exact Submodule.zero_mem _
  · rw [testSpaceMinus_eq_bot hc, Submodule.mem_bot] at h
    rw [h, extDeriv_zero_field]; exact Submodule.zero_mem _

/-! ### The canonical interpolants and the commuting property -/

variable (n) in
/-- Form fields of form degree `k`. -/
def degForms (k : ℕ) : Submodule ℝ (FormField n) where
  carrier := {ω | ∀ x, IsDeg k (ω x)}
  zero_mem' x s _ := rfl
  add_mem' ha hb x s hs := by simp [ha x s hs, hb x s hs]
  smul_mem' c ω h x s hs := by simp [h x s hs]

variable (n) in
/-- Continuous `k`-forms. -/
def contDegForms (k : ℕ) : Submodule ℝ (FormField n) := contForms n ⊓ degForms n k

variable (n) in
/-- `C¹` `k`-forms. -/
def c1DegForms (k : ℕ) : Submodule ℝ (FormField n) := c1Forms n ⊓ degForms n k

theorem c1DegForms_le_contDegForms (k : ℕ) : c1DegForms n k ≤ contDegForms n k :=
  inf_le_inf_right _ c1Forms_le_contForms

/-- The exterior derivative `d : C¹Λᵏ → C⁰Λ^{k+1}`. -/
def extDerivC1Deg (k : ℕ) : c1DegForms n k →ₗ[ℝ] contDegForms n (k + 1) where
  toFun ω := ⟨extDeriv ω, continuous_extDeriv (mem_c1Forms.1 ω.2.1),
    fun x => IsDeg.extDeriv ω.2.2 x⟩
  map_add' ω η := Subtype.ext (funext fun x => extDeriv_add_apply
    ((ContDiff.differentiable (mem_c1Forms.1 ω.2.1) one_ne_zero) x)
    ((ContDiff.differentiable (mem_c1Forms.1 η.2.1) one_ne_zero) x))
  map_smul' c ω := Subtype.ext (funext fun x => extDeriv_smul_const_apply c
    ((ContDiff.differentiable (mem_c1Forms.1 ω.2.1) one_ne_zero) x))

theorem polySpace_le_c1DegForms (r k : ℕ) : polySpace n r k ≤ c1DegForms n k := by
  rintro _ ⟨Ω, hΩ, rfl⟩
  exact ⟨mem_c1Forms.2 ((contDiff_evalForm Ω (r := 1))), fun x s hs => by
    rw [evalForm_apply, hΩ.1 s hs, map_zero]⟩

theorem polyMinusSpace_le_c1DegForms (r k : ℕ) : polyMinusSpace n r k ≤ c1DegForms n k := by
  rintro _ ⟨Ω, hΩ, rfl⟩
  exact ⟨mem_c1Forms.2 ((contDiff_evalForm Ω (r := 1))), fun x s hs => by
    rw [evalForm_apply, (Koszul.polyFormMinus_le_polyForm_succ r k hΩ).1 s hs, map_zero]⟩

theorem localPolySpace_le_c1DegForms (hp : IsUnit (edgeMatrix p).det) (r k : ℕ) :
    localPolySpace p r k ≤ c1DegForms n k := by
  rw [localPolySpace_eq hp]; exact polySpace_le_c1DegForms r k

theorem localPolyMinusSpace_le_c1DegForms (hp : IsUnit (edgeMatrix p).det) (r k : ℕ) :
    localPolyMinusSpace p r k ≤ c1DegForms n k := by
  rw [localPolyMinusSpace_eq hp]; exact polyMinusSpace_le_c1DegForms r k

theorem localPolySpace_le_contDegForms (hp : IsUnit (edgeMatrix p).det) (r k : ℕ) :
    localPolySpace p r k ≤ contDegForms n k :=
  (localPolySpace_le_c1DegForms hp r k).trans (c1DegForms_le_contDegForms k)

theorem localPolyMinusSpace_le_contDegForms (hp : IsUnit (edgeMatrix p).det) (r k : ℕ) :
    localPolyMinusSpace p r k ≤ contDegForms n k :=
  (localPolyMinusSpace_le_c1DegForms hp r k).trans (c1DegForms_le_contDegForms k)

theorem differentiable_of_mem_c1DegForms {k : ℕ} {ω : FormField n} (h : ω ∈ c1DegForms n k) :
    Differentiable ℝ ω :=
  ContDiff.differentiable (mem_c1Forms.1 h.1) one_ne_zero

/-- `d : P_{r+1}Λᵏ(T) → P_rΛ^{k+1}(T)`. -/
def extDerivLocal (hp : IsUnit (edgeMatrix p).det) (r k : ℕ) :
    localPolySpace p (r + 1) k →ₗ[ℝ] localPolySpace p r (k + 1) where
  toFun ω := ⟨extDeriv ω, by
    have hω : (ω : FormField n) ∈ polySpace n (r + 1) k := by
      rw [← localPolySpace_eq hp]; exact ω.2
    rw [localPolySpace_eq hp]
    simpa using extDeriv_mem_polySpace hω⟩
  map_add' ω η := Subtype.ext (funext fun x => extDeriv_add_apply
    (differentiable_of_mem_c1DegForms (localPolySpace_le_c1DegForms hp _ k ω.2) x)
    (differentiable_of_mem_c1DegForms (localPolySpace_le_c1DegForms hp _ k η.2) x))
  map_smul' c ω := Subtype.ext (funext fun x => extDeriv_smul_const_apply c
    (differentiable_of_mem_c1DegForms (localPolySpace_le_c1DegForms hp _ k ω.2) x))

/-- `d : P_r⁻Λᵏ(T) → P_r⁻Λ^{k+1}(T)`. -/
def extDerivLocalMinus (hp : IsUnit (edgeMatrix p).det) (r k : ℕ) :
    localPolyMinusSpace p r k →ₗ[ℝ] localPolyMinusSpace p r (k + 1) where
  toFun ω := ⟨extDeriv ω, by
    have hω : (ω : FormField n) ∈ polyMinusSpace n r k := by
      rw [← localPolyMinusSpace_eq hp]; exact ω.2
    rw [localPolyMinusSpace_eq hp]
    exact extDeriv_mem_polyMinusSpace hω⟩
  map_add' ω η := Subtype.ext (funext fun x => extDeriv_add_apply
    (differentiable_of_mem_c1DegForms (localPolyMinusSpace_le_c1DegForms hp _ k ω.2) x)
    (differentiable_of_mem_c1DegForms (localPolyMinusSpace_le_c1DegForms hp _ k η.2) x))
  map_smul' c ω := Subtype.ext (funext fun x => extDeriv_smul_const_apply c
    (differentiable_of_mem_c1DegForms (localPolyMinusSpace_le_c1DegForms hp _ k ω.2) x))

theorem contDegForms_le_contForms (k : ℕ) : contDegForms n k ≤ contForms n := inf_le_left

theorem c1DegForms_le_contForms (k : ℕ) : c1DegForms n k ≤ contForms n :=
  (c1DegForms_le_contDegForms k).trans (contDegForms_le_contForms k)

/-- **The canonical interpolant** `Π_T : C⁰Λᵏ → P_rΛᵏ(T)`, defined by the degrees of freedom:
`∫_f tr_f (Π_T ω) ∧ η = ∫_f tr_f ω ∧ η`. [AFW2010], §5.2 -/
def polyInterp (hp : IsUnit (edgeMatrix p).det) {r k : ℕ} (hr : 1 ≤ r) (hk : k ≤ n) :
    contDegForms n k →ₗ[ℝ] localPolySpace p r k :=
  interp (isUnisolvent_localDof hp hr hk) fun i =>
    polyDof p r k i.1 i.2 ∘ₗ Submodule.inclusion (contDegForms_le_contForms k)

/-- **The canonical interpolant** `Π_T : C⁰Λᵏ → P_r⁻Λᵏ(T)`. [AFW2010], §5.2 -/
def polyMinusInterp (hp : IsUnit (edgeMatrix p).det) {r k : ℕ} (hr : 1 ≤ r) (hk : k ≤ n) :
    contDegForms n k →ₗ[ℝ] localPolyMinusSpace p r k :=
  interp (isUnisolvent_localDofMinus hp hr hk) fun i =>
    polyMinusDof p r k i.1 i.2 ∘ₗ Submodule.inclusion (contDegForms_le_contForms k)

/-- `Π_T` preserves the degrees of freedom. -/
theorem localDof_polyInterp (hp : IsUnit (edgeMatrix p).det) {r k : ℕ} (hr : 1 ≤ r)
    (hk : k ≤ n) (ω : contDegForms n k) (i : Σ f : Face n, DofIndex r k f) :
    localDof p r k i (polyInterp hp hr hk ω) = polyDof p r k i.1 i.2
      (Submodule.inclusion (contDegForms_le_contForms k) ω) :=
  dof_interp _ _ ω i

/-- `Π_T` is a projection onto `P_rΛᵏ(T)`. -/
theorem polyInterp_inclusion (hp : IsUnit (edgeMatrix p).det) {r k : ℕ} (hr : 1 ≤ r)
    (hk : k ≤ n) (ω : localPolySpace p r k) :
    polyInterp hp hr hk (Submodule.inclusion (localPolySpace_le_contDegForms hp r k) ω) = ω :=
  interp_incl (isUnisolvent_localDof hp hr hk) (fun i =>
    polyDof p r k i.1 i.2 ∘ₗ Submodule.inclusion (contDegForms_le_contForms k))
    (Submodule.inclusion (localPolySpace_le_contDegForms hp r k)) (fun _ => LinearMap.ext
      fun _ => rfl) ω

/-- `Π_T` is a projection onto `P_r⁻Λᵏ(T)`. -/
theorem polyMinusInterp_inclusion (hp : IsUnit (edgeMatrix p).det) {r k : ℕ} (hr : 1 ≤ r)
    (hk : k ≤ n) (ω : localPolyMinusSpace p r k) :
    polyMinusInterp hp hr hk
      (Submodule.inclusion (localPolyMinusSpace_le_contDegForms hp r k) ω) = ω :=
  interp_incl (isUnisolvent_localDofMinus hp hr hk) (fun i =>
    polyMinusDof p r k i.1 i.2 ∘ₗ Submodule.inclusion (contDegForms_le_contForms k))
    (Submodule.inclusion (localPolyMinusSpace_le_contDegForms hp r k)) (fun _ => LinearMap.ext
      fun _ => rfl) ω

theorem polyDof_ofEmb {r k m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1))
    (l : DofIndex r k (Face.ofEmb e)) (ω : contForms n) :
    polyDof p r k (Face.ofEmb e) l ω = faceMoment p e (testBasis r k m l : FormField m) ω := by
  change faceMoment p (Face.ofEmb e).emb _ ω = _
  rw [Face.emb_ofEmb]

theorem polyMinusDof_ofEmb {r k m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1))
    (l : DofIndexMinus r k (Face.ofEmb e)) (ω : contForms n) :
    polyMinusDof p r k (Face.ofEmb e) l ω =
      faceMoment p e (testBasisMinus r k m l : FormField m) ω := by
  change faceMoment p (Face.ofEmb e).emb _ ω = _
  rw [Face.emb_ofEmb]

theorem eq_sum_repr_basis {m : ℕ} {V : Submodule ℝ (FormField m)} {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ V) {ζ : FormField m} (hζ : ζ ∈ V) :
    ζ = ∑ l, b.repr ⟨ζ, hζ⟩ l • (b l : FormField m) := by
  have := b.sum_repr ⟨ζ, hζ⟩
  rw [Subtype.ext_iff, Submodule.coe_sum] at this
  simp only [Submodule.coe_smul] at this
  exact this.symm

/-- A moment against a test form is a combination of the degrees of freedom (on `C¹`
`k`-forms). -/
theorem faceMoment_mem_span {r k m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1)) {ζ : FormField m}
    (hζ : ζ ∈ testSpace r k m) :
    faceMomentₗ p e ζ (contDiff_of_mem_testSpace hζ).continuous ∘ₗ
        Submodule.inclusion (c1DegForms_le_contForms k) ∈
      Submodule.span ℝ (Set.range fun i : Σ f : Face n, DofIndex r k f =>
        polyDof p r k i.1 i.2 ∘ₗ Submodule.inclusion (c1DegForms_le_contForms k)) := by
  set b := testBasis r k m
  have heq : faceMomentₗ p e ζ (contDiff_of_mem_testSpace hζ).continuous ∘ₗ
      Submodule.inclusion (c1DegForms_le_contForms k) = ∑ l, b.repr ⟨ζ, hζ⟩ l •
        (polyDof p r k (Face.ofEmb e) l ∘ₗ Submodule.inclusion (c1DegForms_le_contForms k)) := by
    refine LinearMap.ext fun ω => ?_
    rw [LinearMap.sum_apply]
    have h1 : ∀ l, (b.repr ⟨ζ, hζ⟩ l • (polyDof p r k (Face.ofEmb e) l ∘ₗ
        Submodule.inclusion (c1DegForms_le_contForms k))) ω =
        b.repr ⟨ζ, hζ⟩ l * faceMoment p e (b l : FormField m) ω := fun l => by
      rw [LinearMap.smul_apply, LinearMap.comp_apply, polyDof_ofEmb, smul_eq_mul]; rfl
    rw [sum_congr rfl fun l _ => h1 l]
    have h := faceMoment_sum_smul_right p e univ (fun l => b.repr ⟨ζ, hζ⟩ l)
      (fun l => (contDiff_of_mem_testSpace (b l).2).continuous) (c1DegForms_le_contForms k ω.2)
    rw [← eq_sum_repr_basis b hζ] at h
    exact h
  rw [heq]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨⟨Face.ofEmb e, l⟩, rfl⟩)

/-- A moment against a test form of `P_r⁻` is a combination of the degrees of freedom. -/
theorem faceMoment_mem_span_minus {r k m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1))
    {ζ : FormField m} (hζ : ζ ∈ testSpaceMinus r k m) :
    faceMomentₗ p e ζ (contDiff_of_mem_testSpaceMinus hζ).continuous ∘ₗ
        Submodule.inclusion (c1DegForms_le_contForms k) ∈
      Submodule.span ℝ (Set.range fun i : Σ f : Face n, DofIndexMinus r k f =>
        polyMinusDof p r k i.1 i.2 ∘ₗ Submodule.inclusion (c1DegForms_le_contForms k)) := by
  set b := testBasisMinus r k m
  have heq : faceMomentₗ p e ζ (contDiff_of_mem_testSpaceMinus hζ).continuous ∘ₗ
      Submodule.inclusion (c1DegForms_le_contForms k) = ∑ l, b.repr ⟨ζ, hζ⟩ l •
        (polyMinusDof p r k (Face.ofEmb e) l ∘ₗ
          Submodule.inclusion (c1DegForms_le_contForms k)) := by
    refine LinearMap.ext fun ω => ?_
    rw [LinearMap.sum_apply]
    have h1 : ∀ l, (b.repr ⟨ζ, hζ⟩ l • (polyMinusDof p r k (Face.ofEmb e) l ∘ₗ
        Submodule.inclusion (c1DegForms_le_contForms k))) ω =
        b.repr ⟨ζ, hζ⟩ l * faceMoment p e (b l : FormField m) ω := fun l => by
      rw [LinearMap.smul_apply, LinearMap.comp_apply, polyMinusDof_ofEmb, smul_eq_mul]; rfl
    rw [sum_congr rfl fun l _ => h1 l]
    have h := faceMoment_sum_smul_right p e univ (fun l => b.repr ⟨ζ, hζ⟩ l)
      (fun l => (contDiff_of_mem_testSpaceMinus (b l).2).continuous)
      (c1DegForms_le_contForms k ω.2)
    rw [← eq_sum_repr_basis b hζ] at h
    exact h
  rw [heq]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨⟨Face.ofEmb e, l⟩, rfl⟩)

/-- The degrees of freedom of `dω` are combinations of those of `ω` (Stokes), for the `P` family
`P_{r+1}Λᵏ → P_rΛ^{k+1}`. -/
theorem polyDof_extDeriv_mem_span {r k : ℕ} (i : Σ f : Face n, DofIndex r (k + 1) f) :
    (polyDof p r (k + 1) i.1 i.2 ∘ₗ Submodule.inclusion (contDegForms_le_contForms (k + 1))) ∘ₗ
        extDerivC1Deg k ∈
      Submodule.span ℝ (Set.range fun i : Σ f : Face n, DofIndex (r + 1) k f =>
        polyDof p (r + 1) k i.1 i.2 ∘ₗ Submodule.inclusion (c1DegForms_le_contForms k)) := by
  obtain ⟨⟨⟨d, hd⟩, g⟩, j⟩ := i
  cases d with
  | zero =>
    exfalso
    have h0 : Module.finrank ℝ (testSpace r (k + 1) 0) = 0 := by
      rw [finrank_testSpace]; simp
    have := j.isLt
    change j.val < Module.finrank ℝ (testSpace r (k + 1) 0) at this
    omega
  | succ M =>
    change (polyDof p r (k + 1) ⟨⟨M + 1, hd⟩, g⟩ j ∘ₗ
      Submodule.inclusion (contDegForms_le_contForms (k + 1))) ∘ₗ extDerivC1Deg k ∈ _
    have hη : (testBasis r (k + 1) (M + 1) j : FormField (M + 1)) ∈ testSpace r (k + 1) (M + 1) :=
      (testBasis r (k + 1) (M + 1) j).2
    have heq : (polyDof p r (k + 1) ⟨⟨M + 1, hd⟩, g⟩ j ∘ₗ
        Submodule.inclusion (contDegForms_le_contForms (k + 1))) ∘ₗ extDerivC1Deg k =
        ∑ i : Fin (M + 2), ((-1 : ℝ) ^ (i : ℕ)) • (faceMomentₗ p
          ((Fin.succAboveOrderEmb i).trans (Face.emb ⟨⟨M + 1, hd⟩, g⟩)) _
            (contDiff_of_mem_testSpace (faceTrace_mem_testSpace hη i)).continuous ∘ₗ
          Submodule.inclusion (c1DegForms_le_contForms k)) -
        ((-1 : ℝ) ^ k) • (faceMomentₗ p (Face.emb ⟨⟨M + 1, hd⟩, g⟩) _
          (contDiff_of_mem_testSpace (extDeriv_mem_testSpace hη)).continuous ∘ₗ
          Submodule.inclusion (c1DegForms_le_contForms k)) := by
      refine LinearMap.ext fun ω => ?_
      rw [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply]
      simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
      exact faceMoment_extDeriv p (Face.emb ⟨⟨M + 1, hd⟩, g⟩) (contDiff_of_mem_testSpace hη)
        (mem_c1Forms.1 ω.2.1) ω.2.2
    rw [heq]
    refine Submodule.sub_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ (faceMoment_mem_span _ (extDeriv_mem_testSpace hη)))
    exact faceMoment_mem_span ((Fin.succAboveOrderEmb i).trans (Face.emb ⟨⟨M + 1, hd⟩, g⟩))
      (faceTrace_mem_testSpace hη i)

/-- **The commuting property** `Π_T (dω) = d (Π_T ω)` for `C¹` `k`-forms, for the `P` family
`P_{r+1}Λᵏ(T) → P_rΛ^{k+1}(T)` (`r ≥ 1`): the canonical interpolants form a cochain map. Proved
from the abstract `Feec.FiniteElement.interp_comp_eq` and Stokes' theorem on the faces.
[AFW2010], §5.2; [AFW2006], Lemma 4.24 (the local statement behind Thm 5.2) -/
theorem polyInterp_extDeriv (hp : IsUnit (edgeMatrix p).det) {r k : ℕ} (hr : 1 ≤ r)
    (hk : k + 1 ≤ n) (ω : c1DegForms n k) :
    polyInterp hp hr hk (extDerivC1Deg k ω) = extDerivLocal hp r k
      (polyInterp hp (Nat.le_add_left 1 r) (by omega)
        (Submodule.inclusion (c1DegForms_le_contDegForms k) ω)) := by
  set hℓ := isUnisolvent_localDof hp (r := r + 1) (k := k) (Nat.le_add_left 1 r) (by omega)
  set mY : (Σ f : Face n, DofIndex (r + 1) k f) → c1DegForms n k →ₗ[ℝ] ℝ := fun i =>
    polyDof p (r + 1) k i.1 i.2 ∘ₗ Submodule.inclusion (c1DegForms_le_contForms k)
  have h1 : polyInterp hp (Nat.le_add_left 1 r) (by omega)
      (Submodule.inclusion (c1DegForms_le_contDegForms k) ω) = interp hℓ mY ω :=
    hℓ.ext fun i => by rw [polyInterp, dof_interp, dof_interp]; rfl
  rw [h1]
  exact interp_comp_eq hℓ mY (isUnisolvent_localDof hp hr hk)
    (fun i => polyDof p r (k + 1) i.1 i.2 ∘ₗ
      Submodule.inclusion (contDegForms_le_contForms (k + 1)))
    (Submodule.inclusion (localPolySpace_le_c1DegForms hp (r + 1) k))
    (Submodule.inclusion (localPolySpace_le_contDegForms hp r (k + 1)))
    (fun _ => LinearMap.ext fun _ => rfl) (fun _ => LinearMap.ext fun _ => rfl)
    (extDerivC1Deg k) (extDerivLocal hp r k) (LinearMap.ext fun _ => rfl)
    polyDof_extDeriv_mem_span ω

/-- The degrees of freedom of `dω` are combinations of those of `ω` (Stokes), for the trimmed
family `P_r⁻Λᵏ → P_r⁻Λ^{k+1}`. -/
theorem polyMinusDof_extDeriv_mem_span {r k : ℕ} (i : Σ f : Face n, DofIndexMinus r (k + 1) f) :
    (polyMinusDof p r (k + 1) i.1 i.2 ∘ₗ
        Submodule.inclusion (contDegForms_le_contForms (k + 1))) ∘ₗ extDerivC1Deg k ∈
      Submodule.span ℝ (Set.range fun i : Σ f : Face n, DofIndexMinus r k f =>
        polyMinusDof p r k i.1 i.2 ∘ₗ Submodule.inclusion (c1DegForms_le_contForms k)) := by
  obtain ⟨⟨⟨d, hd⟩, g⟩, j⟩ := i
  cases d with
  | zero =>
    exfalso
    have h0 : Module.finrank ℝ (testSpaceMinus r (k + 1) 0) = 0 := by
      rw [testSpaceMinus_eq_bot (by omega)]; simp
    have := j.isLt
    change j.val < Module.finrank ℝ (testSpaceMinus r (k + 1) 0) at this
    omega
  | succ M =>
    change (polyMinusDof p r (k + 1) ⟨⟨M + 1, hd⟩, g⟩ j ∘ₗ
      Submodule.inclusion (contDegForms_le_contForms (k + 1))) ∘ₗ extDerivC1Deg k ∈ _
    have hη : (testBasisMinus r (k + 1) (M + 1) j : FormField (M + 1)) ∈
        testSpaceMinus r (k + 1) (M + 1) := (testBasisMinus r (k + 1) (M + 1) j).2
    have heq : (polyMinusDof p r (k + 1) ⟨⟨M + 1, hd⟩, g⟩ j ∘ₗ
        Submodule.inclusion (contDegForms_le_contForms (k + 1))) ∘ₗ extDerivC1Deg k =
        ∑ i : Fin (M + 2), ((-1 : ℝ) ^ (i : ℕ)) • (faceMomentₗ p
          ((Fin.succAboveOrderEmb i).trans (Face.emb ⟨⟨M + 1, hd⟩, g⟩)) _
            (contDiff_of_mem_testSpaceMinus (faceTrace_mem_testSpaceMinus hη i)).continuous ∘ₗ
          Submodule.inclusion (c1DegForms_le_contForms k)) -
        ((-1 : ℝ) ^ k) • (faceMomentₗ p (Face.emb ⟨⟨M + 1, hd⟩, g⟩) _
          (contDiff_of_mem_testSpaceMinus (extDeriv_mem_testSpaceMinus hη)).continuous ∘ₗ
          Submodule.inclusion (c1DegForms_le_contForms k)) := by
      refine LinearMap.ext fun ω => ?_
      rw [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply]
      simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
      exact faceMoment_extDeriv p (Face.emb ⟨⟨M + 1, hd⟩, g⟩)
        (contDiff_of_mem_testSpaceMinus hη) (mem_c1Forms.1 ω.2.1) ω.2.2
    rw [heq]
    refine Submodule.sub_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ (faceMoment_mem_span_minus _ (extDeriv_mem_testSpaceMinus hη)))
    exact faceMoment_mem_span_minus
      ((Fin.succAboveOrderEmb i).trans (Face.emb ⟨⟨M + 1, hd⟩, g⟩))
      (faceTrace_mem_testSpaceMinus hη i)

/-- **The commuting property** `Π_T (dω) = d (Π_T ω)` for `C¹` `k`-forms, for the trimmed
family `P_r⁻Λᵏ(T) → P_r⁻Λ^{k+1}(T)` (`r ≥ 1`). [AFW2010], §5.2; [AFW2006], Lemma 4.24 (the local statement behind Thm 5.2) -/
theorem polyMinusInterp_extDeriv (hp : IsUnit (edgeMatrix p).det) {r k : ℕ} (hr : 1 ≤ r)
    (hk : k + 1 ≤ n) (ω : c1DegForms n k) :
    polyMinusInterp hp hr hk (extDerivC1Deg k ω) = extDerivLocalMinus hp r k
      (polyMinusInterp hp hr (by omega)
        (Submodule.inclusion (c1DegForms_le_contDegForms k) ω)) := by
  set hℓ := isUnisolvent_localDofMinus hp (r := r) (k := k) hr (by omega)
  set mY : (Σ f : Face n, DofIndexMinus r k f) → c1DegForms n k →ₗ[ℝ] ℝ := fun i =>
    polyMinusDof p r k i.1 i.2 ∘ₗ Submodule.inclusion (c1DegForms_le_contForms k)
  have h1 : polyMinusInterp hp hr (by omega)
      (Submodule.inclusion (c1DegForms_le_contDegForms k) ω) = interp hℓ mY ω :=
    hℓ.ext fun i => by rw [polyMinusInterp, dof_interp, dof_interp]; rfl
  rw [h1]
  exact interp_comp_eq hℓ mY (isUnisolvent_localDofMinus hp hr hk)
    (fun i => polyMinusDof p r (k + 1) i.1 i.2 ∘ₗ
      Submodule.inclusion (contDegForms_le_contForms (k + 1)))
    (Submodule.inclusion (localPolyMinusSpace_le_c1DegForms hp r k))
    (Submodule.inclusion (localPolyMinusSpace_le_contDegForms hp r (k + 1)))
    (fun _ => LinearMap.ext fun _ => rfl) (fun _ => LinearMap.ext fun _ => rfl)
    (extDerivC1Deg k) (extDerivLocalMinus hp r k) (LinearMap.ext fun _ => rfl)
    polyMinusDof_extDeriv_mem_span ω

/-! ### Dimensions of the bubble spaces ([AFW2006], §4.5–4.6) -/

theorem isUnit_det_edgeMatrix_refVertex : IsUnit (edgeMatrix (refVertex n)).det := by
  rw [edgeMatrix_refVertex, Matrix.det_one]; exact isUnit_one

/-- The simplex itself, as its top-dimensional face. -/
def Face.top (n : ℕ) : Face n := ⟨⟨n, Nat.lt_succ_self n⟩, ⟨univ, by simp⟩⟩

theorem Face.coe_emb_top : ((Face.top n).emb : Fin (n + 1) → Fin (n + 1)) = id :=
  (orderEmbOfFin_unique (Face.top n).2.2 (fun x => mem_univ x) strictMono_id).symm

theorem Face.dim_lt_of_subset {m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1)) (hm : m < n) {g : Face n}
    (hg : g.2.1 ⊆ (Face.ofEmb e).2.1) : g.dim < n := by
  have h1 := card_le_card hg
  rw [g.2.2, (Face.ofEmb e).2.2] at h1
  change g.dim + 1 ≤ m + 1 at h1
  omega

/-- **`P̊_rΛᵏ(T̂)` is dual to `P⁻_{r+k-n}Λ^{n-k}(T̂)`** ([AFW2006], §4.5; [AFW2010], Lemma 5.6):
the moments `ω ↦ ∫_{T̂} ω ∧ η` against a basis of `P⁻_{r+k-n}Λ^{n-k}` are a bijection from the
bubbles onto the coefficient vectors, so `dim P̊_rΛᵏ(T̂) = dim P⁻_{r+k-n}Λ^{n-k}(ℝⁿ)`. -/
theorem finrank_bubbleSpace_polySpace {r k : ℕ} (hr : 1 ≤ r) (hk : k ≤ n) :
    Module.finrank ℝ (bubbleSpace (refVertex n) (polySpace n r k)) =
      Module.finrank ℝ (testSpace r k n) := by
  have hp := isUnit_det_edgeMatrix_refVertex (n := n)
  set b := testBasis r k n
  have hcont : bubbleSpace (refVertex n) (polySpace n r k) ≤ contForms n := fun ω h =>
    (polySpace_le_c1 h.1).continuous
  set Φ : bubbleSpace (refVertex n) (polySpace n r k) →ₗ[ℝ]
      (Fin (Module.finrank ℝ (testSpace r k n)) → ℝ) :=
    LinearMap.pi fun j => faceMomentₗ (refVertex n) (Face.top n).emb (b j : FormField n)
      (contDiff_of_mem_testSpace (b j).2).continuous ∘ₗ Submodule.inclusion hcont
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ω hω
    have hj : ∀ j, faceMoment (refVertex n) (Face.top n).emb (b j : FormField n) ω = 0 :=
      fun j => congrFun hω j
    refine Subtype.ext (eq_zero_of_mem_bubbleSpace_polySpace hr ω.2 fun h η hη => ?_)
    have := faceMoment_eq_zero_of_basis (refVertex n) (Face.top n).emb b
      (fun η h => (contDiff_of_mem_testSpace h).continuous) (hcont ω.2) hj
      (by rw [testSpace_eq ⟨hk, h⟩]; exact hη)
    simp only [faceMoment, Face.coe_emb_top] at this
    change simplexIntegral (refVertex n)
      (wedgeField (faceTrace (refVertex n) id (ω : FormField n)) η) = 0 at this
    rwa [faceTrace_refVertex_id] at this
  have hsurj : Function.Surjective Φ := by
    intro c
    set hℓ := isUnisolvent_localDof hp hr hk
    set c' : (Σ f : Face n, DofIndex r k f) → ℝ := fun i =>
      if h : i.1.dim = n then c ⟨i.2.val, lt_of_lt_of_eq i.2.isLt (by rw [h])⟩ else 0
    set ω := hℓ.equiv.symm c'
    have hω : (ω : FormField n) ∈ polySpace n r k := localPolySpace_eq hp r k ▸ ω.2
    have hbub : IsBubble (refVertex n) ω := by
      intro m e hm
      have h := faceTrace_eq_of_localDof_eq hp hr (Face.ofEmb e) (ω := ω) (ω' := 0)
        fun g hg i => by
          rw [map_zero, hℓ.dof_equiv_symm]
          simp only [c', (Face.dim_lt_of_subset e hm hg).ne, ↓reduceDIte]
      rw [Face.emb_ofEmb] at h
      rw [h]; simp
    refine ⟨⟨ω, hω, hbub⟩, funext fun j => ?_⟩
    have := hℓ.dof_equiv_symm c' ⟨Face.top n, j⟩
    simp only [c', Face.top, ↓reduceDIte] at this
    exact this
  rw [(LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_fin_fun]

/-- **`P̊_r⁻Λᵏ(T̂)` is dual to `P_{r+k-n-1}Λ^{n-k}(T̂)`** ([AFW2006], §4.6; [AFW2010], Lemma 5.6):
`dim P̊_r⁻Λᵏ(T̂) = dim P_{r+k-n-1}Λ^{n-k}(ℝⁿ)`. -/
theorem finrank_bubbleSpace_polyMinusSpace {r k : ℕ} (hr : 1 ≤ r) (hk : k ≤ n) :
    Module.finrank ℝ (bubbleSpace (refVertex n) (polyMinusSpace n r k)) =
      Module.finrank ℝ (testSpaceMinus r k n) := by
  have hp := isUnit_det_edgeMatrix_refVertex (n := n)
  set b := testBasisMinus r k n
  have hcont : bubbleSpace (refVertex n) (polyMinusSpace n r k) ≤ contForms n := fun ω h =>
    (contDiff_of_mem_polyMinusSpace h.1).continuous
  set Φ : bubbleSpace (refVertex n) (polyMinusSpace n r k) →ₗ[ℝ]
      (Fin (Module.finrank ℝ (testSpaceMinus r k n)) → ℝ) :=
    LinearMap.pi fun j => faceMomentₗ (refVertex n) (Face.top n).emb (b j : FormField n)
      (contDiff_of_mem_testSpaceMinus (b j).2).continuous ∘ₗ Submodule.inclusion hcont
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ω hω
    have hj : ∀ j, faceMoment (refVertex n) (Face.top n).emb (b j : FormField n) ω = 0 :=
      fun j => congrFun hω j
    refine Subtype.ext (eq_zero_of_mem_bubbleSpace_polyMinusSpace hr ω.2 fun h η hη => ?_)
    have := faceMoment_eq_zero_of_basis (refVertex n) (Face.top n).emb b
      (fun η h => (contDiff_of_mem_testSpaceMinus h).continuous) (hcont ω.2) hj
      (by rw [testSpaceMinus_eq ⟨hk, h⟩]; exact hη)
    simp only [faceMoment, Face.coe_emb_top] at this
    change simplexIntegral (refVertex n)
      (wedgeField (faceTrace (refVertex n) id (ω : FormField n)) η) = 0 at this
    rwa [faceTrace_refVertex_id] at this
  have hsurj : Function.Surjective Φ := by
    intro c
    set hℓ := isUnisolvent_localDofMinus hp hr hk
    set c' : (Σ f : Face n, DofIndexMinus r k f) → ℝ := fun i =>
      if h : i.1.dim = n then c ⟨i.2.val, lt_of_lt_of_eq i.2.isLt (by rw [h])⟩ else 0
    set ω := hℓ.equiv.symm c'
    have hω : (ω : FormField n) ∈ polyMinusSpace n r k := localPolyMinusSpace_eq hp r k ▸ ω.2
    have hbub : IsBubble (refVertex n) ω := by
      intro m e hm
      have h := faceTrace_eq_of_localDofMinus_eq hp hr (Face.ofEmb e) (ω := ω) (ω' := 0)
        fun g hg i => by
          rw [map_zero, hℓ.dof_equiv_symm]
          simp only [c', (Face.dim_lt_of_subset e hm hg).ne, ↓reduceDIte]
      rw [Face.emb_ofEmb] at h
      rw [h]; simp
    refine ⟨⟨ω, hω, hbub⟩, funext fun j => ?_⟩
    have := hℓ.dof_equiv_symm c' ⟨Face.top n, j⟩
    simp only [c', Face.top, ↓reduceDIte] at this
    exact this
  rw [(LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_fin_fun]

end Feec.FiniteElement
