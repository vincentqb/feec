module

public import Feec.FiniteElement.LocalSpace
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Degrees of freedom of `P_rΛᵏ(T)` and `P_r⁻Λᵏ(T)`

TODO
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
def Face.ofEmb {m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1)) : Face n :=
  ⟨⟨m, by have := Fintype.card_le_of_injective e e.injective; simp at this; omega⟩,
    ⟨univ.map e.toEmbedding, by simp⟩⟩

@[simp] theorem Face.dim_ofEmb {m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1)) :
    (Face.ofEmb e).dim = m := rfl

theorem Face.emb_ofEmb {m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1)) : (Face.ofEmb e).emb = e := by
  refine DFunLike.ext' (orderEmbOfFin_unique _ (fun x => ?_) e.strictMono).symm
  simp [Face.ofEmb]

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
  rw [polySpace, Koszul.finrank_map_of_injOn _ _ fun x _ hx => evalForm_injective (by rw [hx, map_zero]),
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

/-- The **moment** `ω ↦ ∫_f tr_f ω ∧ η` on the face `f` of `p`, with the test form `η` on the
reference face `T̂_{dim f}` (the face is oriented by its vertex order). -/
theorem continuous_faceTrace (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) {ω : FormField n} (hω : Continuous ω) :
    Continuous (faceTrace p e ω) :=
  continuous_affinePullback _ _ hω

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
  have := hdof n (OrderEmbedding.ofStrictMono id strictMono_id) η (by rw [testSpace_eq ⟨by omega, h⟩]; exact hη)
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
  have := hdof n (OrderEmbedding.ofStrictMono id strictMono_id) η (by rw [testSpaceMinus_eq ⟨by omega, h⟩]; exact hη)
  rw [faceMoment] at this
  simpa [faceTrace_refVertex_id] using this

end Feec.FiniteElement
