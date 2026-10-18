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
  simp only [Face.ofEmb, mem_map, mem_univ, true_and, RelEmbedding.coe_toEmbedding,
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
structure LocalElement (p : Fin (n + 1) → Fin n → ℝ) where
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
def polyLocalElement (hp : IsUnit (edgeMatrix p).det) {r k : ℕ} (hr : 1 ≤ r) (hk : k ≤ n) :
    LocalElement p where
  space := localPolySpace p r k
  dofIndex := DofIndex r k
  dof f i := localDof p r k ⟨f, i⟩
  isUnisolvent := isUnisolvent_localDof hp hr hk
  faceTrace_eq f _ _ h := faceTrace_eq_of_localDof_eq hp hr f h

/-- **The finite element `P_r⁻Λᵏ(T)`** ([AFW2006], §4.6; [AFW2010], §5.2). -/
def polyMinusLocalElement (hp : IsUnit (edgeMatrix p).det) {r k : ℕ} (hr : 1 ≤ r)
    (hk : k ≤ n) : LocalElement p where
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

end Feec.FiniteElement
