module

public import Feec.FiniteElement.Stokes
public import Feec.FiniteElement.Dof
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Fintype.Powerset
public import Feec.Algebra.PolynomialForm

/-!
# Whitney forms and the lowest-order finite element spaces `P₁⁻Λᵏ(T)`

Let `T` be an `n`-simplex in `ℝⁿ` with vertices `p₀, …, pₙ` and barycentric coordinates
`λ₀, …, λₙ` (affine, `Σᵢ λᵢ = 1`, `λᵢ(pⱼ) = δᵢⱼ`). For a `k`-face `f = {f₀ < ⋯ < f_k}` of `T`
(a `(k+1)`-subset of the vertices) the **Whitney form** is

  `φ_f = k! Σᵢ (-1)ⁱ λ_{fᵢ} dλ_{f₀} ∧ ⋯ ∧ dλ_{fᵢ}^ ∧ ⋯ ∧ dλ_{f_k}`,

and `P₁⁻Λᵏ(T)` is their span ([Whitney1957], Ch. IV, §27, [AFW2006], §3–4, [Arnold2018], Ch. 7).
The degrees of freedom are the integrals `ℓ_g ω = ∫_g ω` over the `k`-faces `g` of `T`
(`Feec.FiniteElement.simplexIntegral` over the face oriented by increasing vertex order).

## Main definitions

* `Feec.ExteriorFibre.whitneyFibre c θ g = Σ_{i ∈ g} ε(i, g) cᵢ θ_{g ∖ i}^∧`, the algebraic Whitney
  form;
* `Feec.FiniteElement.baryCoord p`, `baryGrad p`: barycentric coordinates and their gradients;
* `Feec.FiniteElement.whitneyForm p f`, `Feec.FiniteElement.whitneySpace p k = P₁⁻Λᵏ(T)`;
* `Feec.FiniteElement.contForms n`, `c1Forms n`: continuous and `C¹` form fields, and
  `extDerivC1 : C¹ → C⁰`;
* `Feec.FiniteElement.faceDof p k g`: the degree of freedom `ω ↦ ∫_g ω` on continuous forms,
  `whitneyDof p k g` its restriction to `P₁⁻Λᵏ(T)`;
* `Feec.FiniteElement.whitneyInterp hp k`: the canonical interpolant `Π_T`;
* `Feec.FiniteElement.evalForm n`: polynomial forms (`Feec.Koszul.PolyForm`) as form fields.

## Main results

* `Feec.ExteriorFibre.wedgeProd_eq_sum_whitneyFibre`: `θ_f^∧ = Σ_{j ∉ f} ε(j, f) W_{f ∪ j}` when
  `Σ c = 1` and `Σ θ = 0`; `Feec.ExteriorFibre.interior_wedgeProd`: contraction is an
  antiderivation, `ι_x θ_g^∧ = W_g` with the scalars `⟨θᵢ, x⟩`, and
  `Feec.ExteriorFibre.pullback_interior`: `B^*(ι_{Bx} α) = ι_x B^* α`;
* `simplexIntegral_whitneyForm`: **the Kronecker property** `∫_g φ_f = δ_{fg}`;
* `extDeriv_whitneyForm`: `dφ_f = (k+1)! dλ_{f₀} ∧ ⋯ ∧ dλ_{f_k}`,
  `extDeriv_whitneyForm_eq_sum`: `dφ_f = Σ_{j ∉ f} ε(j, f) φ_{f ∪ j}`, and
  `extDeriv_mem_whitneySpace`: `d` maps `P₁⁻Λᵏ(T)` into `P₁⁻Λ^{k+1}(T)`;
* `linearIndependent_whitneyForm`, `finrank_whitneySpace`:
  `dim P₁⁻Λᵏ(T) = (n+1 choose k+1)`;
* `isUnisolvent_whitneyDof`: the face integrals are unisolvent on `P₁⁻Λᵏ(T)`;
* `whitneyInterp_eq_sum`: `Π_T ω = Σ_g (∫_g ω) φ_g`;
* `whitneySpace_refVertex_eq_map_polyFormMinus`: on the reference simplex,
  `P₁⁻Λᵏ(T̂) = P₀Λᵏ + κ H₀Λ^{k+1}` is `Feec.Koszul.polyFormMinus 1 k`;
* `affinePullback_whitneyForm_face`: the trace of `φ_f` on a face is the Whitney form of the face
  (or zero if `f` is not a face of it).

## References

* [H. Whitney, *Geometric Integration Theory*][Whitney1957], Ch. IV, §27 (Whitney forms)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3–4 (Whitney forms, `P_r⁻Λᵏ = P_{r-1}Λᵏ + κ H_{r-1}Λ^{k+1}`, degrees of freedom)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MeasureTheory

@[expose] public noncomputable section

namespace Feec.ExteriorFibre

variable {R : Type*} [CommRing R] {d : Type*} [LinearOrder d] {ι : Type*} [LinearOrder ι]

/-- The algebraic Whitney form `W_g = Σ_{i ∈ g} ε(i, g) cᵢ θ_{g ∖ i}^∧` of the scalars `c` and the
covectors `θ` (at a point: `c = λ(x)`, `θ = dλ`). -/
def whitneyFibre (c : ι → R) (θ : ι → d → R) (g : Finset ι) : Finset d → R :=
  ∑ i ∈ g, (sgn i g * c i) • wedgeProd θ (g.erase i)

/-- **The basic identity of Whitney forms**: if `Σ cᵢ = 1` and `Σ θᵢ = 0` then
`θ_f^∧ = Σ_{j ∉ f} ε(j, f) W_{f ∪ j}`. -/
theorem wedgeProd_eq_sum_whitneyFibre [Fintype ι] {c : ι → R} {θ : ι → d → R}
    (hc : ∑ i, c i = 1) (hθ : ∑ i, θ i = 0) (f : Finset ι) :
    wedgeProd θ f = ∑ j ∈ fᶜ, (sgn j f : R) • whitneyFibre c θ (insert j f) := by
  -- expand each `W_{f ∪ j}` into the term `i = j` and the terms `i ∈ f`
  have hexp : ∀ j ∈ fᶜ, (sgn j f : R) • whitneyFibre c θ (insert j f) =
      c j • wedgeProd θ f - ∑ i ∈ f, (sgn i f * c i) • wedge (θ j) (wedgeProd θ (f.erase i)) := by
    intro j hj
    have hjf : j ∉ f := mem_compl.1 hj
    rw [whitneyFibre, sum_insert hjf, sgn_insert_self, erase_insert hjf, smul_add, smul_smul,
      ← mul_assoc, sgn_mul_self, one_mul, smul_sum, sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    have hij : i ≠ j := fun h => hjf (h ▸ hi)
    have hji : j ∉ f.erase i := fun h => hjf (mem_of_mem_erase h)
    rw [erase_insert_of_ne hij.symm, wedgeProd_insert θ hji, sgn_insert hjf, sgn_erase hi]
    simp only [smul_smul]
    rw [← neg_smul]
    congr 1
    have := ite_lt_add_ite_lt (R := R) hij
    have h2 := sgn_mul_self (R := R) j f
    rcases lt_or_gt_of_ne hij with h | h
    · simp only [h, not_lt.2 h.le, ↓reduceIte] at this ⊢
      linear_combination (-(sgn i f * c i)) * h2
    · simp only [h, not_lt.2 h.le, ↓reduceIte] at this ⊢
      linear_combination (-(sgn i f * c i)) * h2
  rw [sum_congr rfl hexp, sum_sub_distrib, sum_comm]
  -- `Σ_{j ∉ f} θⱼ ∧ θ_{f∖i}^∧ = -θᵢ ∧ θ_{f∖i}^∧ = -ε(i, f) θ_f^∧`
  have hin : ∀ i ∈ f, ∑ j ∈ fᶜ, (sgn i f * c i) • wedge (θ j) (wedgeProd θ (f.erase i)) =
      -(c i • wedgeProd θ f) := by
    intro i hi
    rw [← smul_sum, ← wedge_sum_left]
    have hsplit : ∑ j ∈ fᶜ, θ j = -∑ j ∈ f, θ j := by
      rw [eq_neg_iff_add_eq_zero, add_comm, sum_add_sum_compl, hθ]
    have hone : ∑ j ∈ f, wedge (θ j) (wedgeProd θ (f.erase i)) =
        wedge (θ i) (wedgeProd θ (f.erase i)) := by
      rw [← add_sum_erase f _ hi, sum_eq_zero (fun j hj => wedge_wedgeProd_of_mem θ hj),
        add_zero]
    rw [hsplit, wedge_neg_left, wedge_sum_left, hone,
      wedge_wedgeProd_of_notMem θ (notMem_erase i f), insert_erase hi, sgn_erase_self, smul_neg,
      smul_smul]
    rw [show sgn i f * c i * sgn i f = (sgn i f * sgn i f) * c i by ring, sgn_mul_self, one_mul]
  rw [sum_congr rfl hin, sum_neg_distrib, sub_neg_eq_add, ← sum_smul, ← sum_smul, ← add_smul,
    sum_compl_add_sum, hc, one_smul]

theorem whitneyFibre_map {ι' : Type*} [LinearOrder ι'] (c : ι' → R) (θ : ι' → d → R)
    (e : ι ↪o ι') (s : Finset ι) :
    whitneyFibre c θ (s.map e.toEmbedding) = whitneyFibre (c ∘ e) (θ ∘ e) s := by
  rw [whitneyFibre, whitneyFibre, sum_map]
  refine sum_congr rfl fun i _ => ?_
  simp only [RelEmbedding.coe_toEmbedding]
  have : (s.map e.toEmbedding).erase (e i) = (s.erase i).map e.toEmbedding := by
    rw [Finset.map_erase]; rfl
  rw [sgn_map, this, wedgeProd_map]
  rfl

theorem pullback_whitneyFibre [Fintype ι] {κ : Type*} [LinearOrder κ] {μ : Type*} [LinearOrder μ]
    (B : ι → κ → R) (c : μ → R) (θ : μ → ι → R) (g : Finset μ) :
    pullback B (whitneyFibre c θ g) = whitneyFibre c (fun a => covPullback B (θ a)) g := by
  simp only [whitneyFibre, pullback_sum, pullback_smul, pullback_wedgeProd]

theorem isDeg_whitneyFibre (c : ι → R) (θ : ι → d → R) {k : ℕ} {g : Finset ι}
    (hg : #g = k + 1) : IsDeg k (whitneyFibre c θ g) := by
  intro t ht
  simp only [whitneyFibre, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine sum_eq_zero fun i hi => ?_
  rw [isDeg_wedgeProd θ (g.erase i) t (by rw [card_erase_of_mem hi, hg]; simpa using ht),
    mul_zero]

/-- Splitting off a minimal vertex: `W_{a ∪ g} = c_a θ_g^∧ - θ_a ∧ W_g` for `a < g`. -/
theorem whitneyFibre_insert_of_lt (c : ι → R) (θ : ι → d → R) {a : ι} {g : Finset ι}
    (h : ∀ i ∈ g, a < i) :
    whitneyFibre c θ (insert a g) = c a • wedgeProd θ g - wedge (θ a) (whitneyFibre c θ g) := by
  have hag : a ∉ g := fun h' => lt_irrefl a (h a h')
  have hsa : (sgn a (insert a g) : R) = 1 := by
    rw [sgn, filter_eq_empty_iff.2 fun x hx => ?_]
    · simp
    · rcases mem_insert.1 hx with rfl | hx
      · exact lt_irrefl _
      · exact not_lt.2 (h x hx).le
  rw [whitneyFibre, sum_insert hag, hsa, one_mul, erase_insert hag, whitneyFibre, wedge_sum,
    sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  rw [sgn_insert hag, ite_eq_left_of_eq_true _ _ (eq_true (h i hi)),
    erase_insert_of_ne (ne_of_lt (h i hi)),
    wedgeProd_insert_of_lt θ fun x hx => h x (mem_of_mem_erase hx), wedge_smul, ← neg_smul]
  congr 1
  ring

/-- With the coordinate covectors, the Whitney form is the contraction `W_g = ι_c dx_g`. -/
theorem whitneyFibre_single_eq_interior [Fintype d] (x : d → R) (g : Finset d) :
    whitneyFibre x (fun j => Pi.single j 1) g = interior x (Pi.single g 1) := by
  funext s
  set F : d → R := fun i => sgn i g * x i * (Pi.single (g.erase i) (1 : R) : Finset d → R) s
  set G : d → R := fun j => sgn j s * x j * (Pi.single g (1 : R) : Finset d → R) (insert j s)
  have hL : whitneyFibre x (fun j => Pi.single j 1) g s = ∑ i, if i ∈ g then F i else 0 := by
    rw [sum_ite_mem, univ_inter]
    simp only [whitneyFibre, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, wedgeProd_single, F]
  have hR : interior x (Pi.single g 1) s = ∑ j, if j ∈ sᶜ then G j else 0 := by
    rw [sum_ite_mem, univ_inter]
    rfl
  rw [hL, hR]
  refine sum_congr rfl fun j _ => ?_
  simp only [F, G, Pi.single_apply, mem_compl]
  by_cases hj : j ∈ g ∧ s = g.erase j
  · obtain ⟨hjg, rfl⟩ := hj
    simp [hjg, insert_erase hjg, sgn_erase_self]
  · have hjs : ¬(j ∉ s ∧ insert j s = g) := by
      rintro ⟨hjs, rfl⟩
      exact hj ⟨mem_insert_self _ _, (erase_insert hjs).symm⟩
    by_cases h1 : j ∈ g
    · have h2 : s ≠ g.erase j := fun h => hj ⟨h1, h⟩
      by_cases h3 : j ∈ s
      · simp [h1, h2, h3]
      · have h4 : insert j s ≠ g := fun h => hjs ⟨h3, h⟩
        simp [h1, h2, h3, h4]
    · by_cases h3 : j ∈ s
      · simp [h1, h3]
      · have h4 : insert j s ≠ g := fun h => hjs ⟨h3, h⟩
        simp [h1, h3, h4]

theorem interior_eq_sum_single [Fintype d] (x : d → R) (β : Finset d → R) :
    interior x β = ∑ t, β t • interior x (Pi.single t 1) := by
  funext s
  simp only [interior_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_eq_single (insert j s) (fun t _ ht => by simp [Ne.symm ht])
    (by simp)]
  simp only [Pi.single_eq_same, mul_one]
  ring

theorem isDeg_single {k : ℕ} {g : Finset d} (hg : #g = k) : IsDeg k (Pi.single g (1 : R)) := by
  intro s hs
  have : s ≠ g := fun h => hs (h ▸ hg)
  simp [this]

theorem interior_sum [Fintype d] {β : Type*} (x : d → R) (u : Finset β) (ω : β → Finset d → R) :
    interior x (∑ b ∈ u, ω b) = ∑ b ∈ u, interior x (ω b) := by
  funext s; simp only [interior_apply, Finset.sum_apply, mul_sum]; exact sum_comm

/-- **Contraction is an antiderivation**: `ι_x (θ_{g₁} ∧ ⋯ ∧ θ_{g_k}) = W_g` with the scalars
`⟨θᵢ, x⟩`. -/
theorem interior_wedgeProd [Fintype d] (θ : ι → d → R) (x : d → R) (g : Finset ι) :
    interior x (wedgeProd θ g) = whitneyFibre (fun i => ∑ l, θ i l * x l) θ g := by
  induction g using Finset.induction_on_min with
  | empty =>
    funext s
    simp only [wedgeProd_empty, interior_apply, whitneyFibre, sum_empty, Pi.zero_apply]
    refine sum_eq_zero fun j hj => ?_
    have : insert j s ≠ ∅ := insert_ne_empty j s
    simp [this]
  | insert a g ha ih =>
    rw [wedgeProd_insert_of_lt _ ha, whitneyFibre_insert_of_lt _ _ ha, ← ih]
    have h := wedge_interior_add_interior_wedge (θ a) x (wedgeProd θ g)
    rw [eq_sub_of_add_eq' h]

/-- **Pullback commutes with contraction**: `B^*(ι_{Bx} α) = ι_x (B^* α)`. -/
theorem pullback_interior [Fintype ι] {κ : Type*} [LinearOrder κ] [Fintype κ]
    (B : ι → κ → R) (x : κ → R) (α : Finset ι → R) :
    pullback B (interior (fun i => ∑ l, B i l * x l) α) = interior x (pullback B α) := by
  rw [interior_eq_sum_single, pullback_sum, pullback]
  rw [interior_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [pullback_smul, interior_smul, ← whitneyFibre_single_eq_interior, pullback_whitneyFibre,
    interior_wedgeProd]
  congr 2
  funext a l
  simp [covPullback, Pi.single_apply]

end Feec.ExteriorFibre

namespace Feec.FiniteElement

open ExteriorFibre

variable {n k : ℕ}

/-! ### Barycentric coordinates of an `n`-simplex in `ℝⁿ` -/

/-- The edge matrix of `p` as a square matrix. -/
abbrev edgeMatrix (p : Fin (n + 1) → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (simplexMatrix p)

/-- The barycentric coordinates `λ(x) = λ̂(F_p⁻¹ x)` of the simplex `p`. -/
def baryCoord (p : Fin (n + 1) → Fin n → ℝ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  refBary (Matrix.mulVec (edgeMatrix p)⁻¹ (x - p 0))

/-- The gradients `dλᵢ` of the barycentric coordinates (constant covectors). -/
def baryGrad (p : Fin (n + 1) → Fin n → ℝ) : Fin (n + 1) → Fin n → ℝ :=
  Fin.cons (fun l => -∑ m, (edgeMatrix p)⁻¹ m l) fun m l => (edgeMatrix p)⁻¹ m l

theorem sum_baryCoord (p : Fin (n + 1) → Fin n → ℝ) (x : Fin n → ℝ) :
    ∑ i, baryCoord p x i = 1 := by
  simp only [baryCoord]; exact sum_refBary _

theorem sum_baryGrad (p : Fin (n + 1) → Fin n → ℝ) : ∑ i, baryGrad p i = 0 := by
  funext l
  simp [baryGrad, Fin.sum_univ_succ, Finset.sum_apply]

/-- `λᵢ` is affine with gradient `dλᵢ`: `λᵢ(x) = Σₗ (dλᵢ)ₗ xₗ + λᵢ(0)`. -/
theorem baryCoord_apply (p : Fin (n + 1) → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin (n + 1)) :
    baryCoord p x i = ∑ l, baryGrad p i l * x l + baryCoord p 0 i := by
  refine Fin.cases ?_ (fun m => ?_) i
  · simp only [baryCoord, refBary_zero, baryGrad, Fin.cons_zero, Matrix.mulVec, dotProduct,
      Pi.sub_apply, Pi.neg_apply, zero_sub, mul_sub, mul_neg, sum_sub_distrib, sum_neg_distrib,
      neg_mul, sum_mul]
    rw [sum_comm (s := univ) (t := univ) (f := fun l m => (edgeMatrix p)⁻¹ m l * x l)]
    ring
  · simp only [baryCoord, refBary_succ, baryGrad, Fin.cons_succ, Matrix.mulVec, dotProduct,
      Pi.sub_apply, Pi.neg_apply, zero_sub, mul_sub, mul_neg, sum_sub_distrib, sum_neg_distrib]
    ring

theorem baryCoord_sub (p : Fin (n + 1) → Fin n → ℝ) (x y : Fin n → ℝ) (i : Fin (n + 1)) :
    baryCoord p x i - baryCoord p y i = ∑ l, baryGrad p i l * (x l - y l) := by
  rw [baryCoord_apply p x, baryCoord_apply p y, mul_sub_sum]
  ring
where
  mul_sub_sum : ∑ l, baryGrad p i l * (x l - y l) =
      ∑ l, baryGrad p i l * x l - ∑ l, baryGrad p i l * y l := by
    rw [← sum_sub_distrib]; exact sum_congr rfl fun _ _ => by ring

/-- Barycentric coordinates are affine: `λ(Σ cⱼ zⱼ) = Σ cⱼ λ(zⱼ)` for `Σ cⱼ = 1`. -/
theorem baryCoord_sum_smul {ι : Type*} (p : Fin (n + 1) → Fin n → ℝ) (u : Finset ι)
    {c : ι → ℝ} (hc : ∑ j ∈ u, c j = 1) (z : ι → Fin n → ℝ) (i : Fin (n + 1)) :
    baryCoord p (∑ j ∈ u, c j • z j) i = ∑ j ∈ u, c j * baryCoord p (z j) i := by
  rw [baryCoord_apply]
  simp_rw [baryCoord_apply p (z _) i, mul_add, sum_add_distrib, ← sum_mul, hc, one_mul]
  congr 1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

variable {p : Fin (n + 1) → Fin n → ℝ}

theorem edgeMatrix_mulVec_refVertex (p : Fin (n + 1) → Fin n → ℝ) (j : Fin (n + 1)) :
    Matrix.mulVec (edgeMatrix p) (refVertex n j) = p j - p 0 := by
  have := simplexMap_refVertex p j
  rw [simplexMap] at this
  funext i
  have hi := congrFun this i
  simp only [affine_apply] at hi
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.sub_apply]
  linarith

/-- `λᵢ(pⱼ) = δᵢⱼ`. -/
theorem baryCoord_vertex (hp : IsUnit (edgeMatrix p).det) (i j : Fin (n + 1)) :
    baryCoord p (p j) i = if j = i then 1 else 0 := by
  rw [baryCoord, ← edgeMatrix_mulVec_refVertex, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hp, Matrix.one_mulVec, refBary_refVertex]

/-- `λ ∘ F_p = λ̂`. -/
theorem baryCoord_simplexMap (hp : IsUnit (edgeMatrix p).det) (x : Fin n → ℝ) :
    baryCoord p (simplexMap p x) = refBary x := by
  have : simplexMap p x - p 0 = Matrix.mulVec (edgeMatrix p) x := by
    funext i
    simp [simplexMap, affine_apply, Matrix.mulVec, dotProduct]
  rw [baryCoord, this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hp, Matrix.one_mulVec]

/-- The vertices of a Mathlib simplex have an invertible edge matrix. -/
theorem isUnit_det_edgeMatrix (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    IsUnit (edgeMatrix T.points).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_col_iff_isUnit]
  have h := (affineIndependent_iff_linearIndependent_vsub ℝ T.points 0).1 T.independent
  let e : Fin n ≃ {x : Fin (n + 1) // x ≠ 0} :=
    { toFun := fun l => ⟨l.succ, Fin.succ_ne_zero l⟩
      invFun := fun x => x.1.pred x.2
      left_inv := fun l => by simp
      right_inv := fun x => by simp }
  have h2 := h.comp e e.injective
  convert h2 using 1
  funext l
  funext i
  simp [Matrix.col, simplexMatrix, e]

/-! ### Restriction to the faces -/

/-- The gradients `dλ̂ₘ` of the barycentric coordinates of the reference simplex. -/
def refGrad (k : ℕ) (m : Fin (k + 1)) : Fin k → ℝ :=
  fun l => (if l.succ = m then 1 else 0) - if (0 : Fin (k + 1)) = m then 1 else 0

theorem sum_refGrad (k : ℕ) : ∑ m, refGrad k m = 0 := by
  funext l
  simp [refGrad, Finset.sum_apply, sum_sub_distrib]

theorem refGrad_succ (l : Fin k) : refGrad k l.succ = Pi.single l 1 := by
  funext l'
  simp [refGrad, Pi.single_apply, (Fin.succ_ne_zero l).symm]

/-- `λᵢ(F_{p ∘ e}(ŷ)) = Σₘ λ̂ₘ(ŷ) [e m = i]`. -/
theorem baryCoord_simplexMap_comp (hp : IsUnit (edgeMatrix p).det) (e : Fin (k + 1) → Fin (n + 1))
    (y : Fin k → ℝ) (i : Fin (n + 1)) :
    baryCoord p (simplexMap (p ∘ e) y) i = ∑ m, refBary y m * if e m = i then 1 else 0 := by
  rw [simplexMap_eq_sum, baryCoord_sum_smul p univ (sum_refBary y)]
  simp only [Function.comp_apply, baryCoord_vertex hp]

/-- The pullback of `dλᵢ` to the face `p ∘ e`. -/
theorem covPullback_baryGrad (hp : IsUnit (edgeMatrix p).det) (e : Fin (k + 1) → Fin (n + 1))
    (i : Fin (n + 1)) :
    covPullback (simplexMatrix (p ∘ e)) (baryGrad p i) =
      fun l => (if e l.succ = i then 1 else 0) - if e 0 = i then 1 else 0 := by
  funext l
  simp only [covPullback, simplexMatrix, Function.comp_apply]
  rw [← baryCoord_vertex hp i (e l.succ), ← baryCoord_vertex hp i (e 0), baryCoord_sub]

/-! ### Whitney forms -/

/-- The **Whitney form** of the face `f` (a set of `k + 1` vertices) of the simplex `p`:
`φ_f = k! Σᵢ (-1)ⁱ λ_{fᵢ} dλ_{f₀} ∧ ⋯ ∧ dλ_{fᵢ}^ ∧ ⋯ ∧ dλ_{f_k}`. -/
def whitneyForm (p : Fin (n + 1) → Fin n → ℝ) (f : Finset (Fin (n + 1))) : FormField n :=
  fun x => ((#f - 1).factorial : ℝ) • whitneyFibre (baryCoord p x) (baryGrad p) f

/-- Whitney forms of `k`-faces are `k`-forms. -/
theorem isDeg_whitneyForm (p : Fin (n + 1) → Fin n → ℝ) {f : Finset (Fin (n + 1))}
    (hf : #f = k + 1) (x : Fin n → ℝ) : IsDeg k (whitneyForm p f x) := by
  intro t ht
  simp only [whitneyForm, Pi.smul_apply, isDeg_whitneyFibre _ _ hf t ht, smul_zero]

/-- A Whitney form is a sum of affine functions times constant forms. -/
theorem whitneyForm_eq_sum (p : Fin (n + 1) → Fin n → ℝ) (f : Finset (Fin (n + 1))) :
    whitneyForm p f = ∑ i ∈ f, fun x =>
      (∑ l, ((#f - 1).factorial * sgn i f * baryGrad p i l) * x l +
        (#f - 1).factorial * sgn i f * baryCoord p 0 i) • wedgeProd (baryGrad p) (f.erase i) := by
  funext x
  simp only [whitneyForm, whitneyFibre, Finset.sum_apply, smul_sum, smul_smul]
  refine sum_congr rfl fun i _ => ?_
  congr 1
  rw [baryCoord_apply p x i]
  simp only [mul_add, Finset.mul_sum]
  congr 1
  · exact sum_congr rfl fun l _ => by ring
  · ring

theorem contDiff_whitneyForm (p : Fin (n + 1) → Fin n → ℝ) (f : Finset (Fin (n + 1)))
    {r : WithTop ℕ∞} : ContDiff ℝ r (whitneyForm p f) := by
  rw [whitneyForm_eq_sum, Finset.sum_fn]
  exact ContDiff.sum fun i _ => by fun_prop

/-- **`dφ_f = (k+1)! dλ_{f₀} ∧ ⋯ ∧ dλ_{f_k}`**. -/
theorem extDeriv_whitneyForm (p : Fin (n + 1) → Fin n → ℝ) {f : Finset (Fin (n + 1))}
    (hf : f.Nonempty) :
    extDeriv (whitneyForm p f) = fun _ => ((#f).factorial : ℝ) • wedgeProd (baryGrad p) f := by
  funext x
  rw [whitneyForm_eq_sum, extDeriv_sum_apply _ fun i _ => by fun_prop]
  simp only [extDeriv_affine_smul]
  have h : ∀ i ∈ f, wedge (fun l => (#f - 1).factorial * sgn i f * baryGrad p i l)
      (wedgeProd (baryGrad p) (f.erase i)) =
      ((#f - 1).factorial : ℝ) • wedgeProd (baryGrad p) f := by
    intro i hi
    rw [show (fun l => (#f - 1).factorial * sgn i f * baryGrad p i l) =
      (((#f - 1).factorial : ℝ) * sgn i f) • baryGrad p i from by
        funext l; simp [mul_assoc], wedge_smul_left,
      wedge_wedgeProd_of_notMem _ (notMem_erase i f), insert_erase hi, sgn_erase_self,
      smul_smul, mul_assoc, sgn_mul_self, mul_one]
  rw [sum_congr rfl h, sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  obtain ⟨k, hk⟩ : ∃ k, #f = k + 1 := ⟨#f - 1, (Nat.succ_pred_eq_of_pos (card_pos.2 hf)).symm⟩
  rw [hk, Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast; ring

/-- `dφ_f = Σ_{j ∉ f} ε(j, f) φ_{f ∪ j}`: the exterior derivative of a Whitney form is a
combination of Whitney forms. -/
theorem extDeriv_whitneyForm_eq_sum (p : Fin (n + 1) → Fin n → ℝ) {f : Finset (Fin (n + 1))}
    (hf : f.Nonempty) :
    extDeriv (whitneyForm p f) = ∑ j ∈ fᶜ, (sgn j f : ℝ) • whitneyForm p (insert j f) := by
  rw [extDeriv_whitneyForm p hf]
  funext x
  rw [wedgeProd_eq_sum_whitneyFibre (sum_baryCoord p x) (sum_baryGrad p) f]
  simp only [Finset.sum_apply, Pi.smul_apply, whitneyForm, smul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [card_insert_of_notMem (mem_compl.1 hj), Nat.add_sub_cancel, smul_comm]

/-- On the reference simplex, the Whitney form of the whole simplex is `dx̂₀ ∧ ⋯ ∧ dx̂_{k-1}`
(fibrewise, before the factor `k!`). -/
theorem whitneyFibre_refBary_univ (y : Fin k → ℝ) :
    whitneyFibre (refBary y) (refGrad k) univ univ = 1 := by
  have h := wedgeProd_eq_sum_whitneyFibre (sum_refBary y) (sum_refGrad k)
    (univ.erase (0 : Fin (k + 1)))
  have hc : (univ.erase (0 : Fin (k + 1)))ᶜ = {0} := by
    ext x; simp
  rw [hc, sum_singleton, insert_erase (mem_univ 0)] at h
  have hs : (sgn (0 : Fin (k + 1)) (univ.erase 0) : ℝ) = 1 := by
    rw [sgn, filter_eq_empty_iff.2 fun x _ => not_lt.2 (Fin.zero_le x)]; simp
  rw [hs, one_smul] at h
  rw [← h]
  have hmap : univ.erase (0 : Fin (k + 1)) =
      (univ : Finset (Fin k)).map (Fin.succAboveOrderEmb 0).toEmbedding := by
    ext x
    rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨x, rfl⟩
    · simp [Fin.succ_ne_zero]
    · simp [Fin.succ_ne_zero]
  rw [hmap, wedgeProd_map]
  have : (refGrad k ∘ Fin.succAboveOrderEmb 0) = fun l => Pi.single l 1 := by
    funext l
    simp [refGrad_succ]
  rw [this, wedgeProd_single]
  simp

/-! ### The Kronecker property -/

/-- The vertices of the face `g` of `p`, in increasing order. -/
def faceVertices (p : Fin (n + 1) → Fin n → ℝ) (g : Finset (Fin (n + 1))) (hg : #g = k + 1) :
    Fin (k + 1) → Fin n → ℝ :=
  p ∘ g.orderEmbOfFin hg

/-- **The Kronecker property of Whitney forms**: `∫_g φ_f = δ_{fg}` for `k`-faces `f`, `g`. -/
theorem simplexIntegral_whitneyForm (hp : IsUnit (edgeMatrix p).det) {f g : Finset (Fin (n + 1))}
    (hf : #f = k + 1) (hg : #g = k + 1) :
    simplexIntegral (faceVertices p g hg) (whitneyForm p f) = if f = g then 1 else 0 := by
  set e := g.orderEmbOfFin hg
  have hpull : ∀ y, affinePullback (simplexMatrix (faceVertices p g hg)) (faceVertices p g hg 0)
      (whitneyForm p f) y = ((#f - 1).factorial : ℝ) •
        whitneyFibre (fun a => ∑ m, refBary y m * if e m = a then 1 else 0)
          (fun a l => (if e l.succ = a then 1 else 0) - if e 0 = a then 1 else 0) f := by
    intro y
    rw [affinePullback_apply, whitneyForm, pullback_smul, pullback_whitneyFibre]
    congr 2
    · funext a
      exact baryCoord_simplexMap_comp hp e y a
    · funext a
      exact covPullback_baryGrad hp e a
  simp only [simplexIntegral, hpull]
  split_ifs with hfg
  · subst hfg
    have hfe : univ.map e.toEmbedding = f := map_orderEmbOfFin_univ f hf
    have hval : ∀ y : Fin k → ℝ, (((#f - 1).factorial : ℝ) •
        whitneyFibre (fun a => ∑ m, refBary y m * if e m = a then 1 else 0)
          (fun a (l : Fin k) => (if e l.succ = a then 1 else 0) - if e 0 = a then 1 else 0) f)
            univ = (k.factorial : ℝ) := by
      intro y
      conv_lhs => rw [← hfe, whitneyFibre_map]
      have hc : (fun a => ∑ m, refBary y m * if e m = a then 1 else 0) ∘ e = refBary y := by
        funext m
        simp only [Function.comp_apply, e.injective.eq_iff]
        rw [sum_eq_single m (fun m' _ hm' => by simp [hm']) (by simp)]
        simp
      have hθ : (fun a (l : Fin k) => (if e l.succ = a then (1 : ℝ) else 0) -
          if e 0 = a then 1 else 0) ∘ e = refGrad k := by
        funext m l
        simp only [Function.comp_apply, e.injective.eq_iff, refGrad, eq_comm]
      rw [hc, hθ, Pi.smul_apply, whitneyFibre_refBary_univ, hfe, hf, Nat.add_sub_cancel,
        smul_eq_mul,
        mul_one]
    simp only [hval]
    rw [setIntegral_const, volume_real_refSimplex, smul_eq_mul, one_div,
      inv_mul_cancel₀ (by positivity)]
  · have hsub : ¬f ⊆ g := fun h => hfg (eq_of_subset_of_card_le h (by rw [hf, hg]))
    obtain ⟨a, haf, hag⟩ := not_subset.1 hsub
    have hzero : ∀ y : Fin k → ℝ, (((#f - 1).factorial : ℝ) •
        whitneyFibre (fun a => ∑ m, refBary y m * if e m = a then 1 else 0)
          (fun a (l : Fin k) => (if e l.succ = a then 1 else 0) - if e 0 = a then 1 else 0) f)
            univ = 0 := by
      intro y
      have hne : ∀ m, e m ≠ a := fun m h => hag (h ▸ Finset.orderEmbOfFin_mem g hg m)
      rw [Pi.smul_apply, whitneyFibre]
      convert smul_zero _
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine sum_eq_zero fun i hi => ?_
      by_cases hia : i = a
      · subst hia; simp [hne]
      · rw [wedgeProd_eq_zero_of_mem (mem_erase.2 ⟨Ne.symm hia, haf⟩) (by funext l; simp [hne]),
          Pi.zero_apply, mul_zero]
    simp only [hzero, integral_zero]

/-! ### Continuous and `C¹` forms; the exterior derivative as a linear map -/

/-- Continuous form fields. -/
def contForms (n : ℕ) : Submodule ℝ (FormField n) where
  carrier := {ω | Continuous ω}
  add_mem' ha hb := Continuous.add ha hb
  zero_mem' := continuous_const
  smul_mem' c ω h := Continuous.const_smul (h : Continuous ω) c

/-- `C¹` form fields. -/
def c1Forms (n : ℕ) : Submodule ℝ (FormField n) where
  carrier := {ω | ContDiff ℝ 1 ω}
  add_mem' {a b} ha hb := by
    change ContDiff ℝ 1 (fun y => a y + b y)
    exact ContDiff.add (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
  zero_mem' := by
    change ContDiff ℝ 1 (fun _ => (0 : Finset (Fin n) → ℝ))
    exact contDiff_const
  smul_mem' c ω h := by
    change ContDiff ℝ 1 (fun y => c • ω y)
    exact ContDiff.const_smul c (h : ContDiff ℝ 1 ω)

theorem mem_contForms {ω : FormField n} : ω ∈ contForms n ↔ Continuous ω := Iff.rfl

theorem mem_c1Forms {ω : FormField n} : ω ∈ c1Forms n ↔ ContDiff ℝ 1 ω := Iff.rfl

theorem c1Forms_le_contForms : c1Forms n ≤ contForms n := fun _ h =>
  ContDiff.continuous (mem_c1Forms.1 h)

theorem continuous_extDeriv {ω : FormField n} (hω : ContDiff ℝ 1 ω) :
    Continuous (extDeriv ω) := by
  refine continuous_pi fun s => ?_
  change Continuous fun x => ∑ j ∈ s, sgn j s * partialDeriv j (fun y => ω y (s.erase j)) x
  exact continuous_finsetSum _ fun j _ =>
    continuous_const.mul ((contDiff_pi.1 hω _).continuous_partialDeriv j)

/-- The exterior derivative `d : C¹ → C⁰` as a linear map. -/
def extDerivC1 : c1Forms n →ₗ[ℝ] contForms n where
  toFun ω := ⟨extDeriv ω, continuous_extDeriv (mem_c1Forms.1 ω.2)⟩
  map_add' ω η := by
    refine Subtype.ext (funext fun x => ?_)
    exact extDeriv_add_apply ((ContDiff.differentiable (mem_c1Forms.1 ω.2) one_ne_zero) x)
      ((ContDiff.differentiable (mem_c1Forms.1 η.2) one_ne_zero) x)
  map_smul' c ω := by
    refine Subtype.ext (funext fun x => ?_)
    exact extDeriv_smul_const_apply c
      ((ContDiff.differentiable (mem_c1Forms.1 ω.2) one_ne_zero) x)

/-! ### The spaces `P₁⁻Λᵏ(T)` -/

/-- The `k`-faces of an `n`-simplex: the `(k+1)`-subsets of its vertices. -/
abbrev Faces (n k : ℕ) := {f : Finset (Fin (n + 1)) // #f = k + 1}

/-- **The Whitney space** `P₁⁻Λᵏ(T)`: the span of the Whitney forms of the `k`-faces. -/
def whitneySpace (p : Fin (n + 1) → Fin n → ℝ) (k : ℕ) : Submodule ℝ (FormField n) :=
  Submodule.span ℝ (Set.range fun f : Faces n k => whitneyForm p f.1)

theorem whitneyForm_mem_whitneySpace (p : Fin (n + 1) → Fin n → ℝ) (f : Faces n k) :
    whitneyForm p f.1 ∈ whitneySpace p k :=
  Submodule.subset_span ⟨f, rfl⟩

theorem whitneySpace_le_c1Forms (p : Fin (n + 1) → Fin n → ℝ) (k : ℕ) :
    whitneySpace p k ≤ c1Forms n :=
  Submodule.span_le.2 (Set.range_subset_iff.2 fun f => mem_c1Forms.2 (contDiff_whitneyForm p f.1))

theorem whitneySpace_le_contForms (p : Fin (n + 1) → Fin n → ℝ) (k : ℕ) :
    whitneySpace p k ≤ contForms n :=
  (whitneySpace_le_c1Forms p k).trans c1Forms_le_contForms

/-- Elements of `P₁⁻Λᵏ(T)` are `k`-forms. -/
theorem isDeg_of_mem_whitneySpace {p : Fin (n + 1) → Fin n → ℝ} {ω : FormField n}
    (hω : ω ∈ whitneySpace p k) (x : Fin n → ℝ) : IsDeg k (ω x) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hω
  intro t ht
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact sum_eq_zero fun f _ => by rw [isDeg_whitneyForm p f.2 x t ht, mul_zero]

/-- **`d P₁⁻Λᵏ(T) ⊆ P₁⁻Λ^{k+1}(T)`**. -/
theorem extDeriv_mem_whitneySpace {p : Fin (n + 1) → Fin n → ℝ} {ω : FormField n}
    (hω : ω ∈ whitneySpace p k) : extDeriv ω ∈ whitneySpace p (k + 1) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hω
  have hd : extDeriv (∑ f : Faces n k, c f • whitneyForm p f.1) =
      ∑ f : Faces n k, c f • extDeriv (whitneyForm p f.1) := by
    funext x
    rw [extDeriv_sum_apply (ω := fun f : Faces n k => c f • whitneyForm p f.1) _ fun f _ =>
      ((contDiff_whitneyForm p f.1 (r := 1)).const_smul (c f)).differentiable one_ne_zero x]
    simp only [Finset.sum_apply, Pi.smul_apply]
    refine sum_congr rfl fun f _ => ?_
    exact extDeriv_smul_const_apply _
      ((contDiff_whitneyForm p f.1 (r := 1)).differentiable one_ne_zero x)
  rw [hd]
  refine Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ ?_
  have hne : f.1.Nonempty := card_pos.1 (by rw [f.2]; omega)
  rw [extDeriv_whitneyForm_eq_sum p hne]
  refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
  exact whitneyForm_mem_whitneySpace p
    ⟨insert j f.1, by rw [card_insert_of_notMem (mem_compl.1 hj), f.2]⟩

/-! ### Degrees of freedom and unisolvence -/

/-- The degree of freedom `ℓ_g ω = ∫_g ω` of the `k`-face `g`, on continuous forms. -/
def faceDof (p : Fin (n + 1) → Fin n → ℝ) (k : ℕ) (g : Faces n k) : contForms n →ₗ[ℝ] ℝ where
  toFun ω := simplexIntegral (faceVertices p g.1 g.2) ω
  map_add' ω η := simplexIntegral_add (Continuous.continuousOn (mem_contForms.1 ω.2))
    (Continuous.continuousOn (mem_contForms.1 η.2))
  map_smul' c ω := by
    simp only [RingHom.id_apply, smul_eq_mul, Submodule.coe_smul]
    exact simplexIntegral_smul _ c _

/-- The degrees of freedom of `P₁⁻Λᵏ(T)`. -/
def whitneyDof (p : Fin (n + 1) → Fin n → ℝ) (k : ℕ) (g : Faces n k) :
    whitneySpace p k →ₗ[ℝ] ℝ :=
  faceDof p k g ∘ₗ Submodule.inclusion (whitneySpace_le_contForms p k)

/-- The DOFs of a combination of Whitney forms are its coefficients. -/
theorem simplexIntegral_sum_smul_whitneyForm (hp : IsUnit (edgeMatrix p).det)
    (c : Faces n k → ℝ) (g : Faces n k) :
    simplexIntegral (faceVertices p g.1 g.2) (∑ f : Faces n k, c f • whitneyForm p f.1) = c g := by
  rw [simplexIntegral_sum _ _ fun f _ =>
    ((contDiff_whitneyForm p f.1 (r := 0)).continuous.const_smul (c f)).continuousOn]
  have hk : ∀ f : Faces n k, simplexIntegral (faceVertices p g.1 g.2) (whitneyForm p f.1) =
      if f = g then 1 else 0 := fun f => by
    rw [simplexIntegral_whitneyForm hp f.2 g.2]; simp [Subtype.ext_iff]
  simp only [simplexIntegral_smul, hk]
  rw [sum_eq_single g (fun f _ hf => by simp [hf]) (by simp)]
  simp

/-- The Whitney forms of the `k`-faces are linearly independent. -/
theorem linearIndependent_whitneyForm (hp : IsUnit (edgeMatrix p).det) (k : ℕ) :
    LinearIndependent ℝ (fun f : Faces n k => whitneyForm p f.1) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc g
  rw [← simplexIntegral_sum_smul_whitneyForm hp c g, hc]
  have := simplexIntegral_smul (faceVertices p g.1 g.2) 0 0
  simpa using this

/-- **`dim P₁⁻Λᵏ(T) = (n+1 choose k+1)`**. -/
theorem finrank_whitneySpace (hp : IsUnit (edgeMatrix p).det) (k : ℕ) :
    Module.finrank ℝ (whitneySpace p k) = (n + 1).choose (k + 1) := by
  rw [whitneySpace, finrank_span_eq_card (linearIndependent_whitneyForm hp k),
    Fintype.card_finset_len, Fintype.card_fin]

instance (p : Fin (n + 1) → Fin n → ℝ) (k : ℕ) : FiniteDimensional ℝ (whitneySpace p k) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- **Unisolvence**: the face integrals are unisolvent on `P₁⁻Λᵏ(T)`. -/
theorem isUnisolvent_whitneyDof (hp : IsUnit (edgeMatrix p).det) (k : ℕ) :
    IsUnisolvent (whitneyDof p k) := by
  rw [isUnisolvent_iff_forall_eq_zero _
    (by rw [finrank_whitneySpace hp, Fintype.card_finset_len, Fintype.card_fin])]
  intro ω hω
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 ω.2
  have h0 : ∀ g, c g = 0 := by
    intro g
    have := hω g
    change simplexIntegral (faceVertices p g.1 g.2) (ω : FormField n) = 0 at this
    rwa [← hc, simplexIntegral_sum_smul_whitneyForm hp] at this
  refine Subtype.ext ?_
  rw [Submodule.coe_zero, ← hc]
  simp [h0]

/-! ### The canonical interpolant and the commuting property -/

/-- **The canonical interpolant** `Π_T : C⁰ → P₁⁻Λᵏ(T)`, `∫_g Π_T ω = ∫_g ω` for every
`k`-face `g`. -/
def whitneyInterp (hp : IsUnit (edgeMatrix p).det) (k : ℕ) :
    contForms n →ₗ[ℝ] whitneySpace p k :=
  interp (isUnisolvent_whitneyDof hp k) (faceDof p k)

/-- `Π_T` preserves the face integrals. -/
theorem simplexIntegral_whitneyInterp (hp : IsUnit (edgeMatrix p).det) (ω : contForms n)
    (g : Faces n k) :
    simplexIntegral (faceVertices p g.1 g.2) (whitneyInterp hp k ω : FormField n) =
      simplexIntegral (faceVertices p g.1 g.2) (ω : FormField n) := by
  have h := dof_interp (isUnisolvent_whitneyDof hp k) (faceDof p k) ω g
  exact h

/-- `Π_T` is a projection onto `P₁⁻Λᵏ(T)`. -/
theorem whitneyInterp_inclusion (hp : IsUnit (edgeMatrix p).det) (φ : whitneySpace p k) :
    whitneyInterp hp k (Submodule.inclusion (whitneySpace_le_contForms p k) φ) = φ :=
  interp_incl (isUnisolvent_whitneyDof hp k) (faceDof p k) _ (fun _ => rfl) φ

/-- **`Π_T ω = Σ_g (∫_g ω) φ_g`**: the interpolant in the Whitney basis. -/
theorem whitneyInterp_eq_sum (hp : IsUnit (edgeMatrix p).det) (ω : contForms n) :
    (whitneyInterp hp k ω : FormField n) = ∑ g : Faces n k,
      simplexIntegral (faceVertices p g.1 g.2) (ω : FormField n) • whitneyForm p g.1 := by
  set c : Faces n k → ℝ := fun g => simplexIntegral (faceVertices p g.1 g.2) (ω : FormField n)
  have hmem : ∑ g : Faces n k, c g • whitneyForm p g.1 ∈ whitneySpace p k :=
    Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (whitneyForm_mem_whitneySpace p g)
  have h : whitneyInterp hp k ω = ⟨_, hmem⟩ := (isUnisolvent_whitneyDof hp k).ext fun g => by
    change simplexIntegral (faceVertices p g.1 g.2) (whitneyInterp hp k ω : FormField n) =
      simplexIntegral (faceVertices p g.1 g.2) (∑ g : Faces n k, c g • whitneyForm p g.1)
    rw [simplexIntegral_whitneyInterp, simplexIntegral_sum_smul_whitneyForm hp]
  rw [h]

/-! ### Mathlib simplices -/

/-- For a Mathlib `n`-simplex `T` in `ℝⁿ`: `dim P₁⁻Λᵏ(T) = (n+1 choose k+1)`. -/
theorem finrank_whitneySpace_simplex (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    Module.finrank ℝ (whitneySpace T.points k) = (n + 1).choose (k + 1) :=
  finrank_whitneySpace (isUnit_det_edgeMatrix T) k

/-- For a Mathlib `n`-simplex `T` in `ℝⁿ`: the face integrals are unisolvent on
`P₁⁻Λᵏ(T)`. -/
theorem isUnisolvent_whitneyDof_simplex (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    IsUnisolvent (whitneyDof T.points k) :=
  isUnisolvent_whitneyDof (isUnit_det_edgeMatrix T) k

/-! ### The reference simplex: `P₁⁻Λᵏ(T̂) = P₀Λᵏ + κ H₀Λ^{k+1}` -/

theorem edgeMatrix_refVertex : edgeMatrix (refVertex n) = 1 := by
  ext i j
  simp [edgeMatrix, simplexMatrix_refVertex, Matrix.one_apply]

theorem baryCoord_refVertex (x : Fin n → ℝ) : baryCoord (refVertex n) x = refBary x := by
  simp [baryCoord, edgeMatrix_refVertex]

theorem baryGrad_refVertex : baryGrad (refVertex n) = refGrad n := by
  funext m l
  refine Fin.cases ?_ (fun m => ?_) m
  · simp [baryGrad, edgeMatrix_refVertex, refGrad, Matrix.one_apply, Fin.succ_ne_zero]
  · simp [baryGrad, edgeMatrix_refVertex, refGrad, Matrix.one_apply, eq_comm]

theorem refBary_comp_succ (x : Fin n → ℝ) : refBary x ∘ Fin.succAboveOrderEmb 0 = x := by
  funext l; simp

theorem refGrad_comp_succ : refGrad n ∘ Fin.succAboveOrderEmb 0 = fun l => Pi.single l 1 := by
  funext l; simp [refGrad_succ]

/-- On `T̂`, the Whitney form of a face not containing `v̂₀` is `k! ι_x dx_g`. -/
theorem whitneyForm_refVertex_map_succ (g : Finset (Fin n)) (x : Fin n → ℝ) :
    whitneyForm (refVertex n) (g.map (Fin.succAboveOrderEmb 0).toEmbedding) x =
      ((#g - 1).factorial : ℝ) • interior x (Pi.single g 1) := by
  rw [whitneyForm, card_map, baryCoord_refVertex, baryGrad_refVertex, whitneyFibre_map,
    refBary_comp_succ, refGrad_comp_succ, whitneyFibre_single_eq_interior]

/-- On `T̂`, the Whitney form of a face containing `v̂₀` is `k! (dx_g - ι_x (Σⱼ dxⱼ ∧ dx_g))`. -/
theorem whitneyForm_refVertex_insert_zero (g : Finset (Fin n)) (x : Fin n → ℝ) :
    whitneyForm (refVertex n) (insert 0 (g.map (Fin.succAboveOrderEmb 0).toEmbedding)) x =
      ((#g).factorial : ℝ) •
        (Pi.single g 1 - interior x (wedge (fun _ => 1) (Pi.single g 1))) := by
  have h0 : (0 : Fin (n + 1)) ∉ g.map (Fin.succAboveOrderEmb 0).toEmbedding := by
    simp [Fin.succ_ne_zero]
  have hlt : ∀ i ∈ g.map (Fin.succAboveOrderEmb 0).toEmbedding, (0 : Fin (n + 1)) < i := by
    intro i hi
    exact lt_of_le_of_ne (Fin.zero_le i) (fun h => h0 (h ▸ hi))
  rw [whitneyForm, card_insert_of_notMem h0, card_map, Nat.add_sub_cancel, baryCoord_refVertex,
    baryGrad_refVertex, whitneyFibre_insert_of_lt _ _ hlt, whitneyFibre_map, refBary_comp_succ,
    refGrad_comp_succ, whitneyFibre_single_eq_interior, wedgeProd_map, refGrad_comp_succ,
    wedgeProd_single]
  congr 1
  have hθ0 : refGrad n 0 = -(fun _ => 1) := by
    funext l; simp [refGrad, Fin.succ_ne_zero]
  rw [hθ0, wedge_neg_left]
  have hc := wedge_interior_add_interior_wedge (fun _ => (1 : ℝ)) x (Pi.single g 1)
  funext s
  have hs := congrFun hc s
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul] at hs
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, refBary_zero]
  linarith

/-- The contraction `x ↦ ι_x dx_t` (`#t = k + 1`) lies in `P₁⁻Λᵏ(T̂)`. -/
theorem interior_single_mem_whitneySpace {t : Finset (Fin n)} (ht : #t = k + 1) :
    (fun x => interior x (Pi.single t (1 : ℝ))) ∈ whitneySpace (refVertex n) k := by
  have h := whitneyForm_mem_whitneySpace (refVertex n)
    ⟨t.map (Fin.succAboveOrderEmb 0).toEmbedding, by rw [card_map, ht]⟩
  have : (fun x => interior x (Pi.single t (1 : ℝ))) = ((k.factorial : ℝ)⁻¹) •
      whitneyForm (refVertex n) (t.map (Fin.succAboveOrderEmb 0).toEmbedding) := by
    funext x
    rw [Pi.smul_apply, whitneyForm_refVertex_map_succ, ht, Nat.add_sub_cancel, smul_smul,
      inv_mul_cancel₀ (by positivity), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ h

/-- `x ↦ ι_x β` lies in `P₁⁻Λᵏ(T̂)` for every constant `(k+1)`-form `β`. -/
theorem interior_mem_whitneySpace {β : Finset (Fin n) → ℝ} (hβ : IsDeg (k + 1) β) :
    (fun x => interior x β) ∈ whitneySpace (refVertex n) k := by
  have : (fun x => interior x β) = ∑ t, β t • fun x => interior x (Pi.single t (1 : ℝ)) := by
    funext x
    rw [interior_eq_sum_single]
    simp [Finset.sum_apply]
  rw [this]
  refine Submodule.sum_mem _ fun t _ => ?_
  by_cases ht : #t = k + 1
  · exact Submodule.smul_mem _ _ (interior_single_mem_whitneySpace ht)
  · rw [hβ t ht, zero_smul]; exact Submodule.zero_mem _

/-- The constant form `dx_g` (`#g = k`) lies in `P₁⁻Λᵏ(T̂)`. -/
theorem const_single_mem_whitneySpace {g : Finset (Fin n)} (hg : #g = k) :
    (fun _ => Pi.single g (1 : ℝ)) ∈ whitneySpace (refVertex n) k := by
  have h0 : (0 : Fin (n + 1)) ∉ g.map (Fin.succAboveOrderEmb 0).toEmbedding := by
    simp [Fin.succ_ne_zero]
  have h := whitneyForm_mem_whitneySpace (refVertex n)
    ⟨insert 0 (g.map (Fin.succAboveOrderEmb 0).toEmbedding),
      by rw [card_insert_of_notMem h0, card_map, hg]⟩
  have h2 := interior_mem_whitneySpace (k := k)
    (((isDeg_single (R := ℝ) hg).wedge (fun _ : Fin n => (1 : ℝ))))
  have : (fun _ => Pi.single g (1 : ℝ)) = ((k.factorial : ℝ)⁻¹) •
      whitneyForm (refVertex n) (insert 0 (g.map (Fin.succAboveOrderEmb 0).toEmbedding)) +
        fun x => interior x (wedge (fun _ => 1) (Pi.single g 1)) := by
    funext x
    rw [Pi.add_apply, Pi.smul_apply, whitneyForm_refVertex_insert_zero, hg, smul_smul,
      inv_mul_cancel₀ (by positivity), one_smul, sub_add_cancel]
  rw [this]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ h) h2

/-- Constant `k`-forms lie in `P₁⁻Λᵏ(T̂)`. -/
theorem const_mem_whitneySpace {α : Finset (Fin n) → ℝ} (hα : IsDeg k α) :
    (fun _ => α) ∈ whitneySpace (refVertex n) k := by
  have : (fun _ : Fin n → ℝ => α) = ∑ g, α g • fun _ => Pi.single g (1 : ℝ) := by
    funext x s
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  refine Submodule.sum_mem _ fun g _ => ?_
  by_cases hg : #g = k
  · exact Submodule.smul_mem _ _ (const_single_mem_whitneySpace hg)
  · rw [hα g hg, zero_smul]; exact Submodule.zero_mem _

variable (n) in
/-- Evaluation of polynomial forms as form fields. -/
def evalForm : Koszul.PolyForm ℝ (Fin n) →ₗ[ℝ] FormField n where
  toFun ω := fun x s => MvPolynomial.eval x (ω s)
  map_add' ω η := by funext x s; simp
  map_smul' c ω := by funext x s; simp [MvPolynomial.smul_eval]

theorem evalForm_apply (ω : Koszul.PolyForm ℝ (Fin n)) (x : Fin n → ℝ) (s : Finset (Fin n)) :
    evalForm n ω x s = MvPolynomial.eval x (ω s) := rfl

theorem evalForm_koszul (ω : Koszul.PolyForm ℝ (Fin n)) (x : Fin n → ℝ) :
    evalForm n (Koszul.koszul ω) x = interior x (evalForm n ω x) := by
  funext s
  simp [evalForm_apply, Koszul.koszul_apply, interior_apply, sgn]

theorem evalForm_C (α : Finset (Fin n) → ℝ) :
    evalForm n (fun s => MvPolynomial.C (α s)) = fun _ => α := by
  funext x s; simp [evalForm_apply]

/-- A polynomial form with constant coefficients is the constant form of its constant terms. -/
theorem eq_C_of_totalDegree_eq_zero {ω : Koszul.PolyForm ℝ (Fin n)}
    (h : ∀ s, (ω s).totalDegree = 0) :
    ω = fun s => MvPolynomial.C ((ω s).coeff 0) :=
  funext fun s => MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (h s)

/-- **`P₁⁻Λᵏ(T̂) = P₀Λᵏ + κ H₀Λ^{k+1}`**: on the reference simplex the Whitney space is the
space of trimmed linear polynomial forms `Feec.Koszul.polyFormMinus 1 k` (evaluated as form
fields), [AFW2006], §3.3–3.4. -/
theorem whitneySpace_refVertex_eq_map_polyFormMinus (k : ℕ) :
    whitneySpace (refVertex n) k = (Koszul.polyFormMinus ℝ (Fin n) 1 k).map (evalForm n) := by
  refine le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 fun f => ?_)) ?_
  · set g : Finset (Fin n) := univ.filter fun l => l.succ ∈ f.1
    have hmap : ∀ i, i ∈ g.map (Fin.succAboveOrderEmb 0).toEmbedding ↔ i ≠ 0 ∧ i ∈ f.1 := by
      intro i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · simp [Fin.succ_ne_zero]
      · simp [g, Fin.succ_ne_zero]
    by_cases h0 : (0 : Fin (n + 1)) ∈ f.1
    · -- `f = {0} ∪ succ(g)`, `#g = k`
      have hf : f.1 = insert 0 (g.map (Fin.succAboveOrderEmb 0).toEmbedding) := by
        ext i
        rw [mem_insert, hmap]
        by_cases hi : i = 0
        · simp [hi, h0]
        · simp [hi]
      have hg : #g = k := by
        have := f.2
        rw [hf, card_insert_of_notMem (by rw [hmap]; simp), card_map] at this
        omega
      refine ⟨(fun s => MvPolynomial.C ((k.factorial : ℝ) *
          (Pi.single g (1 : ℝ) : Finset (Fin n) → ℝ) s)) +
        Koszul.koszulₗ ℝ (Fin n) (fun s => MvPolynomial.C (-(k.factorial : ℝ) *
          wedge (fun _ => 1) (Pi.single g (1 : ℝ) : Finset (Fin n) → ℝ) s)), ?_, ?_⟩
      · refine Submodule.add_mem _ (Submodule.mem_sup_left
          (show _ ∈ Koszul.polyForm ℝ (Fin n) 0 k from
            ⟨fun s hs => ?_, fun s => (MvPolynomial.totalDegree_C _).le⟩))
          (Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := Koszul.koszulₗ ℝ (Fin n))
            (show _ ∈ Koszul.homForm ℝ (Fin n) 0 (k + 1) from ⟨fun s hs => ?_, fun s =>
              MvPolynomial.isHomogeneous_C _ _⟩)))
        · simp [isDeg_single (R := ℝ) hg s hs]
        · simp [((isDeg_single (R := ℝ) hg).wedge (fun _ => (1 : ℝ))) s hs]
      · funext x
        rw [map_add, Pi.add_apply, Koszul.koszulₗ_apply, evalForm_koszul, evalForm_C, evalForm_C,
          hf,
          whitneyForm_refVertex_insert_zero, hg]
        have : (fun s => -(k.factorial : ℝ) *
            wedge (fun _ => 1) (Pi.single g (1 : ℝ) : Finset (Fin n) → ℝ) s) =
            (-(k.factorial : ℝ)) • wedge (fun _ => 1) (Pi.single g 1) := rfl
        rw [this, ExteriorFibre.interior_smul]
        funext s
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
    · -- `f = succ(g)`, `#g = k + 1`
      have hf : f.1 = g.map (Fin.succAboveOrderEmb 0).toEmbedding := by
        ext i
        rw [hmap]
        by_cases hi : i = 0
        · simp [hi, h0]
        · simp [hi]
      have hg : #g = k + 1 := by
        have := f.2
        rwa [hf, card_map] at this
      refine ⟨Koszul.koszulₗ ℝ (Fin n) (fun s => MvPolynomial.C ((k.factorial : ℝ) *
          (Pi.single g (1 : ℝ) : Finset (Fin n) → ℝ) s)),
        Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := Koszul.koszulₗ ℝ (Fin n))
          (show _ ∈ Koszul.homForm ℝ (Fin n) 0 (k + 1) from ⟨fun s hs => ?_, fun s =>
            MvPolynomial.isHomogeneous_C _ _⟩)), ?_⟩
      · simp [isDeg_single (R := ℝ) hg s hs]
      · funext x
        rw [Koszul.koszulₗ_apply, evalForm_koszul, evalForm_C, hf, whitneyForm_refVertex_map_succ,
          hg,
          Nat.add_sub_cancel]
        have : (fun s => (k.factorial : ℝ) * (Pi.single g (1 : ℝ) : Finset (Fin n) → ℝ) s) =
            (k.factorial : ℝ) • (Pi.single g 1 : Finset (Fin n) → ℝ) := rfl
        rw [this, ExteriorFibre.interior_smul]
  · rw [Submodule.map_le_iff_le_comap]
    intro ω hω
    obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.1 hω
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hy
    rw [Submodule.mem_comap, map_add]
    refine Submodule.add_mem _ ?_ ?_
    · have ha0 : ∀ s, (a s).totalDegree = 0 := fun s => Nat.le_zero.1 (ha.2 s)
      rw [eq_C_of_totalDegree_eq_zero ha0, evalForm_C]
      refine const_mem_whitneySpace fun s hs => ?_
      change (a s).coeff 0 = 0
      rw [ha.1 s hs]; simp
    · have hb0 : ∀ s, (b s).totalDegree = 0 := fun s => Nat.le_zero.1 ((hb.2 s).totalDegree_le)
      have : evalForm n (Koszul.koszulₗ ℝ (Fin n) b) =
          fun x => interior x (fun s => (b s).coeff 0) := by
        funext x
        rw [Koszul.koszulₗ_apply, evalForm_koszul, eq_C_of_totalDegree_eq_zero hb0, evalForm_C]
        simp
      rw [this]
      refine interior_mem_whitneySpace fun s hs => ?_
      change (b s).coeff 0 = 0
      rw [hb.1 s hs]; simp

/-! ### Traces of Whitney forms on faces -/

/-- **Traces of Whitney forms**: pulled back to the face `p ∘ e` of `p` (parametrized by `T̂_m`),
the Whitney form `φ_f` is the Whitney form of the face `e⁻¹(f)` of the reference simplex if the
vertices of `f` are vertices of the face, and vanishes otherwise. This is the face compatibility
underlying the conformity of `P₁⁻Λᵏ` on simplicial meshes ([AFW2006], §4). -/
theorem affinePullback_whitneyForm_face (hp : IsUnit (edgeMatrix p).det) {m : ℕ}
    (e : Fin (m + 1) ↪o Fin (n + 1)) (f : Finset (Fin (n + 1))) :
    affinePullback (simplexMatrix (p ∘ e)) (p (e 0)) (whitneyForm p f) =
      if f ⊆ univ.map e.toEmbedding then
        whitneyForm (refVertex m) (f.preimage e e.injective.injOn) else 0 := by
  have hpull : ∀ y, affinePullback (simplexMatrix (p ∘ e)) (p (e 0)) (whitneyForm p f) y =
      ((#f - 1).factorial : ℝ) •
        whitneyFibre (fun a => ∑ j, refBary y j * if e j = a then 1 else 0)
          (fun a l => (if e l.succ = a then 1 else 0) - if e 0 = a then 1 else 0) f := by
    intro y
    rw [affinePullback_apply, whitneyForm, pullback_smul, pullback_whitneyFibre]
    congr 2
    · funext a
      exact baryCoord_simplexMap_comp hp e y a
    · funext a
      exact covPullback_baryGrad hp e a
  funext y
  rw [hpull]
  split_ifs with hf
  · obtain ⟨g, -, rfl⟩ := Finset.subset_map_iff.1 hf
    have hpre : (g.map e.toEmbedding).preimage e e.injective.injOn = g := by
      ext j; simp
    rw [hpre, whitneyForm, baryCoord_refVertex, baryGrad_refVertex, card_map,
      whitneyFibre_map]
    have hc : (fun a => ∑ j, refBary y j * if e j = a then 1 else 0) ∘ e = refBary y := by
      funext j
      simp only [Function.comp_apply, e.injective.eq_iff]
      rw [sum_eq_single j (fun j' _ hj' => by simp [hj']) (by simp)]
      simp
    have hθ : (fun a (l : Fin m) => (if e l.succ = a then (1 : ℝ) else 0) -
        if e 0 = a then 1 else 0) ∘ e = refGrad m := by
      funext j l
      simp only [Function.comp_apply, e.injective.eq_iff, refGrad, eq_comm]
    rw [hc, hθ]
  · obtain ⟨a, haf, hae⟩ := not_subset.1 hf
    have hne : ∀ j, e j ≠ a := fun j h => hae (h ▸ mem_map_of_mem _ (mem_univ j))
    rw [Pi.zero_apply, whitneyFibre]
    convert smul_zero _
    refine sum_eq_zero fun i hi => ?_
    by_cases hia : i = a
    · subst hia; simp [hne]
    · rw [wedgeProd_eq_zero_of_mem (mem_erase.2 ⟨Ne.symm hia, haf⟩) (by funext l; simp [hne]),
        smul_zero]

end Feec.FiniteElement
