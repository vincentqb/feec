module

public import Feec.Domain.VectorProxy

/-!
# `H¹`-regular decompositions of maximal complexes and the BGG hypothesis

A field `u ∈ L²(Ω; 𝕜^ι)` on an open `Ω ⊆ ℝⁿ` is **`H¹`** when every component has its weak
gradient in `L²` (`fieldH1`, the domain of the maximal componentwise gradient `fieldGradOp`).
`H¹` fields lie in the maximal domain of every homogeneous first-order operator
(`fieldH1_le_maximal_domain`: such an operator is a constant matrix applied to the gradient) and
constant matrices preserve them (`ofMatrixCLM_mem_fieldH1`).

A complex of constant-coefficient operators has the **`H¹`-regular decompositions from `J` on**
(`ConstCoeffComplex.HasRegularDecomposition`) when every `u ∈ D(Aⁱ⁺¹_max)`, `i ≥ J`, is
`Aⁱ p + w` with `p ∈ D(Aⁱ_max)` and `w ∈ H¹`: for the `L²` de Rham complex these are the
regular decompositions `HΛᵏ(Ω) = d HΛᵏ⁻¹(Ω) + H¹Λᵏ(Ω)` of [ArnoldHu2021], §2, Theorem 3
(`H(curl) = grad H¹ + H¹`, `H(div) = curl H(curl) + H¹`, `L² = div H(div) + H¹`).

* They pass from the de Rham complex of `ℝ³` in forms to the vector-proxy complexes
  `deRhamVec ℝ m`, row by row (`deRhamVec_hasRegularDecomposition`; the proxies of
  `Feec.Domain.VectorProxy` and the row matrices `rowMat`).
* **They give the regular decompositions of BGG data** (`Feec.BGG.HilbertData.RegularDecomposition`,
  the hypothesis of the analytic BGG theorem): if the top row has the `H¹`-regular decompositions
  from `J` on, the connecting matrices `M k`, `k ≥ J`, have right inverses and the operators of
  the bottom row are homogeneous of order `1`, then `R(dʲ⁻¹) + R(Sʲ⁻¹) = D(dʲ)` for `j > J`
  (`ConstCoeffBGG.maximalData_regularDecomposition`): the `H¹` part `w` is `Sʲ⁻¹ (N w)`, and
  `N w ∈ H¹` lies in the bottom domain. For the Hessian, elasticity and div-div diagrams the
  matrices have right inverses from `J` on (`hessianSMat_rightInv`, …), so their regular
  decompositions follow from those of the rows (`hessianMaximalData_regularDecomposition`, …).
  On the cube `Q = (0, ½)³` the rows have them (`Feec.Models.Cube.MaximalRegularDecomposition`),
  which removes the hypothesis from the FEEC theorems there (`Feec.Models.Cube.BGGFEEC`).
* **Finite-dimensional cohomology passes from forms to vector proxies**, row by row
  (`deRhamVec_finiteDimensional_cohomology`): the rows and the row embeddings are cochain maps
  and a field is the sum of its rows.

## Main definitions

* `fieldGradOp`, `fieldH1`; `ConstCoeffComplex.HasRegularDecomposition`; `rowMat`,
  `rowFormMat`, `formRowMat`.

## Main results

* `ConstCoeffOp.maximal_domain_le_of_apply_eq`, **`fieldH1_le_maximal_domain`**,
  `ofMatrixCLM_mem_fieldH1`.
* `vecOp_rowMat`, `vecOp_rowMat_transpose`, `sum_rowMat_transpose_mul`;
  `extDerivOp_rowFormMat`, `vecOp_formRowMat`, `sum_formRowMat_mul_rowFormMat`.
* **`deRhamVec_hasRegularDecomposition`**, **`deRhamVec_finiteDimensional_cohomology`**.
* **`ConstCoeffBGG.maximalData_regularDecomposition`** (through
  `Feec.BGG.HilbertData.regularDecomposition_of_forall_exists`).
* `hessianSMat_rightInv`, `elasticitySMat_rightInv`, `divDivSMat_rightInv`;
  **`hessianMaximalData_regularDecomposition`**, `elasticityMaximalData_regularDecomposition`,
  `divDivMaximalData_regularDecomposition`.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §2 (regular decompositions,
  Theorem 3), §4 (the BGG construction)
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], Lemma 2.4
  (regular decomposition)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §2 (vector proxies)

Bibliography: [references.bib](../../docs/references.bib)
-/

open MeasureTheory
open scoped ContDiff

@[expose] public noncomputable section

namespace Feec.Domain

open ConstCoeffOp

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {Ω : Set (Fin n → ℝ)} {ι κ : Type*} [Fintype ι]
  [Fintype κ]

/-! ### Fields with components in `H¹` -/

open scoped Classical in
variable (𝕜 n ι) in
/-- The componentwise gradient `𝕜^ι → 𝕜^{ι × n}` on `ℝⁿ`, `(∇u)_{(i, j)} = ∂ⱼ uᵢ` (the row-wise
gradient `gradOp n m` for `ι = Fin m`). -/
def fieldGradOp : ConstCoeffOp (Fin n → ℝ) 𝕜 ι (ι × Fin n) where
  coeff ij i := if i = ij.1 then [([coordDir ij.2], 1)] else []

theorem fieldGradOp_apply (f : ι → (Fin n → ℝ) → 𝕜) (ij : ι × Fin n) (x : Fin n → ℝ) :
    (fieldGradOp 𝕜 n ι).apply f ij x = fderiv ℝ (f ij.1) x (coordDir ij.2) := by
  classical
  simp [ConstCoeffOp.apply, fieldGradOp, applyEntry_ite, iterDeriv_singleton]

variable (𝕜 Ω ι) in
/-- **The `H¹` fields** of `L²(Ω; 𝕜^ι)`: every component has its weak gradient in `L²(Ω)` (the
domain of the maximal componentwise gradient). -/
def fieldH1 : Submodule 𝕜 (L2F 𝕜 Ω ι) := ((fieldGradOp 𝕜 n ι).maximal Ω).domain

/-- **A constant matrix after `B` bounds `A` on the maximal domains**: if `A = L B` on smooth
fields, then `D(B_max) ⊆ D(A_max)`. -/
theorem ConstCoeffOp.maximal_domain_le_of_apply_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [(volume : Measure E).IsAddHaarMeasure] {Ω : Set E} (hΩ : IsOpen Ω) {κ' : Type*}
    [Fintype κ'] {A : ConstCoeffOp E 𝕜 ι κ} {B : ConstCoeffOp E 𝕜 ι κ'} {L : Matrix κ κ' 𝕜}
    (h : ∀ f : ι → E → 𝕜, (∀ i, ContDiff ℝ ∞ (f i)) →
      A.apply f = (ofMatrix L).apply (B.apply f)) :
    (B.maximal Ω).domain ≤ (A.maximal Ω).domain := by
  classical
  intro u hu
  obtain ⟨h', -⟩ := maximal_ofMatrixCLM_of_comm hΩ (A := A) (B := B) (M := 1) (M' := L)
    (fun f hf => by rw [ofMatrix_one_apply]; exact h f hf) ⟨u, hu⟩
  simpa [L2F.ofMatrixCLM_one] using h'

/-- A first-order entry `Σ c ∂_v` is `Σ_l (Σ c v_l) ∂_l`. -/
theorem applyEntry_eq_sum_of_length_eq_one {P : List (List (Fin n → ℝ) × 𝕜)}
    (hP : ∀ t ∈ P, t.1.length = 1) (f : (Fin n → ℝ) → 𝕜) (x : Fin n → ℝ) :
    applyEntry P f x =
      ∑ l, (P.map fun t => t.2 * ((t.1.headD 0) l : 𝕜)).sum * fderiv ℝ f x (coordDir l) := by
  induction P with
  | nil => simp
  | cons t P ih =>
    obtain ⟨v, hv⟩ := List.length_eq_one_iff.1 (hP t List.mem_cons_self)
    rw [applyEntry_cons]
    change t.2 * iterDeriv t.1 f x + applyEntry P f x = _
    rw [ih fun s hs => hP s (List.mem_cons_of_mem t hs), hv, iterDeriv_singleton]
    have e : fderiv ℝ f x v = ∑ l, ((v l : ℝ) : 𝕜) * fderiv ℝ f x (coordDir l) := by
      have := LinearMap.pi_apply_eq_sum_univ (fderiv ℝ f x).toLinearMap v
      simp only [ContinuousLinearMap.coe_coe] at this
      rw [this]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [RCLike.real_smul_eq_coe_mul]
      congr 2
      funext j
      simp [coordDir, Pi.single_apply, eq_comm]
    simp only [e, hv, List.map_cons, List.sum_cons, List.headD_cons, Finset.mul_sum, add_mul,
      Finset.sum_add_distrib, mul_assoc]

/-- The matrix `L` of a homogeneous first-order operator, `A = L ∇` (`apply_eq_ofMatrix_grad`). -/
def ConstCoeffOp.gradMatrix (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ) : Matrix κ (ι × Fin n) 𝕜 :=
  fun j il => ((A.coeff j il.1).map fun t => t.2 * ((t.1.headD 0) il.2 : 𝕜)).sum

omit [Fintype κ] in
/-- **A homogeneous first-order operator is a constant matrix applied to the gradient.** -/
theorem ConstCoeffOp.apply_eq_ofMatrix_grad {A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ}
    (hA : A.IsHomogeneous 1) (f : ι → (Fin n → ℝ) → 𝕜) :
    A.apply f = (ofMatrix A.gradMatrix).apply ((fieldGradOp 𝕜 n ι).apply f) := by
  funext j x
  rw [ofMatrix_apply, Fintype.sum_prod_type]
  change ∑ i, applyEntry (A.coeff j i) (f i) x = _
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [applyEntry_eq_sum_of_length_eq_one (hA j i)]
  simp only [fieldGradOp_apply]
  rfl

/-- **`H¹` fields lie in the maximal domain of every homogeneous first-order operator.** -/
theorem fieldH1_le_maximal_domain (hΩ : IsOpen Ω) {A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ}
    (hA : A.IsHomogeneous 1) : fieldH1 𝕜 Ω ι ≤ (A.maximal Ω).domain :=
  maximal_domain_le_of_apply_eq hΩ fun f _ => A.apply_eq_ofMatrix_grad hA f

/-- **Constant matrices preserve `H¹` fields**: `∇ (N u) = (N ⊗ 1) ∇u`. -/
theorem ofMatrixCLM_mem_fieldH1 (hΩ : IsOpen Ω) (N : Matrix κ ι 𝕜) {u : L2F 𝕜 Ω ι}
    (hu : u ∈ fieldH1 𝕜 Ω ι) : L2F.ofMatrixCLM N u ∈ fieldH1 𝕜 Ω κ := by
  classical
  refine (maximal_ofMatrixCLM_of_comm hΩ (A := fieldGradOp 𝕜 n κ) (B := fieldGradOp 𝕜 n ι)
    (M := N) (M' := Matrix.kroneckerMap (· * ·) N (1 : Matrix (Fin n) (Fin n) 𝕜))
    (fun f hf => ?_) ⟨u, hu⟩).1
  funext jl x
  have e : (ofMatrix N).apply f jl.1 = fun y => ∑ i, N jl.1 i * f i y :=
    funext fun y => ofMatrix_apply N f jl.1 y
  rw [fieldGradOp_apply, e, fderiv_sum_const_mul _ _ hf, ofMatrix_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.kroneckerMap_apply, Matrix.one_apply, fieldGradOp_apply]

/-- Every field of `L²(Ω; 𝕜^ι)` with `ι` empty is `H¹`. -/
theorem mem_fieldH1_of_isEmpty [IsEmpty ι] (u : L2F 𝕜 Ω ι) : u ∈ fieldH1 𝕜 Ω ι := by
  rw [Subsingleton.elim u 0]; exact Submodule.zero_mem _

/-! ### `H¹`-regular decompositions -/

namespace ConstCoeffComplex

/-- **The `H¹`-regular decompositions from `J` on**: every `u ∈ D(Aⁱ⁺¹_max)`, `i ≥ J`, is
`Aⁱ p + w` with `p ∈ D(Aⁱ_max)` and `w` an `H¹` field. For the `L²` de Rham complex these are
the regular decompositions of [ArnoldHu2021], §2, Theorem 3. -/
def HasRegularDecomposition (C : ConstCoeffComplex (Fin n → ℝ) 𝕜) (Ω : Set (Fin n → ℝ))
    (J : ℤ) : Prop :=
  ∀ i, J ≤ i → ∀ u ∈ ((C.A (i + 1)).maximal Ω).domain, ∃ p : ((C.A i).maximal Ω).domain,
    u - (C.A i).maximal Ω p ∈ fieldH1 𝕜 Ω (C.ι (i + 1))

theorem HasRegularDecomposition.mono {C : ConstCoeffComplex (Fin n → ℝ) 𝕜} {J J' : ℤ}
    (h : C.HasRegularDecomposition Ω J) (hJ : J ≤ J') : C.HasRegularDecomposition Ω J' :=
  fun i hi => h i (hJ.trans hi)

end ConstCoeffComplex

/-! ### From forms to vector proxies, row by row -/

variable {m : ℕ}

variable (𝕜) in
/-- **The `r`-th row** `𝕜^{vecIdx m k} → 𝕜^{vecIdx 1 k}` of a field of the de Rham complex with
values in `𝕜ᵐ`. -/
def rowMat (r : Fin m) : ∀ k : ℤ, Matrix (vecIdx 1 k) (vecIdx m k) 𝕜
  | .ofNat 0 => Matrix.of fun _ i => if i = r then 1 else 0
  | .ofNat 1 => Matrix.of fun a b => if b = (r, a.2) then 1 else 0
  | .ofNat 2 => Matrix.of fun a b => if b = (r, a.2) then 1 else 0
  | .ofNat 3 => Matrix.of fun _ i => if i = r then 1 else 0
  | .ofNat (_ + 4) => 0
  | .negSucc _ => 0

section Rows

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ofMatrix_rowMat_zero (r : Fin m) (f : Fin m → E → 𝕜) :
    (ofMatrix (rowMat 𝕜 r 0)).apply f = fun _ => f r := by
  funext a x; rw [ofMatrix_apply]; simp [rowMat]

theorem ofMatrix_rowMat_one (r : Fin m) (f : Fin m × Fin 3 → E → 𝕜) :
    (ofMatrix (rowMat 𝕜 r 1)).apply f = fun a => f (r, a.2) := by
  funext a x; rw [ofMatrix_apply]; simp [rowMat]

theorem ofMatrix_rowMat_two (r : Fin m) (f : Fin m × Fin 3 → E → 𝕜) :
    (ofMatrix (rowMat 𝕜 r 2)).apply f = fun a => f (r, a.2) := by
  funext a x; rw [ofMatrix_apply]; simp [rowMat]

theorem ofMatrix_rowMat_three (r : Fin m) (f : Fin m → E → 𝕜) :
    (ofMatrix (rowMat 𝕜 r 3)).apply f = fun _ => f r := by
  funext a x; rw [ofMatrix_apply]; simp [rowMat]

theorem ofMatrix_rowMat_transpose_zero (r : Fin m) (f : Fin 1 → E → 𝕜) :
    (ofMatrix (rowMat 𝕜 r 0).transpose).apply f = fun i => if i = r then f 0 else 0 := by
  funext i x; rw [ofMatrix_apply]; by_cases h : i = r <;> simp [rowMat, h]

theorem ofMatrix_rowMat_transpose_one (r : Fin m) (f : Fin 1 × Fin 3 → E → 𝕜) :
    (ofMatrix (rowMat 𝕜 r 1).transpose).apply f =
      fun b => if b.1 = r then f (0, b.2) else 0 := by
  funext b x
  rw [ofMatrix_apply]
  by_cases h : b.1 = r
  · rw [Finset.sum_eq_single (0, b.2)]
    · simp [rowMat, h, Prod.ext_iff]
    · rintro ⟨a, l⟩ _ hl
      simp only [rowMat, Matrix.transpose_apply, Matrix.of_apply]
      rw [ite_eq_right fun h' => hl (by rw [h', Fin.fin_one_eq_zero a]), zero_mul]
    · simp
  · simp [rowMat, h, Prod.ext_iff]

theorem ofMatrix_rowMat_transpose_two (r : Fin m) (f : Fin 1 × Fin 3 → E → 𝕜) :
    (ofMatrix (rowMat 𝕜 r 2).transpose).apply f =
      fun b => if b.1 = r then f (0, b.2) else 0 :=
  ofMatrix_rowMat_transpose_one r f

theorem ofMatrix_rowMat_transpose_three (r : Fin m) (f : Fin 1 → E → 𝕜) :
    (ofMatrix (rowMat 𝕜 r 3).transpose).apply f = fun i => if i = r then f 0 else 0 :=
  ofMatrix_rowMat_transpose_zero r f

end Rows

/-- **Rows commute with the operators**: `A (r-th row of f) = r-th row of A f`. -/
theorem vecOp_rowMat (r : Fin m) (k : ℤ) (f : vecIdx m k → (Fin 3 → ℝ) → 𝕜) :
    (vecOp 𝕜 1 k).apply ((ofMatrix (rowMat 𝕜 r k)).apply f) =
      (ofMatrix (rowMat 𝕜 r (k + 1))).apply ((vecOp 𝕜 m k).apply f) := by
  match k with
  | .ofNat 0 =>
    change (gradOp 3 1).apply ((ofMatrix (rowMat 𝕜 r 0)).apply (f : Fin m → _ → 𝕜)) =
      (ofMatrix (rowMat 𝕜 r 1)).apply ((gradOp 3 m).apply f)
    rw [ofMatrix_rowMat_zero, ofMatrix_rowMat_one]
    funext a x; simp [gradOp_apply]
  | .ofNat 1 =>
    change (curlOp 1).apply ((ofMatrix (rowMat 𝕜 r 1)).apply (f : Fin m × Fin 3 → _ → 𝕜)) =
      (ofMatrix (rowMat 𝕜 r 2)).apply ((curlOp m).apply f)
    rw [ofMatrix_rowMat_one, ofMatrix_rowMat_two]
    funext a x; simp [curlOp_apply]
  | .ofNat 2 =>
    change (divOp 3 1).apply ((ofMatrix (rowMat 𝕜 r 2)).apply (f : Fin m × Fin 3 → _ → 𝕜)) =
      (ofMatrix (rowMat 𝕜 r 3)).apply ((divOp 3 m).apply f)
    rw [ofMatrix_rowMat_two, ofMatrix_rowMat_three]
    funext a x; simp [divOp_apply]
  | .ofNat (j + 3) =>
    have : IsEmpty (vecIdx 1 (Int.ofNat (j + 3) + 1)) :=
      isEmpty_vecIdx 1 (Or.inr (by simp only [Int.ofNat_eq_natCast]; omega))
    rw [apply_eq_zero_of_isEmpty _ _ (Or.inr this),
      apply_eq_zero_of_isEmpty (ofMatrix _) _ (Or.inr this)]
  | .negSucc j =>
    have h1 : IsEmpty (vecIdx 1 (Int.negSucc j)) :=
      isEmpty_vecIdx 1 (Or.inl (Int.negSucc_lt_zero j))
    have hm : IsEmpty (vecIdx m (Int.negSucc j)) :=
      isEmpty_vecIdx m (Or.inl (Int.negSucc_lt_zero j))
    rw [apply_eq_zero_of_isEmpty _ _ (Or.inl h1), apply_eq_zero_of_isEmpty (vecOp 𝕜 m _) _
      (Or.inl hm), apply_zero]

/-- **Row embeddings commute with the operators.** -/
theorem vecOp_rowMat_transpose (r : Fin m) (k : ℤ) (f : vecIdx 1 k → (Fin 3 → ℝ) → 𝕜) :
    (vecOp 𝕜 m k).apply ((ofMatrix (rowMat 𝕜 r k).transpose).apply f) =
      (ofMatrix (rowMat 𝕜 r (k + 1)).transpose).apply ((vecOp 𝕜 1 k).apply f) := by
  match k with
  | .ofNat 0 =>
    change (gradOp 3 m).apply ((ofMatrix (rowMat 𝕜 r 0).transpose).apply
      (f : Fin 1 → _ → 𝕜)) = (ofMatrix (rowMat 𝕜 r 1).transpose).apply ((gradOp 3 1).apply f)
    rw [ofMatrix_rowMat_transpose_zero, ofMatrix_rowMat_transpose_one]
    funext b x
    by_cases h : b.1 = r <;> simp [gradOp_apply, h]
  | .ofNat 1 =>
    change (curlOp m).apply ((ofMatrix (rowMat 𝕜 r 1).transpose).apply
      (f : Fin 1 × Fin 3 → _ → 𝕜)) = (ofMatrix (rowMat 𝕜 r 2).transpose).apply
        ((curlOp 1).apply f)
    rw [ofMatrix_rowMat_transpose_one, ofMatrix_rowMat_transpose_two]
    funext b x
    by_cases h : b.1 = r <;> simp [curlOp_apply, h]
  | .ofNat 2 =>
    change (divOp 3 m).apply ((ofMatrix (rowMat 𝕜 r 2).transpose).apply
      (f : Fin 1 × Fin 3 → _ → 𝕜)) = (ofMatrix (rowMat 𝕜 r 3).transpose).apply
        ((divOp 3 1).apply f)
    rw [ofMatrix_rowMat_transpose_two, ofMatrix_rowMat_transpose_three]
    funext i x
    by_cases h : i = r <;> simp [divOp_apply, h]
  | .ofNat (j + 3) =>
    have : IsEmpty (vecIdx m (Int.ofNat (j + 3) + 1)) :=
      isEmpty_vecIdx m (Or.inr (by simp only [Int.ofNat_eq_natCast]; omega))
    rw [apply_eq_zero_of_isEmpty _ _ (Or.inr this),
      apply_eq_zero_of_isEmpty (ofMatrix _) _ (Or.inr this)]
  | .negSucc j =>
    have h1 : IsEmpty (vecIdx 1 (Int.negSucc j)) :=
      isEmpty_vecIdx 1 (Or.inl (Int.negSucc_lt_zero j))
    have hm : IsEmpty (vecIdx m (Int.negSucc j)) :=
      isEmpty_vecIdx m (Or.inl (Int.negSucc_lt_zero j))
    rw [apply_eq_zero_of_isEmpty _ _ (Or.inl hm), apply_eq_zero_of_isEmpty (vecOp 𝕜 1 _) _
      (Or.inl h1), apply_zero]

/-- **The rows split a field**: `Σ_r rowᵣᵀ rowᵣ = 1`. -/
theorem sum_rowMat_transpose_mul (k : ℤ) :
    ∑ r : Fin m, (rowMat 𝕜 r k).transpose * rowMat 𝕜 r k = 1 := by
  match k with
  | .ofNat 0 | .ofNat 3 =>
    ext i j
    simp [Matrix.sum_apply, Matrix.mul_apply, rowMat, Matrix.one_apply, eq_comm]
  | .ofNat 1 | .ofNat 2 =>
    ext b c
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply, rowMat,
      Fintype.sum_prod_type, Fin.sum_univ_one, Matrix.one_apply]
    obtain ⟨b₁, b₂⟩ := b
    obtain ⟨c₁, c₂⟩ := c
    by_cases h : (b₁, b₂) = (c₁, c₂)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [ite_and, Finset.sum_ite_eq]
    · rw [ite_eq_right h]
      refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun l _ => ?_
      by_cases h1 : (b₁, b₂) = (r, l) <;> by_cases h2 : (c₁, c₂) = (r, l) <;> simp_all
  | .ofNat (_ + 4) => ext a; exact isEmptyElim (α := Empty) a
  | .negSucc _ => ext a; exact isEmptyElim (α := Empty) a

omit [Fintype κ] in
/-- A constant matrix sum acts as the sum of the actions. -/
theorem L2F.ofMatrixCLM_sum {α : Type*} (s : Finset α)
    (M : α → Matrix κ ι 𝕜) (u : L2F 𝕜 Ω ι) :
    L2F.ofMatrixCLM (∑ a ∈ s, M a) u = ∑ a ∈ s, L2F.ofMatrixCLM (M a) u := by
  refine (WithLp.ext_iff 2).2 (funext fun j => ?_)
  change L2F.ofMatrixCLM (∑ a ∈ s, M a) u j = (∑ a ∈ s, L2F.ofMatrixCLM (M a) u) j
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [L2F.ofMatrixCLM_apply, Matrix.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

/-- **The `r`-th row of a field of `deRhamVec ℝ m` as a form**: `P_k⁻¹ rowᵣ`, through the
proxies `proxyMat`. -/
def rowFormMat (r : Fin m) (k : ℤ) : Matrix (formIdx 3 k) (vecIdx m k) ℝ :=
  (proxyMat k).transpose * rowMat ℝ r k

/-- **A form as the `r`-th row of a field of `deRhamVec ℝ m`**: `rowᵣᵀ P_k`. -/
def formRowMat (r : Fin m) (k : ℤ) : Matrix (vecIdx m k) (formIdx 3 k) ℝ :=
  (rowMat ℝ r k).transpose * proxyMat k

/-- The rows of smooth fields commute with `d`. -/
theorem extDerivOp_rowFormMat (r : Fin m) (k : ℤ) (f : vecIdx m k → (Fin 3 → ℝ) → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (extDerivOp ℝ 3 k).apply ((ofMatrix (rowFormMat r k)).apply f) =
      (ofMatrix (rowFormMat r (k + 1))).apply ((vecOp ℝ m k).apply f) := by
  rw [rowFormMat, rowFormMat, ← ofMatrix_apply_ofMatrix, apply_ofMatrix_inv
    (proxyMat_mul_transpose k) (transpose_mul_proxyMat (k + 1)) (fun g _ => vecOp_proxyMat k g) _
    ((ofMatrix (rowMat ℝ r k)).contDiff_apply hf), vecOp_rowMat, ofMatrix_apply_ofMatrix]

/-- Forms placed in a row commute with `d`. -/
theorem vecOp_formRowMat (r : Fin m) (k : ℤ) (f : formIdx 3 k → (Fin 3 → ℝ) → ℝ) :
    (vecOp ℝ m k).apply ((ofMatrix (formRowMat r k)).apply f) =
      (ofMatrix (formRowMat r (k + 1))).apply ((extDerivOp ℝ 3 k).apply f) := by
  rw [formRowMat, formRowMat, ← ofMatrix_apply_ofMatrix, vecOp_rowMat_transpose, vecOp_proxyMat,
    ofMatrix_apply_ofMatrix]

/-- **A field is the sum of its rows**: `Σ_r (rowᵣᵀ P_k) (P_k⁻¹ rowᵣ) = 1`. -/
theorem sum_formRowMat_mul_rowFormMat (k : ℤ) :
    ∑ r : Fin m, formRowMat r k * rowFormMat r k = 1 := by
  simp only [formRowMat, rowFormMat, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc (proxyMat k), proxyMat_mul_transpose, Matrix.one_mul]
  exact sum_rowMat_transpose_mul k

/-- **The `H¹`-regular decompositions pass from forms to vector proxies**: if the `L²` de Rham
complex of `Ω ⊆ ℝ³` in forms has them from `J` on, so has the de Rham complex with values in
`ℝᵐ` (row by row: the `r`-th row of a field is a form, `rowFormMat`, `formRowMat`). -/
theorem deRhamVec_hasRegularDecomposition {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) {J : ℤ}
    (h : (deRham ℝ 3).HasRegularDecomposition Ω J) (m : ℕ) :
    (deRhamVec ℝ m).HasRegularDecomposition Ω J := by
  have h' : ∀ i, J ≤ i → ∀ u ∈ ((extDerivOp ℝ 3 (i + 1)).maximal Ω).domain,
      ∃ p : ((extDerivOp ℝ 3 i).maximal Ω).domain,
        u - (extDerivOp ℝ 3 i).maximal Ω p ∈ fieldH1 ℝ Ω (formIdx 3 (i + 1)) := h
  intro i hi u hu
  have hur : ∀ r : Fin m, L2F.ofMatrixCLM (rowFormMat r (i + 1)) u ∈
      ((extDerivOp ℝ 3 (i + 1)).maximal Ω).domain := fun r =>
    (maximal_ofMatrixCLM_of_comm hΩ (extDerivOp_rowFormMat r (i + 1)) ⟨u, hu⟩).1
  choose p hp using fun r => h' i hi _ (hur r)
  choose hq hqe using fun r =>
    maximal_ofMatrixCLM_of_comm hΩ (fun f _ => vecOp_formRowMat r i f) (p r)
  refine ⟨∑ r, ⟨_, hq r⟩, ?_⟩
  have hsum : (vecOp ℝ m i).maximal Ω (∑ r, ⟨_, hq r⟩) =
      ∑ r, L2F.ofMatrixCLM (formRowMat r (i + 1)) ((extDerivOp ℝ 3 i).maximal Ω (p r)) :=
    (map_sum ((vecOp ℝ m i).maximal Ω).toFun _ Finset.univ).trans
      (Finset.sum_congr rfl fun r _ => hqe r)
  have hu' : u = ∑ r, L2F.ofMatrixCLM (formRowMat r (i + 1))
      (L2F.ofMatrixCLM (rowFormMat r (i + 1)) u) := by
    simp only [L2F.ofMatrixCLM_ofMatrixCLM]
    rw [← L2F.ofMatrixCLM_sum, sum_formRowMat_mul_rowFormMat, L2F.ofMatrixCLM_one]
  change u - (vecOp ℝ m i).maximal Ω (∑ r, ⟨_, hq r⟩) ∈ fieldH1 ℝ Ω (vecIdx m (i + 1))
  rw [hsum, hu', ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun r _ => ?_
  rw [← map_sub]
  exact ofMatrixCLM_mem_fieldH1 hΩ _ (hp r)

/-! ### Finite-dimensional cohomology, row by row -/

/-- **Finite-dimensional cohomology passes from forms to vector proxies**: if the maximal `L²`
de Rham complex of `Ω ⊆ ℝ³` in forms has finite-dimensional cohomology in degree `i`, so has the
de Rham complex with values in `ℝᵐ`. The rows `rowFormMat r` and the embeddings `formRowMat r`
are cochain maps (`ConstCoeffComplex.maximalComplex_ofMatrixCLM_comm`) and a field is the sum of
its rows, so `[u] ↦ ([rowᵣ u])_r` is one-to-one
(`HilbertComplex.finiteDimensional_cohomology_of_sum_eq_id`). -/
theorem deRhamVec_finiteDimensional_cohomology {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) (m : ℕ)
    (i : ℤ) [FiniteDimensional ℝ (((deRham ℝ 3).maximalComplex hΩ).cohomology i)] :
    FiniteDimensional ℝ (((deRhamVec ℝ m).maximalComplex hΩ).cohomology i) := by
  have hP := fun r : Fin m => ConstCoeffComplex.maximalComplex_ofMatrixCLM_comm hΩ
    (C := deRhamVec ℝ m) (C' := deRham ℝ 3) (M := rowFormMat r) (extDerivOp_rowFormMat r)
  have hR := fun r : Fin m => ConstCoeffComplex.maximalComplex_ofMatrixCLM_comm hΩ
    (C := deRham ℝ 3) (C' := deRhamVec ℝ m) (M := formRowMat r)
    fun k f _ => vecOp_formRowMat r k f
  refine HilbertComplex.finiteDimensional_cohomology_of_sum_eq_id
    (H := (deRham ℝ 3).maximalComplex hΩ) (H' := (deRhamVec ℝ m).maximalComplex hΩ)
    (fun r => (L2F.ofMatrixCLM (rowFormMat r i) : _ →L[ℝ] _).toLinearMap)
    (fun r => (L2F.ofMatrixCLM (formRowMat r i) : _ →L[ℝ] _).toLinearMap)
    (fun r _ hx => HilbertComplex.apply_mem_cycles
      (T := fun j => (L2F.ofMatrixCLM (rowFormMat r j) : _ →L[ℝ] _).toLinearMap) (hP r) hx)
    (fun r _ hx => HilbertComplex.apply_mem_boundaries
      (T := fun j => (L2F.ofMatrixCLM (rowFormMat r j) : _ →L[ℝ] _).toLinearMap) (hP r) hx)
    (fun r _ hx => HilbertComplex.apply_mem_boundaries
      (T := fun j => (L2F.ofMatrixCLM (formRowMat r j) : _ →L[ℝ] _).toLinearMap) (hR r) hx)
    fun x => ?_
  change ∑ r, L2F.ofMatrixCLM (formRowMat r i) (L2F.ofMatrixCLM (rowFormMat r i) x) = x
  simp only [L2F.ofMatrixCLM_ofMatrixCLM]
  rw [← L2F.ofMatrixCLM_sum, sum_formRowMat_mul_rowFormMat, L2F.ofMatrixCLM_one]

/-! ### The regular decompositions of BGG data -/

/-- **The regular decompositions of BGG data of maximal realizations**
(`Feec.BGG.HilbertData.RegularDecomposition`, the hypothesis of the analytic BGG theorem for
`bgg J`): `R(dʲ⁻¹) + R(Sʲ⁻¹) = D(dʲ)` for `j > J` when the top row has the `H¹`-regular
decompositions from `J` on, the operators of the bottom row from `J` on are homogeneous of
order `1` and the connecting matrices `M k`, `k ≥ J`, have right inverses `N`: the `H¹` part
`w` of `u = dʲ⁻¹ p + w` is `Sʲ⁻¹ (N w)`, and `N w`, an `H¹` field, lies in the bottom domain
(`fieldH1_le_maximal_domain`). [ArnoldHu2021], §2, Theorem 3 and §4 -/
theorem ConstCoeffBGG.maximalData_regularDecomposition (B : ConstCoeffBGG (Fin n → ℝ) 𝕜)
    [∀ k, DecidableEq (B.top.ι k)] (M : ∀ k, Matrix (B.top.ι (k + 1)) (B.bot.ι k) 𝕜)
    (hM : ∀ k f, (B.S k).apply f = (ConstCoeffOp.ofMatrix (M k)).apply f) (hΩ : IsOpen Ω)
    {J : ℤ} (hbot : ∀ k, J ≤ k → (B.bot.A k).IsHomogeneous 1)
    (hN : ∀ k, J ≤ k → ∃ N : Matrix (B.bot.ι k) (B.top.ι (k + 1)) 𝕜, M k * N = 1)
    (htop : B.top.HasRegularDecomposition Ω J) :
    (B.maximalData M hM hΩ).RegularDecomposition J := by
  refine (B.maximalData M hM hΩ).regularDecomposition_of_forall_exists fun i hi u hu => ?_
  have hu' : u ∈ ((B.top.A (i + 1)).maximal Ω).domain := by
    change u ∈ ((B.top.maximalComplex hΩ).d (i + 1) (i + 1 + 1)).domain at hu
    rwa [ConstCoeffComplex.maximalComplex_d] at hu
  obtain ⟨p, hp⟩ := htop i hi u hu'
  obtain ⟨N, hMN⟩ := hN i hi
  have hφ := fieldH1_le_maximal_domain hΩ (hbot i hi) (ofMatrixCLM_mem_fieldH1 hΩ N hp)
  have hpm : (p : L2F 𝕜 Ω (B.top.ι i)) ∈ ((B.top.maximalComplex hΩ).d i (i + 1)).domain := by
    rw [ConstCoeffComplex.maximalComplex_d]; exact p.2
  have hφm : L2F.ofMatrixCLM N (u - (B.top.A i).maximal Ω p) ∈
      ((B.bot.maximalComplex hΩ).d i (i + 1)).domain := by
    rw [ConstCoeffComplex.maximalComplex_d]; exact hφ
  refine ⟨⟨_, hpm⟩, ⟨_, hφm⟩, ?_⟩
  change (B.top.maximalComplex hΩ).d i (i + 1) ⟨_, hpm⟩ +
    (B.maximalData M hM hΩ).S i (i + 1) (L2F.ofMatrixCLM N (u - (B.top.A i).maximal Ω p)) = u
  rw [maximalData_S, L2F.ofMatrixCLM_ofMatrixCLM, hMN, L2F.ofMatrixCLM_one,
    LinearPMap.apply_eq_of_eq (ConstCoeffComplex.maximalComplex_d _ hΩ i) _ p rfl]
  abel

/-! ### The Hessian, elasticity and div-div diagrams -/

section Instances

variable {Ω : Set (Fin 3 → ℝ)}

/-- `I`, `2 vskw` and `tr` have right inverses (from `0` on; the later matrices map into the
zero space). -/
theorem hessianSMat_rightInv :
    ∀ k : ℤ, 0 ≤ k → ∃ N : Matrix (vecIdx 3 k) (vecIdx 1 (k + 1)) 𝕜,
      (hessianSMat k : Matrix _ _ 𝕜) * N = 1
  | .ofNat 0, _ => ⟨hessN0, hessS0_mul_hessN0⟩
  | .ofNat 1, _ => ⟨hessN1, hessS1_mul_hessN1⟩
  | .ofNat 2, _ => ⟨hessN2, hessS2_mul_hessN2⟩
  | .ofNat (j + 3), _ => ⟨0, by
      have := isEmpty_vecIdx 1 (k := Int.ofNat (j + 3) + 1)
        (Or.inr (by simp only [Int.ofNat_eq_natCast]; omega))
      ext i; exact isEmptyElim i⟩
  | .negSucc j, h => absurd h (by have := Int.negSucc_lt_zero j; omega)

/-- `T - tr` and `2 vskw` have right inverses (from `1` on). -/
theorem elasticitySMat_rightInv :
    ∀ k : ℤ, 1 ≤ k → ∃ N : Matrix (vecIdx 3 k) (vecIdx 3 (k + 1)) 𝕜,
      (elasticitySMat k : Matrix _ _ 𝕜) * N = 1
  | .ofNat 0, h => absurd h (by simp)
  | .ofNat 1, _ => ⟨elN1, elS1_mul_elN1⟩
  | .ofNat 2, _ => ⟨elN2, elS2_mul_elN2⟩
  | .ofNat (j + 3), _ => ⟨0, by
      have := isEmpty_vecIdx 3 (k := Int.ofNat (j + 3) + 1)
        (Or.inr (by simp only [Int.ofNat_eq_natCast]; omega))
      ext i; exact isEmptyElim i⟩
  | .negSucc j, h => absurd h (by have := Int.negSucc_lt_zero j; omega)

/-- `I` has a right inverse (from `2` on). -/
theorem divDivSMat_rightInv :
    ∀ k : ℤ, 2 ≤ k → ∃ N : Matrix (vecIdx 1 k) (vecIdx 3 (k + 1)) 𝕜,
      (divDivSMat k : Matrix _ _ 𝕜) * N = 1
  | .ofNat 0, h => absurd h (by simp)
  | .ofNat 1, h => absurd h (by simp)
  | .ofNat 2, _ => ⟨ddN2, ddS2_mul_ddN2⟩
  | .ofNat (j + 3), _ => ⟨0, by
      have := isEmpty_vecIdx 3 (k := Int.ofNat (j + 3) + 1)
        (Or.inr (by simp only [Int.ofNat_eq_natCast]; omega))
      ext i; exact isEmptyElim i⟩
  | .negSucc j, h => absurd h (by have := Int.negSucc_lt_zero j; omega)

/-- **The regular decompositions of the Hessian diagram** after `0` from the `H¹`-regular
decompositions of the scalar de Rham complex (`H(curl) = grad H¹ + H¹`, `H(div) = curl H(curl) +
H¹`, `L² = div H(div) + H¹`). -/
theorem hessianMaximalData_regularDecomposition (hΩ : IsOpen Ω)
    (h : (deRhamVec 𝕜 1).HasRegularDecomposition Ω 0) :
    (hessianMaximalData 𝕜 hΩ).RegularDecomposition 0 :=
  (hessianBGG 𝕜).maximalData_regularDecomposition hessianSMat hessianS_apply_eq hΩ
    (fun k _ => isHomogeneous_vecOp 3 k) hessianSMat_rightInv h

/-- **The regular decompositions of the elasticity diagram** after `1` from the `H¹`-regular
decompositions of the `𝕜³`-valued de Rham complex from `1` on. -/
theorem elasticityMaximalData_regularDecomposition (hΩ : IsOpen Ω)
    (h : (deRhamVec 𝕜 3).HasRegularDecomposition Ω 1) :
    (elasticityMaximalData 𝕜 hΩ).RegularDecomposition 1 :=
  (elasticityBGG 𝕜).maximalData_regularDecomposition elasticitySMat elasticityS_apply_eq hΩ
    (fun k _ => isHomogeneous_vecOp 3 k) elasticitySMat_rightInv h

/-- **The regular decompositions of the div-div diagram** after `2` from the `H¹`-regular
decompositions of the `𝕜³`-valued de Rham complex from `2` on. -/
theorem divDivMaximalData_regularDecomposition (hΩ : IsOpen Ω)
    (h : (deRhamVec 𝕜 3).HasRegularDecomposition Ω 2) :
    (divDivMaximalData 𝕜 hΩ).RegularDecomposition 2 :=
  (divDivBGG 𝕜).maximalData_regularDecomposition divDivSMat divDivS_apply_eq hΩ
    (fun k _ => isHomogeneous_vecOp 1 k) divDivSMat_rightInv h

end Instances

end Feec.Domain
