module

public import Feec.Algebra.Proxy3
public import Feec.Domain.BGGRealization
public import Feec.Domain.FormPullback
public import Feec.ForMathlib.Calculus.Partial

/-!
# Vector proxies: the `L²` de Rham complex of `ℝ³` is `H¹ → H(curl) → H(div) → L²`

On an open `Ω ⊆ ℝ³`, the vector proxies of `Feec.Algebra.Proxy3` identify `k`-forms with scalar
and vector fields: `f = ω_∅`, `v_j = ω_{j}`, `u_k = ±ω_{{k}ᶜ}` (`u = (ω_{12}, -ω_{02}, ω_{01})`),
`g = ω_{012}`. In each degree this is a signed permutation of the components
(`proxyMat k`, the signed bijection `proxyIdx k : vecIdx 1 k ≃ formIdx 3 k` with signs
`proxySgn k`), hence a unitary map `proxy k : L²Λᵏ(Ω) ≃ L²(Ω; vecIdx 1 k)`.

* `extD_eq_coordD`: the exterior derivative of smooth forms is the coordinate exterior derivative
  of `Feec.Koszul.Proxy3` for the partial derivatives `∂_j`, so the proxy identities
  `d = grad, curl, div` of polynomial forms (`Feec.Koszul.Proxy3.vec1_coordD`, `vec2_coordD`,
  `vol_coordD`) hold for smooth fields: **`vecOp_proxyMat`**,
  `(vecOp k) (P_k f) = P_{k+1} (d f)` on all fields, in every degree.
* `ConstCoeffComplex.maximalComplex_eq_transport_ofMatrix`: for two complexes of
  constant-coefficient operators intertwined by constant matrices with two-sided inverses
  (`C'.A k ∘ M_k = M_{k+1} ∘ C.A k` on smooth fields), the maximal complex of `C'` is the
  transport of that of `C` along the matrices (from `ConstCoeffOp.maximal_ofMatrixCLM` in both
  directions).
* **`deRhamVec_maximalComplex_eq_map`**: the maximal vector-proxy complex
  `H¹(Ω) --grad--> H(curl, Ω) --curl--> H(div, Ω) --div--> L²(Ω)` (`deRhamVec ℝ 1`) is the
  unitary transport of the maximal de Rham complex `HΛ⁰(Ω) → HΛ¹(Ω) → HΛ²(Ω) → L²Λ³(Ω)` along the
  proxies: `grad = P₁ d P₀⁻¹`, `curl = P₂ d P₁⁻¹`, `div = P₃ d P₂⁻¹` with the same domains.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §2 (vector proxies of the de Rham complex in three dimensions)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4 (the `L²` de Rham complex; in vector proxies `H¹`, `H(curl)`, `H(div)`, `L²`)
* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003] (the spaces `H(curl)`,
  `H(div)`)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff
open MeasureTheory

@[expose] public noncomputable section

namespace Feec.Domain

/-! ### Constant matrices intertwining complexes of constant-coefficient operators -/

section Intertwining

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type*} [RCLike 𝕜]
  [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
  {Ω : Set E} {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']

namespace L2F

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] [Fintype κ] in
theorem ofMatrixCLM_neg (M : Matrix κ ι 𝕜) (u : L2F 𝕜 Ω ι) :
    ofMatrixCLM (-M) u = -ofMatrixCLM M u := by
  refine (WithLp.ext_iff 2).2 (funext fun j => ?_)
  change ofMatrixCLM (-M) u j = -ofMatrixCLM M u j
  simp [ofMatrixCLM_apply, neg_smul]

variable [DecidableEq ι] [DecidableEq κ]

/-- A constant matrix with a two-sided inverse, as an isomorphism of `L²` fields. -/
def ofMatrixEquiv (M : Matrix κ ι 𝕜) (N : Matrix ι κ 𝕜) (hMN : M * N = 1) (hNM : N * M = 1) :
    L2F 𝕜 Ω ι ≃L[𝕜] L2F 𝕜 Ω κ :=
  ContinuousLinearEquiv.equivOfInverse (ofMatrixCLM M) (ofMatrixCLM N)
    (fun u => by rw [ofMatrixCLM_ofMatrixCLM, hNM, ofMatrixCLM_one])
    (fun v => by rw [ofMatrixCLM_ofMatrixCLM, hMN, ofMatrixCLM_one])

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
@[simp] theorem coe_ofMatrixEquiv (M : Matrix κ ι 𝕜) (N : Matrix ι κ 𝕜) (hMN : M * N = 1)
    (hNM : N * M = 1) : ⇑(ofMatrixEquiv (Ω := Ω) M N hMN hNM) = ofMatrixCLM M := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
@[simp] theorem coe_ofMatrixEquiv_symm (M : Matrix κ ι 𝕜) (N : Matrix ι κ 𝕜) (hMN : M * N = 1)
    (hNM : N * M = 1) : ⇑(ofMatrixEquiv (Ω := Ω) M N hMN hNM).symm = ofMatrixCLM N := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] [DecidableEq κ] in
/-- A constant matrix with `Mᴴ M = 1` preserves inner products of `L²` fields. -/
theorem inner_ofMatrixCLM_ofMatrixCLM {M : Matrix κ ι 𝕜} (hM : M.conjTranspose * M = 1)
    (u v : L2F 𝕜 Ω ι) : ⟪ofMatrixCLM M u, ofMatrixCLM M v⟫_𝕜 = ⟪u, v⟫_𝕜 := by
  rw [inner_ofMatrixCLM, ofMatrixCLM_ofMatrixCLM, hM, ofMatrixCLM_one]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] [DecidableEq κ] in
/-- A constant matrix with `Mᴴ M = 1` is an isometry of `L²` fields. -/
theorem norm_ofMatrixCLM {M : Matrix κ ι 𝕜} (hM : M.conjTranspose * M = 1) (u : L2F 𝕜 Ω ι) :
    ‖ofMatrixCLM M u‖ = ‖u‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜), norm_eq_sqrt_re_inner (𝕜 := 𝕜),
    inner_ofMatrixCLM_ofMatrixCLM hM]

end L2F

namespace ConstCoeffOp

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] [Fintype κ'] in
theorem ofMatrix_neg_apply (M : Matrix κ' κ 𝕜) (f : κ → E → 𝕜) :
    (ofMatrix (-M) : ConstCoeffOp E 𝕜 κ κ').apply f = -(ofMatrix M).apply f := by
  funext j x
  simp [ofMatrix_apply, Finset.sum_neg_distrib]

/-- **A constant matrix intertwining two operators maps maximal domains**: if `A M = M' B` on
smooth fields, then `M D(B_max) ⊆ D(A_max)` with `A_max (M u) = M' (B_max u)`. -/
theorem maximal_ofMatrixCLM_of_comm (hΩ : IsOpen Ω) {A : ConstCoeffOp E 𝕜 ι' κ'}
    {B : ConstCoeffOp E 𝕜 ι κ} {M : Matrix ι' ι 𝕜} {M' : Matrix κ' κ 𝕜}
    (h : ∀ f : ι → E → 𝕜, (∀ i, ContDiff ℝ ∞ (f i)) →
      A.apply ((ofMatrix M).apply f) = (ofMatrix M').apply (B.apply f))
    (u : (B.maximal Ω).domain) :
    ∃ hu : L2F.ofMatrixCLM M (u : L2F 𝕜 Ω ι) ∈ (A.maximal Ω).domain,
      A.maximal Ω ⟨_, hu⟩ = L2F.ofMatrixCLM M' (B.maximal Ω u) := by
  obtain ⟨hu, he⟩ := maximal_ofMatrixCLM hΩ (M' := -M') (fun f hf => by
    rw [h f hf, ofMatrix_neg_apply, neg_neg]) u
  exact ⟨hu, by rw [he, L2F.ofMatrixCLM_neg, neg_neg]⟩

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- An intertwining by matrices with two-sided inverses passes to the inverses:
`A M = M' B` gives `B N = N' A` when `N M = 1`, `M N = 1` and `N' M' = 1`. -/
theorem apply_ofMatrix_inv [DecidableEq ι] [DecidableEq ι'] [DecidableEq κ]
    {A : ConstCoeffOp E 𝕜 ι' κ'} {B : ConstCoeffOp E 𝕜 ι κ} {M : Matrix ι' ι 𝕜}
    {M' : Matrix κ' κ 𝕜} {N : Matrix ι ι' 𝕜} {N' : Matrix κ κ' 𝕜} (hMN : M * N = 1)
    (hN'M' : N' * M' = 1)
    (h : ∀ f : ι → E → 𝕜, (∀ i, ContDiff ℝ ∞ (f i)) →
      A.apply ((ofMatrix M).apply f) = (ofMatrix M').apply (B.apply f))
    (g : ι' → E → 𝕜) (hg : ∀ i, ContDiff ℝ ∞ (g i)) :
    B.apply ((ofMatrix N).apply g) = (ofMatrix N').apply (A.apply g) := by
  have hNg : ∀ i, ContDiff ℝ ∞ ((ofMatrix N : ConstCoeffOp E 𝕜 ι' ι).apply g i) :=
    (ofMatrix N).contDiff_apply hg
  rw [← ofMatrix_one_apply (B.apply _), ← hN'M', ← ofMatrix_apply_ofMatrix, ← h _ hNg,
    ofMatrix_apply_ofMatrix, hMN, ofMatrix_one_apply]

end ConstCoeffOp

namespace ConstCoeffComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] {Ω : Set E}
  (C C' : ConstCoeffComplex E ℝ) [∀ k, DecidableEq (C.ι k)] [∀ k, DecidableEq (C'.ι k)]
  (M : ∀ k, Matrix (C'.ι k) (C.ι k) ℝ) (N : ∀ k, Matrix (C.ι k) (C'.ι k) ℝ)
  (hMN : ∀ k, M k * N k = 1) (hNM : ∀ k, N k * M k = 1)

/-- **Constant matrices intertwining two complexes of constant-coefficient operators transport
their maximal complexes**: if `C'.A k ∘ M_k = M_{k+1} ∘ C.A k` on smooth fields and the `M_k`
have two-sided inverses, then `d'_max = M d_max M⁻¹` with `D(d'_max) = M D(d_max)`. -/
theorem maximalComplex_eq_transport_ofMatrix (hΩ : IsOpen Ω)
    (h : ∀ k (f : C.ι k → E → ℝ), (∀ i, ContDiff ℝ ∞ (f i)) →
      (C'.A k).apply ((ConstCoeffOp.ofMatrix (M k)).apply f) =
        (ConstCoeffOp.ofMatrix (M (k + 1))).apply ((C.A k).apply f)) :
    C'.maximalComplex hΩ = (C.maximalComplex hΩ).transport
      (fun k => L2F.ofMatrixEquiv (M k) (N k) (hMN k) (hNM k)) (fun _ _ => 1)
      (fun _ _ => one_ne_zero) := by
  refine HilbertComplex.ext_d (funext fun i => funext fun j => ?_)
  by_cases hij : i + 1 = j
  · subst hij
    refine eq_transportD_of_conj (C.maximalComplex hΩ)
      (fun k => L2F.ofMatrixEquiv (M k) (N k) (hMN k) (hNM k)) _ (fun y => ?_) fun x _ => ?_
    · rw [maximalComplex_d, maximalComplex_d, L2F.coe_ofMatrixEquiv_symm]
      refine ⟨fun hy => (ConstCoeffOp.maximal_ofMatrixCLM_of_comm hΩ
        (ConstCoeffOp.apply_ofMatrix_inv (hMN i) (hNM (i + 1)) (h i)) ⟨y, hy⟩).1, fun hy => ?_⟩
      have e : L2F.ofMatrixCLM (M i) (L2F.ofMatrixCLM (N i) y) = y := by
        rw [L2F.ofMatrixCLM_ofMatrixCLM, hMN, L2F.ofMatrixCLM_one]
      exact e ▸ (ConstCoeffOp.maximal_ofMatrixCLM_of_comm hΩ (h i) ⟨_, hy⟩).1
    · have hx : x.1 ∈ ((C.A i).maximal Ω).domain := by
        rw [← maximalComplex_d C hΩ i]; exact x.2
      obtain ⟨h', hv⟩ := ConstCoeffOp.maximal_ofMatrixCLM_of_comm hΩ (h i) ⟨_, hx⟩
      refine ((LinearPMap.apply_eq_of_eq (maximalComplex_d C' hΩ i) _ ⟨_, h'⟩ rfl).trans
        hv).trans ?_
      exact congrArg _ (LinearPMap.apply_eq_of_eq (maximalComplex_d C hΩ i) x ⟨_, hx⟩ rfl).symm
  · have hr : ¬ (ComplexShape.up ℤ).Rel i j := by simpa using hij
    exact ((C'.maximalComplex hΩ).shape i j hr).trans
      (((C.maximalComplex hΩ).transport (fun k => L2F.ofMatrixEquiv (M k) (N k) (hMN k) (hNM k))
        (fun _ _ => 1) (fun _ _ => one_ne_zero)).shape i j hr).symm

end ConstCoeffComplex

end Intertwining

/-! ### The exterior derivative of smooth fields in coordinates -/

open Feec.Koszul.Proxy3 Feec.ExteriorFibre

/-- **The exterior derivative of fields is the coordinate exterior derivative** of
`Feec.Koszul.Proxy3` for the partial derivatives `∂_j` (`_root_.partialDeriv`). -/
theorem extD_eq_coordD (F : Finset (Fin 3) → (Fin 3 → ℝ) → ℝ) (s : Finset (Fin 3)) :
    extD F s = coordD (partialDeriv (𝕜 := ℝ)) F s := by
  funext x
  simp only [extD, coordD, Finset.sum_apply, zsmul_eq_mul, sgn]
  push_cast
  rfl

/-! ### The vector proxies -/

/-- **The vector-proxy dictionary** `vecIdx 1 k ≃ formIdx 3 k`: `∅` in degree `0`, `j ↦ {j}` in
degree `1`, `k ↦ {k}ᶜ` in degree `2`, `{0, 1, 2}` in degree `3`, and empty index types outside
`0 ≤ k ≤ 3`. -/
def proxyIdx : ∀ k : ℤ, vecIdx 1 k ≃ formIdx 3 k
  | .ofNat 0 => Equiv.ofBijective (fun _ => ⟨∅, by simp⟩) (by decide)
  | .ofNat 1 => Equiv.ofBijective (fun v => ⟨{v.2}, by simp⟩) (by decide)
  | .ofNat 2 => Equiv.ofBijective (fun v => ⟨{v.2}ᶜ, by rw [Finset.card_compl]; simp⟩)
      (by decide)
  | .ofNat 3 => Equiv.ofBijective (fun _ => ⟨Finset.univ, by simp⟩) (by decide)
  | .ofNat (m + 4) => @Equiv.equivOfIsEmpty _ _ (inferInstanceAs (IsEmpty Empty))
      ⟨fun s => by have := s.2; have := Finset.card_le_univ s.1; simp at *; omega⟩
  | .negSucc m => @Equiv.equivOfIsEmpty _ _ (inferInstanceAs (IsEmpty Empty))
      ⟨fun s => by have := s.2; omega⟩

/-- The signs of the vector proxies: `vec2Sign` in degree `2`, `1` otherwise. -/
def proxySgn : ∀ k : ℤ, vecIdx 1 k → ℝ
  | .ofNat 0 => fun _ => 1
  | .ofNat 1 => fun _ => 1
  | .ofNat 2 => fun v => vec2Sign v.2
  | .ofNat 3 => fun _ => 1
  | .ofNat (_ + 4) => fun _ => 1
  | .negSucc _ => fun _ => 1

theorem proxySgn_mul_self (k : ℤ) (v : vecIdx 1 k) : proxySgn k v * proxySgn k v = 1 := by
  match k with
  | .ofNat 2 => simp only [proxySgn]; exact_mod_cast vec2Sign_mul_self v.2
  | .ofNat 0 | .ofNat 1 | .ofNat 3 | .ofNat (_ + 4) | .negSucc _ => simp [proxySgn]

/-- The signed permutation matrix of a bijection `e : κ ≃ ι` and signs `ε`:
`(P f)_a = ε_a f_{e a}`. -/
def signedPerm {ι κ : Type*} [DecidableEq ι] (e : κ ≃ ι) (ε : κ → ℝ) : Matrix κ ι ℝ :=
  fun a i => if e a = i then ε a else 0

section SignedPerm

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : κ ≃ ι)
  (ε : κ → ℝ)

omit [Fintype κ] [DecidableEq κ] in
theorem ofMatrix_signedPerm_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ι → E → ℝ) :
    (ConstCoeffOp.ofMatrix (signedPerm e ε) : ConstCoeffOp E ℝ ι κ).apply f =
      fun a => ε a • f (e a) := by
  funext a x
  simp [ConstCoeffOp.ofMatrix_apply, signedPerm]

variable {ε} (hε : ∀ a, ε a * ε a = 1)
include hε

omit [Fintype κ] in
theorem signedPerm_mul_transpose : signedPerm e ε * (signedPerm e ε).transpose = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, signedPerm, Matrix.one_apply, ite_mul,
    zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hab : a = b
  · subst hab; simp [hε]
  · simp [e.injective.ne hab, hab]

omit [Fintype ι] [DecidableEq κ] in
theorem transpose_mul_signedPerm : (signedPerm e ε).transpose * signedPerm e ε = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, signedPerm, Matrix.one_apply]
  rw [Finset.sum_eq_single (e.symm i) (fun a _ ha => by
    have : e a ≠ i := fun h => ha (by rw [← h, Equiv.symm_apply_apply])
    simp [this]) (by simp)]
  by_cases hij : i = j
  · subst hij; simp [hε]
  · simp [hij]

end SignedPerm

/-- The proxy matrix in degree `k`: the signed permutation `(P_k ω)_v = ε_v ω_{e v}`. -/
def proxyMat (k : ℤ) : Matrix (vecIdx 1 k) (formIdx 3 k) ℝ := signedPerm (proxyIdx k) (proxySgn k)

theorem proxyMat_mul_transpose (k : ℤ) : proxyMat k * (proxyMat k).transpose = 1 :=
  signedPerm_mul_transpose _ (proxySgn_mul_self k)

theorem transpose_mul_proxyMat (k : ℤ) : (proxyMat k).transpose * proxyMat k = 1 :=
  transpose_mul_signedPerm _ (proxySgn_mul_self k)

/-! #### The proxies in each degree -/

theorem ofMatrix_proxyMat_zero (w : formIdx 3 0 → (Fin 3 → ℝ) → ℝ) :
    (ConstCoeffOp.ofMatrix (proxyMat 0)).apply w = fun _ => formExt w ∅ := by
  rw [proxyMat, ofMatrix_signedPerm_apply]
  funext v
  exact (one_smul ℝ _).trans (formExt_of_card w (by simp)).symm

theorem ofMatrix_proxyMat_one (w : formIdx 3 1 → (Fin 3 → ℝ) → ℝ) :
    (ConstCoeffOp.ofMatrix (proxyMat 1)).apply w = fun v => vec1 (formExt w) v.2 := by
  rw [proxyMat, ofMatrix_signedPerm_apply]
  funext v
  exact (one_smul ℝ _).trans (formExt_of_card w (by simp)).symm

theorem ofMatrix_proxyMat_two (w : formIdx 3 2 → (Fin 3 → ℝ) → ℝ) :
    (ConstCoeffOp.ofMatrix (proxyMat 2)).apply w = fun v => vec2 (formExt w) v.2 := by
  rw [proxyMat, ofMatrix_signedPerm_apply]
  funext v
  rw [vec2_apply, ← Int.cast_smul_eq_zsmul ℝ,
    formExt_of_card w (by rw [Finset.card_compl]; simp)]
  rfl

theorem ofMatrix_proxyMat_three (w : formIdx 3 3 → (Fin 3 → ℝ) → ℝ) :
    (ConstCoeffOp.ofMatrix (proxyMat 3)).apply w = fun _ => vol (formExt w) := by
  rw [proxyMat, ofMatrix_signedPerm_apply]
  funext v
  exact (one_smul ℝ _).trans (formExt_of_card w (by decide)).symm

/-- `grad = P₁ d P₀⁻¹`: `Feec.Koszul.Proxy3.vec1_coordD` for the partial derivatives. -/
theorem gradOp_proxyMat (f : formIdx 3 0 → (Fin 3 → ℝ) → ℝ) :
    (gradOp 3 1).apply ((ConstCoeffOp.ofMatrix (proxyMat 0)).apply f) =
      (ConstCoeffOp.ofMatrix (proxyMat 1)).apply ((extDerivOp ℝ 3 0).apply f) := by
  rw [ofMatrix_proxyMat_zero, ofMatrix_proxyMat_one]
  funext v x
  rw [gradOp_apply]
  have h := congrFun (vec1_coordD (partialDeriv (𝕜 := ℝ)) (formExt f)) v.2
  simp only [vec1, gradOf, ← extD_eq_coordD] at h
  rw [vec1, formExt_extDerivOp_apply f (by simp), h]
  rfl

/-- `curl = P₂ d P₁⁻¹`: `Feec.Koszul.Proxy3.vec2_coordD` for the partial derivatives. -/
theorem curlOp_proxyMat (f : formIdx 3 1 → (Fin 3 → ℝ) → ℝ) :
    (curlOp 1).apply ((ConstCoeffOp.ofMatrix (proxyMat 1)).apply f) =
      (ConstCoeffOp.ofMatrix (proxyMat 2)).apply ((extDerivOp ℝ 3 1).apply f) := by
  rw [ofMatrix_proxyMat_one, ofMatrix_proxyMat_two]
  funext ⟨i, k⟩ x
  rw [curlOp_apply]
  have h : vec2 (formExt ((extDerivOp ℝ 3 1).apply f)) =
      curlOf (partialDeriv (𝕜 := ℝ)) (vec1 (formExt f)) := by
    rw [← vec2_coordD]
    funext j
    rw [vec2_apply, vec2_apply, formExt_extDerivOp_apply f (by rw [Finset.card_compl]; simp),
      extD_eq_coordD]
  rw [h]
  fin_cases k <;> rfl

/-- `div = P₃ d P₂⁻¹`: `Feec.Koszul.Proxy3.vol_coordD` for the partial derivatives. -/
theorem divOp_proxyMat (f : formIdx 3 2 → (Fin 3 → ℝ) → ℝ) :
    (divOp 3 1).apply ((ConstCoeffOp.ofMatrix (proxyMat 2)).apply f) =
      (ConstCoeffOp.ofMatrix (proxyMat 3)).apply ((extDerivOp ℝ 3 2).apply f) := by
  rw [ofMatrix_proxyMat_two, ofMatrix_proxyMat_three]
  funext v x
  rw [divOp_apply, vol, formExt_extDerivOp_apply f (by decide), extD_eq_coordD]
  change _ = vol (coordD (partialDeriv (𝕜 := ℝ)) (formExt f)) x
  rw [vol_coordD _ fun j m => funext (partialDeriv_neg m j)]
  simp [divOf, partialDeriv]

/-- **The vector proxies intertwine `d` with `grad`, `curl`, `div`** on all fields, in every
degree: `(vecOp k) (P_k f) = P_{k+1} (d f)` (`gradOp_proxyMat`, `curlOp_proxyMat`,
`divOp_proxyMat`; outside `0 ≤ k ≤ 2` one side of each operator is an empty index type). -/
theorem vecOp_proxyMat (k : ℤ) (f : formIdx 3 k → (Fin 3 → ℝ) → ℝ) :
    (vecOp ℝ 1 k).apply ((ConstCoeffOp.ofMatrix (proxyMat k)).apply f) =
      (ConstCoeffOp.ofMatrix (proxyMat (k + 1))).apply ((extDerivOp ℝ 3 k).apply f) := by
  match k with
  | .ofNat 0 => exact gradOp_proxyMat f
  | .ofNat 1 => exact curlOp_proxyMat f
  | .ofNat 2 => exact divOp_proxyMat f
  | .ofNat 3 => funext v; exact isEmptyElim (α := Empty) v
  | .ofNat (m + 4) => funext v; exact isEmptyElim (α := Empty) v
  | .negSucc m =>
    have : IsEmpty (formIdx 3 (.negSucc m)) := ⟨fun s => by have := s.2; omega⟩
    have : IsEmpty (vecIdx 1 (.negSucc m)) := inferInstanceAs (IsEmpty Empty)
    rw [(extDerivOp ℝ 3 _).apply_of_isEmpty, ConstCoeffOp.apply_zero]
    exact (vecOp ℝ 1 _).apply_of_isEmpty _

instance (k : ℤ) : DecidableEq ((deRham ℝ 3).ι k) := inferInstanceAs (DecidableEq (formIdx 3 k))

variable {Ω : Set (Fin 3 → ℝ)}

/-- **The vector proxy** `L²Λᵏ(Ω) ≃ L²(Ω; vecIdx 1 k)`, the signed permutation `proxyMat k`
of the components (`f = ω_∅`, `v_j = ω_{j}`, `u = (ω_{12}, -ω_{02}, ω_{01})`, `g = ω_{012}`):
a unitary map. -/
def proxy (k : ℤ) : L2F ℝ Ω (formIdx 3 k) ≃ₗᵢ[ℝ] L2F ℝ Ω (vecIdx 1 k) where
  toLinearEquiv := (L2F.ofMatrixEquiv (proxyMat k) (proxyMat k).transpose
    (proxyMat_mul_transpose k) (transpose_mul_proxyMat k)).toLinearEquiv
  norm_map' := L2F.norm_ofMatrixCLM (by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact transpose_mul_proxyMat k)

@[simp] theorem proxy_apply (k : ℤ) (u : L2F ℝ Ω (formIdx 3 k)) :
    proxy k u = L2F.ofMatrixCLM (proxyMat k) u := rfl

/-- **The vector-proxy complex is the de Rham complex in proxies**: on every open `Ω ⊆ ℝ³`, the
maximal complex `H¹(Ω) --grad--> H(curl, Ω) --curl--> H(div, Ω) --div--> L²(Ω)` of
`deRhamVec ℝ 1` is the unitary transport of `HΛ(Ω)` along the vector proxies. [AFW2006], §2;
[AFW2010], §4 -/
theorem deRhamVec_maximalComplex_eq_map (hΩ : IsOpen Ω) :
    (deRhamVec ℝ 1).maximalComplex hΩ = ((deRham ℝ 3).maximalComplex hΩ).map proxy :=
  ConstCoeffComplex.maximalComplex_eq_transport_ofMatrix (deRham ℝ 3) (deRhamVec ℝ 1) proxyMat
    (fun k => (proxyMat k).transpose) proxyMat_mul_transpose transpose_mul_proxyMat hΩ
    fun k f _ => vecOp_proxyMat k f

end Feec.Domain
