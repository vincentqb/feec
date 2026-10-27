module

public import Feec.Domain.BGG
public import Feec.Domain.Elasticity
public import Feec.Domain.HessianComplex

/-!
# The elasticity complex as a BGG complex

The de Rham complex of `ℝ³` with values in `𝕜³` (`deRhamVec 3`) stacked over itself, linked by
`S⁰ = -mskw` (`(S⁰ψ)_{i,i+1} = -ψ_{i+2}`), `S¹ u = uᵀ - tr u · I` and `S² = 2 vskw`
(`(S² u)ᵢ = u_{i+1,i+2} − u_{i+2,i+1}`), is BGG data of constant-coefficient operators
(`elasticityBGG`): `S⁰` is one-to-one, `S¹` is bijective and `S²` is onto, so the
injectivity/surjectivity condition holds at `J = 1` (**`injSurj_elasticityBGG`**). Its BGG complex
`bgg 1` eliminates `V²`, `V³` against `S¹`, `S²` and `Ṽ⁰` against `S⁰`, and **is the elasticity
complex** `𝕜³ --sym grad--> Sym --inc--> Sym --div--> 𝕜³` of `Feec.Domain.Elasticity` on smooth
fields (**`elasticityBGGIso`**): in degree `0` the quotient `V⁰ = (V⁰ × Ṽ⁰) / (0 × Ṽ⁰)`, in degree
`1` the quotient `V¹ / R(S⁰) = 𝕜^{3×3} / skew ≅ Sym`, `[σ] ↦ sym σ` (the pairs `(σ, (S¹)⁻¹ curl σ)`
modulo `(-S⁰ψ, grad ψ)`), with differentials `u ↦ sym grad u` and
`σ ↦ curl (S¹)⁻¹ curl σ = inc (sym σ)` (`curlOp_elN1_curlOp`), and after `1` the fields
`0 × N(Sᵏ)`, symmetric in degree `2`, with the divergence. Hence the smooth elasticity complex has
the cohomology of the twisted de Rham complex (`elasticitySmoothComplexHomologyIso`).

## Main definitions

* `Feec.Domain.elasticityBGG`: the BGG diagram of the elasticity complex.
* `Feec.Domain.elasticitySmoothComplex`: the smooth elasticity complex (`elasticityOp`,
  `elasticityMat`).

## Main results

* **`injSurj_elasticityBGG`**, `elasticityBGGHomologyIso`.
* **`elasticityBGGIso`**, `elasticitySmoothComplexHomologyIso`.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §4.1, (32) (the elasticity
  complex, `J = 1`)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §11 (the elasticity complex from two de Rham complexes)
* [M. Eastwood, *A complex from linear elasticity*][Eastwood2000] (the elasticity complex from the
  BGG resolution)
* [A. Čap, J. Slovák, V. Souček, *Bernstein–Gelfand–Gelfand sequences*][CapSlovakSoucek2001]
  (BGG sequences)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped ContDiff
open CategoryTheory

@[expose] public noncomputable section

namespace Feec.Domain

variable {𝕜 : Type*} [RCLike 𝕜]

section Elasticity

open ConstCoeffOp Matrix

/-- `S⁰ = -mskw : 𝕜³ → 𝕜^{3×3}`: `(S⁰ψ)_{i,i+1} = -ψ_{i+2}`, `(S⁰ψ)_{i+1,i} = ψ_{i+2}`. -/
def elS0 : Matrix (Fin 3 × Fin 3) (Fin 3) 𝕜 := fun ij l =>
  if ij.2 = ij.1 + 1 ∧ l = ij.1 + 2 then -1 else if ij.1 = ij.2 + 1 ∧ l = ij.2 + 2 then 1 else 0

/-- `S¹ u = uᵀ - tr u · I`. -/
def elS1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) 𝕜 := fun ij kl =>
  (if kl = (ij.2, ij.1) then 1 else 0) - (if ij.1 = ij.2 ∧ kl.1 = kl.2 then 1 else 0)

/-- `S² = 2 vskw : 𝕜^{3×3} → 𝕜³`, `(S² u)ᵢ = u_{i+1,i+2} − u_{i+2,i+1}`. -/
def elS2 : Matrix (Fin 3) (Fin 3 × Fin 3) 𝕜 := fun i kl =>
  if kl = (i + 1, i + 2) then 1 else if kl = (i + 2, i + 1) then -1 else 0

variable (𝕜) in
/-- The connecting operators of the elasticity diagram: `-mskw`, `T - tr`, `2 vskw`. -/
def elasticityS : ∀ k : ℤ, ConstCoeffOp (Fin 3 → ℝ) 𝕜 (vecIdx 3 k) (vecIdx 3 (k + 1))
  | .ofNat 0 => ofMatrix elS0
  | .ofNat 1 => ofMatrix elS1
  | .ofNat 2 => ofMatrix elS2
  | .ofNat (_ + 3) => zeroOp _ _
  | .negSucc _ => zeroOp _ _

theorem ofMatrix_elS0_apply (f : Fin 3 → (Fin 3 → ℝ) → 𝕜) (i j : Fin 3) :
    (ofMatrix elS0 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f (i, j) =
      if j = i + 1 then -f (i + 2) else if i = j + 1 then f (j + 2) else 0 := by
  funext x
  simp only [ofMatrix_apply, elS0, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp

theorem ofMatrix_elS1_apply (f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) (i j : Fin 3) :
    (ofMatrix elS1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f (i, j) =
      f (j, i) - if i = j then f (0, 0) + f (1, 1) + f (2, 2) else 0 := by
  funext x
  simp only [ofMatrix_apply, elS1, Fintype.sum_prod_type, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem ofMatrix_elS2_apply (f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) (i : Fin 3) :
    (ofMatrix elS2 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f i =
      f (i + 1, i + 2) - f (i + 2, i + 1) := by
  funext x
  simp only [ofMatrix_apply, elS2, Fintype.sum_prod_type, Fin.sum_univ_three, Pi.sub_apply]
  fin_cases i <;> simp <;> ring

/-- `curl S⁰ = -S¹ grad`. -/
theorem curlOp_elS0 (f : Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    (curlOp 3).apply ((ofMatrix elS0).apply f) =
      -(ofMatrix elS1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply ((gradOp 3 3).apply f) := by
  funext ⟨i, k⟩ x
  rw [curlOp_apply, Pi.neg_apply, Pi.neg_apply, ofMatrix_elS1_apply, ofMatrix_elS0_apply,
    ofMatrix_elS0_apply]
  fin_cases i <;> fin_cases k <;> simp [gradOp_apply, fderiv_neg] <;> ring

/-- `div S¹ = -S² curl`. -/
theorem divOp_elS1 {f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜} (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (divOp 3 3).apply ((ofMatrix elS1).apply f) =
      -(ofMatrix elS2 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply ((curlOp 3).apply f) := by
  funext i x
  have hd : ∀ a : Fin 3 × Fin 3, DifferentiableAt ℝ (f a) x :=
    fun a => ((hf a).differentiable (by simp)).differentiableAt
  have key : ∀ j : Fin 3, fderiv ℝ (f (j, i) - if i = j then f (0, 0) + f (1, 1) + f (2, 2) else 0)
      x = fderiv ℝ (f (j, i)) x - if i = j then
        fderiv ℝ (f (0, 0)) x + fderiv ℝ (f (1, 1)) x + fderiv ℝ (f (2, 2)) x else 0 := by
    intro j
    split_ifs
    · rw [fderiv_sub (hd _) (((hd _).add (hd _)).add (hd _)),
        fderiv_add ((hd _).add (hd _)) (hd _), fderiv_add (hd _) (hd _)]
    · rw [sub_zero, sub_zero]
  rw [divOp_apply, Pi.neg_apply, Pi.neg_apply, ofMatrix_elS2_apply]
  simp only [ofMatrix_elS1_apply, key, Fin.sum_univ_three, Pi.sub_apply, curlOp_apply]
  fin_cases i <;> simp <;> ring

theorem elasticityS_anticomm (k : ℤ) (f : vecIdx 3 k → (Fin 3 → ℝ) → 𝕜)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (vecOp 𝕜 3 (k + 1)).apply ((elasticityS 𝕜 k).apply f) =
      -(elasticityS 𝕜 (k + 1)).apply ((vecOp 𝕜 3 k).apply f) := by
  by_cases h0 : k = 0
  · subst h0; exact curlOp_elS0 f
  by_cases h1 : k = 1
  · subst h1; exact divOp_elS1 hf
  rcases lt_or_gt_of_ne h0 with hk | hk
  · have := isEmpty_vecIdx 3 (k := k) (Or.inl hk)
    rw [ConstCoeffOp.apply_eq_zero_of_isEmpty _ f (Or.inl this),
      ConstCoeffOp.apply_eq_zero_of_isEmpty _ f (Or.inl this), apply_zero, apply_zero, neg_zero]
  · have := isEmpty_vecIdx 3 (k := k + 1 + 1) (Or.inr (by omega))
    exact funext fun j => isEmptyElim j

variable (𝕜) in
/-- **The BGG diagram of the elasticity complex**: the de Rham complex with values in `𝕜³` over
itself, linked by `-mskw`, `T - tr`, `2 vskw`. [ArnoldHu2021], §4.1, (32) -/
abbrev elasticityBGG : ConstCoeffBGG (Fin 3 → ℝ) 𝕜 where
  top := deRhamVec 𝕜 3
  bot := deRhamVec 𝕜 3
  S := elasticityS 𝕜
  anticomm := elasticityS_anticomm

/-- A left inverse of `S⁰`: `ψ_l = M_{l+2,l+1}`. -/
def elN0 : Matrix (Fin 3) (Fin 3 × Fin 3) 𝕜 := fun l ij => if ij = (l + 2, l + 1) then 1 else 0

/-- The inverse of `S¹`: `w ↦ wᵀ - (tr w / 2) I`. -/
def elN1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) 𝕜 := fun ij kl =>
  (if kl = (ij.2, ij.1) then 1 else 0) - (if ij.1 = ij.2 ∧ kl.1 = kl.2 then 2⁻¹ else 0)

/-- A right inverse of `S²`: `v ↦ u` with `u_{i+1,i+2} = vᵢ` and the other entries `0`. -/
def elN2 : Matrix (Fin 3 × Fin 3) (Fin 3) 𝕜 := fun kl i => if kl = (i + 1, i + 2) then 1 else 0

theorem elN0_mul_elS0 : elN0 * elS0 = (1 : Matrix (Fin 3) (Fin 3) 𝕜) := by
  ext l l'
  fin_cases l <;> fin_cases l' <;>
    simp [Matrix.mul_apply, elS0, elN0, Fintype.sum_prod_type, Fin.sum_univ_three]

theorem elS1_mul_elN1 : elS1 * elN1 = (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) 𝕜) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Matrix.mul_apply, elS1, elN1, Fintype.sum_prod_type, Fin.sum_univ_three] <;> norm_num

theorem elN1_mul_elS1 : elN1 * elS1 = (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) 𝕜) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Matrix.mul_apply, elS1, elN1, Fintype.sum_prod_type, Fin.sum_univ_three] <;> norm_num

theorem elS2_mul_elN2 : elS2 * elN2 = (1 : Matrix (Fin 3) (Fin 3) 𝕜) := by
  ext i i'
  fin_cases i <;> fin_cases i' <;>
    simp [Matrix.mul_apply, elS2, elN2]

/-- **The elasticity diagram satisfies the injectivity/surjectivity condition at `J = 1`**:
`-mskw` is one-to-one, `T - tr` and `2 vskw` are onto. [ArnoldHu2021], (23), §4.1 -/
theorem injSurj_elasticityBGG : (elasticityBGG 𝕜).smoothData.InjSurj 1 := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [ConstCoeffBGG.smoothData_S]
    by_cases h0 : i = 0
    · subst h0
      have h := smoothMap_ofMatrix_injective (E := Fin 3 → ℝ) (elN0_mul_elS0 (𝕜 := 𝕜))
      exact h
    have := isEmpty_vecIdx 3 (k := i) (Or.inl (by omega))
    have hs := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 3 i)
    exact fun a b _ => hs.elim a b
  · rw [ConstCoeffBGG.smoothData_S]
    by_cases h1 : i = 1
    · subst h1
      have h := smoothMap_ofMatrix_surjective (E := Fin 3 → ℝ) (elS1_mul_elN1 (𝕜 := 𝕜))
      exact h
    by_cases h2 : i = 2
    · subst h2
      have h := smoothMap_ofMatrix_surjective (E := Fin 3 → ℝ) (elS2_mul_elN2 (𝕜 := 𝕜))
      exact h
    have := isEmpty_vecIdx 3 (k := i + 1) (Or.inr (by omega))
    have hs := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 3 (i + 1))
    exact fun y => ⟨0, hs.elim _ _⟩

/-- **The elasticity BGG complex has the cohomology of the twisted de Rham complex.**
[ArnoldHu2021], §5.2 -/
def elasticityBGGHomologyIso (i : ℤ) :
    ((elasticityBGG 𝕜).smoothData.bgg 1).homology i ≅
      (elasticityBGG 𝕜).smoothData.twistComplex.homology i :=
  BGG.Data.bggHomologyIso injSurj_elasticityBGG i

/-! ### Pointwise identities -/

theorem ofMatrix_elN1_apply (f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) (i j : Fin 3) :
    (ofMatrix elN1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f (i, j) =
      f (j, i) - if i = j then (2⁻¹ : 𝕜) • (f (0, 0) + f (1, 1) + f (2, 2)) else 0 := by
  funext x
  simp only [ofMatrix_apply, elN1, Fintype.sum_prod_type, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem ofMatrix_elN0_apply (f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) (l : Fin 3) :
    (ofMatrix elN0 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f l = f (l + 2, l + 1) := by
  funext x
  simp only [ofMatrix_apply, elN0, Fintype.sum_prod_type, Fin.sum_univ_three]
  fin_cases l <;> simp

/-- `sym S⁰ = 0`: `S⁰ψ` is skew. -/
theorem matMulField_symMat_elS0 (f : Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    matMulField (symMat 3) ((ofMatrix elS0 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f) = 0 := by
  funext ⟨i, j⟩ x
  rw [matMulField_symMat, ofMatrix_elS0_apply, ofMatrix_elS0_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- A skew field is `S⁰` of its axial vector: `S⁰ (N⁰ σ) = σ` when `sym σ = 0`. -/
theorem elS0_elN0_of_skew {σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜}
    (h : matMulField (symMat 3) σ = 0) :
    (ofMatrix elS0 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply ((ofMatrix elN0).apply σ) = σ := by
  have h' : ∀ i j x, σ (i, j) x = -σ (j, i) x := fun i j x => by
    have := congrFun (congrFun h (i, j)) x
    rw [matMulField_symMat] at this
    simp only [Pi.zero_apply] at this
    linear_combination (2 : 𝕜) * this
  funext ⟨i, j⟩ x
  rw [ofMatrix_elS0_apply, ofMatrix_elN0_apply, ofMatrix_elN0_apply]
  fin_cases i <;> fin_cases j <;> simp <;>
    first
    | linear_combination (-1 / 2 : 𝕜) * h' 0 0 x
    | linear_combination (-1 / 2 : 𝕜) * h' 1 1 x
    | linear_combination (-1 / 2 : 𝕜) * h' 2 2 x
    | linear_combination h' 0 1 x | linear_combination h' 1 0 x
    | linear_combination h' 0 2 x | linear_combination h' 2 0 x
    | linear_combination h' 1 2 x | linear_combination h' 2 1 x
    | linear_combination -h' 0 1 x | linear_combination -h' 1 0 x
    | linear_combination -h' 0 2 x | linear_combination -h' 2 0 x
    | linear_combination -h' 1 2 x

/-- **`curl (S¹)⁻¹ curl σ = inc (sym σ)`**: the differential in degree `1` of the elasticity BGG
complex is the incompatibility operator on the symmetric part. -/
theorem curlOp_elN1_curlOp {σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜} (hσ : ∀ i, ContDiff ℝ ∞ (σ i)) :
    (curlOp 3).apply ((ofMatrix elN1).apply ((curlOp 3).apply σ)) =
      (incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply (matMulField (symMat 3) σ) := by
  set s := matMulField (symMat 3) σ with hsdef
  have hs : ∀ i, ContDiff ℝ ∞ (s i) := contDiff_matMulField _ hσ
  set w := σ - s with hwdef
  have hw : ∀ i, ContDiff ℝ ∞ (w i) := fun i => (hσ i).sub (hs i)
  have hσ' : σ = s + w := by rw [hwdef, add_sub_cancel]
  have hcs : ∀ i, ContDiff ℝ ∞ ((curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply s i) :=
    (curlOp 3).contDiff_apply hs
  have hcw : ∀ i, ContDiff ℝ ∞ ((curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply w i) :=
    (curlOp 3).contDiff_apply hw
  rw [hσ', (curlOp 3).apply_add hs hw, (ofMatrix elN1).apply_add hcs hcw,
    (curlOp 3).apply_add ((ofMatrix elN1).contDiff_apply hcs) ((ofMatrix elN1).contDiff_apply hcw)]
  -- the skew part contributes nothing
  have hskew : matMulField (symMat 3) w = 0 := by
    funext ij x
    simp only [hwdef, hsdef, matMulField, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
      Pi.zero_apply]
    have := congrFun (congrFun (isProjMat_symMat (𝕜 := 𝕜) (n := 3).matMulField_matMulField σ) ij) x
    simp only [matMulField] at this
    rw [this, sub_self]
  set ψ := (ofMatrix elN0 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply w
  have hψ : ∀ i, ContDiff ℝ ∞ (ψ i) := (ofMatrix elN0).contDiff_apply hw
  have hw0 : (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      ((ofMatrix elN1).apply ((curlOp 3).apply w)) = 0 := by
    rw [← elS0_elN0_of_skew hskew, curlOp_elS0, (ofMatrix elN1).apply_neg
      ((ofMatrix elS1).contDiff_apply ((gradOp 3 3).contDiff_apply hψ)),
      ofMatrix_apply_ofMatrix, elN1_mul_elS1, ofMatrix_one_apply,
      (curlOp 3).apply_neg ((gradOp 3 3).contDiff_apply hψ), isComplexPair_grad_curl ψ hψ,
      neg_zero]
  rw [hw0, add_zero]
  -- the symmetric part: `(S¹)⁻¹ curl s = (curl s)ᵀ`
  have hsym : ∀ i j, s (i, j) = s (j, i) := matMulField_symMat_symm σ
  have htr : (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply s (0, 0) +
      (curlOp 3).apply s (1, 1) + (curlOp 3).apply s (2, 2) = 0 := by
    funext x
    have := trace_curlOp_eq_zero_of_symm hsym x
    simpa [Fin.sum_univ_three] using this
  have hT : (ofMatrix elN1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply ((curlOp 3).apply s) =
      fun ik => (curlOp 3).apply s (ik.2, ik.1) := by
    funext ⟨i, k⟩
    rw [ofMatrix_elN1_apply, htr, smul_zero, ite_self, sub_zero]
  rw [hT, incOp_apply hs]

/-! ### The BGG complex is the smooth elasticity complex -/

variable (𝕜) in
/-- The smooth elasticity complex `𝕜³ --sym grad--> Sym --inc--> Sym --div--> 𝕜³` of
`Feec.Domain.Elasticity`. -/
abbrev elasticitySmoothComplex : CochainComplex (ModuleCat 𝕜) ℤ :=
  (elasticityConstCoeffComplex 𝕜).smoothComplex (elasticityMat 𝕜) elasticityOp_matMapsTo

theorem bijective_elasticityBGG_S_one :
    Function.Bijective ((elasticityBGG 𝕜).smoothData.S 1 (1 + 1)) := by
  rw [ConstCoeffBGG.smoothData_S]
  have h1 := smoothMap_ofMatrix_injective (E := Fin 3 → ℝ) (elN1_mul_elS1 (𝕜 := 𝕜))
  have h2 := smoothMap_ofMatrix_surjective (E := Fin 3 → ℝ) (elS1_mul_elN1 (𝕜 := 𝕜))
  exact ⟨h1, h2⟩

theorem range_elasticityBGG_S_neg_one :
    LinearMap.range ((elasticityBGG 𝕜).smoothData.S (0 - 1) 0) = ⊥ := by
  have := isEmpty_vecIdx 3 (k := 0 - 1) (Or.inl (by norm_num))
  have hs := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 3 (0 - 1))
  refine eq_bot_iff.2 ?_
  rintro _ ⟨ψ, rfl⟩
  rw [hs.elim ψ 0, map_zero]
  exact zero_mem _

theorem elasticityBGG_Δ_eq_bot {k : ℤ} (hk : k < 0 ∨ 1 < k) :
    (elasticityBGG 𝕜).smoothData.Δ (· < 1) k = ⊥ := by
  rcases hk with hk | hk
  · have := isEmpty_vecIdx 3 (k := k) (Or.inl hk)
    have h3 := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 3 k)
    exact eq_bot_iff.2 fun x _ => (Submodule.mem_bot 𝕜).2 (Prod.ext (h3.elim _ _) (h3.elim _ _))
  · exact (elasticityBGG 𝕜).smoothData.bgg_Δ_of_gt hk

/-- `σ ↦ sym σ` on smooth matrix fields. -/
def symSmoothMap : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3) →ₗ[𝕜]
    smoothFieldsIn (Fin 3 → ℝ) (symMat 3 : _ → _ → 𝕜) where
  toFun σ := ⟨matMulField (symMat 3) σ, contDiff_matMulField _ σ.2,
    isProjMat_symMat.matMulField_matMulField _⟩
  map_add' _ _ := Subtype.ext (funext fun _ => funext fun _ => by
    simp [matMulField, mul_add, Finset.sum_add_distrib])
  map_smul' _ _ := Subtype.ext (funext fun _ => funext fun _ => by
    simp [matMulField, Finset.mul_sum, mul_left_comm])

theorem symSmoothMap_surjective : Function.Surjective (symSmoothMap (𝕜 := 𝕜)) := fun s =>
  ⟨⟨s, s.2.1⟩, Subtype.ext s.2.2⟩

/-- The kernel of `sym` is the range of `-mskw` (`S⁰` of the elasticity diagram, `S¹` of the
div-div diagram). -/
theorem ker_symSmoothMap :
    LinearMap.ker (symSmoothMap (𝕜 := 𝕜)) =
      LinearMap.range (ofMatrix elS0 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).smoothMap := by
  ext σ
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro h
    have h' : matMulField (symMat 3) (σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) = 0 :=
      congrArg Subtype.val h
    exact ⟨(ofMatrix elN0).smoothMap σ, Subtype.ext (elS0_elN0_of_skew h')⟩
  · rintro ⟨ψ, rfl⟩
    exact Subtype.ext (matMulField_symMat_elS0
      (Subtype.val (p := fun f => f ∈ smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3)) ψ))

/-- `𝕜^{3×3} / skew ≃ Sym`, `[σ] ↦ sym σ`, for any presentation `p` of the skew fields. -/
def symQuotEquiv {p : Submodule 𝕜 (smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3))}
    (hp : p = LinearMap.range (ofMatrix elS0 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).smoothMap) :
    (smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3) ⧸ p) ≃ₗ[𝕜]
      smoothFieldsIn (Fin 3 → ℝ) (symMat 3 : _ → _ → 𝕜) :=
  (Submodule.quotEquivOfEq _ _ (hp.trans ker_symSmoothMap.symm)).trans
    (LinearMap.quotKerEquivOfSurjective _ symSmoothMap_surjective)

/-- The kernel of `S² = 2 vskw` is the symmetric constraint. -/
def kerElS2Equiv : LinearMap.ker ((elasticityBGG 𝕜).smoothData.S 2 (2 + 1)) ≃ₗ[𝕜]
    smoothFieldsIn (Fin 3 → ℝ) (symMat 3 : _ → _ → 𝕜) where
  toFun u := ⟨((u : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3)) : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜),
    fun i => (u : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3)).2 i,
    matMulField_symMat_of_symm (vskw_eq_zero_iff.1 fun k => by
      have h := congrArg (fun v : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3) =>
        (v : Fin 3 → (Fin 3 → ℝ) → 𝕜) k) (LinearMap.mem_ker.1 u.2)
      change (ofMatrix elS2 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
        ((u : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3)) : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) k =
          0 at h
      rwa [ofMatrix_elS2_apply] at h)⟩
  invFun f := ⟨⟨(f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜), f.2.1⟩, LinearMap.mem_ker.2 (by
    refine Subtype.ext (funext fun k => ?_)
    change (ofMatrix elS2 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      (f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) k = 0
    rw [ofMatrix_elS2_apply]
    refine (vskw_eq_zero_iff.2 fun i j => ?_) k
    rw [← f.2.2]
    exact matMulField_symMat_symm _ i j)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The kernel of `S³ = 0` is all of `Ṽ³`. -/
def kerElS3Equiv : LinearMap.ker ((elasticityBGG 𝕜).smoothData.S 3 (3 + 1)) ≃ₗ[𝕜]
    smoothFieldsIn (Fin 3 → ℝ) (idMat (Fin 3) : _ → _ → 𝕜) where
  toFun u := ⟨((u : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3)) : Fin 3 → (Fin 3 → ℝ) → 𝕜),
    fun i => (u : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3)).2 i, matMulField_idMat _⟩
  invFun f := ⟨⟨(f : Fin 3 → (Fin 3 → ℝ) → 𝕜), f.2.1⟩, LinearMap.mem_ker.2
    (Subtype.ext (funext fun j => isEmptyElim (α := Empty) j))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem subsingleton_elasticitySmoothComplex_X {k : ℤ} (hk : k < 0 ∨ 3 < k) :
    Subsingleton (smoothFieldsIn (Fin 3 → ℝ) (elasticityMat 𝕜 k)) := by
  have : IsEmpty (elasticityIdx k) :=
    isEmpty_elasticityIdx (by omega) (by omega) (by omega) (by omega)
  exact ⟨fun a b => Subtype.ext (funext fun i => isEmptyElim i)⟩

theorem subsingleton_elasticityBGG_Γ {k : ℤ} (hk : k < 0 ∨ 3 < k) :
    Subsingleton ((elasticityBGG 𝕜).smoothData.Γ (1 < ·) k) := by
  have := isEmpty_vecIdx 3 hk
  have h3 := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 3 k)
  exact ⟨fun a b => Subtype.ext (Prod.ext (h3.elim _ _) (h3.elim _ _))⟩

/-- The components of the identification of the BGG complex with the elasticity complex. -/
def elasticityBGGEquiv : ∀ k : ℤ, ((elasticityBGG 𝕜).smoothData.bgg 1).X k ≃ₗ[𝕜]
    (elasticitySmoothComplex 𝕜).X k
  | .ofNat 0 => ((elasticityBGG 𝕜).smoothData.bggXEquivOfLt (J := 1) (i := 0) one_pos).trans
      ((Submodule.quotEquivOfEqBot _ range_elasticityBGG_S_neg_one).trans smoothFieldsEquivIdMat)
  | .ofNat 1 => ((elasticityBGG 𝕜).smoothData.bggXEquivOfBijective
      bijective_elasticityBGG_S_one).trans (symQuotEquiv rfl)
  | .ofNat 2 => ((elasticityBGG 𝕜).smoothData.derivedXEquiv (1 < ·) (· < 1)
      (elasticityBGG_Δ_eq_bot (Or.inr one_lt_two))).trans
      (((elasticityBGG 𝕜).smoothData.bggΓEquivKer (J := 1) (i := 2) one_lt_two).trans
        kerElS2Equiv)
  | .ofNat 3 => ((elasticityBGG 𝕜).smoothData.derivedXEquiv (1 < ·) (· < 1)
      (elasticityBGG_Δ_eq_bot (Or.inr (by norm_num)))).trans
      (((elasticityBGG 𝕜).smoothData.bggΓEquivKer (J := 1) (i := 3) (by norm_num)).trans
        kerElS3Equiv)
  | .ofNat (n + 4) =>
      have := subsingleton_elasticityBGG_Γ (𝕜 := 𝕜) (k := .ofNat (n + 4))
        (Or.inr (by rw [Int.ofNat_eq_natCast]; omega))
      have : Subsingleton ((elasticitySmoothComplex 𝕜).X (.ofNat (n + 4))) :=
        subsingleton_elasticitySmoothComplex_X (𝕜 := 𝕜) (k := .ofNat (n + 4))
          (Or.inr (by rw [Int.ofNat_eq_natCast]; omega))
      ((elasticityBGG 𝕜).smoothData.derivedXEquiv (1 < ·) (· < 1)
        (elasticityBGG_Δ_eq_bot (k := .ofNat (n + 4))
          (Or.inr (by rw [Int.ofNat_eq_natCast]; omega)))).trans (LinearEquiv.ofSubsingleton _ _)
  | .negSucc n =>
      have := subsingleton_elasticityBGG_Γ (𝕜 := 𝕜) (k := .negSucc n)
        (Or.inl (Int.negSucc_lt_zero n))
      have : Subsingleton ((elasticitySmoothComplex 𝕜).X (.negSucc n)) :=
        subsingleton_elasticitySmoothComplex_X (𝕜 := 𝕜) (k := .negSucc n)
          (Or.inl (Int.negSucc_lt_zero n))
      ((elasticityBGG 𝕜).smoothData.derivedXEquiv (1 < ·) (· < 1)
        (elasticityBGG_Δ_eq_bot (k := .negSucc n) (Or.inl (Int.negSucc_lt_zero n)))).trans
        (LinearEquiv.ofSubsingleton _ _)

theorem elasticityBGGEquiv_comm_zero :
    (elasticityBGGEquiv 0).toModuleIso.hom ≫ (elasticitySmoothComplex 𝕜).d 0 (0 + 1) =
      ((elasticityBGG 𝕜).smoothData.bgg 1).d 0 (0 + 1) ≫
        (elasticityBGGEquiv (0 + 1)).toModuleIso.hom := by
  refine ModuleCat.hom_ext (LinearMap.ext fun q => ?_)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨⟨u, ψ⟩, hx⟩ := (x : (elasticityBGG 𝕜).smoothData.Γ (1 < ·) 0)
  apply Subtype.ext
  change (symGradOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply (u : Fin 3 → (Fin 3 → ℝ) → 𝕜) =
    matMulField (symMat 3) ((gradOp 3 3).apply (u : Fin 3 → (Fin 3 → ℝ) → 𝕜) -
      (ofMatrix elS0).apply (ψ : Fin 3 → (Fin 3 → ℝ) → 𝕜))
  rw [symGradOp_apply]
  have h0 := matMulField_symMat_elS0 (𝕜 := 𝕜) ψ
  funext ij x
  have := congrFun (congrFun h0 ij) x
  simp only [matMulField, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.zero_apply] at this ⊢
  rw [this, sub_zero]

theorem elasticityBGGEquiv_comm_one :
    (elasticityBGGEquiv 1).toModuleIso.hom ≫ (elasticitySmoothComplex 𝕜).d 1 (1 + 1) =
      ((elasticityBGG 𝕜).smoothData.bgg 1).d 1 (1 + 1) ≫
        (elasticityBGGEquiv (1 + 1)).toModuleIso.hom := by
  refine ModuleCat.hom_ext (LinearMap.ext fun q => ?_)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨⟨σ, φ⟩, hx⟩ := (x : (elasticityBGG 𝕜).smoothData.Γ (1 < ·) 1)
  apply Subtype.ext
  change (incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      (matMulField (symMat 3) (σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜)) =
    (curlOp 3).apply (φ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜)
  have h := congrArg Subtype.val ((elasticityBGG 𝕜).smoothData.mem_bgg_Γ_self.1 hx)
  change (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      (σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) =
    (ofMatrix elS1).apply (φ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) at h
  have hφ : (φ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) =
      (ofMatrix elN1).apply ((curlOp 3).apply (σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜)) := by
    rw [h, ofMatrix_apply_ofMatrix, elN1_mul_elS1, ofMatrix_one_apply]
  rw [hφ, curlOp_elN1_curlOp σ.2]

theorem elasticityBGGEquiv_comm_two :
    (elasticityBGGEquiv 2).toModuleIso.hom ≫ (elasticitySmoothComplex 𝕜).d 2 (2 + 1) =
      ((elasticityBGG 𝕜).smoothData.bgg 1).d 2 (2 + 1) ≫
        (elasticityBGGEquiv (2 + 1)).toModuleIso.hom := by
  refine ModuleCat.hom_ext (LinearMap.ext fun q => ?_)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨⟨σ, u⟩, hx⟩ := (x : (elasticityBGG 𝕜).smoothData.Γ (1 < ·) 2)
  apply Subtype.ext
  change (divSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      (u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) =
    (divOp 3 3).apply (u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜)
  have h := congrArg Subtype.val
    (((elasticityBGG 𝕜).smoothData.mem_bgg_Γ_of_gt one_lt_two).1 hx).2
  change (ofMatrix elS2 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
    (u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) = 0 at h
  rw [divSymOp_apply u.2, matMulField_symMat_of_symm (vskw_eq_zero_iff.1 fun k => by
    rw [← ofMatrix_elS2_apply, h]; rfl)]

theorem subsingleton_elasticityBGG_bgg_X {k : ℤ} (hk : k < 0 ∨ 3 < k) :
    Subsingleton (((elasticityBGG 𝕜).smoothData.bgg 1).X k) :=
  have : Subsingleton ((elasticitySmoothComplex 𝕜).X k) :=
    subsingleton_elasticitySmoothComplex_X hk
  (elasticityBGGEquiv k).injective.subsingleton

theorem elasticityBGGEquiv_comm (i : ℤ) :
    (elasticityBGGEquiv i).toModuleIso.hom ≫ (elasticitySmoothComplex 𝕜).d i (i + 1) =
      ((elasticityBGG 𝕜).smoothData.bgg 1).d i (i + 1) ≫
        (elasticityBGGEquiv (i + 1)).toModuleIso.hom := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i < 0 ∨ 2 < i) with rfl | rfl | rfl | hi | hi
  · exact elasticityBGGEquiv_comm_zero
  · exact elasticityBGGEquiv_comm_one
  · exact elasticityBGGEquiv_comm_two
  · have := subsingleton_elasticityBGG_bgg_X (𝕜 := 𝕜) (Or.inl hi)
    exact ModuleCat.hom_ext (LinearMap.ext fun q => by
      rw [Subsingleton.elim q 0, map_zero, map_zero])
  · have : Subsingleton ((elasticitySmoothComplex 𝕜).X (i + 1)) :=
      subsingleton_elasticitySmoothComplex_X (Or.inr (by omega))
    exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

/-- **The BGG complex of the elasticity diagram is the elasticity complex**: `bgg 1` of
`elasticityBGG` is isomorphic to the smooth elasticity complex `sym grad → inc → div` on symmetric
fields of `Feec.Domain.Elasticity` (`elasticityOp`, `elasticityMat`). [ArnoldHu2021], §4.1, (32) -/
def elasticityBGGIso : (elasticityBGG 𝕜).smoothData.bgg 1 ≅ elasticitySmoothComplex 𝕜 :=
  HomologicalComplex.Hom.isoOfComponents (fun k => (elasticityBGGEquiv k).toModuleIso)
    fun i j hij => by
      obtain rfl : i + 1 = j := hij
      exact elasticityBGGEquiv_comm i

/-- **The cohomology of the smooth elasticity complex is that of the twisted de Rham complex**
of the elasticity diagram. [ArnoldHu2021], §5.2 -/
def elasticitySmoothComplexHomologyIso (i : ℤ) :
    (elasticitySmoothComplex 𝕜).homology i ≅
      (elasticityBGG 𝕜).smoothData.twistComplex.homology i :=
  ((HomologicalComplex.homologyFunctor _ _ i).mapIso elasticityBGGIso).symm ≪≫
    elasticityBGGHomologyIso i

end Elasticity

end Feec.Domain
