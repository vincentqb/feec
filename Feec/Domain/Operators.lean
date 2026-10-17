module

public import Feec.Domain.Complexes
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Standard constant-coefficient operators on `ℝⁿ`

Coordinates on `ℝⁿ = Fin n → ℝ`, with partial derivatives `∂ₖ f = fderiv ℝ f · (Pi.single k 1)`.

* `gradOp n m`: the row-wise gradient `𝕜^m → 𝕜^{m×n}`, `(grad φ)_{ij} = ∂ⱼ φᵢ`; its formal
  adjoint is minus the row-wise divergence (`gradOp_formalAdj_apply`);
* `divOp n m`: the row-wise divergence `𝕜^{m×n} → 𝕜^m`;
* `curlOp m`: the row-wise curl on `ℝ³`, `(curl Φ)_{ik} = ∂_{k+1} Φ_{i,k+2} − ∂_{k+2} Φ_{i,k+1}`,
  formally self-adjoint (`curlOp_formalAdj_apply`);
* `hessOp n`: the Hessian `𝕜 → 𝕜^{n×n}`, `(∇² h)_{ij} = ∂ⱼ ∂ᵢ h`.

The complex identities `curl ∘ grad = 0`, `div ∘ curl = 0`, `curl ∘ hess = 0`
(`isComplexPair_grad_curl`, `isComplexPair_curl_div`, `isComplexPair_hess_curl`) follow from
Schwarz (`fderiv_fderiv_comm`).

## References

* [Arnold2018], §6.2; [AFW2010], §2
-/

open scoped InnerProductSpace ContDiff ComplexConjugate
open MeasureTheory Set

@[expose] public noncomputable section

namespace Feec.Domain

/-- **Schwarz**: directional derivatives of a `C²` function commute. -/
theorem fderiv_fderiv_comm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 2 f) (v w x : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have e : ∀ v w : E, fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
    intro v w
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  rw [e, e]
  exact (ContDiffAt.isSymmSndFDerivAt (hf.contDiffAt (x := x)) (by simp)) _ _

namespace ConstCoeffOp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type*} [RCLike 𝕜]

@[simp] theorem applyEntry_singleton (vs : List E) (c : 𝕜) (f : E → 𝕜) (x : E) :
    applyEntry [(vs, c)] f x = c * iterDeriv vs f x := by
  simp [applyEntry]

theorem applyEntry_ite (p : Prop) [Decidable p] (P Q : List (List E × 𝕜)) (f : E → 𝕜) (x : E) :
    applyEntry (if p then P else Q) f x = if p then applyEntry P f x else applyEntry Q f x := by
  split_ifs <;> rfl

@[simp] theorem applyEntry_nil' (f : E → 𝕜) (x : E) :
    applyEntry ([] : List (List E × 𝕜)) f x = 0 := by
  simp [applyEntry]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem adjEntry_singleton (vs : List E) (c : 𝕜) :
    adjEntry [(vs, c)] = [(vs.reverse, (-1) ^ vs.length * conj c)] := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem adjEntry_ite (p : Prop) [Decidable p] (P Q : List (List E × 𝕜)) :
    adjEntry (if p then P else Q) = if p then adjEntry P else adjEntry Q := by
  split_ifs <;> rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem adjEntry_nil : adjEntry ([] : List (List E × 𝕜)) = [] := rfl

/-! ### Post-composition with a constant matrix -/

variable {ι κ κ' : Type*} [Fintype κ]

/-- `M ∘ A` for a constant matrix `M : 𝕜^κ → 𝕜^{κ'}` (e.g. the symmetric part of a matrix). -/
def postComp (M : κ' → κ → 𝕜) (A : ConstCoeffOp E 𝕜 ι κ) : ConstCoeffOp E 𝕜 ι κ' where
  coeff j' i := Finset.univ.toList.flatMap fun j => (A.coeff j i).map fun t => (t.1, M j' j * t.2)

theorem applyEntry_append (P Q : List (List E × 𝕜)) (f : E → 𝕜) (x : E) :
    applyEntry (P ++ Q) f x = applyEntry P f x + applyEntry Q f x := by
  simp [applyEntry, List.map_append, List.sum_append]

theorem applyEntry_map_smul (c : 𝕜) (P : List (List E × 𝕜)) (f : E → 𝕜) (x : E) :
    applyEntry (P.map fun t => (t.1, c * t.2)) f x = c * applyEntry P f x := by
  induction P with
  | nil => simp [applyEntry]
  | cons t P ih =>
    simp only [List.map_cons] at ih ⊢
    rw [applyEntry_cons, applyEntry_cons]
    simp only at ih ⊢
    rw [ih]
    ring

theorem applyEntry_flatMap {α : Type*} (l : List α) (P : α → List (List E × 𝕜)) (f : E → 𝕜)
    (x : E) : applyEntry (l.flatMap P) f x = (l.map fun a => applyEntry (P a) f x).sum := by
  induction l with
  | nil => simp [applyEntry]
  | cons a l ih => simp [List.flatMap_cons, applyEntry_append, ih]

theorem postComp_apply [Fintype ι] (M : κ' → κ → 𝕜) (A : ConstCoeffOp E 𝕜 ι κ)
    (f : ι → E → 𝕜) (j' : κ') (x : E) :
    (postComp M A).apply f j' x = ∑ j, M j' j * A.apply f j x := by
  simp only [apply, postComp, applyEntry_flatMap, applyEntry_map_smul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_map_toList]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem IsOrderLE.postComp {A : ConstCoeffOp E 𝕜 ι κ} {N : ℕ} (h : A.IsOrderLE N)
    (M : κ' → κ → 𝕜) : (A.postComp M).IsOrderLE N := by
  intro j' i t ht
  simp only [ConstCoeffOp.postComp, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨j, -, t', ht', rfl⟩ := ht
  exact h j i t' ht'

end ConstCoeffOp

open ConstCoeffOp

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The `k`-th coordinate direction of `ℝⁿ`. -/
abbrev coordDir {n : ℕ} (k : Fin n) : Fin n → ℝ := Pi.single k 1

/-! ## Gradient and divergence -/

/-- The row-wise gradient `𝕜^m → 𝕜^{m×n}` on `ℝⁿ`: `(grad φ)_{ij} = ∂ⱼ φᵢ`. -/
def gradOp (n m : ℕ) : ConstCoeffOp (Fin n → ℝ) 𝕜 (Fin m) (Fin m × Fin n) where
  coeff ij i := if i = ij.1 then [([coordDir ij.2], 1)] else []

/-- The row-wise divergence `𝕜^{m×n} → 𝕜^m` on `ℝⁿ`: `(div B)ᵢ = Σⱼ ∂ⱼ B_{ij}`. -/
def divOp (n m : ℕ) : ConstCoeffOp (Fin n → ℝ) 𝕜 (Fin m × Fin n) (Fin m) where
  coeff i ij := if ij.1 = i then [([coordDir ij.2], 1)] else []

variable {n m : ℕ}

theorem gradOp_apply (f : Fin m → (Fin n → ℝ) → 𝕜) (ij : Fin m × Fin n) (x : Fin n → ℝ) :
    (gradOp n m).apply f ij x = fderiv ℝ (f ij.1) x (coordDir ij.2) := by
  simp [ConstCoeffOp.apply, gradOp, applyEntry_ite, iterDeriv_singleton]

theorem divOp_apply (B : Fin m × Fin n → (Fin n → ℝ) → 𝕜) (i : Fin m) (x : Fin n → ℝ) :
    (divOp n m).apply B i x = ∑ j, fderiv ℝ (B (i, j)) x (coordDir j) := by
  simp only [ConstCoeffOp.apply, divOp, applyEntry_ite, applyEntry_singleton, one_mul,
    applyEntry_nil', Fintype.sum_prod_type, iterDeriv_singleton]
  simp

/-- `gradᵗ = -div`. -/
theorem gradOp_formalAdj_apply (B : Fin m × Fin n → (Fin n → ℝ) → 𝕜) (i : Fin m)
    (x : Fin n → ℝ) :
    (gradOp n m).formalAdj.apply B i x = -∑ j, fderiv ℝ (B (i, j)) x (coordDir j) := by
  simp only [ConstCoeffOp.apply, ConstCoeffOp.formalAdj, gradOp, adjEntry_ite, adjEntry_singleton,
    adjEntry_nil, applyEntry_ite, applyEntry_singleton, applyEntry_nil', Fintype.sum_prod_type,
    List.reverse_singleton, List.length_singleton, pow_one, map_one, mul_one,
    iterDeriv_singleton]
  simp [Finset.sum_neg_distrib]

/-- `divᵗ = -grad`. -/
theorem divOp_formalAdj_apply (f : Fin m → (Fin n → ℝ) → 𝕜) (ij : Fin m × Fin n)
    (x : Fin n → ℝ) :
    (divOp n m).formalAdj.apply f ij x = -fderiv ℝ (f ij.1) x (coordDir ij.2) := by
  simp [ConstCoeffOp.apply, ConstCoeffOp.formalAdj, divOp, adjEntry_ite, adjEntry_singleton,
    applyEntry_ite, iterDeriv_singleton]

/-! ## Row-wise curl on `ℝ³` -/

/-- The row-wise curl `𝕜^{m×3} → 𝕜^{m×3}` on `ℝ³`:
`(curl Φ)_{ik} = ∂_{k+1} Φ_{i,k+2} − ∂_{k+2} Φ_{i,k+1}` (indices mod 3). -/
def curlOp (m : ℕ) : ConstCoeffOp (Fin 3 → ℝ) 𝕜 (Fin m × Fin 3) (Fin m × Fin 3) where
  coeff ik jl := if jl.1 = ik.1 then
    (if jl.2 = ik.2 + 2 then [([coordDir (ik.2 + 1)], 1)]
      else if jl.2 = ik.2 + 1 then [([coordDir (ik.2 + 2)], -1)] else []) else []

theorem curlOp_apply (Φ : Fin m × Fin 3 → (Fin 3 → ℝ) → 𝕜) (ik : Fin m × Fin 3)
    (x : Fin 3 → ℝ) :
    (curlOp m).apply Φ ik x = fderiv ℝ (Φ (ik.1, ik.2 + 2)) x (coordDir (ik.2 + 1)) -
      fderiv ℝ (Φ (ik.1, ik.2 + 1)) x (coordDir (ik.2 + 2)) := by
  obtain ⟨i, k⟩ := ik
  simp only [ConstCoeffOp.apply, curlOp, applyEntry_ite, applyEntry_singleton, applyEntry_nil',
    Fintype.sum_prod_type, iterDeriv_singleton]
  simp only [Fin.sum_univ_three]
  fin_cases k <;> simp [Finset.sum_add_distrib] <;> ring

/-- The row-wise curl is formally self-adjoint. -/
theorem curlOp_formalAdj_apply (Φ : Fin m × Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    (curlOp m).formalAdj.apply Φ = (curlOp m).apply Φ := by
  funext ⟨i, k⟩ x
  rw [curlOp_apply]
  simp only [ConstCoeffOp.apply, ConstCoeffOp.formalAdj, curlOp, adjEntry_ite, adjEntry_singleton,
    adjEntry_nil, applyEntry_ite, applyEntry_singleton, applyEntry_nil', Fintype.sum_prod_type,
    List.reverse_singleton, List.length_singleton, iterDeriv_singleton]
  simp only [Fin.sum_univ_three]
  fin_cases k <;> simp [Finset.sum_add_distrib] <;> ring

/-! ## The Hessian -/

/-- The Hessian `𝕜 → 𝕜^{n×n}` (scalar fields indexed by `Unit`): `(∇² h)_{ij} = ∂ⱼ ∂ᵢ h`. -/
def hessOp (n : ℕ) : ConstCoeffOp (Fin n → ℝ) 𝕜 Unit (Fin n × Fin n) where
  coeff ij _ := [([coordDir ij.2, coordDir ij.1], 1)]

theorem hessOp_apply (h : Unit → (Fin n → ℝ) → 𝕜) (ij : Fin n × Fin n) (x : Fin n → ℝ) :
    (hessOp n).apply h ij x =
      fderiv ℝ (fun y => fderiv ℝ (h ()) y (coordDir ij.1)) x (coordDir ij.2) := by
  simp [ConstCoeffOp.apply, hessOp, iterDeriv_cons]

/-! ## Double divergence and the symmetric curl -/

/-- The double divergence `div div B = Σ_{ij} ∂_i ∂_j B_{ij}` (values indexed by `Unit`). -/
def divdivOp (n : ℕ) : ConstCoeffOp (Fin n → ℝ) 𝕜 (Fin n × Fin n) Unit where
  coeff _ ij := [([coordDir ij.1, coordDir ij.2], 1)]

theorem divdivOp_apply (B : Fin n × Fin n → (Fin n → ℝ) → 𝕜) (u : Unit) (x : Fin n → ℝ) :
    (divdivOp n).apply B u x =
      ∑ ij : Fin n × Fin n, fderiv ℝ (fun y => fderiv ℝ (B ij) y (coordDir ij.2)) x (coordDir ij.1) := by
  simp [ConstCoeffOp.apply, divdivOp, iterDeriv_cons]

/-- The symmetric part `sym M = (M + Mᵀ)/2` as a constant matrix on `𝕜^{n×n}`. -/
def symMat (n : ℕ) : Fin n × Fin n → Fin n × Fin n → 𝕜 := fun ij kl =>
  ((if kl = ij then 1 else 0) + (if kl = (ij.2, ij.1) then 1 else 0)) / 2

/-- The symmetric curl `sym curl` on `ℝ³` (row-wise). -/
def symCurlOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3) (Fin 3 × Fin 3) :=
  (curlOp 3).postComp (symMat 3)

theorem symCurlOp_apply (Φ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) (ij : Fin 3 × Fin 3)
    (x : Fin 3 → ℝ) :
    (symCurlOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply Φ ij x =
      ((curlOp 3).apply Φ ij x + (curlOp 3).apply Φ (ij.2, ij.1) x) / 2 := by
  rw [symCurlOp, postComp_apply]
  simp only [symMat, add_div, add_mul, Finset.sum_add_distrib, div_mul_eq_mul_div, ite_mul,
    one_mul, zero_mul, ite_div, zero_div, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-! ## Orders -/

theorem gradOp_isOrderLE : (gradOp n m : ConstCoeffOp (Fin n → ℝ) 𝕜 _ _).IsOrderLE 1 := by
  intro j i t ht
  simp only [gradOp] at ht
  split_ifs at ht <;> simp_all

theorem divOp_isOrderLE : (divOp n m : ConstCoeffOp (Fin n → ℝ) 𝕜 _ _).IsOrderLE 1 := by
  intro j i t ht
  simp only [divOp] at ht
  split_ifs at ht <;> simp_all

theorem curlOp_isOrderLE : (curlOp m : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).IsOrderLE 1 := by
  intro j i t ht
  simp only [curlOp] at ht
  split_ifs at ht <;> simp_all

theorem hessOp_isOrderLE : (hessOp n : ConstCoeffOp (Fin n → ℝ) 𝕜 _ _).IsOrderLE 2 := by
  intro j i t ht
  simp only [hessOp, List.mem_singleton] at ht
  subst ht
  simp

theorem divdivOp_isOrderLE : (divdivOp n : ConstCoeffOp (Fin n → ℝ) 𝕜 _ _).IsOrderLE 2 := by
  intro j i t ht
  simp only [divdivOp, List.mem_singleton] at ht
  subst ht
  simp

theorem symCurlOp_isOrderLE : (symCurlOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).IsOrderLE 1 :=
  curlOp_isOrderLE.postComp _

/-! ## Complex identities -/

/-- `curl ∘ grad = 0`. -/
theorem isComplexPair_grad_curl :
    (gradOp 3 m : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).IsComplexPair (curlOp m) := by
  intro f hf
  funext ⟨i, k⟩ x
  rw [curlOp_apply]
  have hg : ∀ ij, (gradOp 3 m).apply f ij = fun y => fderiv ℝ (f ij.1) y (coordDir ij.2) :=
    fun ij => funext fun y => gradOp_apply f ij y
  rw [hg, hg]
  simp only [Pi.zero_apply]
  rw [fderiv_fderiv_comm ((hf i).of_le (by simp)), sub_self]

/-- `div ∘ curl = 0` (row-wise). -/
theorem isComplexPair_curl_div :
    (curlOp m : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).IsComplexPair (divOp 3 m) := by
  intro f hf
  funext i x
  rw [divOp_apply]
  have hc : ∀ ik, (curlOp m).apply f ik = fun y =>
      fderiv ℝ (f (ik.1, ik.2 + 2)) y (coordDir (ik.2 + 1)) -
        fderiv ℝ (f (ik.1, ik.2 + 1)) y (coordDir (ik.2 + 2)) :=
    fun ik => funext fun y => curlOp_apply f ik y
  have hd : ∀ (a : Fin m × Fin 3) (v : Fin 3 → ℝ), Differentiable ℝ fun y => fderiv ℝ (f a) y v :=
    fun a v => (((hf a).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable
      (by simp)
  simp only [hc, Pi.zero_apply]
  simp only [Fin.sum_univ_three]
  rw [fderiv_fun_sub (hd _ _ _) (hd _ _ _), fderiv_fun_sub (hd _ _ _) (hd _ _ _),
    fderiv_fun_sub (hd _ _ _) (hd _ _ _)]
  simp only [sub_apply]
  simp only [Fin.isValue, Fin.reduceAdd]
  rw [fderiv_fderiv_comm ((hf (i, 2)).of_le (by simp)) (coordDir 1) (coordDir 0),
    fderiv_fderiv_comm ((hf (i, 0)).of_le (by simp)) (coordDir 2) (coordDir 1),
    fderiv_fderiv_comm ((hf (i, 1)).of_le (by simp)) (coordDir 0) (coordDir 2)]
  ring

/-- `curl ∘ hess = 0`. -/
theorem isComplexPair_hess_curl :
    (hessOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).IsComplexPair (curlOp 3) := by
  intro h hh
  funext ⟨i, k⟩ x
  rw [curlOp_apply]
  have he : ∀ ij, (hessOp 3).apply h ij = fun y =>
      fderiv ℝ (fun z => fderiv ℝ (h ()) z (coordDir ij.1)) y (coordDir ij.2) :=
    fun ij => funext fun y => hessOp_apply h ij y
  rw [he, he]
  simp only [Pi.zero_apply]
  have hs : ContDiff ℝ ∞ fun z => fderiv ℝ (h ()) z (coordDir i) :=
    ((hh ()).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  rw [fderiv_fderiv_comm (hs.of_le (by simp)), sub_self]

end Feec.Domain
