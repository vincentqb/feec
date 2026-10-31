module

public import Feec.Domain.BGG
public import Feec.Domain.HessianComplex

/-!
# The Hessian complex as a BGG complex

The de Rham complex of `ℝ³` (`deRhamVec 1`) stacked over the de Rham complex with values in
`𝕜³` (`deRhamVec 3`), linked by `S⁰ = I`, `S¹ = 2 vskw` (`(S¹ u)ₖ = u_{k+1,k+2} − u_{k+2,k+1}`,
the normalization `curl S⁰ = -S¹ grad` of [QuennevilleBelair2015], §5.1) and `S² = tr`, is BGG
data of constant-coefficient operators (`hessianBGG`). `S⁰, S¹, S²` are onto, so the
injectivity/surjectivity condition holds at `J = 0` with the explicit right inverses `hessianT`
(**`injSurjWith_hessianBGG`**, `injSurj_hessianBGG`): a de Rham instance of
`Feec.BGG.Data.InjSurjWith` (the first two rows of [ArnoldHu2021], (32)). Its BGG complex `bgg 0`
eliminates `V¹, V², V³` against `S⁰, S¹, S²`, and **is the Hessian complex**
`𝕜 --grad grad--> Sym --curl--> T --div--> 𝕜³` of `Feec.Domain.HessianComplex` on smooth fields
(**`hessianBGGIso`**): in degree `0` the pairs `(σ, grad σ)` (`S⁰` is bijective), with
`(σ, grad σ) ↦ (0, grad grad σ)`; after `0` the fields `0 × N(Sᵏ)`, symmetric in degree `1`
(`N(2 vskw)`), trace-free in degree `2` (`N(tr)`), with the differentials of the bottom row.
Hence the smooth Hessian complex has the cohomology of the twisted de Rham complex
(`hessianSmoothComplexHomologyIso`).

## Main definitions

* `Feec.Domain.hessianBGG`: the BGG diagram of the Hessian complex.
* `Feec.Domain.hessianSmoothComplex`: the smooth Hessian complex (`hessianOp`, `hessianMat`).

## Main results

* **`injSurjWith_hessianBGG`**, `injSurj_hessianBGG`, `hessianBGGHomologyIso`.
* **`hessianBGGIso`**, `hessianSmoothComplexHomologyIso`.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §4.1 ((32), the Hessian complex
  from the first two rows, `J = 0`)
* [A. Čap, J. Slovák, V. Souček, *Bernstein–Gelfand–Gelfand sequences*][CapSlovakSoucek2001]
  (BGG sequences)
* [D. Pauly, W. Zulehner, *The divDiv-complex and applications to biharmonic equations*][PaulyZulehner2020]
  (the Hessian complex)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.1 (the connecting maps `S₀ = I`, `S₁ = 2 vskw`)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped ContDiff
open CategoryTheory

@[expose] public noncomputable section

namespace Feec.Domain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type*} [RCLike 𝕜]

section Hessian

open ConstCoeffOp Matrix

/-- `S⁰ = I : 𝕜³ → 𝕜^{1×3}`. -/
def hessS0 : Matrix (Fin 1 × Fin 3) (Fin 3) 𝕜 := fun a j => if j = a.2 then 1 else 0

/-- `S¹ = 2 vskw : 𝕜^{3×3} → 𝕜^{1×3}`, `(S¹ u)ₖ = u_{k+1,k+2} − u_{k+2,k+1}`. -/
def hessS1 : Matrix (Fin 1 × Fin 3) (Fin 3 × Fin 3) 𝕜 := fun a ij =>
  if ij = (a.2 + 1, a.2 + 2) then 1 else if ij = (a.2 + 2, a.2 + 1) then -1 else 0

/-- `S² = tr : 𝕜^{3×3} → 𝕜^{1}`. -/
def hessS2 : Matrix (Fin 1) (Fin 3 × Fin 3) 𝕜 := fun _ ij => if ij.1 = ij.2 then 1 else 0

variable (𝕜) in
/-- The connecting operators of the Hessian diagram: `I`, `2 vskw`, `tr`. -/
def hessianS : ∀ k : ℤ, ConstCoeffOp (Fin 3 → ℝ) 𝕜 (vecIdx 3 k) (vecIdx 1 (k + 1))
  | .ofNat 0 => ofMatrix hessS0
  | .ofNat 1 => ofMatrix hessS1
  | .ofNat 2 => ofMatrix hessS2
  | .ofNat (_ + 3) => zeroOp _ _
  | .negSucc _ => zeroOp _ _

theorem ofMatrix_hessS0_apply (f : Fin 3 → (Fin 3 → ℝ) → 𝕜) (a : Fin 1 × Fin 3) :
    (ofMatrix hessS0 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f a = f a.2 := by
  funext x; simp [ofMatrix_apply, hessS0]

theorem ofMatrix_hessS1_apply (f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) (a : Fin 1 × Fin 3) :
    (ofMatrix hessS1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f a =
      f (a.2 + 1, a.2 + 2) - f (a.2 + 2, a.2 + 1) := by
  funext x
  obtain ⟨i, k⟩ := a
  simp only [ofMatrix_apply, hessS1, Fintype.sum_prod_type, Fin.sum_univ_three, Pi.sub_apply]
  fin_cases k <;> simp <;> ring

theorem ofMatrix_hessS2_apply (f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) (a : Fin 1) :
    (ofMatrix hessS2 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f a = ∑ i, f (i, i) := by
  funext x
  simp only [ofMatrix_apply, hessS2, Fintype.sum_prod_type, Fin.sum_univ_three,
    Finset.sum_apply]
  simp

/-- `curl S⁰ = -S¹ grad`. -/
theorem curlOp_hessS0 (f : Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    (curlOp 1).apply ((ofMatrix hessS0).apply f) =
      -(ofMatrix hessS1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply ((gradOp 3 3).apply f) := by
  funext ⟨i, k⟩ x
  rw [curlOp_apply, Pi.neg_apply, Pi.neg_apply, ofMatrix_hessS1_apply, ofMatrix_hessS0_apply,
    ofMatrix_hessS0_apply]
  simp only [Pi.sub_apply, gradOp_apply]
  ring

/-- `div S¹ = -S² curl`. -/
theorem divOp_hessS1 {f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜} (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (divOp 3 1).apply ((ofMatrix hessS1).apply f) =
      -(ofMatrix hessS2 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply ((curlOp 3).apply f) := by
  funext i x
  have hd : ∀ a : Fin 3 × Fin 3, DifferentiableAt ℝ (f a) x :=
    fun a => ((hf a).differentiable (by simp)).differentiableAt
  rw [divOp_apply, Pi.neg_apply, Pi.neg_apply, ofMatrix_hessS2_apply]
  simp only [ofMatrix_hessS1_apply, Finset.sum_apply, curlOp_apply,
    fderiv_sub (hd _) (hd _), _root_.sub_apply, Fin.sum_univ_three]
  simp only [Fin.isValue, Fin.reduceAdd]
  ring

theorem hessianS_anticomm (k : ℤ) (f : vecIdx 3 k → (Fin 3 → ℝ) → 𝕜)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (vecOp 𝕜 1 (k + 1)).apply ((hessianS 𝕜 k).apply f) =
      -(hessianS 𝕜 (k + 1)).apply ((vecOp 𝕜 3 k).apply f) := by
  by_cases h0 : k = 0
  · subst h0; exact curlOp_hessS0 f
  by_cases h1 : k = 1
  · subst h1; exact divOp_hessS1 hf
  rcases lt_or_gt_of_ne h0 with hk | hk
  · have := isEmpty_vecIdx 3 (k := k) (Or.inl hk)
    rw [ConstCoeffOp.apply_eq_zero_of_isEmpty _ f (Or.inl this),
      ConstCoeffOp.apply_eq_zero_of_isEmpty _ f (Or.inl this), apply_zero, apply_zero, neg_zero]
  · have := isEmpty_vecIdx 1 (k := k + 1 + 1) (Or.inr (by omega))
    exact funext fun j => isEmptyElim j

variable (𝕜) in
/-- **The BGG diagram of the Hessian complex**: the de Rham complex `𝕜 → 𝕜³ → 𝕜³ → 𝕜` over the
de Rham complex with values in `𝕜³`, linked by `I`, `2 vskw`, `tr`. [ArnoldHu2021], (32) -/
abbrev hessianBGG : ConstCoeffBGG (Fin 3 → ℝ) 𝕜 where
  top := deRhamVec 𝕜 1
  bot := deRhamVec 𝕜 3
  S := hessianS 𝕜
  anticomm := hessianS_anticomm

/-- A right inverse of `S⁰`. -/
def hessN0 : Matrix (Fin 3) (Fin 1 × Fin 3) 𝕜 := fun j a => if j = a.2 then 1 else 0

/-- A right inverse of `S¹`: `v ↦ u` with `u_{k+1,k+2} = vₖ` and the other entries `0`. -/
def hessN1 : Matrix (Fin 3 × Fin 3) (Fin 1 × Fin 3) 𝕜 := fun ij a =>
  if ij = (a.2 + 1, a.2 + 2) then 1 else 0

/-- A right inverse of `S²`: `t ↦ t e₀ ⊗ e₀`. -/
def hessN2 : Matrix (Fin 3 × Fin 3) (Fin 1) 𝕜 := fun ij _ => if ij = (0, 0) then 1 else 0

theorem hessS0_mul_hessN0 : hessS0 * hessN0 = (1 : Matrix _ _ 𝕜) := by
  ext ⟨i, k⟩ ⟨i', k'⟩
  fin_cases i; fin_cases i'
  fin_cases k <;> fin_cases k' <;>
    simp [Matrix.mul_apply, hessS0, hessN0]

theorem hessS1_mul_hessN1 : hessS1 * hessN1 = (1 : Matrix _ _ 𝕜) := by
  ext ⟨i, k⟩ ⟨i', k'⟩
  fin_cases i; fin_cases i'
  fin_cases k <;> fin_cases k' <;>
    simp [Matrix.mul_apply, hessS1, hessN1]

theorem hessS2_mul_hessN2 : hessS2 * hessN2 = (1 : Matrix _ _ 𝕜) := by
  ext i i'
  fin_cases i; fin_cases i'
  simp [Matrix.mul_apply, hessS2, hessN2]

theorem hessN0_mul_hessS0 : hessN0 * hessS0 = (1 : Matrix (Fin 3) (Fin 3) 𝕜) := by
  ext j j'
  fin_cases j <;> fin_cases j' <;>
    simp [Matrix.mul_apply, hessS0, hessN0, Fintype.sum_prod_type]

variable (𝕜) in
/-- The right inverses `hessN0`, `hessN1`, `hessN2` of `I`, `2 vskw`, `tr` on smooth fields. -/
def hessianT : ∀ k : ℤ, smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx 1 (k + 1)) →ₗ[𝕜]
    smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx 3 k)
  | .ofNat 0 => (ofMatrix hessN0).smoothMap
  | .ofNat 1 => (ofMatrix hessN1).smoothMap
  | .ofNat 2 => (ofMatrix hessN2).smoothMap
  | .ofNat (_ + 3) => 0
  | .negSucc _ => 0

/-- **The Hessian diagram satisfies the injectivity/surjectivity condition at `J = 0` with the
right inverses `hessianT`**: `I`, `2 vskw` and `tr` are onto, with right inverses `hessN0`,
`hessN1`, `hessN2`. The first de Rham instance of `Data.InjSurjWith` ([ArnoldHu2021], (23),
(32)). -/
theorem injSurjWith_hessianBGG :
    (hessianBGG 𝕜).smoothData.InjSurjWith 0 ((hessianBGG 𝕜).predMap (hessianT 𝕜)) := by
  refine ConstCoeffBGG.injSurjWith_predMap _ (fun k hk => ?_) fun k hk v => ?_
  · by_cases h0 : k = 0
    · subst h0; exact smoothMap_ofMatrix_injective (hessN0_mul_hessS0 (𝕜 := 𝕜))
    have := isEmpty_vecIdx 3 (k := k) (Or.inl (by omega))
    exact fun a b _ => (subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜)).elim a b
  · refine Subtype.ext ?_
    match k, hk with
    | .ofNat 0, _ =>
      change (ofMatrix hessS0 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
        ((ofMatrix hessN0).apply v.1) = v.1
      rw [ofMatrix_apply_ofMatrix, hessS0_mul_hessN0, ofMatrix_one_apply]
    | .ofNat 1, _ =>
      change (ofMatrix hessS1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
        ((ofMatrix hessN1).apply v.1) = v.1
      rw [ofMatrix_apply_ofMatrix, hessS1_mul_hessN1, ofMatrix_one_apply]
    | .ofNat 2, _ =>
      change (ofMatrix hessS2 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
        ((ofMatrix hessN2).apply v.1) = v.1
      rw [ofMatrix_apply_ofMatrix, hessS2_mul_hessN2, ofMatrix_one_apply]
    | .ofNat (n + 3), _ =>
      have := isEmpty_vecIdx 1 (k := .ofNat (n + 3) + 1)
        (Or.inr (by simp only [Int.ofNat_eq_natCast]; omega))
      exact funext fun i => isEmptyElim i

/-- **The Hessian diagram satisfies the injectivity/surjectivity condition at `J = 0`**
(`injSurjWith_hessianBGG`): `I`, `2 vskw` and `tr` are onto. [ArnoldHu2021], (23), (32) -/
theorem injSurj_hessianBGG : (hessianBGG 𝕜).smoothData.InjSurj 0 :=
  injSurjWith_hessianBGG.injSurj

/-- **The Hessian BGG complex has the cohomology of the twisted de Rham complex.**
[ArnoldHu2021], §5.2 -/
def hessianBGGHomologyIso (i : ℤ) :
    ((hessianBGG 𝕜).smoothData.bgg 0).homology i ≅
      (hessianBGG 𝕜).smoothData.twistComplex.homology i :=
  BGG.Data.bggHomologyIso injSurj_hessianBGG i

/-! ### The BGG complex is the smooth Hessian complex -/

theorem bijective_hessianBGG_S_zero :
    Function.Bijective ((hessianBGG 𝕜).smoothData.S 0 (0 + 1)) :=
  injSurjWith_hessianBGG.bijective

/-- The BGG complex of the Hessian diagram has no exact part: `Δⁱ = 0`. -/
theorem hessianBGG_Δ_eq_bot (i : ℤ) : (hessianBGG 𝕜).smoothData.Δ (· < 0) i = ⊥ := by
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · have := isEmpty_vecIdx 1 (k := i) (Or.inl hi)
    have := isEmpty_vecIdx 3 (k := i) (Or.inl hi)
    have h1 := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 1 i)
    have h3 := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 3 i)
    exact eq_bot_iff.2 fun x _ => (Submodule.mem_bot 𝕜).2 (Prod.ext (h1.elim _ _) (h3.elim _ _))
  · refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨φ, ψ, hφ, rfl⟩ := ((hessianBGG 𝕜).smoothData.mem_bgg_Δ_of_le le_rfl).1 hx
    have := isEmpty_vecIdx 3 (k := 0 - 1) (Or.inl (by omega))
    have hs := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 3 (0 - 1))
    obtain rfl : φ = 0 := hφ.resolve_left (lt_irrefl 0)
    obtain rfl : ψ = 0 := hs.elim _ _
    simp
  · exact (hessianBGG 𝕜).smoothData.bgg_Δ_of_gt hi

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `S¹ u = 0` iff `u` is symmetric. -/
theorem hessS1_apply_eq_zero_iff {u : Fin 3 × Fin 3 → E → 𝕜} :
    (∀ a : Fin 1 × Fin 3, u (a.2 + 1, a.2 + 2) - u (a.2 + 2, a.2 + 1) = 0) ↔
      ∀ i j, u (i, j) = u (j, i) :=
  ⟨fun h => vskw_eq_zero_iff.1 fun k => h (0, k), fun h a => vskw_eq_zero_iff.2 h a.2⟩

/-- The kernel of `S¹` is the symmetric constraint of the Hessian complex. -/
def kerHessS1Equiv : LinearMap.ker ((hessianBGG 𝕜).smoothData.S 1 (1 + 1)) ≃ₗ[𝕜]
    smoothFieldsIn (Fin 3 → ℝ) (symMat 3 : _ → _ → 𝕜) where
  toFun u := ⟨((u : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3)) : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜),
    fun i => (u : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3)).2 i,
    matMulField_symMat_of_symm (hessS1_apply_eq_zero_iff.1 fun a => by
      have h := congrArg (fun v : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 1 × Fin 3) =>
        (v : Fin 1 × Fin 3 → (Fin 3 → ℝ) → 𝕜) a) (LinearMap.mem_ker.1 u.2)
      change (ofMatrix hessS1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
        ((u : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3)) : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) a =
          0 at h
      rwa [ofMatrix_hessS1_apply] at h)⟩
  invFun f := ⟨⟨(f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜), f.2.1⟩, LinearMap.mem_ker.2 (by
    refine Subtype.ext (funext fun a => ?_)
    change (ofMatrix hessS1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      (f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) a = 0
    rw [ofMatrix_hessS1_apply]
    refine (hessS1_apply_eq_zero_iff.2 fun i j => ?_) a
    rw [← f.2.2]
    exact matMulField_symMat_symm _ i j)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A field in the range of `dev` is trace-free. -/
theorem trace_eq_zero_of_matMulField_deviatoricMat {u : Fin 3 × Fin 3 → E → 𝕜}
    (h : matMulField (deviatoricMat 3) u = u) (x : E) : ∑ k, u (k, k) x = 0 := by
  rw [← h]
  simp only [matMulField_deviatoricMat]
  exact sum_diag_sub_trace (𝕜 := 𝕜) (n := 3) fun kl => u kl x

/-- The kernel of `S² = tr` is the trace-free constraint of the Hessian complex. -/
def kerHessS2Equiv : LinearMap.ker ((hessianBGG 𝕜).smoothData.S 2 (2 + 1)) ≃ₗ[𝕜]
    smoothFieldsIn (Fin 3 → ℝ) (deviatoricMat 3 : _ → _ → 𝕜) where
  toFun u := ⟨((u : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3)) : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜),
    fun i => (u : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3)).2 i,
    matMulField_deviatoricMat_of_trace fun x => by
      have h := congrArg (fun v : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 1) =>
        (v : Fin 1 → (Fin 3 → ℝ) → 𝕜) 0 x) (LinearMap.mem_ker.1 u.2)
      change (ofMatrix hessS2 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
        ((u : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3)) : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) 0 x =
          0 at h
      rwa [ofMatrix_hessS2_apply, Finset.sum_apply] at h⟩
  invFun f := ⟨⟨(f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜), f.2.1⟩, LinearMap.mem_ker.2 (by
    refine Subtype.ext (funext fun a => funext fun x => ?_)
    change (ofMatrix hessS2 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      (f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) a x = 0
    rw [ofMatrix_hessS2_apply, Finset.sum_apply]
    exact trace_eq_zero_of_matMulField_deviatoricMat f.2.2 x)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The kernel of `S³ = 0` is all of `Ṽ³`. -/
def kerHessS3Equiv : LinearMap.ker ((hessianBGG 𝕜).smoothData.S 3 (3 + 1)) ≃ₗ[𝕜]
    smoothFieldsIn (Fin 3 → ℝ) (idMat (Fin 3) : _ → _ → 𝕜) where
  toFun u := ⟨((u : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3)) : Fin 3 → (Fin 3 → ℝ) → 𝕜),
    fun i => (u : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3)).2 i, matMulField_idMat _⟩
  invFun f := ⟨⟨(f : Fin 3 → (Fin 3 → ℝ) → 𝕜), f.2.1⟩, LinearMap.mem_ker.2
    (Subtype.ext (funext fun j => isEmptyElim (α := Empty) j))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- In degree `0`, `grad φ = grad grad σ` when `grad σ = S⁰ φ`. -/
theorem gradOp_eq_hessOp {σ : Fin 1 → (Fin 3 → ℝ) → 𝕜} {φ : Fin 3 → (Fin 3 → ℝ) → 𝕜}
    (h : (gradOp 3 1).apply σ = (ofMatrix hessS0).apply φ) :
    (gradOp 3 3).apply φ = (hessOp 3).apply fun _ => σ 0 := by
  have hφ : ∀ i, φ i = fun y => fderiv ℝ (σ 0) y (coordDir i) := fun i => by
    have := congrFun h (0, i)
    rw [ofMatrix_hessS0_apply] at this
    rw [← this]
    funext y
    rw [gradOp_apply]
  funext ⟨i, j⟩ x
  rw [gradOp_apply, hessOp_apply, hφ]

variable (𝕜) in
/-- The smooth Hessian complex `𝕜 --grad grad--> Sym --curl--> T --div--> 𝕜³` of
`Feec.Domain.HessianComplex`. -/
abbrev hessianSmoothComplex : CochainComplex (ModuleCat 𝕜) ℤ :=
  (hessianConstCoeffComplex 𝕜).smoothComplex (hessianMat 𝕜) hessianOp_matMapsTo

theorem subsingleton_hessianBGG_Γ {k : ℤ} (hk : k < 0 ∨ 3 < k) :
    Subsingleton ((hessianBGG 𝕜).smoothData.Γ (0 < ·) k) := by
  have := isEmpty_vecIdx 1 hk
  have := isEmpty_vecIdx 3 hk
  have h1 := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 1 k)
  have h3 := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 3 k)
  exact ⟨fun a b => Subtype.ext (Prod.ext (h1.elim _ _) (h3.elim _ _))⟩

theorem subsingleton_hessianSmoothComplex_X {k : ℤ} (hk : k < 0 ∨ 3 < k) :
    Subsingleton (smoothFieldsIn (Fin 3 → ℝ) (hessianMat 𝕜 k)) := by
  have : IsEmpty (hessianIdx k) := isEmpty_hessianIdx (by omega) (by omega) (by omega) (by omega)
  exact ⟨fun a b => Subtype.ext (funext fun i => isEmptyElim i)⟩

/-- The components of the identification of the BGG complex with the Hessian complex. -/
def hessianBGGEquiv : ∀ k : ℤ, ((hessianBGG 𝕜).smoothData.bgg 0).X k ≃ₗ[𝕜]
    (hessianSmoothComplex 𝕜).X k
  | .ofNat 0 => ((hessianBGG 𝕜).smoothData.derivedXEquiv (0 < ·) (· < 0)
      (hessianBGG_Δ_eq_bot 0)).trans
      (((hessianBGG 𝕜).smoothData.bggΓEquivOfBijective bijective_hessianBGG_S_zero).trans
        scalarFieldsEquiv)
  | .ofNat 1 => ((hessianBGG 𝕜).smoothData.derivedXEquiv (0 < ·) (· < 0)
      (hessianBGG_Δ_eq_bot 1)).trans
      (((hessianBGG 𝕜).smoothData.bggΓEquivKer (J := 0) (i := 1) one_pos).trans kerHessS1Equiv)
  | .ofNat 2 => ((hessianBGG 𝕜).smoothData.derivedXEquiv (0 < ·) (· < 0)
      (hessianBGG_Δ_eq_bot 2)).trans
      (((hessianBGG 𝕜).smoothData.bggΓEquivKer (J := 0) (i := 2) two_pos).trans kerHessS2Equiv)
  | .ofNat 3 => ((hessianBGG 𝕜).smoothData.derivedXEquiv (0 < ·) (· < 0)
      (hessianBGG_Δ_eq_bot 3)).trans
      (((hessianBGG 𝕜).smoothData.bggΓEquivKer (J := 0) (i := 3) three_pos).trans kerHessS3Equiv)
  | .ofNat (n + 4) =>
      have := subsingleton_hessianBGG_Γ (𝕜 := 𝕜) (k := .ofNat (n + 4))
        (Or.inr (by rw [Int.ofNat_eq_natCast]; omega))
      have : Subsingleton ((hessianSmoothComplex 𝕜).X (.ofNat (n + 4))) :=
        subsingleton_hessianSmoothComplex_X (𝕜 := 𝕜) (k := .ofNat (n + 4))
        (Or.inr (by rw [Int.ofNat_eq_natCast]; omega))
      ((hessianBGG 𝕜).smoothData.derivedXEquiv (0 < ·) (· < 0)
        (hessianBGG_Δ_eq_bot (.ofNat (n + 4)))).trans (LinearEquiv.ofSubsingleton _ _)
  | .negSucc n =>
      have := subsingleton_hessianBGG_Γ (𝕜 := 𝕜) (k := .negSucc n)
        (Or.inl (Int.negSucc_lt_zero n))
      have : Subsingleton ((hessianSmoothComplex 𝕜).X (.negSucc n)) :=
        subsingleton_hessianSmoothComplex_X (𝕜 := 𝕜) (k := .negSucc n)
        (Or.inl (Int.negSucc_lt_zero n))
      ((hessianBGG 𝕜).smoothData.derivedXEquiv (0 < ·) (· < 0)
        (hessianBGG_Δ_eq_bot (.negSucc n))).trans (LinearEquiv.ofSubsingleton _ _)

theorem hessianBGGEquiv_comm_zero :
    (hessianBGGEquiv 0).toModuleIso.hom ≫ (hessianSmoothComplex 𝕜).d 0 (0 + 1) =
      ((hessianBGG 𝕜).smoothData.bgg 0).d 0 (0 + 1) ≫
        (hessianBGGEquiv (0 + 1)).toModuleIso.hom := by
  refine ModuleCat.hom_ext (LinearMap.ext fun q => ?_)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨⟨σ, φ⟩, hx⟩ := (x : (hessianBGG 𝕜).smoothData.Γ (0 < ·) 0)
  apply Subtype.ext
  change (hessOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      (fun _ => (σ : Fin 1 → (Fin 3 → ℝ) → 𝕜) 0) =
    (gradOp 3 3).apply (φ : Fin 3 → (Fin 3 → ℝ) → 𝕜)
  have h := congrArg Subtype.val ((hessianBGG 𝕜).smoothData.mem_bgg_Γ_self.1 hx)
  change (gradOp 3 1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply (σ : Fin 1 → (Fin 3 → ℝ) → 𝕜) =
    (ofMatrix hessS0).apply (φ : Fin 3 → (Fin 3 → ℝ) → 𝕜) at h
  exact (gradOp_eq_hessOp h).symm

theorem hessianBGGEquiv_comm_one :
    (hessianBGGEquiv 1).toModuleIso.hom ≫ (hessianSmoothComplex 𝕜).d 1 (1 + 1) =
      ((hessianBGG 𝕜).smoothData.bgg 0).d 1 (1 + 1) ≫
        (hessianBGGEquiv (1 + 1)).toModuleIso.hom := by
  refine ModuleCat.hom_ext (LinearMap.ext fun q => ?_)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨⟨σ, u⟩, hx⟩ := (x : (hessianBGG 𝕜).smoothData.Γ (0 < ·) 1)
  apply Subtype.ext
  change (curlSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      (u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) =
    (curlOp 3).apply (u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜)
  have h := congrArg Subtype.val (((hessianBGG 𝕜).smoothData.mem_bgg_Γ_of_gt one_pos).1 hx).2
  change (ofMatrix hessS1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
    (u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) = 0 at h
  rw [curlSymOp_apply u.2, matMulField_symMat_of_symm (hessS1_apply_eq_zero_iff.1 fun a => by
    rw [← ofMatrix_hessS1_apply, h]; rfl)]

theorem hessianBGGEquiv_comm_two :
    (hessianBGGEquiv 2).toModuleIso.hom ≫ (hessianSmoothComplex 𝕜).d 2 (2 + 1) =
      ((hessianBGG 𝕜).smoothData.bgg 0).d 2 (2 + 1) ≫
        (hessianBGGEquiv (2 + 1)).toModuleIso.hom := by
  refine ModuleCat.hom_ext (LinearMap.ext fun q => ?_)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨⟨σ, u⟩, hx⟩ := (x : (hessianBGG 𝕜).smoothData.Γ (0 < ·) 2)
  apply Subtype.ext
  change (divDevOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      (u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) =
    (divOp 3 3).apply (u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜)
  have h := congrArg Subtype.val (((hessianBGG 𝕜).smoothData.mem_bgg_Γ_of_gt two_pos).1 hx).2
  change (ofMatrix hessS2 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
    (u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) = 0 at h
  rw [divDevOp_apply u.2, matMulField_deviatoricMat_of_trace fun x => by
    have := congrFun (congrFun h 0) x
    rwa [ofMatrix_hessS2_apply, Finset.sum_apply] at this]

theorem subsingleton_hessianBGG_bgg_X {k : ℤ} (hk : k < 0 ∨ 3 < k) :
    Subsingleton (((hessianBGG 𝕜).smoothData.bgg 0).X k) :=
  have : Subsingleton ((hessianSmoothComplex 𝕜).X k) := subsingleton_hessianSmoothComplex_X hk
  (hessianBGGEquiv k).injective.subsingleton

theorem hessianBGGEquiv_comm (i : ℤ) :
    (hessianBGGEquiv i).toModuleIso.hom ≫ (hessianSmoothComplex 𝕜).d i (i + 1) =
      ((hessianBGG 𝕜).smoothData.bgg 0).d i (i + 1) ≫
        (hessianBGGEquiv (i + 1)).toModuleIso.hom := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i < 0 ∨ 2 < i) with rfl | rfl | rfl | hi | hi
  · exact hessianBGGEquiv_comm_zero
  · exact hessianBGGEquiv_comm_one
  · exact hessianBGGEquiv_comm_two
  · have := subsingleton_hessianBGG_bgg_X (𝕜 := 𝕜) (Or.inl hi)
    exact ModuleCat.hom_ext (LinearMap.ext fun q => by
      rw [Subsingleton.elim q 0, map_zero, map_zero])
  · have : Subsingleton ((hessianSmoothComplex 𝕜).X (i + 1)) :=
      subsingleton_hessianSmoothComplex_X (Or.inr (by omega))
    exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

/-- **The BGG complex of the Hessian diagram is the Hessian complex**: `bgg 0` of
`hessianBGG` is isomorphic to the smooth Hessian complex `grad grad → curl → div` on symmetric and
trace-free fields of `Feec.Domain.HessianComplex` (`hessianOp`, `hessianMat`).
[ArnoldHu2021], §4.1 -/
def hessianBGGIso : (hessianBGG 𝕜).smoothData.bgg 0 ≅ hessianSmoothComplex 𝕜 :=
  HomologicalComplex.Hom.isoOfComponents (fun k => (hessianBGGEquiv k).toModuleIso)
    fun i j hij => by
      obtain rfl : i + 1 = j := hij
      exact hessianBGGEquiv_comm i

/-- **The cohomology of the smooth Hessian complex is that of the twisted de Rham complex**
of the Hessian diagram. [ArnoldHu2021], §5.2 -/
def hessianSmoothComplexHomologyIso (i : ℤ) :
    (hessianSmoothComplex 𝕜).homology i ≅
      (hessianBGG 𝕜).smoothData.twistComplex.homology i :=
  ((HomologicalComplex.homologyFunctor _ _ i).mapIso hessianBGGIso).symm ≪≫
    hessianBGGHomologyIso i

end Hessian

end Feec.Domain
