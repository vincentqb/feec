module

public import Feec.Domain.ConstrainedComplex
public import Feec.HilbertComplex.BGG.Derived

/-!
# BGG complexes of constant-coefficient operators

Two complexes of constant-coefficient operators `A, Ã` (`Feec.Domain.ConstCoeffComplex`) linked
by operators `S k : 𝕜^{ι̃ k} → 𝕜^{ι (k+1)}` with `A S = -S Ã` on smooth fields
(`Feec.Domain.ConstCoeffBGG`) are BGG data on the smooth fields (`ConstCoeffBGG.smoothData`), so
the algebraic BGG construction of `Feec.HilbertComplex.BGG.Derived` applies: for zeroth-order `S`
given by constant matrices (`ConstCoeffOp.ofMatrix`), left inverses make `S` injective and right
inverses surjective on smooth fields, which is how the injectivity/surjectivity condition
`Data.InjSurj J` is checked, and then the BGG complex `bgg J` has the cohomology of the twisted
complex (`Data.bggHomologyIso`).

The de Rham complex of `ℝ³` with values in `𝕜ᵐ` is `deRhamVec m`, in vector proxies
`𝕜ᵐ --grad--> 𝕜^{m×3} --curl--> 𝕜^{m×3} --div--> 𝕜ᵐ` (row-wise operators); stacked de Rham
diagrams of this kind give the Hessian, elasticity and div-div complexes
(`Feec.Domain.HessianBGG`, `Feec.Domain.ElasticityBGG`, `Feec.Domain.DivDivBGG`). A pointwise-constrained complex of constant-coefficient operators
(`Feec.Domain.ConstrainedComplex.ofMatrices`) has a smooth version
(`ConstCoeffComplex.smoothComplex`), the target of the identifications.

## Main definitions

* `Feec.Domain.smoothFields E 𝕜 ι`, `ConstCoeffOp.smoothMap`: smooth fields and the action of a
  constant-coefficient operator on them.
* `ConstCoeffOp.ofMatrix M`: the zeroth-order operator of a constant matrix.
* `Feec.Domain.ConstCoeffBGG`, `ConstCoeffBGG.smoothData`.
* `Feec.Domain.smoothFieldsIn E M`, `ConstCoeffComplex.smoothComplex`: smooth constrained
  complexes.
* `Feec.Domain.deRhamVec m`: the de Rham complex of `ℝ³` with values in `𝕜ᵐ`, vector proxies.

## Main results

* `ConstCoeffOp.smoothMap_ofMatrix_injective`, `ConstCoeffOp.smoothMap_ofMatrix_surjective`:
  matrices with left (right) inverses are injective (surjective) on smooth fields.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §4 (complexes from stacked
  de Rham complexes)
* [A. Čap, J. Slovák, V. Souček, *Bernstein–Gelfand–Gelfand sequences*][CapSlovakSoucek2001]
  (BGG sequences)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §11 (complexes from two de Rham complexes)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.1 (BGG data)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace Feec.Domain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type*} [RCLike 𝕜]

/-! ## Smooth fields -/

variable (E 𝕜) in
/-- The smooth `𝕜^ι`-valued fields on `E`. -/
def smoothFields (ι : Type*) : Submodule 𝕜 (ι → E → 𝕜) where
  carrier := {f | ∀ i, ContDiff ℝ ∞ (f i)}
  add_mem' hf hg i := (hf i).add (hg i)
  zero_mem' _ := contDiff_const
  smul_mem' _ _ hf i := contDiff_const.mul (hf i)

theorem subsingleton_smoothFields {ι : Type*} [IsEmpty ι] : Subsingleton (smoothFields E 𝕜 ι) :=
  ⟨fun _ _ => Subtype.ext (funext fun i => isEmptyElim i)⟩

namespace ConstCoeffOp

variable {ι κ μ : Type*} [Fintype ι]

/-- A constant-coefficient operator on smooth fields, as a linear map. -/
def smoothMap (A : ConstCoeffOp E 𝕜 ι κ) : smoothFields E 𝕜 ι →ₗ[𝕜] smoothFields E 𝕜 κ where
  toFun f := ⟨A.apply f, A.contDiff_apply f.2⟩
  map_add' f g := Subtype.ext (A.apply_add f.2 g.2)
  map_smul' c f := Subtype.ext (A.apply_smul c f.2)

@[simp] theorem coe_smoothMap (A : ConstCoeffOp E 𝕜 ι κ) (f : smoothFields E 𝕜 ι) :
    (A.smoothMap f : κ → E → 𝕜) = A.apply f := rfl

theorem apply_neg (A : ConstCoeffOp E 𝕜 ι κ) {f : ι → E → 𝕜} (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    A.apply (-f) = -A.apply f := by
  simpa using A.apply_smul (-1) hf

/-- The zeroth-order operator of a constant matrix, `(M f)ⱼ = Σᵢ M j i fᵢ`. -/
def ofMatrix (M : Matrix κ ι 𝕜) : ConstCoeffOp E 𝕜 ι κ where
  coeff j i := [([], M j i)]

theorem ofMatrix_apply (M : Matrix κ ι 𝕜) (f : ι → E → 𝕜) (j : κ) (x : E) :
    (ofMatrix M : ConstCoeffOp E 𝕜 ι κ).apply f j x = ∑ i, M j i * f i x := by
  simp [apply, ofMatrix, applyEntry]

theorem ofMatrix_apply_ofMatrix [Fintype κ] (N : Matrix μ κ 𝕜) (M : Matrix κ ι 𝕜)
    (f : ι → E → 𝕜) :
    (ofMatrix N : ConstCoeffOp E 𝕜 κ μ).apply ((ofMatrix M).apply f) =
      (ofMatrix (N * M)).apply f := by
  funext l x
  simp only [ofMatrix_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem ofMatrix_one_apply [DecidableEq ι] (f : ι → E → 𝕜) :
    (ofMatrix (1 : Matrix ι ι 𝕜) : ConstCoeffOp E 𝕜 ι ι).apply f = f := by
  funext i x
  simp [ofMatrix_apply, Matrix.one_apply]

/-- A matrix with a left inverse is injective on smooth fields. -/
theorem smoothMap_ofMatrix_injective [Fintype κ] [DecidableEq ι] {M : Matrix κ ι 𝕜}
    {N : Matrix ι κ 𝕜} (h : N * M = 1) :
    Function.Injective (ofMatrix M : ConstCoeffOp E 𝕜 ι κ).smoothMap := fun f g hfg => by
  have := congrArg (fun u : smoothFields E 𝕜 κ => (ofMatrix N : ConstCoeffOp E 𝕜 κ ι).apply u) hfg
  simp only [coe_smoothMap, ofMatrix_apply_ofMatrix, h, ofMatrix_one_apply] at this
  exact Subtype.ext this

/-- A matrix with a right inverse is surjective on smooth fields. -/
theorem smoothMap_ofMatrix_surjective [Fintype κ] [DecidableEq κ] {M : Matrix κ ι 𝕜}
    {N : Matrix ι κ 𝕜} (h : M * N = 1) :
    Function.Surjective (ofMatrix M : ConstCoeffOp E 𝕜 ι κ).smoothMap := fun g =>
  ⟨(ofMatrix N).smoothMap g, Subtype.ext (by
    simp only [coe_smoothMap, ofMatrix_apply_ofMatrix, h, ofMatrix_one_apply])⟩

end ConstCoeffOp

/-! ## Smooth constrained complexes -/

section Constrained

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

variable (E) in
/-- The smooth fields with values in the range of a constant matrix `M`: `M f = f`. -/
def smoothFieldsIn (M : ι → ι → 𝕜) : Submodule 𝕜 (ι → E → 𝕜) where
  carrier := {f | (∀ i, ContDiff ℝ ∞ (f i)) ∧ matMulField M f = f}
  add_mem' {f g} hf hg := ⟨fun i => (hf.1 i).add (hg.1 i), by
    conv_rhs => rw [← hf.2, ← hg.2]
    funext i x
    simp [matMulField, mul_add, Finset.sum_add_distrib]⟩
  zero_mem' := ⟨fun _ => contDiff_const, by funext i x; simp [matMulField]⟩
  smul_mem' c f hf := ⟨fun i => contDiff_const.mul (hf.1 i), by
    conv_rhs => rw [← hf.2]
    funext i x
    simp [matMulField, Finset.mul_sum, mul_left_comm]⟩

/-- Unconstrained smooth fields are the fields in the range of the identity. -/
def smoothFieldsEquivIdMat [DecidableEq ι] :
    smoothFields E 𝕜 ι ≃ₗ[𝕜] smoothFieldsIn E (idMat ι : _ → _ → 𝕜) where
  toFun f := ⟨f, f.2, matMulField_idMat _⟩
  invFun f := ⟨f, f.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Scalar fields indexed by `Fin 1` are scalar fields indexed by `Unit`. -/
def scalarFieldsEquiv : smoothFields E 𝕜 (Fin 1) ≃ₗ[𝕜] smoothFieldsIn E (idMat Unit : _ → _ → 𝕜) where
  toFun f := ⟨fun _ => (f : Fin 1 → E → 𝕜) 0, fun _ => f.2 0, matMulField_idMat _⟩
  invFun g := ⟨fun _ => (g : Unit → E → 𝕜) (), fun _ => g.2.1 ()⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := Subtype.ext (funext fun i => by rw [Subsingleton.elim i 0])
  right_inv _ := rfl

theorem ConstCoeffOp.ofMatrix_apply_eq_matMulField (M : ι → ι → 𝕜) (f : ι → E → 𝕜) :
    (ConstCoeffOp.ofMatrix M : ConstCoeffOp E 𝕜 ι ι).apply f = matMulField M f := by
  funext i x
  exact ConstCoeffOp.ofMatrix_apply (M := (M : Matrix ι ι 𝕜)) f i x

/-- A constant-coefficient operator mapping `M`-constrained to `N`-constrained smooth fields. -/
def ConstCoeffOp.smoothMapIn {A : ConstCoeffOp E 𝕜 ι κ} {M : ι → ι → 𝕜} {N : κ → κ → 𝕜}
    (hA : A.MatMapsTo M N) : smoothFieldsIn E M →ₗ[𝕜] smoothFieldsIn E N where
  toFun f := ⟨A.apply f, A.contDiff_apply f.2.1, by
    conv_rhs => rw [← f.2.2]
    conv_lhs => rw [← f.2.2]
    exact hA f f.2.1⟩
  map_add' f g := Subtype.ext (A.apply_add f.2.1 g.2.1)
  map_smul' c f := Subtype.ext (A.apply_smul c f.2.1)

@[simp] theorem ConstCoeffOp.coe_smoothMapIn {A : ConstCoeffOp E 𝕜 ι κ} {M : ι → ι → 𝕜}
    {N : κ → κ → 𝕜} (hA : A.MatMapsTo M N) (f : smoothFieldsIn E M) :
    (ConstCoeffOp.smoothMapIn hA f : κ → E → 𝕜) = A.apply f := rfl

/-- **The smooth constrained complex** of a complex of constant-coefficient operators with
pointwise constraints `M k` mapped to each other by the operators: the smooth version of
`Feec.Domain.ConstrainedComplex.ofMatrices`. -/
def ConstCoeffComplex.smoothComplex (C : ConstCoeffComplex E 𝕜) (M : ∀ k, C.ι k → C.ι k → 𝕜)
    (hM : ∀ k, (C.A k).MatMapsTo (M k) (M (k + 1))) : CochainComplex (ModuleCat 𝕜) ℤ :=
  CochainComplex.of (fun k => ModuleCat.of 𝕜 (smoothFieldsIn E (M k)))
    (fun k => ModuleCat.ofHom (ConstCoeffOp.smoothMapIn (hM k)))
    fun k => ModuleCat.hom_ext (LinearMap.ext fun f => Subtype.ext (C.comp k f f.2.1))

end Constrained

/-! ## BGG data of constant-coefficient operators -/

variable (E 𝕜) in
/-- **BGG data of constant-coefficient operators**: two complexes `A`, `Ã` on `ℤ` and connecting
operators `S k : 𝕜^{ι̃ k} → 𝕜^{ι (k+1)}` with `A (k+1) S k = -S (k+1) Ã k` on smooth fields. -/
structure ConstCoeffBGG where
  /-- the top complex -/
  top : ConstCoeffComplex E 𝕜
  /-- the bottom complex -/
  bot : ConstCoeffComplex E 𝕜
  /-- the connecting operators -/
  S : ∀ k, ConstCoeffOp E 𝕜 (bot.ι k) (top.ι (k + 1))
  anticomm : ∀ k (f : bot.ι k → E → 𝕜), (∀ i, ContDiff ℝ ∞ (f i)) →
    (top.A (k + 1)).apply ((S k).apply f) = -(S (k + 1)).apply ((bot.A k).apply f)

namespace ConstCoeffBGG

variable (B : ConstCoeffBGG E 𝕜)

/-- **The BGG data of smooth fields**: the two complexes and the connecting operators acting on
smooth fields. -/
def smoothData : BGG.Data 𝕜 (ComplexShape.up ℤ) (fun k => smoothFields E 𝕜 (B.top.ι k))
    (fun k => smoothFields E 𝕜 (B.bot.ι k)) :=
  BGG.Data.ofSucc (fun k => (B.top.A k).smoothMap) (fun k => (B.bot.A k).smoothMap)
    (fun k => (B.S k).smoothMap)
    (fun k f => Subtype.ext (B.top.comp k f f.2))
    (fun k f => Subtype.ext (B.bot.comp k f f.2))
    (fun k f => Subtype.ext (B.anticomm k f f.2))

@[simp] theorem smoothData_d (k : ℤ) : B.smoothData.d k (k + 1) = (B.top.A k).smoothMap :=
  BGG.Data.succMap_succ (X := fun k => smoothFields E 𝕜 (B.top.ι k))
    (Y := fun k => smoothFields E 𝕜 (B.top.ι k)) (fun k => (B.top.A k).smoothMap) k

@[simp] theorem smoothData_dt (k : ℤ) : B.smoothData.dt k (k + 1) = (B.bot.A k).smoothMap :=
  BGG.Data.succMap_succ (X := fun k => smoothFields E 𝕜 (B.bot.ι k))
    (Y := fun k => smoothFields E 𝕜 (B.bot.ι k)) (fun k => (B.bot.A k).smoothMap) k

@[simp] theorem smoothData_S (k : ℤ) : B.smoothData.S k (k + 1) = (B.S k).smoothMap :=
  BGG.Data.succMap_succ (X := fun k => smoothFields E 𝕜 (B.bot.ι k))
    (Y := fun k => smoothFields E 𝕜 (B.top.ι k)) (fun k => (B.S k).smoothMap) k

end ConstCoeffBGG

/-! ## The de Rham complex of `ℝ³` with values in `𝕜ᵐ` -/

/-- `u_{k+1,k+2} = u_{k+2,k+1}` for all `k` (`2 vskw u = 0`) iff `u` is symmetric. -/
theorem vskw_eq_zero_iff {α : Type*} [AddGroup α] {u : Fin 3 × Fin 3 → α} :
    (∀ k : Fin 3, u (k + 1, k + 2) - u (k + 2, k + 1) = 0) ↔ ∀ i j, u (i, j) = u (j, i) := by
  constructor
  · intro h i j
    have h0 := sub_eq_zero.1 (h 0)
    have h1 := sub_eq_zero.1 (h 1)
    have h2 := sub_eq_zero.1 (h 2)
    simp only [Fin.isValue, Fin.reduceAdd, zero_add] at h0 h1 h2
    fin_cases i <;> fin_cases j <;> simp_all
  · intro h k
    rw [h, sub_self]


/-- The component index types of the de Rham complex with values in `𝕜ᵐ` (vector proxies). -/
abbrev vecIdx (m : ℕ) : ℤ → Type
  | .ofNat 0 => Fin m
  | .ofNat 1 => Fin m × Fin 3
  | .ofNat 2 => Fin m × Fin 3
  | .ofNat 3 => Fin m
  | .ofNat (_ + 4) => Empty
  | .negSucc _ => Empty

instance instFintypeVecIdx (m : ℕ) : ∀ k, Fintype (vecIdx m k)
  | .ofNat 0 => inferInstanceAs (Fintype (Fin m))
  | .ofNat 1 => inferInstanceAs (Fintype (Fin m × Fin 3))
  | .ofNat 2 => inferInstanceAs (Fintype (Fin m × Fin 3))
  | .ofNat 3 => inferInstanceAs (Fintype (Fin m))
  | .ofNat (_ + 4) => inferInstanceAs (Fintype Empty)
  | .negSucc _ => inferInstanceAs (Fintype Empty)

instance instDecidableEqVecIdx (m : ℕ) : ∀ k, DecidableEq (vecIdx m k)
  | .ofNat 0 => inferInstanceAs (DecidableEq (Fin m))
  | .ofNat 1 => inferInstanceAs (DecidableEq (Fin m × Fin 3))
  | .ofNat 2 => inferInstanceAs (DecidableEq (Fin m × Fin 3))
  | .ofNat 3 => inferInstanceAs (DecidableEq (Fin m))
  | .ofNat (_ + 4) => inferInstanceAs (DecidableEq Empty)
  | .negSucc _ => inferInstanceAs (DecidableEq Empty)

theorem isEmpty_vecIdx (m : ℕ) {k : ℤ} (h : k < 0 ∨ 3 < k) : IsEmpty (vecIdx m k) := by
  match k with
  | .ofNat 0 | .ofNat 1 | .ofNat 2 | .ofNat 3 => exact absurd h (by decide)
  | .ofNat (_ + 4) => exact inferInstanceAs (IsEmpty Empty)
  | .negSucc _ => exact inferInstanceAs (IsEmpty Empty)

variable (𝕜) in
/-- The operators of the de Rham complex with values in `𝕜ᵐ`: row-wise `grad`, `curl`, `div`. -/
def vecOp (m : ℕ) : ∀ k : ℤ, ConstCoeffOp (Fin 3 → ℝ) 𝕜 (vecIdx m k) (vecIdx m (k + 1))
  | .ofNat 0 => gradOp 3 m
  | .ofNat 1 => curlOp m
  | .ofNat 2 => divOp 3 m
  | .ofNat (_ + 3) => ConstCoeffOp.zeroOp _ _
  | .negSucc _ => ConstCoeffOp.zeroOp _ _

/-- An operator out of a space of fields with empty index type, or into one, is zero. -/
theorem ConstCoeffOp.apply_eq_zero_of_isEmpty {ι κ : Type*} [Fintype ι]
    (A : ConstCoeffOp E 𝕜 ι κ) (f : ι → E → 𝕜) (h : IsEmpty ι ∨ IsEmpty κ) : A.apply f = 0 := by
  rcases h with h | h
  · exact A.apply_of_isEmpty f
  · exact funext fun j => isEmptyElim j

theorem vecOp_comp (m : ℕ) (k : ℤ) : (vecOp 𝕜 m k).IsComplexPair (vecOp 𝕜 m (k + 1)) := by
  intro f hf
  by_cases h0 : k = 0
  · subst h0; exact isComplexPair_grad_curl f hf
  by_cases h1 : k = 1
  · subst h1; exact isComplexPair_curl_div f hf
  rcases lt_or_gt_of_ne h0 with hk | hk
  · have := isEmpty_vecIdx m (k := k) (Or.inl hk)
    rw [ConstCoeffOp.apply_eq_zero_of_isEmpty _ f (Or.inl this)]
    exact (vecOp 𝕜 m (k + 1)).apply_zero
  · exact ConstCoeffOp.apply_eq_zero_of_isEmpty _ _ (Or.inr (isEmpty_vecIdx m (by omega)))

variable (𝕜) in
/-- **The de Rham complex of `ℝ³` with values in `𝕜ᵐ`**, in vector proxies:
`𝕜ᵐ --grad--> 𝕜^{m×3} --curl--> 𝕜^{m×3} --div--> 𝕜ᵐ` (row-wise). -/
abbrev deRhamVec (m : ℕ) : ConstCoeffComplex (Fin 3 → ℝ) 𝕜 where
  ι := vecIdx m
  A := vecOp 𝕜 m
  comp := vecOp_comp m

end Feec.Domain
