module

public import Feec.Domain.ConstrainedComplex

/-!
# The Hessian complex on an open set of `ℝ³`

The Hessian complex `𝕜 --grad grad--> Sym --curl--> T --div--> 𝕜³`, with row-wise `curl` and `div`,
is a complex of constrained realizations on every open `Ω ⊆ ℝ³`; the formal adjoints of its
operators are `div div`, `sym curl` and `-dev grad`.
-/

open scoped InnerProductSpace ContDiff ComplexConjugate LinearPMap
open MeasureTheory Set

@[expose] public noncomputable section

namespace Feec.Domain

open ConstCoeffOp

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## The operators -/

/-- The row-wise curl of symmetric fields, `curl ∘ sym` (equal to `curl` on `Sym`). -/
def curlSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3) (Fin 3 × Fin 3) :=
  (curlOp 3).preComp (symMat 3)

/-- The row-wise divergence of trace-free fields, `div ∘ dev` (equal to `div` on `T`). -/
def divDevOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3) (Fin 3) :=
  (divOp 3 3).preComp (deviatoricMat 3)

/-- The deviatoric gradient `dev grad : 𝕜³ → 𝕜^{3×3}_dev`. -/
def devGradOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 (Fin 3) (Fin 3 × Fin 3) :=
  (gradOp 3 3).postComp (deviatoricMat 3)

theorem curlSymOp_apply {f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜} (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (curlSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f =
      (curlOp 3).apply (matMulField (symMat 3) f) :=
  preComp_apply_eq_matMulField _ _ hf

theorem divDevOp_apply {f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜} (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (divDevOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f =
      (divOp 3 3).apply (matMulField (deviatoricMat 3) f) :=
  preComp_apply_eq_matMulField _ _ hf

theorem devGradOp_apply (f : Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    (devGradOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f =
      matMulField (deviatoricMat 3) ((gradOp 3 3).apply f) :=
  postComp_apply_eq_matMulField _ _ _

theorem trace_curlOp_eq_zero_of_symm {Φ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜}
    (hs : ∀ i j, Φ (i, j) = Φ (j, i)) (x : Fin 3 → ℝ) :
    ∑ i, (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply Φ (i, i) x = 0 := by
  simp only [Fin.sum_univ_three, curlOp_apply]
  simp only [Fin.isValue, Fin.reduceAdd]
  rw [hs 0 2, hs 0 1, hs 1 2]
  ring

theorem matMulField_deviatoricMat_curlOp_symMat (f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    matMulField (deviatoricMat 3)
        ((curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply (matMulField (symMat 3) f)) =
      (curlOp 3).apply (matMulField (symMat 3) f) :=
  matMulField_deviatoricMat_of_trace fun x =>
    trace_curlOp_eq_zero_of_symm (fun i j => matMulField_symMat_symm f i j) x

/-! ## The complex identities -/

theorem isComplexPair_hess_curlSym :
    (hessOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).IsComplexPair curlSymOp := by
  intro h hh
  rw [curlSymOp_apply ((hessOp 3).contDiff_apply hh),
    matMulField_symMat_of_symm fun i j => hessOp_apply_swap hh i j]
  exact isComplexPair_hess_curl h hh

theorem isComplexPair_curlSym_divDev :
    (curlSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).IsComplexPair divDevOp := by
  intro f hf
  rw [divDevOp_apply ((curlSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).contDiff_apply hf),
    curlSymOp_apply hf, matMulField_deviatoricMat_curlOp_symMat]
  exact isComplexPair_curl_div _ fun i => contDiff_matMulField _ hf i

/-! ## Formal adjoints -/

theorem curlSymOp_formalAdj :
    (curlSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj =
      (curlOp 3).formalAdj.postComp (symMat 3) := by
  rw [curlSymOp, formalAdj_preComp, symMat_conjTranspose (𝕜 := 𝕜)]

theorem curlSymOp_formalAdj_apply (f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    (curlSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.apply f = symCurlOp.apply f := by
  rw [curlSymOp_formalAdj, postComp_apply_eq_matMulField, curlOp_formalAdj_apply, symCurlOp,
    postComp_apply_eq_matMulField]

theorem divDevOp_formalAdj :
    (divDevOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj =
      (divOp 3 3).formalAdj.postComp (deviatoricMat 3) := by
  rw [divDevOp, formalAdj_preComp, deviatoricMat_conjTranspose (𝕜 := 𝕜)]

theorem divDevOp_formalAdj_apply (f : Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    (divDevOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.apply f = -devGradOp.apply f := by
  rw [divDevOp_formalAdj, postComp_apply_eq_matMulField, devGradOp_apply, ← matMulField_neg]
  congr 1
  funext ij x
  rw [divOp_formalAdj_apply, Pi.neg_apply, Pi.neg_apply, gradOp_apply]

theorem devGradOp_formalAdj :
    (devGradOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj =
      (gradOp 3 3).formalAdj.preComp (deviatoricMat 3) := by
  rw [devGradOp, formalAdj_postComp, deviatoricMat_conjTranspose (𝕜 := 𝕜)]

theorem devGradOp_formalAdj_apply {f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (devGradOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.apply f = -divDevOp.apply f := by
  rw [devGradOp_formalAdj, preComp_apply_eq_matMulField _ _ hf, divDevOp_apply hf]
  funext i x
  rw [gradOp_formalAdj_apply, Pi.neg_apply, Pi.neg_apply, divOp_apply]

/-! ## Mapping properties of the constraints -/

theorem hessOp_matMapsTo :
    (hessOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).MatMapsTo (idMat Unit) (symMat 3) :=
  fun _ hφ => matMulField_symMat_of_symm fun i j =>
    hessOp_apply_swap (fun u => contDiff_matMulField _ hφ u) i j

theorem curlSymOp_matMapsTo :
    (curlSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).MatMapsTo (symMat 3) (deviatoricMat 3) :=
  fun φ hφ => by
    rw [curlSymOp_apply (contDiff_matMulField _ hφ), isProjMat_symMat.matMulField_matMulField,
      matMulField_deviatoricMat_curlOp_symMat]

theorem curlSymOp_formalAdj_matMapsTo :
    (curlSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.MatMapsTo (deviatoricMat 3)
      (symMat 3) := by
  rw [curlSymOp_formalAdj]
  exact matMapsTo_postComp _ _ isProjMat_symMat

theorem divDevOp_formalAdj_matMapsTo :
    (divDevOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.MatMapsTo (idMat (Fin 3))
      (deviatoricMat 3) := by
  rw [divDevOp_formalAdj]
  exact matMapsTo_postComp _ _ isProjMat_deviatoricMat

/-! ## The Hessian complex on an open set -/

/-- The component index types of the Hessian complex. -/
def hessianIdx : ℤ → Type
  | .ofNat 0 => Unit
  | .ofNat 1 => Fin 3 × Fin 3
  | .ofNat 2 => Fin 3 × Fin 3
  | .ofNat 3 => Fin 3
  | .ofNat (_ + 4) => Empty
  | .negSucc _ => Empty

instance instFintypeHessianIdx : ∀ k, Fintype (hessianIdx k)
  | .ofNat 0 => inferInstanceAs (Fintype Unit)
  | .ofNat 1 => inferInstanceAs (Fintype (Fin 3 × Fin 3))
  | .ofNat 2 => inferInstanceAs (Fintype (Fin 3 × Fin 3))
  | .ofNat 3 => inferInstanceAs (Fintype (Fin 3))
  | .ofNat (_ + 4) => inferInstanceAs (Fintype Empty)
  | .negSucc _ => inferInstanceAs (Fintype Empty)

instance instDecidableEqHessianIdx : ∀ k, DecidableEq (hessianIdx k)
  | .ofNat 0 => inferInstanceAs (DecidableEq Unit)
  | .ofNat 1 => inferInstanceAs (DecidableEq (Fin 3 × Fin 3))
  | .ofNat 2 => inferInstanceAs (DecidableEq (Fin 3 × Fin 3))
  | .ofNat 3 => inferInstanceAs (DecidableEq (Fin 3))
  | .ofNat (_ + 4) => inferInstanceAs (DecidableEq Empty)
  | .negSucc _ => inferInstanceAs (DecidableEq Empty)

theorem isEmpty_hessianIdx {k : ℤ} (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3) :
    IsEmpty (hessianIdx k) := by
  match k with
  | .ofNat 0 => exact absurd rfl h0
  | .ofNat 1 => exact absurd rfl h1
  | .ofNat 2 => exact absurd rfl h2
  | .ofNat 3 => exact absurd rfl h3
  | .ofNat (_ + 4) => exact inferInstanceAs (IsEmpty Empty)
  | .negSucc _ => exact inferInstanceAs (IsEmpty Empty)

variable (𝕜) in
/-- The operators of the Hessian complex: `hess`, `curl ∘ sym`, `div ∘ dev`, and `0`. -/
def hessianOp : ∀ k : ℤ, ConstCoeffOp (Fin 3 → ℝ) 𝕜 (hessianIdx k) (hessianIdx (k + 1))
  | .ofNat 0 => hessOp 3
  | .ofNat 1 => curlSymOp
  | .ofNat 2 => divDevOp
  | .ofNat (_ + 3) => zeroOp _ _
  | .negSucc _ => zeroOp _ _

variable (𝕜) in
/-- The constraints: `Sym` in degree `1`, `T` in degree `2`, none elsewhere. -/
def hessianMat : ∀ k : ℤ, hessianIdx k → hessianIdx k → 𝕜
  | .ofNat 0 => idMat _
  | .ofNat 1 => symMat 3
  | .ofNat 2 => deviatoricMat 3
  | .ofNat (_ + 3) => idMat _
  | .negSucc _ => idMat _

theorem hessianOp_comp (k : ℤ) : (hessianOp 𝕜 k).IsComplexPair (hessianOp 𝕜 (k + 1)) := by
  intro f hf
  by_cases h0 : k = 0
  · subst h0
    exact isComplexPair_hess_curlSym f hf
  by_cases h1 : k = 1
  · subst h1
    exact isComplexPair_curlSym_divDev f hf
  by_cases hneg : k < 0
  · have : IsEmpty (hessianIdx k) :=
      isEmpty_hessianIdx (by omega) (by omega) (by omega) (by omega)
    rw [(hessianOp 𝕜 k).apply_of_isEmpty]
    exact (hessianOp 𝕜 (k + 1)).apply_zero
  · have : IsEmpty (hessianIdx (k + 1 + 1)) :=
      isEmpty_hessianIdx (by omega) (by omega) (by omega) (by omega)
    exact funext fun j => isEmptyElim j

theorem isProjMat_hessianMat : ∀ k : ℤ, IsProjMat (hessianMat 𝕜 k)
  | .ofNat 0 => isProjMat_idMat
  | .ofNat 1 => isProjMat_symMat
  | .ofNat 2 => isProjMat_deviatoricMat
  | .ofNat (_ + 3) => isProjMat_idMat
  | .negSucc _ => isProjMat_idMat

theorem hessianOp_matMapsTo (k : ℤ) :
    (hessianOp 𝕜 k).MatMapsTo (hessianMat 𝕜 k) (hessianMat 𝕜 (k + 1)) := by
  by_cases h0 : k = 0
  · subst h0
    exact hessOp_matMapsTo
  by_cases h1 : k = 1
  · subst h1
    exact curlSymOp_matMapsTo
  by_cases h2 : k = 2
  · subst h2
    exact matMapsTo_idMat (κ := Fin 3) _ _
  by_cases hneg : k < 0
  · have : IsEmpty (hessianIdx k) :=
      isEmpty_hessianIdx (by omega) (by omega) (by omega) (by omega)
    exact matMapsTo_of_isEmpty_left _ _ _
  · have : IsEmpty (hessianIdx (k + 1)) :=
      isEmpty_hessianIdx (by omega) (by omega) (by omega) (by omega)
    exact matMapsTo_of_isEmpty_right _ _ _

theorem hessianOp_formalAdj_matMapsTo (k : ℤ) :
    (hessianOp 𝕜 k).formalAdj.MatMapsTo (hessianMat 𝕜 (k + 1)) (hessianMat 𝕜 k) := by
  by_cases h0 : k = 0
  · subst h0
    exact matMapsTo_idMat (κ := Unit) _ _
  by_cases h1 : k = 1
  · subst h1
    exact curlSymOp_formalAdj_matMapsTo
  by_cases h2 : k = 2
  · subst h2
    exact divDevOp_formalAdj_matMapsTo
  by_cases hneg : k < 0
  · have : IsEmpty (hessianIdx k) :=
      isEmpty_hessianIdx (by omega) (by omega) (by omega) (by omega)
    exact matMapsTo_of_isEmpty_right _ _ _
  · have : IsEmpty (hessianIdx (k + 1)) :=
      isEmpty_hessianIdx (by omega) (by omega) (by omega) (by omega)
    exact matMapsTo_of_isEmpty_left _ _ _

variable (𝕜) in
/-- The Hessian complex as a complex of constant-coefficient operators. -/
def hessianConstCoeffComplex : ConstCoeffComplex (Fin 3 → ℝ) 𝕜 where
  ι := hessianIdx
  A := hessianOp 𝕜
  comp := hessianOp_comp

variable (𝕜) in
/-- **The Hessian complex on an open `Ω ⊆ ℝ³`**, a complex of constrained realizations. -/
def hessianComplex {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) : ConstrainedComplex (Fin 3 → ℝ) 𝕜 Ω :=
  ConstrainedComplex.ofMatrices hΩ (hessianConstCoeffComplex 𝕜) (hessianMat 𝕜)
    isProjMat_hessianMat hessianOp_matMapsTo hessianOp_formalAdj_matMapsTo

section OnOmega

variable {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω)

end OnOmega

end Feec.Domain
