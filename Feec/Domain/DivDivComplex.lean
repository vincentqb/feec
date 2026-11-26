module

public import Feec.Domain.HessianComplex

/-!
# The div-div complex on an open set of `ℝ³`, and its duality with the Hessian complex

The div-div complex `𝕜³ --dev grad--> T --sym curl--> Sym --div div--> 𝕜` is a complex of
constrained realizations on every open `Ω ⊆ ℝ³`, and the dual of the minimal Hessian (div-div)
complex is the maximal div-div (Hessian) complex read backwards, up to the sign of one differential.

## Main results

* `hessian_dual_minimalComplex_d₀` and its analogues: the dual of the minimal Hessian complex.
* `divDiv_dual_minimalComplex_d₀` and its analogues: the dual of the minimal div-div complex.
-/

open scoped InnerProductSpace ContDiff ComplexConjugate LinearPMap
open MeasureTheory Set

@[expose] public noncomputable section

namespace Feec.Domain

open ConstCoeffOp

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## The complex identities -/

theorem matMulField_deviatoricMat_three (f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    matMulField (deviatoricMat 3) f =
      f + (-(3 : 𝕜)⁻¹) • fun ij => if ij.1 = ij.2 then fun x => ∑ k, f (k, k) x else 0 := by
  funext ij x
  rw [matMulField_deviatoricMat]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp [sub_eq_add_neg]

theorem matMulField_symMat_curlOp_smul_id (g : (Fin 3 → ℝ) → 𝕜) :
    matMulField (symMat 3) ((curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      fun ij => if ij.1 = ij.2 then g else 0) = 0 := by
  funext ij x
  obtain ⟨i, k⟩ := ij
  rw [matMulField_symMat, curlOp_apply, curlOp_apply]
  fin_cases i <;> fin_cases k <;> simp

theorem isComplexPair_devGrad_symCurl :
    (devGradOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).IsComplexPair symCurlOp := by
  intro u hu
  set G := (gradOp 3 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply u with hGdef
  have hG : ∀ ij, ContDiff ℝ ∞ (G ij) := (gradOp 3 3).contDiff_apply hu
  set D : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜 :=
    fun ij => if ij.1 = ij.2 then fun x => ∑ k, G (k, k) x else 0 with hDdef
  have hD : ∀ ij, ContDiff ℝ ∞ (D ij) := fun ij => by
    simp only [hDdef]
    split_ifs
    · exact ContDiff.sum fun k _ => hG (k, k)
    · exact contDiff_const
  rw [devGradOp_apply, matMulField_deviatoricMat_three, ← hGdef, ← hDdef, symCurlOp,
    postComp_apply_eq_matMulField,
    (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply_add (f := G) (g := (-(3 : 𝕜)⁻¹) • D) hG
      fun ij => (hD ij).const_smul (-(3 : 𝕜)⁻¹),
    (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply_smul _ (f := D) hD, hGdef,
    isComplexPair_grad_curl u hu, zero_add]
  funext ij x
  have h0 := congrFun (congrFun (matMulField_symMat_curlOp_smul_id (𝕜 := 𝕜)
    fun x => ∑ k, G (k, k) x) ij) x
  simp only [matMulField, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0 ⊢
  have h0' : ∑ j, symMat 3 ij j * (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply D j x = 0 :=
    h0
  rw [show (∑ j, symMat 3 ij j * (-(3 : 𝕜)⁻¹ *
      (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply D j x)) =
      -(3 : 𝕜)⁻¹ * ∑ j, symMat 3 ij j * (curlOp 3).apply D j x by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, h0', mul_zero]

/-! ## Formal adjoints and mapping properties -/

theorem symCurlOp_formalAdj :
    (symCurlOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj =
      (curlOp 3).formalAdj.preComp (symMat 3) := by
  rw [symCurlOp, formalAdj_postComp, symMat_conjTranspose (𝕜 := 𝕜)]

theorem symCurlOp_formalAdj_apply {f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (symCurlOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.apply f = curlSymOp.apply f := by
  rw [symCurlOp_formalAdj, preComp_apply_eq_matMulField _ _ hf, curlOp_formalAdj_apply,
    curlSymOp_apply hf]

theorem devGradOp_matMapsTo :
    (devGradOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).MatMapsTo (idMat (Fin 3)) (deviatoricMat 3) :=
  matMapsTo_postComp (gradOp 3 3) _ isProjMat_deviatoricMat

theorem symCurlOp_matMapsTo :
    (symCurlOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).MatMapsTo (deviatoricMat 3) (symMat 3) :=
  matMapsTo_postComp (curlOp 3) _ isProjMat_symMat

theorem symCurlOp_formalAdj_matMapsTo :
    (symCurlOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.MatMapsTo (symMat 3)
      (deviatoricMat 3) := fun φ hφ => by
  rw [symCurlOp_formalAdj_apply (contDiff_matMulField _ hφ)]
  exact curlSymOp_matMapsTo φ hφ

theorem divdivOp_formalAdj_matMapsTo :
    (divdivOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.MatMapsTo (idMat Unit)
      (symMat 3) := by
  rw [divdivOp_formalAdj]
  exact hessOp_matMapsTo

/-! ## The div-div complex on an open set -/

/-- The component index types of the div-div complex. -/
def divDivIdx : ℤ → Type
  | .ofNat 0 => Fin 3
  | .ofNat 1 => Fin 3 × Fin 3
  | .ofNat 2 => Fin 3 × Fin 3
  | .ofNat 3 => Unit
  | .ofNat (_ + 4) => Empty
  | .negSucc _ => Empty

instance instFintypeDivDivIdx : ∀ k, Fintype (divDivIdx k)
  | .ofNat 0 => inferInstanceAs (Fintype (Fin 3))
  | .ofNat 1 => inferInstanceAs (Fintype (Fin 3 × Fin 3))
  | .ofNat 2 => inferInstanceAs (Fintype (Fin 3 × Fin 3))
  | .ofNat 3 => inferInstanceAs (Fintype Unit)
  | .ofNat (_ + 4) => inferInstanceAs (Fintype Empty)
  | .negSucc _ => inferInstanceAs (Fintype Empty)

instance instDecidableEqDivDivIdx : ∀ k, DecidableEq (divDivIdx k)
  | .ofNat 0 => inferInstanceAs (DecidableEq (Fin 3))
  | .ofNat 1 => inferInstanceAs (DecidableEq (Fin 3 × Fin 3))
  | .ofNat 2 => inferInstanceAs (DecidableEq (Fin 3 × Fin 3))
  | .ofNat 3 => inferInstanceAs (DecidableEq Unit)
  | .ofNat (_ + 4) => inferInstanceAs (DecidableEq Empty)
  | .negSucc _ => inferInstanceAs (DecidableEq Empty)

theorem isEmpty_divDivIdx {k : ℤ} (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3) :
    IsEmpty (divDivIdx k) := by
  match k with
  | .ofNat 0 => exact absurd rfl h0
  | .ofNat 1 => exact absurd rfl h1
  | .ofNat 2 => exact absurd rfl h2
  | .ofNat 3 => exact absurd rfl h3
  | .ofNat (_ + 4) => exact inferInstanceAs (IsEmpty Empty)
  | .negSucc _ => exact inferInstanceAs (IsEmpty Empty)

variable (𝕜) in
/-- The operators of the div-div complex: `dev grad`, `sym curl`, `div div`, and `0`. -/
def divDivOp : ∀ k : ℤ, ConstCoeffOp (Fin 3 → ℝ) 𝕜 (divDivIdx k) (divDivIdx (k + 1))
  | .ofNat 0 => devGradOp
  | .ofNat 1 => symCurlOp
  | .ofNat 2 => divdivOp 3
  | .ofNat (_ + 3) => zeroOp _ _
  | .negSucc _ => zeroOp _ _

variable (𝕜) in
/-- The constraints: `T` in degree `1`, `Sym` in degree `2`, none elsewhere. -/
def divDivMat : ∀ k : ℤ, divDivIdx k → divDivIdx k → 𝕜
  | .ofNat 0 => idMat _
  | .ofNat 1 => deviatoricMat 3
  | .ofNat 2 => symMat 3
  | .ofNat (_ + 3) => idMat _
  | .negSucc _ => idMat _

theorem divDivOp_comp (k : ℤ) : (divDivOp 𝕜 k).IsComplexPair (divDivOp 𝕜 (k + 1)) := by
  intro f hf
  by_cases h0 : k = 0
  · subst h0
    exact isComplexPair_devGrad_symCurl f hf
  by_cases h1 : k = 1
  · subst h1
    exact isComplexPair_symCurl_divdiv f hf
  by_cases hneg : k < 0
  · have : IsEmpty (divDivIdx k) :=
      isEmpty_divDivIdx (by omega) (by omega) (by omega) (by omega)
    rw [(divDivOp 𝕜 k).apply_of_isEmpty]
    exact (divDivOp 𝕜 (k + 1)).apply_zero
  · have : IsEmpty (divDivIdx (k + 1 + 1)) :=
      isEmpty_divDivIdx (by omega) (by omega) (by omega) (by omega)
    exact funext fun j => isEmptyElim j

theorem isProjMat_divDivMat : ∀ k : ℤ, IsProjMat (divDivMat 𝕜 k)
  | .ofNat 0 => isProjMat_idMat
  | .ofNat 1 => isProjMat_deviatoricMat
  | .ofNat 2 => isProjMat_symMat
  | .ofNat (_ + 3) => isProjMat_idMat
  | .negSucc _ => isProjMat_idMat

theorem divDivOp_matMapsTo (k : ℤ) :
    (divDivOp 𝕜 k).MatMapsTo (divDivMat 𝕜 k) (divDivMat 𝕜 (k + 1)) := by
  by_cases h0 : k = 0
  · subst h0
    exact devGradOp_matMapsTo
  by_cases h1 : k = 1
  · subst h1
    exact symCurlOp_matMapsTo
  by_cases h2 : k = 2
  · subst h2
    exact matMapsTo_idMat (κ := Unit) _ _
  by_cases hneg : k < 0
  · have : IsEmpty (divDivIdx k) :=
      isEmpty_divDivIdx (by omega) (by omega) (by omega) (by omega)
    exact matMapsTo_of_isEmpty_left _ _ _
  · have : IsEmpty (divDivIdx (k + 1)) :=
      isEmpty_divDivIdx (by omega) (by omega) (by omega) (by omega)
    exact matMapsTo_of_isEmpty_right _ _ _

theorem divDivOp_formalAdj_matMapsTo (k : ℤ) :
    (divDivOp 𝕜 k).formalAdj.MatMapsTo (divDivMat 𝕜 (k + 1)) (divDivMat 𝕜 k) := by
  by_cases h0 : k = 0
  · subst h0
    exact matMapsTo_idMat (κ := Fin 3) _ _
  by_cases h1 : k = 1
  · subst h1
    exact symCurlOp_formalAdj_matMapsTo
  by_cases h2 : k = 2
  · subst h2
    exact divdivOp_formalAdj_matMapsTo
  by_cases hneg : k < 0
  · have : IsEmpty (divDivIdx k) :=
      isEmpty_divDivIdx (by omega) (by omega) (by omega) (by omega)
    exact matMapsTo_of_isEmpty_right _ _ _
  · have : IsEmpty (divDivIdx (k + 1)) :=
      isEmpty_divDivIdx (by omega) (by omega) (by omega) (by omega)
    exact matMapsTo_of_isEmpty_left _ _ _

variable (𝕜) in
/-- The div-div complex as a complex of constant-coefficient operators. -/
def divDivConstCoeffComplex : ConstCoeffComplex (Fin 3 → ℝ) 𝕜 where
  ι := divDivIdx
  A := divDivOp 𝕜
  comp := divDivOp_comp

variable (𝕜) in
/-- **The div-div complex on an open `Ω ⊆ ℝ³`**, a complex of constrained realizations. -/
def divDivComplex {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) : ConstrainedComplex (Fin 3 → ℝ) 𝕜 Ω :=
  ConstrainedComplex.ofMatrices hΩ (divDivConstCoeffComplex 𝕜) (divDivMat 𝕜)
    isProjMat_divDivMat divDivOp_matMapsTo divDivOp_formalAdj_matMapsTo

section OnOmega

variable {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω)

/-! ## Duality of the Hessian and div-div complexes -/

theorem hessOp_formalAdj_formalAdj_apply (ψ : Unit → (Fin 3 → ℝ) → 𝕜) :
    (hessOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.formalAdj.apply ψ =
      (divdivOp 3).formalAdj.apply ψ := by
  rw [hessOp_formalAdj]

theorem curlSymOp_formalAdj_formalAdj_apply {ψ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜}
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) :
    (curlSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.formalAdj.apply ψ =
      symCurlOp.formalAdj.apply ψ := by
  rw [formalAdj_formalAdj, symCurlOp_formalAdj_apply hψ]

theorem divDevOp_formalAdj_formalAdj_apply {ψ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜}
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) :
    (divDevOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.formalAdj.apply ψ =
      devGradOp.negOp.formalAdj.apply ψ := by
  rw [formalAdj_formalAdj, formalAdj_negOp, negOp_apply, devGradOp_formalAdj_apply hψ, neg_neg]

theorem divdivOp_formalAdj_formalAdj_apply (ψ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    (divdivOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.formalAdj.apply ψ =
      (hessOp 3).formalAdj.apply ψ := by
  rw [formalAdj_formalAdj, hessOp_formalAdj]

theorem symCurlOp_formalAdj_formalAdj_apply (ψ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    (symCurlOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.formalAdj.apply ψ =
      curlSymOp.formalAdj.apply ψ := by
  rw [formalAdj_formalAdj, curlSymOp_formalAdj_apply]

theorem devGradOp_formalAdj_formalAdj_apply (ψ : Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    (devGradOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.formalAdj.apply ψ =
      divDevOp.negOp.formalAdj.apply ψ := by
  rw [formalAdj_formalAdj, formalAdj_negOp, negOp_apply, divDevOp_formalAdj_apply, neg_neg]

/-- **The dual of the minimal Hessian complex is the maximal div-div complex**, degree `0`. -/
theorem hessian_dual_minimalComplex_d₀ :
    (hessianComplex 𝕜 hΩ).minimalComplex.dual.d 1 0 =
      ((divDivComplex 𝕜 hΩ).maximalComplex hΩ).d 2 3 :=
  ((hessianComplex 𝕜 hΩ).dual_minimalComplex_d 0).trans
    ((maximalVia_congr _ _ _ fun ψ _ _ _ =>
      testField_congr _ _ (hessOp_formalAdj_formalAdj_apply ψ)).trans
      ((divDivComplex 𝕜 hΩ).maximalComplex_d hΩ 2).symm)

theorem hessian_dual_minimalComplex_d₁ :
    (hessianComplex 𝕜 hΩ).minimalComplex.dual.d 2 1 =
      ((divDivComplex 𝕜 hΩ).maximalComplex hΩ).d 1 2 :=
  ((hessianComplex 𝕜 hΩ).dual_minimalComplex_d 1).trans
    ((maximalVia_congr _ _ _ fun _ hψ _ _ =>
      testField_congr _ _ (curlSymOp_formalAdj_formalAdj_apply fun i => (hψ i).contDiff)).trans
      ((divDivComplex 𝕜 hΩ).maximalComplex_d hΩ 1).symm)

theorem hessian_dual_minimalComplex_d₂ :
    (hessianComplex 𝕜 hΩ).minimalComplex.dual.d 3 2 =
      devGradOp.negOp.maximalVia (freeEmb 𝕜 Ω (Fin 3)) (traceFreeEmb 𝕜 Ω 3) :=
  ((hessianComplex 𝕜 hΩ).dual_minimalComplex_d 2).trans
    (maximalVia_congr _ _ _ fun _ hψ _ _ =>
      testField_congr _ _ (divDevOp_formalAdj_formalAdj_apply fun i => (hψ i).contDiff))

/-- **The dual of the minimal div-div complex**, degree `0`: `((dev grad)_min)† = (-div)_max`. -/
theorem divDiv_dual_minimalComplex_d₀ :
    (divDivComplex 𝕜 hΩ).minimalComplex.dual.d 1 0 =
      divDevOp.negOp.maximalVia (traceFreeEmb 𝕜 Ω 3) (freeEmb 𝕜 Ω (Fin 3)) :=
  ((divDivComplex 𝕜 hΩ).dual_minimalComplex_d 0).trans
    (maximalVia_congr _ _ _ fun ψ _ _ _ =>
      testField_congr _ _ (devGradOp_formalAdj_formalAdj_apply ψ))

theorem divDiv_dual_minimalComplex_d₁ :
    (divDivComplex 𝕜 hΩ).minimalComplex.dual.d 2 1 =
      ((hessianComplex 𝕜 hΩ).maximalComplex hΩ).d 1 2 :=
  ((divDivComplex 𝕜 hΩ).dual_minimalComplex_d 1).trans
    ((maximalVia_congr _ _ _ fun ψ _ _ _ =>
      testField_congr _ _ (symCurlOp_formalAdj_formalAdj_apply ψ)).trans
      ((hessianComplex 𝕜 hΩ).maximalComplex_d hΩ 1).symm)

theorem divDiv_dual_minimalComplex_d₂ :
    (divDivComplex 𝕜 hΩ).minimalComplex.dual.d 3 2 =
      ((hessianComplex 𝕜 hΩ).maximalComplex hΩ).d 0 1 :=
  ((divDivComplex 𝕜 hΩ).dual_minimalComplex_d 2).trans
    ((maximalVia_congr _ _ _ fun ψ _ _ _ =>
      testField_congr _ _ (divdivOp_formalAdj_formalAdj_apply ψ)).trans
      ((hessianComplex 𝕜 hΩ).maximalComplex_d hΩ 0).symm)

end OnOmega

end Feec.Domain
