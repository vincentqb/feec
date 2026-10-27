module

public import Feec.Domain.ConstrainedComplex

/-!
# The elasticity complex on an open set of `ℝ³`

The elasticity (Kröner, Calabi) complex
`𝕜³ --sym grad--> 𝕜^{3×3}_sym --inc--> 𝕜^{3×3}_sym --div--> 𝕜³` on `ℝ³`, with
`inc σ = curl (curl σ)ᵀ` (row-wise curls, `Feec.Domain.curlOp`), as constant-coefficient
operators (`symGradOp`, `incOp`, `divSymOp`; `divSymOp = div ∘ sym` is the divergence of
symmetric fields, `div` on `Sym`), and as a complex of constrained realizations on every open
`Ω ⊆ ℝ³` (`elasticityComplex`, the middle spaces being `L²(Ω; Sym)`):

* the complex identities `inc ∘ sym grad = 0` (`isComplexPair_symGrad_inc`) and
  `div ∘ inc = 0` (`isComplexPair_inc_div`, `isComplexPair_inc_divSym`), and the symmetry of
  `inc` (`incOp_apply_transpose`: `inc (σᵀ) = (inc σ)ᵀ`);
* the formal adjoints `(sym grad)ᵗ = -div ∘ sym` (`symGradOp_formalAdj_apply`), `incᵗ = inc`
  (`incOp_formalAdj_apply`) and
  `divᵗ = -sym grad` (`divSymOp_formalAdj_apply`);
* the minimal complex `H̊(sym grad) → H̊(inc, Sym) → H̊(div, Sym) → L²` and the maximal complex
  `H(sym grad) → H(inc, Sym) → H(div, Sym) → L²`, where `H(sym grad) = {u ∈ L² : ε(u) ∈ L²}`
  (weakly) and `H̊(sym grad)` is the closure of the test fields in its graph norm (these are
  `H̊¹` and, for regular `Ω`, `H¹` by Korn's inequalities, which are not proved here)
  (`elasticityComplex.minimalComplex`, `elasticityComplex.maximalComplex`), whose differentials
  are the realizations of `sym grad`, `inc`, `div`;
* **self-duality**: the dual of the minimal complex is the maximal complex read backwards with
  the signs `-div, inc, -sym grad` (`elasticity_dual_minimalComplex_d₀`, …), and vice versa by
  taking adjoints.

No closed-range statement is made (it needs the regularity of `Ω`).

**As a BGG complex.** The elasticity complex is the output of the BGG construction
(`Feec.BGG.Data.bgg`, `J = 1`) applied to two copies of the de Rham complex tensored with `ℝ³`,
`ℝ³ → ℝ³ˣ³ → ℝ³ˣ³ → ℝ³`, linked by `-mskw`, `S u = uᵀ - tr(u) I` and `2 vskw`: the middle two rows
of [ArnoldHu2021], (32); the construction goes back to [Eastwood2000] (the BGG resolution) and
[AFW2006], §11. On smooth fields this is formalized in `Feec.Domain.ElasticityBGG`: the diagram
satisfies the injectivity/surjectivity condition at `J = 1` and its BGG complex is the smooth
version of `elasticityComplex` (same operators, same constraints). The identification of the `L²`
realizations is not formalized.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §11 (the elasticity complex)
* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §4.1 (the elasticity complex as the
  BGG output of the middle two rows of (32), `J = 1`), (5)
* [M. Eastwood, *A complex from linear elasticity*][Eastwood2000] (the elasticity complex from the
  BGG resolution)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff ComplexConjugate LinearPMap
open MeasureTheory Set

@[expose] public noncomputable section

namespace Feec.Domain

open ConstCoeffOp

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Transposition -/

/-- The transposition `M ↦ Mᵀ` as a constant matrix on `𝕜^{n×n}`. -/
def transposeMat (n : ℕ) : Fin n × Fin n → Fin n × Fin n → 𝕜 := fun ij kl =>
  if kl = (ij.2, ij.1) then 1 else 0

theorem matMulField_transposeMat {E : Type*} {n : ℕ} (φ : Fin n × Fin n → E → 𝕜)
    (ij : Fin n × Fin n) (x : E) : matMulField (transposeMat n) φ ij x = φ (ij.2, ij.1) x := by
  simp [matMulField, transposeMat]

theorem transposeMat_conj {n : ℕ} :
    (fun j j' => conj (transposeMat n j' j : 𝕜)) = transposeMat n := by
  funext ij kl
  simp only [transposeMat, apply_ite (starRingEnd 𝕜), map_one, map_zero]
  exact if_congr ⟨fun h => by rw [h], fun h => by rw [h]⟩ rfl rfl

/-! ## The operators -/

/-- The symmetric gradient `𝕜³ → 𝕜^{3×3}`, `ε(u) = sym grad u`. -/
def symGradOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 (Fin 3) (Fin 3 × Fin 3) :=
  (gradOp 3 3).postComp (symMat 3)

/-- The incompatibility operator `inc σ = curl (curl σ)ᵀ` (second order). -/
def incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3) (Fin 3 × Fin 3) :=
  (curlOp 3).comp ((curlOp 3).postComp (transposeMat 3))

/-- The divergence of symmetric matrix fields, `div ∘ sym` (equal to `div` on `Sym`). -/
def divSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3) (Fin 3) :=
  (divOp 3 3).preComp (symMat 3)

theorem symGradOp_apply (f : Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    (symGradOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f =
      matMulField (symMat 3) ((gradOp 3 3).apply f) :=
  postComp_apply_eq_matMulField _ _ _

theorem divSymOp_apply {f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜} (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (divSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f =
      (divOp 3 3).apply (matMulField (symMat 3) f) :=
  preComp_apply_eq_matMulField _ _ hf

theorem incOp_apply {f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜} (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f =
      (curlOp 3).apply fun ik => (curlOp 3).apply f (ik.2, ik.1) := by
  rw [incOp, comp_apply _ _ hf, postComp_apply_eq_matMulField]
  congr 1
  funext ik x
  exact matMulField_transposeMat _ ik x

/-- `inc` in coordinates: `(inc f)_{jl} = ∂_{l+1}∂_{j+1} f_{l+2,j+2} - ∂_{l+1}∂_{j+2} f_{l+2,j+1}
- ∂_{l+2}∂_{j+1} f_{l+1,j+2} + ∂_{l+2}∂_{j+2} f_{l+1,j+1}`. -/
theorem incOp_apply_eq {f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (j l : Fin 3) (x : Fin 3 → ℝ) :
    (incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f (j, l) x =
      fderiv ℝ (fun y => fderiv ℝ (f (l + 2, j + 2)) y (coordDir (j + 1))) x (coordDir (l + 1)) -
      fderiv ℝ (fun y => fderiv ℝ (f (l + 2, j + 1)) y (coordDir (j + 2))) x (coordDir (l + 1)) -
      fderiv ℝ (fun y => fderiv ℝ (f (l + 1, j + 2)) y (coordDir (j + 1))) x (coordDir (l + 2)) +
      fderiv ℝ (fun y => fderiv ℝ (f (l + 1, j + 1)) y (coordDir (j + 2))) x
        (coordDir (l + 2)) := by
  have hc : ∀ ik : Fin 3 × Fin 3, (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f ik =
      fun y => fderiv ℝ (f (ik.1, ik.2 + 2)) y (coordDir (ik.2 + 1)) -
        fderiv ℝ (f (ik.1, ik.2 + 1)) y (coordDir (ik.2 + 2)) :=
    fun ik => funext fun y => curlOp_apply f ik y
  have hd : ∀ (a : Fin 3 × Fin 3) (v : Fin 3 → ℝ), Differentiable ℝ fun y => fderiv ℝ (f a) y v :=
    fun a v => (contDiff_fderiv_apply (hf a) v).differentiable (by simp)
  rw [incOp_apply hf, curlOp_apply]
  simp only [hc]
  rw [fderiv_fun_sub (hd _ _ _) (hd _ _ _), fderiv_fun_sub (hd _ _ _) (hd _ _ _)]
  simp only [sub_apply]
  ring

/-- **`inc (fᵀ) = (inc f)ᵀ`** (Schwarz); in particular `inc` maps symmetric fields to symmetric
fields. -/
theorem incOp_apply_transpose {f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (j l : Fin 3) :
    (incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply (fun ij => f (ij.2, ij.1)) (l, j) =
      (incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f (j, l) := by
  funext x
  rw [incOp_apply_eq (fun i => hf _), incOp_apply_eq hf]
  simp only
  rw [fderiv_fderiv_comm ((hf (l + 2, j + 2)).of_le (by simp)) (coordDir (l + 1)),
    fderiv_fderiv_comm ((hf (l + 1, j + 2)).of_le (by simp)) (coordDir (l + 2)),
    fderiv_fderiv_comm ((hf (l + 2, j + 1)).of_le (by simp)) (coordDir (l + 1)),
    fderiv_fderiv_comm ((hf (l + 1, j + 1)).of_le (by simp)) (coordDir (l + 2))]
  ring

/-- `sym (inc f) = inc (sym f)`. -/
theorem matMulField_symMat_incOp {f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    matMulField (symMat 3) ((incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f) =
      incOp.apply (matMulField (symMat 3) f) := by
  set fT : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜 := fun ij => f (ij.2, ij.1) with hfTdef
  have hfT : ∀ i, ContDiff ℝ ∞ (fT i) := fun i => hf _
  rw [matMulField_symMat_eq f, ← hfTdef,
    (incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply_smul (1 / 2) (f := f + fT)
      fun i => (hf i).add (hfT i),
    (incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply_add hf hfT, matMulField_symMat_eq]
  funext ⟨j, l⟩ x
  simp only [Pi.smul_apply, Pi.add_apply, hfTdef]
  rw [incOp_apply_transpose hf]

/-! ## The complex identities -/

/-- **`inc ∘ sym grad = 0`.** -/
theorem isComplexPair_symGrad_inc :
    (symGradOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).IsComplexPair incOp := by
  intro u hu
  set G := (gradOp 3 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply u with hGdef
  have hG : ∀ ij, ContDiff ℝ ∞ (G ij) := (gradOp 3 3).contDiff_apply hu
  have h0 : (incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply G = 0 := by
    rw [incOp_apply hG, hGdef, isComplexPair_grad_curl u hu]
    exact (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply_zero
  rw [symGradOp_apply, ← matMulField_symMat_incOp hG, h0]
  funext ij x
  simp [matMulField]

/-- **`div ∘ inc = 0`.** -/
theorem isComplexPair_inc_div :
    (incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).IsComplexPair (divOp 3 3) := by
  intro f hf
  rw [incOp_apply hf]
  exact isComplexPair_curl_div _ fun ik => (curlOp 3).contDiff_apply hf _

/-- **`div ∘ inc = 0`** with the divergence of symmetric fields. -/
theorem isComplexPair_inc_divSym :
    (incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).IsComplexPair divSymOp := by
  intro f hf
  rw [divSymOp_apply ((incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).contDiff_apply hf),
    matMulField_symMat_incOp hf]
  exact isComplexPair_inc_div _ fun i => contDiff_matMulField _ hf i

/-! ## Formal adjoints -/

theorem symGradOp_formalAdj :
    (symGradOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj =
      (gradOp 3 3).formalAdj.preComp (symMat 3) := by
  rw [symGradOp, formalAdj_postComp, symMat_conjTranspose (𝕜 := 𝕜)]

/-- `(sym grad)ᵗ = -div ∘ sym`. -/
theorem symGradOp_formalAdj_apply {f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (symGradOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.apply f =
      -(divSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f := by
  rw [symGradOp_formalAdj, preComp_apply_eq_matMulField _ _ hf, divSymOp_apply hf]
  funext i x
  rw [gradOp_formalAdj_apply, Pi.neg_apply, Pi.neg_apply, divOp_apply]

/-- **`incᵗ = inc`.** -/
theorem incOp_formalAdj_apply {f : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.apply f = incOp.apply f := by
  let C : ConstCoeffOp (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3) (Fin 3 × Fin 3) := curlOp 3
  have hC : ∀ i, ContDiff ℝ ∞ (C.formalAdj.apply f i) := C.formalAdj.contDiff_apply hf
  change (C.comp (C.postComp (transposeMat 3))).formalAdj.apply f =
    (C.comp (C.postComp (transposeMat 3))).apply f
  rw [formalAdj_comp_apply C (C.postComp (transposeMat 3)) hf, formalAdj_postComp,
    transposeMat_conj (𝕜 := 𝕜), preComp_apply_eq_matMulField _ _ hC, comp_apply _ _ hf,
    postComp_apply_eq_matMulField]
  simp only [C, curlOp_formalAdj_apply]

theorem divSymOp_formalAdj :
    (divSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj =
      (divOp 3 3).formalAdj.postComp (symMat 3) := by
  rw [divSymOp, formalAdj_preComp, symMat_conjTranspose (𝕜 := 𝕜)]

/-- **`divᵗ = -sym grad`.** -/
theorem divSymOp_formalAdj_apply (f : Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    (divSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.apply f = -symGradOp.apply f := by
  rw [divSymOp_formalAdj, postComp_apply_eq_matMulField, symGradOp_apply, ← matMulField_neg]
  congr 1
  funext ij x
  rw [divOp_formalAdj_apply, Pi.neg_apply, Pi.neg_apply, gradOp_apply]

/-! ## The elasticity complex on an open set -/

/-- The component index types of the elasticity complex (vectors as `Fin 3`, matrices as
`Fin 3 × Fin 3`). -/
def elasticityIdx : ℤ → Type
  | .ofNat 0 => Fin 3
  | .ofNat 1 => Fin 3 × Fin 3
  | .ofNat 2 => Fin 3 × Fin 3
  | .ofNat 3 => Fin 3
  | .ofNat (_ + 4) => Empty
  | .negSucc _ => Empty

instance instFintypeElasticityIdx : ∀ k, Fintype (elasticityIdx k)
  | .ofNat 0 => inferInstanceAs (Fintype (Fin 3))
  | .ofNat 1 => inferInstanceAs (Fintype (Fin 3 × Fin 3))
  | .ofNat 2 => inferInstanceAs (Fintype (Fin 3 × Fin 3))
  | .ofNat 3 => inferInstanceAs (Fintype (Fin 3))
  | .ofNat (_ + 4) => inferInstanceAs (Fintype Empty)
  | .negSucc _ => inferInstanceAs (Fintype Empty)

instance instDecidableEqElasticityIdx : ∀ k, DecidableEq (elasticityIdx k)
  | .ofNat 0 => inferInstanceAs (DecidableEq (Fin 3))
  | .ofNat 1 => inferInstanceAs (DecidableEq (Fin 3 × Fin 3))
  | .ofNat 2 => inferInstanceAs (DecidableEq (Fin 3 × Fin 3))
  | .ofNat 3 => inferInstanceAs (DecidableEq (Fin 3))
  | .ofNat (_ + 4) => inferInstanceAs (DecidableEq Empty)
  | .negSucc _ => inferInstanceAs (DecidableEq Empty)

theorem isEmpty_elasticityIdx {k : ℤ} (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3) :
    IsEmpty (elasticityIdx k) := by
  match k with
  | .ofNat 0 => exact absurd rfl h0
  | .ofNat 1 => exact absurd rfl h1
  | .ofNat 2 => exact absurd rfl h2
  | .ofNat 3 => exact absurd rfl h3
  | .ofNat (_ + 4) => exact inferInstanceAs (IsEmpty Empty)
  | .negSucc _ => exact inferInstanceAs (IsEmpty Empty)

variable (𝕜) in
/-- The operators of the elasticity complex: `sym grad`, `inc`, `div`, and `0` elsewhere. -/
def elasticityOp : ∀ k : ℤ, ConstCoeffOp (Fin 3 → ℝ) 𝕜 (elasticityIdx k) (elasticityIdx (k + 1))
  | .ofNat 0 => symGradOp
  | .ofNat 1 => incOp
  | .ofNat 2 => divSymOp
  | .ofNat (_ + 3) => zeroOp _ _
  | .negSucc _ => zeroOp _ _

variable (𝕜) in
/-- The constraints: symmetric matrices in degrees `1, 2`, none elsewhere. -/
def elasticityMat : ∀ k : ℤ, elasticityIdx k → elasticityIdx k → 𝕜
  | .ofNat 0 => idMat _
  | .ofNat 1 => symMat 3
  | .ofNat 2 => symMat 3
  | .ofNat (_ + 3) => idMat _
  | .negSucc _ => idMat _

/-- `inc` maps symmetric fields to symmetric fields. -/
theorem incOp_matMapsTo :
    (incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).MatMapsTo (symMat 3) (symMat 3) := fun φ hφ => by
  rw [matMulField_symMat_incOp (contDiff_matMulField _ hφ),
    isProjMat_symMat.matMulField_matMulField]

theorem incOp_formalAdj_matMapsTo :
    (incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.MatMapsTo (symMat 3) (symMat 3) :=
  fun φ hφ => by
    rw [incOp_formalAdj_apply (contDiff_matMulField _ hφ)]
    exact incOp_matMapsTo φ hφ

theorem divSymOp_formalAdj_matMapsTo :
    (divSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.MatMapsTo (idMat (Fin 3))
      (symMat 3) := by
  rw [divSymOp_formalAdj]
  exact matMapsTo_postComp _ _ isProjMat_symMat

theorem elasticityOp_comp (k : ℤ) :
    (elasticityOp 𝕜 k).IsComplexPair (elasticityOp 𝕜 (k + 1)) := by
  intro f hf
  by_cases h0 : k = 0
  · subst h0
    exact isComplexPair_symGrad_inc f hf
  by_cases h1 : k = 1
  · subst h1
    exact isComplexPair_inc_divSym f hf
  by_cases hneg : k < 0
  · have : IsEmpty (elasticityIdx k) :=
      isEmpty_elasticityIdx (by omega) (by omega) (by omega) (by omega)
    rw [(elasticityOp 𝕜 k).apply_of_isEmpty]
    exact (elasticityOp 𝕜 (k + 1)).apply_zero
  · have : IsEmpty (elasticityIdx (k + 1 + 1)) :=
      isEmpty_elasticityIdx (by omega) (by omega) (by omega) (by omega)
    exact funext fun j => isEmptyElim j

theorem isProjMat_elasticityMat : ∀ k : ℤ, IsProjMat (elasticityMat 𝕜 k)
  | .ofNat 0 => isProjMat_idMat
  | .ofNat 1 => isProjMat_symMat
  | .ofNat 2 => isProjMat_symMat
  | .ofNat (_ + 3) => isProjMat_idMat
  | .negSucc _ => isProjMat_idMat

theorem elasticityOp_matMapsTo (k : ℤ) :
    (elasticityOp 𝕜 k).MatMapsTo (elasticityMat 𝕜 k) (elasticityMat 𝕜 (k + 1)) := by
  by_cases h0 : k = 0
  · subst h0
    exact matMapsTo_postComp (gradOp 3 3) _ isProjMat_symMat
  by_cases h1 : k = 1
  · subst h1
    exact incOp_matMapsTo
  by_cases h2 : k = 2
  · subst h2
    exact matMapsTo_idMat (κ := Fin 3) _ _
  by_cases hneg : k < 0
  · have : IsEmpty (elasticityIdx k) :=
      isEmpty_elasticityIdx (by omega) (by omega) (by omega) (by omega)
    exact matMapsTo_of_isEmpty_left _ _ _
  · have : IsEmpty (elasticityIdx (k + 1)) :=
      isEmpty_elasticityIdx (by omega) (by omega) (by omega) (by omega)
    exact matMapsTo_of_isEmpty_right _ _ _

theorem elasticityOp_formalAdj_matMapsTo (k : ℤ) :
    (elasticityOp 𝕜 k).formalAdj.MatMapsTo (elasticityMat 𝕜 (k + 1)) (elasticityMat 𝕜 k) := by
  by_cases h0 : k = 0
  · subst h0
    exact matMapsTo_idMat (κ := Fin 3) _ _
  by_cases h1 : k = 1
  · subst h1
    exact incOp_formalAdj_matMapsTo
  by_cases h2 : k = 2
  · subst h2
    exact divSymOp_formalAdj_matMapsTo
  by_cases hneg : k < 0
  · have : IsEmpty (elasticityIdx k) :=
      isEmpty_elasticityIdx (by omega) (by omega) (by omega) (by omega)
    exact matMapsTo_of_isEmpty_right _ _ _
  · have : IsEmpty (elasticityIdx (k + 1)) :=
      isEmpty_elasticityIdx (by omega) (by omega) (by omega) (by omega)
    exact matMapsTo_of_isEmpty_left _ _ _

variable (𝕜) in
/-- The elasticity complex as a complex of constant-coefficient operators. -/
def elasticityConstCoeffComplex : ConstCoeffComplex (Fin 3 → ℝ) 𝕜 where
  ι := elasticityIdx
  A := elasticityOp 𝕜
  comp := elasticityOp_comp

variable (𝕜) in
/-- **The elasticity complex on an open `Ω ⊆ ℝ³`**:
`L²(Ω; 𝕜³) --sym grad--> L²(Ω; Sym) --inc--> L²(Ω; Sym) --div--> L²(Ω; 𝕜³)`, a complex of
constrained realizations. -/
def elasticityComplex {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) :
    ConstrainedComplex (Fin 3 → ℝ) 𝕜 Ω :=
  ConstrainedComplex.ofMatrices hΩ (elasticityConstCoeffComplex 𝕜) (elasticityMat 𝕜)
    isProjMat_elasticityMat elasticityOp_matMapsTo elasticityOp_formalAdj_matMapsTo

section OnOmega

variable {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω)

/-! ### Self-duality -/

theorem symGradOp_formalAdj_formalAdj_apply_eq (ψ : Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    (symGradOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.formalAdj.apply ψ =
      divSymOp.negOp.formalAdj.apply ψ := by
  rw [formalAdj_formalAdj, formalAdj_negOp, negOp_apply, divSymOp_formalAdj_apply, neg_neg]

theorem divSymOp_formalAdj_formalAdj_apply_eq {ψ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜}
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) :
    (divSymOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.formalAdj.apply ψ =
      symGradOp.negOp.formalAdj.apply ψ := by
  rw [formalAdj_formalAdj, formalAdj_negOp, negOp_apply, symGradOp_formalAdj_apply hψ, neg_neg]

theorem incOp_formalAdj_formalAdj_apply_eq {ψ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜}
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) :
    (incOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).formalAdj.formalAdj.apply ψ =
      incOp.formalAdj.apply ψ := by
  rw [formalAdj_formalAdj, incOp_formalAdj_apply hψ]

/-! The formal adjoints of `sym grad, inc, div` are `-div, inc, -sym grad`
(`ConstCoeffOp.negOp`). -/

/-- **Self-duality of the elasticity complex**, degree `0`: `((sym grad)_min)†` is the maximal
realization of `-div` on symmetric fields. -/
theorem elasticity_dual_minimalComplex_d₀ :
    (elasticityComplex 𝕜 hΩ).minimalComplex.dual.d 1 0 =
      divSymOp.negOp.maximalVia (symEmb 𝕜 Ω 3) (freeEmb 𝕜 Ω (Fin 3)) := by
  exact ((elasticityComplex 𝕜 hΩ).dual_minimalComplex_d 0).trans
    (maximalVia_congr _ _ _ fun ψ _ _ _ =>
      testField_congr _ _ (symGradOp_formalAdj_formalAdj_apply_eq ψ))

/-- Self-duality, degree `1`: `(inc_min)† = inc_max`. -/
theorem elasticity_dual_minimalComplex_d₁ :
    (elasticityComplex 𝕜 hΩ).minimalComplex.dual.d 2 1 =
      ((elasticityComplex 𝕜 hΩ).maximalComplex hΩ).d 1 2 := by
  exact ((elasticityComplex 𝕜 hΩ).dual_minimalComplex_d 1).trans
    ((maximalVia_congr _ _ _ fun _ hψ _ _ => testField_congr _ _
      (incOp_formalAdj_formalAdj_apply_eq fun i => (hψ i).contDiff)).trans
      ((elasticityComplex 𝕜 hΩ).maximalComplex_d hΩ 1).symm)

/-- Self-duality, degree `2`: `(div_min)†` on symmetric fields is the maximal realization of
`-sym grad`. -/
theorem elasticity_dual_minimalComplex_d₂ :
    (elasticityComplex 𝕜 hΩ).minimalComplex.dual.d 3 2 =
      symGradOp.negOp.maximalVia (freeEmb 𝕜 Ω (Fin 3)) (symEmb 𝕜 Ω 3) := by
  exact ((elasticityComplex 𝕜 hΩ).dual_minimalComplex_d 2).trans
    (maximalVia_congr _ _ _ fun _ hψ _ _ => testField_congr _ _
      (divSymOp_formalAdj_formalAdj_apply_eq fun i => (hψ i).contDiff))

end OnOmega

end Feec.Domain
