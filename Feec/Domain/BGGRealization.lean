module

public import Feec.Domain.DivDivBGG
public import Feec.Domain.HessianBGG
public import Feec.HilbertComplex.BGG.DomainData

/-!
# `L²` realizations of BGG data of constant-coefficient operators

BGG data of constant-coefficient operators whose connecting operators are constant matrices
(`ConstCoeffBGG` with `S k = M k` pointwise) are analytic BGG data (`Feec.BGG.HilbertData`) on
the maximal (weak) realizations of the two complexes on every open `Ω`
(**`ConstCoeffBGG.maximalData`**): a constant matrix maps `D(B_max)` into `D(A_max)` when
`A M = -M' B` on smooth fields, with `A_max (M u) = -M' (B_max u)`
(`ConstCoeffOp.maximal_ofMatrixCLM`; the identity passes to the formal adjoints by Green's
formula against test fields). Hence the analytic BGG theorem
(`Feec.BGG.HilbertData.derivedVerdict`) applies to the Hessian, elasticity and div-div diagrams
on every open `Ω ⊆ ℝ³` (`hessianMaximalData_derivedVerdict`,
`elasticityMaximalData_derivedVerdict`, `divDivMaximalData_derivedVerdict`): **wherever the two
`L²` de Rham complexes of `Ω` have finite-dimensional cohomology, and the elimination hypotheses
hold between their domains (with closed exact part), the derived complex is a closed Hilbert
complex with closed range and `dim Hⁱ ≤ dim Hⁱ(V) + dim Hⁱ(Ṽ)`**. The elimination hypotheses
`R(d) + R(S) = D(d)` are regular decompositions of `H(curl)`, `H(div)` (for Lipschitz `Ω`,
[ArnoldHu2021], §5, [CapHu2024]); they are not formalized here.

## Main definitions

* `Feec.Domain.L2F.ofMatrixCLM M`: a constant matrix acting on `L²(Ω; 𝕜^ι)`.
* `Feec.Domain.ConstCoeffBGG.maximalData`: the analytic BGG data of the maximal realizations.
* `hessianMaximalData`, `elasticityMaximalData`, `divDivMaximalData`.

## Main results

* `ConstCoeffOp.maximal_ofMatrixCLM`.
* `hessianMaximalData_derivedVerdict`, `elasticityMaximalData_derivedVerdict`,
  `divDivMaximalData_derivedVerdict`.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §5 (bounded Hilbert complexes
  and the analytic BGG construction)
* [A. Čap, K. Hu, *BGG sequences with weak regularity and applications*][CapHu2024] (BGG
  sequences of Sobolev spaces)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], §6.2 (the maximal realizations)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff ComplexConjugate
open MeasureTheory

@[expose] public noncomputable section

namespace Feec.Domain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type*} [RCLike 𝕜]
  [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
  {Ω : Set E} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ## Constant matrices on `L²` fields -/

namespace L2F

/-- A constant matrix `M : 𝕜^ι → 𝕜^κ` acting on `L²(Ω; 𝕜^ι)`. -/
def ofMatrixCLM (M : Matrix κ ι 𝕜) : L2F 𝕜 Ω ι →L[𝕜] L2F 𝕜 Ω κ :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : κ => L2 𝕜 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => ∑ i, M j i • PiLp.proj 2 (fun _ : ι => L2 𝕜 Ω) i)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] [Fintype κ] in
theorem ofMatrixCLM_apply (M : Matrix κ ι 𝕜) (u : L2F 𝕜 Ω ι) (j : κ) :
    ofMatrixCLM M u j = ∑ i, M j i • u i := by
  simp [ofMatrixCLM]

omit [FiniteDimensional ℝ E] [Fintype κ] in
/-- `ofMatrixCLM` acts pointwise on test fields. -/
theorem ofMatrixCLM_testField (M : Matrix κ ι 𝕜) {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) :
    ofMatrixCLM M (testField hφ) =
      testField ((ConstCoeffOp.ofMatrix M : ConstCoeffOp E 𝕜 ι κ).isTestField_apply hφ) := by
  refine (WithLp.ext_iff 2).2 (funext fun j => Lp.ext ?_)
  rw [ofMatrixCLM_apply]
  have h1 := Lp.coeFn_fun_finsetSum (μ := volume.restrict Ω) Finset.univ
    (fun i => M j i • testField hφ i)
  filter_upwards [h1, coeFn_testField ((ConstCoeffOp.ofMatrix M : ConstCoeffOp E 𝕜 ι κ).isTestField_apply hφ) j,
    ae_all_iff.2 fun i => Lp.coeFn_smul (M j i) (testField hφ i),
    ae_all_iff.2 fun i => coeFn_testField hφ i] with x h1 h2 h3 h4
  rw [h1, h2, ConstCoeffOp.ofMatrix_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h3 i, Pi.smul_apply, h4 i, smul_eq_mul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- `⟪M u, v⟫ = ⟪u, Mᴴ v⟫`. -/
theorem inner_ofMatrixCLM (M : Matrix κ ι 𝕜) (u : L2F 𝕜 Ω ι) (v : L2F 𝕜 Ω κ) :
    ⟪ofMatrixCLM M u, v⟫_𝕜 = ⟪u, ofMatrixCLM M.conjTranspose v⟫_𝕜 := by
  rw [L2F.inner_def, L2F.inner_def]
  simp only [ofMatrixCLM_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  rfl

end L2F

/-! ## Constant matrices map maximal domains to maximal domains -/

/-- The formal adjoint of `A M = -M' B` on test fields: `Mᴴ Aᵗ φ = -Bᵗ M'ᴴ φ`. -/
theorem ConstCoeffOp.testField_ofMatrix_formalAdj (hΩ : IsOpen Ω) {ι' κ' : Type*} [Fintype ι']
    [Fintype κ'] {A : ConstCoeffOp E 𝕜 ι' κ'} {B : ConstCoeffOp E 𝕜 ι κ} {M : Matrix ι' ι 𝕜}
    {M' : Matrix κ' κ 𝕜}
    (h : ∀ f : ι → E → 𝕜, (∀ i, ContDiff ℝ ∞ (f i)) →
      A.apply ((ConstCoeffOp.ofMatrix M).apply f) = -(ConstCoeffOp.ofMatrix M').apply (B.apply f))
    {φ : κ' → E → 𝕜} (hφ : IsTestField Ω φ) :
    L2F.ofMatrixCLM M.conjTranspose (testField (A.formalAdj.isTestField_apply hφ)) =
      -testField (B.formalAdj.isTestField_apply
        ((ConstCoeffOp.ofMatrix M'.conjTranspose).isTestField_apply hφ)) := by
  refine L2F.ext_of_forall_inner_testField hΩ fun g hg => ?_
  have hMg := (ConstCoeffOp.ofMatrix M : ConstCoeffOp E 𝕜 ι ι').isTestField_apply hg
  have hBg := B.isTestField_apply hg
  have e1 : ⟪L2F.ofMatrixCLM M.conjTranspose (testField (A.formalAdj.isTestField_apply hφ)),
      testField hg⟫_𝕜 = conj ⟪testField (A.isTestField_apply hMg), testField hφ⟫_𝕜 := by
    rw [L2F.inner_ofMatrixCLM, Matrix.conjTranspose_conjTranspose, L2F.ofMatrixCLM_testField,
      ← inner_conj_symm, A.inner_testField_apply_testField hMg hφ]
  have e2 : testField (A.isTestField_apply hMg) = -L2F.ofMatrixCLM M' (testField hBg) := by
    have hneg := ((ConstCoeffOp.ofMatrix M' : ConstCoeffOp E 𝕜 κ κ').isTestField_apply hBg).smul
      (-1 : 𝕜)
    rw [testField_congr _ hneg (by rw [h g fun i => (hg i).contDiff, neg_one_smul]),
      testField_smul, neg_one_smul, L2F.ofMatrixCLM_testField]
  rw [e1, e2, inner_neg_left, L2F.inner_ofMatrixCLM, L2F.ofMatrixCLM_testField,
    B.inner_testField_apply_testField hg, map_neg, inner_conj_symm, inner_neg_left]

/-- **A constant matrix maps `D(B_max)` into `D(A_max)`** when `A M = -M' B` on smooth fields,
with `A_max (M u) = -M' (B_max u)`. -/
theorem ConstCoeffOp.maximal_ofMatrixCLM (hΩ : IsOpen Ω) {ι' κ' : Type*} [Fintype ι']
    [Fintype κ'] {A : ConstCoeffOp E 𝕜 ι' κ'} {B : ConstCoeffOp E 𝕜 ι κ} {M : Matrix ι' ι 𝕜}
    {M' : Matrix κ' κ 𝕜}
    (h : ∀ f : ι → E → 𝕜, (∀ i, ContDiff ℝ ∞ (f i)) →
      A.apply ((ConstCoeffOp.ofMatrix M).apply f) = -(ConstCoeffOp.ofMatrix M').apply (B.apply f))
    (u : (B.maximal Ω).domain) :
    ∃ hu : L2F.ofMatrixCLM M (u : L2F 𝕜 Ω ι) ∈ (A.maximal Ω).domain,
      A.maximal Ω ⟨_, hu⟩ = -L2F.ofMatrixCLM M' (B.maximal Ω u) := by
  have hw : ∀ φ : κ' → E → 𝕜, ∀ hφ : IsTestField Ω φ,
      ⟪-L2F.ofMatrixCLM M' (B.maximal Ω u), testField hφ⟫_𝕜 =
        ⟪L2F.ofMatrixCLM M (u : L2F 𝕜 Ω ι), testField (A.formalAdj.isTestField_apply hφ)⟫_𝕜 :=
    fun φ hφ => by
      rw [inner_neg_left, L2F.inner_ofMatrixCLM, L2F.ofMatrixCLM_testField,
        B.maximal_inner_testField hΩ u, L2F.inner_ofMatrixCLM,
        ConstCoeffOp.testField_ofMatrix_formalAdj hΩ h hφ, inner_neg_right]
  have hu := (A.mem_maximal_domain_iff hΩ).2 ⟨_, hw⟩
  exact ⟨hu, A.maximal_apply_eq hΩ ⟨_, hu⟩ hw⟩

/-! ## The analytic BGG data of the maximal realizations -/

namespace ConstCoeffBGG

variable (B : ConstCoeffBGG E 𝕜) (M : ∀ k, Matrix (B.top.ι (k + 1)) (B.bot.ι k) 𝕜)
  (hM : ∀ k f, (B.S k).apply f = (ConstCoeffOp.ofMatrix (M k)).apply f)
include hM

omit [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem anticomm_ofMatrix (k : ℤ) (f : B.bot.ι k → E → 𝕜) (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (B.top.A (k + 1)).apply ((ConstCoeffOp.ofMatrix (M k)).apply f) =
      -(ConstCoeffOp.ofMatrix (M (k + 1))).apply ((B.bot.A k).apply f) := by
  rw [← hM, ← hM]
  exact B.anticomm k f hf

/-- **The analytic BGG data of the maximal realizations** on an open `Ω`: the maximal complexes
of the two rows, linked by the constant matrices `M k` acting on `L²` fields. -/
def maximalData (hΩ : IsOpen Ω) :
    BGG.HilbertData 𝕜 (ComplexShape.up ℤ) (fun k => L2F 𝕜 Ω (B.top.ι k))
      (fun k => L2F 𝕜 Ω (B.bot.ι k)) :=
  BGG.HilbertData.ofSucc (B.top.maximalComplex hΩ) (B.bot.maximalComplex hΩ)
    (fun k => L2F.ofMatrixCLM (M k))
    (fun k φ => by
      have key : ∀ x : L2F 𝕜 Ω (B.bot.ι k),
          x ∈ ((B.bot.maximalComplex hΩ).d k (k + 1)).domain →
            x ∈ ((B.bot.A k).maximal Ω).domain := fun x hx => by
        rwa [ConstCoeffComplex.maximalComplex_d] at hx
      have hφ := key _ φ.2
      rw [ConstCoeffComplex.maximalComplex_d]
      exact (ConstCoeffOp.maximal_ofMatrixCLM hΩ (B.anticomm_ofMatrix M hM k) ⟨_, hφ⟩).1)
    (fun k φ => by
      have key : ∀ x : L2F 𝕜 Ω (B.bot.ι k),
          x ∈ ((B.bot.maximalComplex hΩ).d k (k + 1)).domain →
            x ∈ ((B.bot.A k).maximal Ω).domain := fun x hx => by
        rwa [ConstCoeffComplex.maximalComplex_d] at hx
      have hφ := key _ φ.2
      obtain ⟨hu, he⟩ := ConstCoeffOp.maximal_ofMatrixCLM hΩ (B.anticomm_ofMatrix M hM k)
        ⟨_, hφ⟩
      rw [LinearPMap.apply_eq_of_eq (B.top.maximalComplex_d hΩ (k + 1)) _ ⟨_, hu⟩ rfl, he,
        LinearPMap.apply_eq_of_eq (B.bot.maximalComplex_d hΩ k).symm ⟨_, hφ⟩ φ rfl])

end ConstCoeffBGG

/-! ## The Hessian, elasticity and div-div diagrams on an open `Ω ⊆ ℝ³` -/

section Instances

open ConstCoeffOp

variable {Ω : Set (Fin 3 → ℝ)}

/-- The connecting matrices `I`, `2 vskw`, `tr` of the Hessian diagram. -/
def hessianSMat : ∀ k : ℤ, Matrix (vecIdx 1 (k + 1)) (vecIdx 3 k) 𝕜
  | .ofNat 0 => hessS0
  | .ofNat 1 => hessS1
  | .ofNat 2 => hessS2
  | .ofNat (_ + 3) => 0
  | .negSucc _ => 0

/-- The connecting matrices `-mskw`, `T - tr`, `2 vskw` of the elasticity diagram. -/
def elasticitySMat : ∀ k : ℤ, Matrix (vecIdx 3 (k + 1)) (vecIdx 3 k) 𝕜
  | .ofNat 0 => elS0
  | .ofNat 1 => elS1
  | .ofNat 2 => elS2
  | .ofNat (_ + 3) => 0
  | .negSucc _ => 0

/-- The connecting matrices `· I`, `-mskw`, `I` of the div-div diagram. -/
def divDivSMat : ∀ k : ℤ, Matrix (vecIdx 3 (k + 1)) (vecIdx 1 k) 𝕜
  | .ofNat 0 => ddS0
  | .ofNat 1 => ddS1
  | .ofNat 2 => ddS2
  | .ofNat (_ + 3) => 0
  | .negSucc _ => 0

theorem ofMatrix_zero_apply {ι κ : Type*} [Fintype ι] (f : ι → (Fin 3 → ℝ) → 𝕜) :
    (ofMatrix (0 : Matrix κ ι 𝕜) : ConstCoeffOp (Fin 3 → ℝ) 𝕜 ι κ).apply f =
      (zeroOp ι κ).apply f := by
  funext j x
  rw [ofMatrix_apply]
  simp [ConstCoeffOp.apply, zeroOp]

theorem hessianS_apply_eq (k : ℤ) (f : vecIdx 3 k → (Fin 3 → ℝ) → 𝕜) :
    (hessianS 𝕜 k).apply f = (ofMatrix (hessianSMat k)).apply f := by
  match k with
  | .ofNat 0 | .ofNat 1 | .ofNat 2 => rfl
  | .ofNat (_ + 3) | .negSucc _ => exact (ofMatrix_zero_apply f).symm

theorem elasticityS_apply_eq (k : ℤ) (f : vecIdx 3 k → (Fin 3 → ℝ) → 𝕜) :
    (elasticityS 𝕜 k).apply f = (ofMatrix (elasticitySMat k)).apply f := by
  match k with
  | .ofNat 0 | .ofNat 1 | .ofNat 2 => rfl
  | .ofNat (_ + 3) | .negSucc _ => exact (ofMatrix_zero_apply f).symm

theorem divDivS_apply_eq (k : ℤ) (f : vecIdx 1 k → (Fin 3 → ℝ) → 𝕜) :
    (divDivS 𝕜 k).apply f = (ofMatrix (divDivSMat k)).apply f := by
  match k with
  | .ofNat 0 | .ofNat 1 | .ofNat 2 => rfl
  | .ofNat (_ + 3) | .negSucc _ => exact (ofMatrix_zero_apply f).symm

variable (𝕜) in
/-- **The Hessian diagram on `L²(Ω)`**: the maximal de Rham complexes of `Ω` with values in `𝕜`
and `𝕜³`, linked by `I`, `2 vskw`, `tr`. -/
abbrev hessianMaximalData (hΩ : IsOpen Ω) :=
  (hessianBGG 𝕜).maximalData hessianSMat hessianS_apply_eq hΩ

variable (𝕜) in
/-- **The elasticity diagram on `L²(Ω)`**: two copies of the maximal de Rham complex of `Ω` with
values in `𝕜³`, linked by `-mskw`, `T - tr`, `2 vskw`. -/
abbrev elasticityMaximalData (hΩ : IsOpen Ω) :=
  (elasticityBGG 𝕜).maximalData elasticitySMat elasticityS_apply_eq hΩ

variable (𝕜) in
/-- **The div-div diagram on `L²(Ω)`**: the maximal de Rham complexes of `Ω` with values in `𝕜³`
and `𝕜`, linked by `· I`, `-mskw`, `I`. -/
abbrev divDivMaximalData (hΩ : IsOpen Ω) :=
  (divDivBGG 𝕜).maximalData divDivSMat divDivS_apply_eq hΩ

/-- **The analytic BGG theorem for the Hessian diagram on `Ω`**: wherever the scalar and
`𝕜³`-valued `L²` de Rham complexes of `Ω` have finite-dimensional cohomology (and the eliminations
hold between their domains, with closed exact part), the Hessian BGG complex is a closed Hilbert
complex with closed range at `i`, its cohomology of dimension at most the sum of those of the two
rows. -/
theorem hessianMaximalData_derivedVerdict (hΩ : IsOpen Ω)
    (hΔ : ∀ i, IsClosed ((hessianMaximalData 𝕜 hΩ).domainData.Δ (· < 0) i :
      Set ((hessianMaximalData 𝕜 hΩ).H.domainSpace i × (hessianMaximalData 𝕜 hΩ).Ht.domainSpace i)))
    (h : (hessianMaximalData 𝕜 hΩ).domainData.Eliminates (0 < ·) (· < 0)) (i : ℤ)
    [h₁ : FiniteDimensional 𝕜 (((deRhamVec 𝕜 1).maximalComplex hΩ).cohomology i)]
    [h₃ : FiniteDimensional 𝕜 (((deRhamVec 𝕜 3).maximalComplex hΩ).cohomology i)] :
    (hessianMaximalData 𝕜 hΩ).DerivedVerdict (0 < ·) (· < 0) i :=
  have : FiniteDimensional 𝕜 ((hessianMaximalData 𝕜 hΩ).H.cohomology i) := h₁
  have : FiniteDimensional 𝕜 ((hessianMaximalData 𝕜 hΩ).Ht.cohomology i) := h₃
  (hessianMaximalData 𝕜 hΩ).derivedVerdict hΔ h i

/-- **The analytic BGG theorem for the elasticity diagram on `Ω`.** -/
theorem elasticityMaximalData_derivedVerdict (hΩ : IsOpen Ω)
    (hΔ : ∀ i, IsClosed ((elasticityMaximalData 𝕜 hΩ).domainData.Δ (· < 1) i :
      Set ((elasticityMaximalData 𝕜 hΩ).H.domainSpace i ×
        (elasticityMaximalData 𝕜 hΩ).Ht.domainSpace i)))
    (h : (elasticityMaximalData 𝕜 hΩ).domainData.Eliminates (1 < ·) (· < 1)) (i : ℤ)
    [h₃ : FiniteDimensional 𝕜 (((deRhamVec 𝕜 3).maximalComplex hΩ).cohomology i)] :
    (elasticityMaximalData 𝕜 hΩ).DerivedVerdict (1 < ·) (· < 1) i :=
  have : FiniteDimensional 𝕜 ((elasticityMaximalData 𝕜 hΩ).H.cohomology i) := h₃
  have : FiniteDimensional 𝕜 ((elasticityMaximalData 𝕜 hΩ).Ht.cohomology i) := h₃
  (elasticityMaximalData 𝕜 hΩ).derivedVerdict hΔ h i

/-- **The analytic BGG theorem for the div-div diagram on `Ω`.** -/
theorem divDivMaximalData_derivedVerdict (hΩ : IsOpen Ω)
    (hΔ : ∀ i, IsClosed ((divDivMaximalData 𝕜 hΩ).domainData.Δ (· < 2) i :
      Set ((divDivMaximalData 𝕜 hΩ).H.domainSpace i × (divDivMaximalData 𝕜 hΩ).Ht.domainSpace i)))
    (h : (divDivMaximalData 𝕜 hΩ).domainData.Eliminates (2 < ·) (· < 2)) (i : ℤ)
    [h₃ : FiniteDimensional 𝕜 (((deRhamVec 𝕜 3).maximalComplex hΩ).cohomology i)]
    [h₁ : FiniteDimensional 𝕜 (((deRhamVec 𝕜 1).maximalComplex hΩ).cohomology i)] :
    (divDivMaximalData 𝕜 hΩ).DerivedVerdict (2 < ·) (· < 2) i :=
  have : FiniteDimensional 𝕜 ((divDivMaximalData 𝕜 hΩ).H.cohomology i) := h₃
  have : FiniteDimensional 𝕜 ((divDivMaximalData 𝕜 hΩ).Ht.cohomology i) := h₁
  (divDivMaximalData 𝕜 hΩ).derivedVerdict hΔ h i

end Instances

end Feec.Domain
