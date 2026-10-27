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
formula against test fields). A matrix with a left inverse is bounded below on `L²` fields
(`L2F.antilipschitz_ofMatrixCLM`), so the analytic BGG theorem for the BGG complex
(`Feec.BGG.HilbertData.bggVerdict`) applies once the matrices up to `J` have left inverses
(`ConstCoeffBGG.maximalData_bggVerdict`): the exact part is closed and the injectivity
hypotheses hold, and **the only hypotheses left are the regular decompositions after `J`**
(`Feec.BGG.HilbertData.RegularDecomposition`) and finite-dimensional cohomology of the rows.

This is the case of the Hessian, elasticity and div-div diagrams on every open `Ω ⊆ ℝ³`
(`hessianMaximalData_derivedVerdict`, `elasticityMaximalData_derivedVerdict`,
`divDivMaximalData_derivedVerdict`): **wherever the two `L²` de Rham complexes of `Ω` have
finite-dimensional cohomology and the regular decompositions `R(d) + R(S) = D(d)` hold after `J`,
the BGG complex has closed range and `dim Hⁱ ≤ dim Hⁱ(V) + dim Hⁱ(Ṽ)`**. The regular
decompositions of `H(curl)`, `H(div)` hold on bounded Lipschitz domains ([ArnoldHu2021], §2,
Theorem 3; [CapHu2024]) and are not formalized for the maximal realizations: the cube result
`Feec.Models.Cube.WeakSymmetry.curlPotential` is the regular decomposition of `H̊(curl)` on
`Q = (0, ½)³`, for the minimal complex in form proxies (`deRham`), and the decomposition of
`H(div)` has no counterpart. The finite-dimensionality of the cohomology of `deRhamVec m` is not
derived from the cube results on `deRham` either (no identification of the vector proxies with the
forms is formalized).

## Main definitions

* `Feec.Domain.L2F.ofMatrixCLM M`: a constant matrix acting on `L²(Ω; 𝕜^ι)`;
  `L2F.antilipschitz_ofMatrixCLM`: bounded below when `M` has a left inverse.
* `Feec.Domain.ConstCoeffBGG.maximalData`: the analytic BGG data of the maximal realizations.
* `hessianMaximalData`, `elasticityMaximalData`, `divDivMaximalData`.

## Main results

* `ConstCoeffOp.maximal_ofMatrixCLM`.
* `ConstCoeffBGG.maximalData_bggVerdict`.
* `hessianMaximalData_derivedVerdict`, `elasticityMaximalData_derivedVerdict`,
  `divDivMaximalData_derivedVerdict`.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §3 (bounded Hilbert complexes
  and linking maps, Theorem 6), §2 (regular decompositions, Theorem 3)
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
  filter_upwards [h1,
    coeFn_testField ((ConstCoeffOp.ofMatrix M : ConstCoeffOp E 𝕜 ι κ).isTestField_apply hφ) j,
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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem ofMatrixCLM_ofMatrixCLM {μ : Type*} [Fintype μ] (N : Matrix μ κ 𝕜) (M : Matrix κ ι 𝕜)
    (u : L2F 𝕜 Ω ι) : ofMatrixCLM N (ofMatrixCLM M u) = ofMatrixCLM (N * M) u := by
  refine (WithLp.ext_iff 2).2 (funext fun l => ?_)
  change ofMatrixCLM N (ofMatrixCLM M u) l = ofMatrixCLM (N * M) u l
  simp only [ofMatrixCLM_apply, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] [Fintype κ] in
theorem ofMatrixCLM_one [DecidableEq ι] (u : L2F 𝕜 Ω ι) : ofMatrixCLM (1 : Matrix ι ι 𝕜) u = u := by
  refine (WithLp.ext_iff 2).2 (funext fun l => ?_)
  change ofMatrixCLM 1 u l = u l
  simp [ofMatrixCLM_apply, Matrix.one_apply]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- **A matrix with a left inverse is bounded below on `L²` fields**: `‖u‖ ≤ ‖N‖ ‖M u‖` when
`N M = 1`. -/
theorem antilipschitz_ofMatrixCLM [DecidableEq ι] {M : Matrix κ ι 𝕜} {N : Matrix ι κ 𝕜}
    (h : N * M = 1) :
    AntilipschitzWith ‖(ofMatrixCLM N : L2F 𝕜 Ω κ →L[𝕜] L2F 𝕜 Ω ι)‖₊
      (ofMatrixCLM M : L2F 𝕜 Ω ι →L[𝕜] L2F 𝕜 Ω κ) :=
  (ofMatrixCLM M).antilipschitz_of_bound fun u => by
    calc ‖u‖ = ‖ofMatrixCLM N (ofMatrixCLM M u)‖ := by
          rw [ofMatrixCLM_ofMatrixCLM, h, ofMatrixCLM_one]
      _ ≤ _ := (ofMatrixCLM N).le_opNorm _

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
      rw [ConstCoeffComplex.maximalComplex_d]
      exact (ConstCoeffOp.maximal_ofMatrixCLM hΩ (B.anticomm_ofMatrix M hM k)
        ⟨φ, B.bot.maximalComplex_d hΩ k ▸ φ.2⟩).1)
    (fun k φ => by
      obtain ⟨hu, he⟩ := ConstCoeffOp.maximal_ofMatrixCLM hΩ (B.anticomm_ofMatrix M hM k)
        ⟨φ, B.bot.maximalComplex_d hΩ k ▸ φ.2⟩
      rw [LinearPMap.apply_eq_of_eq (B.top.maximalComplex_d hΩ (k + 1)) _ ⟨_, hu⟩ rfl, he,
        LinearPMap.apply_eq_of_eq (B.bot.maximalComplex_d hΩ k).symm _ φ rfl])

theorem maximalData_S (hΩ : IsOpen Ω) (k : ℤ) :
    (B.maximalData M hM hΩ).S k (k + 1) = L2F.ofMatrixCLM (M k) :=
  BGG.HilbertData.succCLM_succ (X := fun k => L2F 𝕜 Ω (B.bot.ι k))
    (Y := fun k => L2F 𝕜 Ω (B.top.ι k)) (fun k => L2F.ofMatrixCLM (M k)) k

/-- **Analytic BGG for the maximal realizations**: if the matrices `M k`, `k ≤ J`, have left
inverses, then wherever the maximal complexes of the two rows have finite-dimensional cohomology
and the regular decompositions after `J` hold, the BGG complex `bgg J` of their domain complexes
has closed range and `dim Hⁱ ≤ dim Hⁱ(V) + dim Hⁱ(Ṽ)`. -/
theorem maximalData_bggVerdict [∀ k, DecidableEq (B.bot.ι k)] (hΩ : IsOpen Ω) {J : ℤ}
    (hN : ∀ k ≤ J, ∃ N : Matrix (B.bot.ι k) (B.top.ι (k + 1)) 𝕜, N * M k = 1)
    (htop : (B.maximalData M hM hΩ).RegularDecomposition J)
    (i : ℤ) [FiniteDimensional 𝕜 ((B.top.maximalComplex hΩ).cohomology i)]
    [FiniteDimensional 𝕜 ((B.bot.maximalComplex hΩ).cohomology i)] :
    (B.maximalData M hM hΩ).DerivedVerdict (J < ·) (· < J) i :=
  have : FiniteDimensional 𝕜 ((B.maximalData M hM hΩ).H.cohomology i) :=
    ‹FiniteDimensional 𝕜 ((B.top.maximalComplex hΩ).cohomology i)›
  have : FiniteDimensional 𝕜 ((B.maximalData M hM hΩ).Ht.cohomology i) :=
    ‹FiniteDimensional 𝕜 ((B.bot.maximalComplex hΩ).cohomology i)›
  (B.maximalData M hM hΩ).bggVerdict (fun k hk => by
    obtain ⟨N, hN⟩ := hN k hk
    rw [maximalData_S]
    exact ⟨_, L2F.antilipschitz_ofMatrixCLM hN⟩) htop i

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

/-- `I` has a left inverse (and the connecting matrices before it act on zero spaces). -/
theorem hessianSMat_leftInv :
    ∀ k : ℤ, k ≤ 0 → ∃ N : Matrix (vecIdx 3 k) (vecIdx 1 (k + 1)) 𝕜,
      N * (hessianSMat k : Matrix _ _ 𝕜) = 1
  | .ofNat 0, _ => ⟨hessN0, hessN0_mul_hessS0⟩
  | .ofNat (_ + 1), h => absurd h (by simp only [Int.ofNat_eq_natCast] at h ⊢; omega)
  | .negSucc _, _ => ⟨0, Matrix.ext fun i => isEmptyElim (α := Empty) i⟩

/-- `-mskw` and `T - tr` have left inverses. -/
theorem elasticitySMat_leftInv :
    ∀ k : ℤ, k ≤ 1 → ∃ N : Matrix (vecIdx 3 k) (vecIdx 3 (k + 1)) 𝕜,
      N * (elasticitySMat k : Matrix _ _ 𝕜) = 1
  | .ofNat 0, _ => ⟨elN0, elN0_mul_elS0⟩
  | .ofNat 1, _ => ⟨elN1, elN1_mul_elS1⟩
  | .ofNat (_ + 2), h => absurd h (by simp only [Int.ofNat_eq_natCast] at h ⊢; omega)
  | .negSucc _, _ => ⟨0, Matrix.ext fun i => isEmptyElim (α := Empty) i⟩

/-- `· I`, `-mskw` and `I` have left inverses. -/
theorem divDivSMat_leftInv :
    ∀ k : ℤ, k ≤ 2 → ∃ N : Matrix (vecIdx 1 k) (vecIdx 3 (k + 1)) 𝕜,
      N * (divDivSMat k : Matrix _ _ 𝕜) = 1
  | .ofNat 0, _ => ⟨ddN0, ddN0_mul_ddS0⟩
  | .ofNat 1, _ => ⟨ddN1, ddN1_mul_ddS1⟩
  | .ofNat 2, _ => ⟨ddN2, ddN2_mul_ddS2⟩
  | .ofNat (_ + 3), h => absurd h (by simp only [Int.ofNat_eq_natCast] at h ⊢; omega)
  | .negSucc _, _ => ⟨0, Matrix.ext fun i => isEmptyElim (α := Empty) i⟩

/-- **The analytic BGG theorem for the Hessian diagram on `Ω`**: wherever the scalar and
`𝕜³`-valued `L²` de Rham complexes of `Ω` have finite-dimensional cohomology and the regular
decompositions of `H(curl)`, `H(div)`, `L²` after `0` hold, the Hessian BGG complex has closed
range at `i`, its cohomology of dimension at most the sum of those of the two rows. -/
theorem hessianMaximalData_derivedVerdict (hΩ : IsOpen Ω)
    (htop : (hessianMaximalData 𝕜 hΩ).RegularDecomposition 0) (i : ℤ)
    [FiniteDimensional 𝕜 (((deRhamVec 𝕜 1).maximalComplex hΩ).cohomology i)]
    [FiniteDimensional 𝕜 (((deRhamVec 𝕜 3).maximalComplex hΩ).cohomology i)] :
    (hessianMaximalData 𝕜 hΩ).DerivedVerdict (0 < ·) (· < 0) i :=
  (hessianBGG 𝕜).maximalData_bggVerdict hessianSMat hessianS_apply_eq hΩ hessianSMat_leftInv
    htop i

/-- **The analytic BGG theorem for the elasticity diagram on `Ω`**, under the regular
decompositions after `1`. -/
theorem elasticityMaximalData_derivedVerdict (hΩ : IsOpen Ω)
    (htop : (elasticityMaximalData 𝕜 hΩ).RegularDecomposition 1) (i : ℤ)
    [FiniteDimensional 𝕜 (((deRhamVec 𝕜 3).maximalComplex hΩ).cohomology i)] :
    (elasticityMaximalData 𝕜 hΩ).DerivedVerdict (1 < ·) (· < 1) i :=
  (elasticityBGG 𝕜).maximalData_bggVerdict elasticitySMat elasticityS_apply_eq hΩ
    elasticitySMat_leftInv htop i

/-- **The analytic BGG theorem for the div-div diagram on `Ω`**, under the regular decompositions
after `2`. -/
theorem divDivMaximalData_derivedVerdict (hΩ : IsOpen Ω)
    (htop : (divDivMaximalData 𝕜 hΩ).RegularDecomposition 2) (i : ℤ)
    [FiniteDimensional 𝕜 (((deRhamVec 𝕜 3).maximalComplex hΩ).cohomology i)]
    [FiniteDimensional 𝕜 (((deRhamVec 𝕜 1).maximalComplex hΩ).cohomology i)] :
    (divDivMaximalData 𝕜 hΩ).DerivedVerdict (2 < ·) (· < 2) i :=
  (divDivBGG 𝕜).maximalData_bggVerdict divDivSMat divDivS_apply_eq hΩ divDivSMat_leftInv htop i

end Instances

end Feec.Domain
