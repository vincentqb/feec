module

public import Feec.Domain.DivDivBGG
public import Feec.Domain.HessianBGG
public import Feec.Domain.Scaling
public import Feec.HilbertComplex.BGG.DomainData

/-!
# `L²` realizations of BGG data of constant-coefficient operators

BGG data of constant-coefficient operators linked by constant matrices give analytic BGG data on the
maximal realizations on every open `Ω`; for the Hessian, elasticity and div-div diagrams on a
nonempty open `Ω ⊆ ℝ³`, `Sᴶ` is not onto between the domains.

## Main results

* `ConstCoeffBGG.maximalData_bggVerdict`: the analytic BGG theorem for the maximal realizations.
* `hessianMaximalData_derivedVerdict` and its analogues: the Hessian, elasticity and div-div cases.
* `hessianMaximalData_not_surjective` and its analogues: `Sᴶ` is not onto between the domains.
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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] [Fintype ι] [Fintype κ] in
theorem ConstCoeffOp.isHomogeneous_ofMatrix (M : Matrix κ ι 𝕜) :
    (ConstCoeffOp.ofMatrix M : ConstCoeffOp E 𝕜 ι κ).IsHomogeneous 0 := fun j i t ht => by
  rw [show t = ([], M j i) from List.mem_singleton.1 ht]; rfl

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

/-- **The analytic BGG data of the maximal realizations** on an open `Ω`. -/
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

/-- **Analytic BGG for the maximal realizations**: `HilbertData.BGGVerdict J i`. -/
theorem maximalData_bggVerdict [∀ k, DecidableEq (B.bot.ι k)] (hΩ : IsOpen Ω) {J : ℤ}
    (hN : ∀ k ≤ J, ∃ N : Matrix (B.bot.ι k) (B.top.ι (k + 1)) 𝕜, N * M k = 1)
    (htop : (B.maximalData M hM hΩ).RegularDecomposition J)
    (i : ℤ) [FiniteDimensional 𝕜 ((B.top.maximalComplex hΩ).cohomology i)]
    [FiniteDimensional 𝕜 ((B.bot.maximalComplex hΩ).cohomology i)] :
    (B.maximalData M hM hΩ).BGGVerdict J i :=
  have : FiniteDimensional 𝕜 ((B.maximalData M hM hΩ).H.cohomology i) :=
    ‹FiniteDimensional 𝕜 ((B.top.maximalComplex hΩ).cohomology i)›
  have : FiniteDimensional 𝕜 ((B.maximalData M hM hΩ).Ht.cohomology i) :=
    ‹FiniteDimensional 𝕜 ((B.bot.maximalComplex hΩ).cohomology i)›
  (B.maximalData M hM hΩ).bggVerdict (fun k hk => by
    obtain ⟨N, hN⟩ := hN k hk
    rw [maximalData_S]
    exact ⟨_, L2F.antilipschitz_ofMatrixCLM hN⟩) htop i

theorem not_surjective_maximalData_domainS (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {k : ℤ}
    [DecidableEq (B.bot.ι k)] {N : Matrix (B.bot.ι k) (B.top.ι (k + 1)) 𝕜} (hN : N * M k = 1)
    {a r : ℕ} (htop : (B.top.A (k + 1)).IsHomogeneous a) (hbot : (B.bot.A k).IsHomogeneous r)
    (hr : 0 < r) {ψ : B.bot.ι k → E → 𝕜} (hψ : IsTestField Set.univ ψ)
    (hSψ : (B.top.A (k + 1)).apply ((B.S k).apply ψ) = 0) (hdψ : (B.bot.A k).apply ψ ≠ 0) :
    ¬ Function.Surjective ((B.maximalData M hM hΩ).domainData.S k (k + 1)) := by
  refine (B.maximalData M hM hΩ).not_surjective_domainS (k := k + 1 + 1) rfl rfl (by
    rw [maximalData_S]; exact (L2F.antilipschitz_ofMatrixCLM hN).injective) fun C => ?_
  obtain ⟨α, β, hφ, hlt⟩ := ConstCoeffOp.exists_lt_norm_testField_comp_aff hΩ hne hbot hr hψ hdψ C
  have hMφ := (ConstCoeffOp.ofMatrix (M k)).isTestField_apply hφ
  -- `Aᵏ⁺¹ Sᵏ φ = 0` for the rescaling `φ` of `ψ`
  have h0 : (B.top.A (k + 1)).apply ((ConstCoeffOp.ofMatrix (M k)).apply
      fun i x => ψ i (aff α β x)) = 0 := by
    rw [ConstCoeffOp.apply_comp_aff (ConstCoeffOp.isHomogeneous_ofMatrix (M k))
      (fun i => (hψ i).contDiff) α β]
    simp only [pow_zero, RCLike.ofReal_one, one_mul]
    rw [ConstCoeffOp.apply_comp_aff htop
      (fun i => ((ConstCoeffOp.ofMatrix (M k)).isTestField_apply hψ i).contDiff) α β, ← hM, hSψ]
    funext j x
    simp
  have hmin := (B.bot.A k).testField_mem_minimal_domain hΩ hφ
  have hmax := ((B.bot.A k).minimal_le_maximal hΩ).1 hmin
  have hmem : testField hφ ∈ ((B.maximalData M hM hΩ).Ht.d k (k + 1)).domain := by
    change testField hφ ∈ ((B.bot.maximalComplex hΩ).d k (k + 1)).domain
    rw [ConstCoeffComplex.maximalComplex_d]; exact hmax
  have hminM := (B.top.A (k + 1)).testField_mem_minimal_domain hΩ hMφ
  have hmaxM := ((B.top.A (k + 1)).minimal_le_maximal hΩ).1 hminM
  have hιw : (B.maximalData M hM hΩ).S k (k + 1) (testField hφ) = testField hMφ := by
    rw [maximalData_S, L2F.ofMatrixCLM_testField]
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · change (B.top.maximalComplex hΩ).d (k + 1) (k + 1 + 1) ⟨_, _⟩ = 0
    rw [LinearPMap.apply_eq_of_eq (B.top.maximalComplex_d hΩ (k + 1)) _ ⟨_, hmaxM⟩ hιw,
      ← ((B.top.A (k + 1)).minimal_le_maximal hΩ).2 (x := ⟨_, hminM⟩) rfl,
      (B.top.A (k + 1)).minimal_testField hΩ hMφ, testField_congr _ IsTestField.zero h0,
      testField_zero]
  · change C * ‖testField hφ‖ < ‖(B.bot.maximalComplex hΩ).d k (k + 1) ⟨_, hmem⟩‖
    rw [LinearPMap.apply_eq_of_eq (B.bot.maximalComplex_d hΩ k) _ ⟨_, hmax⟩ rfl,
      ← ((B.bot.A k).minimal_le_maximal hΩ).2 (x := ⟨_, hmin⟩) rfl,
      (B.bot.A k).minimal_testField hΩ hφ]
    exact hlt

theorem not_injSurjWith_maximalData (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {k : ℤ}
    [DecidableEq (B.bot.ι k)] {N : Matrix (B.bot.ι k) (B.top.ι (k + 1)) 𝕜} (hN : N * M k = 1)
    {a r : ℕ} (htop : (B.top.A (k + 1)).IsHomogeneous a) (hbot : (B.bot.A k).IsHomogeneous r)
    (hr : 0 < r) {ψ : B.bot.ι k → E → 𝕜} (hψ : IsTestField Set.univ ψ)
    (hSψ : (B.top.A (k + 1)).apply ((B.S k).apply ψ) = 0) (hdψ : (B.bot.A k).apply ψ ≠ 0)
    {J : ℤ} (hJ : J ≤ k) (t : ∀ i j, (B.maximalData M hM hΩ).H.domainSpace j →ₗ[𝕜]
      (B.maximalData M hM hΩ).Ht.domainSpace i) :
    ¬ (B.maximalData M hM hΩ).domainData.InjSurjWith J t := fun h =>
  B.not_surjective_maximalData_domainS M hM hΩ hne hN htop hbot hr hψ hSψ hdψ fun w =>
    ⟨t k (k + 1) w, h.S_t' hJ w⟩

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
/-- **The Hessian diagram on `L²(Ω)`**, linked by `I`, `2 vskw`, `tr`. -/
abbrev hessianMaximalData (hΩ : IsOpen Ω) :=
  (hessianBGG 𝕜).maximalData hessianSMat hessianS_apply_eq hΩ

variable (𝕜) in
/-- **The elasticity diagram on `L²(Ω)`**, linked by `-mskw`, `T - tr`, `2 vskw`. -/
abbrev elasticityMaximalData (hΩ : IsOpen Ω) :=
  (elasticityBGG 𝕜).maximalData elasticitySMat elasticityS_apply_eq hΩ

variable (𝕜) in
/-- **The div-div diagram on `L²(Ω)`**, linked by `· I`, `-mskw`, `I`. -/
abbrev divDivMaximalData (hΩ : IsOpen Ω) :=
  (divDivBGG 𝕜).maximalData divDivSMat divDivS_apply_eq hΩ

theorem hessianSMat_leftInv :
    ∀ k : ℤ, k ≤ 0 → ∃ N : Matrix (vecIdx 3 k) (vecIdx 1 (k + 1)) 𝕜,
      N * (hessianSMat k : Matrix _ _ 𝕜) = 1
  | .ofNat 0, _ => ⟨hessN0, hessN0_mul_hessS0⟩
  | .ofNat (_ + 1), h => absurd h (by simp only [Int.ofNat_eq_natCast] at h ⊢; omega)
  | .negSucc _, _ => ⟨0, Matrix.ext fun i => isEmptyElim (α := Empty) i⟩

theorem elasticitySMat_leftInv :
    ∀ k : ℤ, k ≤ 1 → ∃ N : Matrix (vecIdx 3 k) (vecIdx 3 (k + 1)) 𝕜,
      N * (elasticitySMat k : Matrix _ _ 𝕜) = 1
  | .ofNat 0, _ => ⟨elN0, elN0_mul_elS0⟩
  | .ofNat 1, _ => ⟨elN1, elN1_mul_elS1⟩
  | .ofNat (_ + 2), h => absurd h (by simp only [Int.ofNat_eq_natCast] at h ⊢; omega)
  | .negSucc _, _ => ⟨0, Matrix.ext fun i => isEmptyElim (α := Empty) i⟩

theorem divDivSMat_leftInv :
    ∀ k : ℤ, k ≤ 2 → ∃ N : Matrix (vecIdx 1 k) (vecIdx 3 (k + 1)) 𝕜,
      N * (divDivSMat k : Matrix _ _ 𝕜) = 1
  | .ofNat 0, _ => ⟨ddN0, ddN0_mul_ddS0⟩
  | .ofNat 1, _ => ⟨ddN1, ddN1_mul_ddS1⟩
  | .ofNat 2, _ => ⟨ddN2, ddN2_mul_ddS2⟩
  | .ofNat (_ + 3), h => absurd h (by simp only [Int.ofNat_eq_natCast] at h ⊢; omega)
  | .negSucc _, _ => ⟨0, Matrix.ext fun i => isEmptyElim (α := Empty) i⟩

/-- **The analytic BGG theorem for the Hessian diagram on `Ω`.** -/
theorem hessianMaximalData_derivedVerdict (hΩ : IsOpen Ω)
    (htop : (hessianMaximalData 𝕜 hΩ).RegularDecomposition 0) (i : ℤ)
    [FiniteDimensional 𝕜 (((deRhamVec 𝕜 1).maximalComplex hΩ).cohomology i)]
    [FiniteDimensional 𝕜 (((deRhamVec 𝕜 3).maximalComplex hΩ).cohomology i)] :
    (hessianMaximalData 𝕜 hΩ).DerivedVerdict (0 < ·) (· < 0) i :=
  ((hessianBGG 𝕜).maximalData_bggVerdict hessianSMat hessianS_apply_eq hΩ hessianSMat_leftInv
    htop i).toDerivedVerdict

theorem elasticityMaximalData_derivedVerdict (hΩ : IsOpen Ω)
    (htop : (elasticityMaximalData 𝕜 hΩ).RegularDecomposition 1) (i : ℤ)
    [FiniteDimensional 𝕜 (((deRhamVec 𝕜 3).maximalComplex hΩ).cohomology i)] :
    (elasticityMaximalData 𝕜 hΩ).DerivedVerdict (1 < ·) (· < 1) i :=
  ((elasticityBGG 𝕜).maximalData_bggVerdict elasticitySMat elasticityS_apply_eq hΩ
    elasticitySMat_leftInv htop i).toDerivedVerdict

theorem divDivMaximalData_derivedVerdict (hΩ : IsOpen Ω)
    (htop : (divDivMaximalData 𝕜 hΩ).RegularDecomposition 2) (i : ℤ)
    [FiniteDimensional 𝕜 (((deRhamVec 𝕜 3).maximalComplex hΩ).cohomology i)]
    [FiniteDimensional 𝕜 (((deRhamVec 𝕜 1).maximalComplex hΩ).cohomology i)] :
    (divDivMaximalData 𝕜 hΩ).DerivedVerdict (2 < ·) (· < 2) i :=
  ((divDivBGG 𝕜).maximalData_bggVerdict divDivSMat divDivS_apply_eq hΩ divDivSMat_leftInv htop
    i).toDerivedVerdict

/-! ### `Sᴶ` is not onto between the `L²` domains -/

theorem isHomogeneous_vecOp (m : ℕ) : ∀ k : ℤ, (vecOp 𝕜 m k).IsHomogeneous 1
  | .ofNat 0 => fun ij i t ht => by
    simp only [vecOp, gradOp] at ht
    split_ifs at ht <;> simp_all
  | .ofNat 1 => fun ik jl t ht => by
    simp only [vecOp, curlOp] at ht
    split_ifs at ht <;> simp_all
  | .ofNat 2 => fun i ij t ht => by
    simp only [vecOp, divOp] at ht
    split_ifs at ht <;> simp_all
  | .ofNat (_ + 3) => fun _ _ t ht => by simp [vecOp, zeroOp] at ht
  | .negSucc _ => fun _ _ t ht => by simp [vecOp, zeroOp] at ht

theorem IsTest.fderiv_fderiv_ne_zero {χ : (Fin 3 → ℝ) → 𝕜} (hχ : IsTest Set.univ χ)
    (hχ0 : χ ≠ 0) (l j : Fin 3) :
    (fun x => fderiv ℝ (fun y => fderiv ℝ χ y (coordDir l)) x (coordDir j)) ≠ 0 :=
  (hχ.fderiv_apply _).fderiv_apply_ne_zero (hχ.fderiv_apply_ne_zero hχ0 (by simp)) (by simp)

theorem gradOp_grad_swap {χ : (Fin 3 → ℝ) → 𝕜} (hχ : IsTest Set.univ χ) (l j : Fin 3) :
    (gradOp 3 3).apply (fun l x => fderiv ℝ χ x (coordDir l)) (l, j) =
      (gradOp 3 3).apply (fun l x => fderiv ℝ χ x (coordDir l)) (j, l) := by
  funext x
  rw [gradOp_apply, gradOp_apply]
  exact fderiv_fderiv_comm (hχ.contDiff.of_le (by simp)) _ _ x

/-- **`S⁰ = I : H¹(Ω; 𝕜³) → H(curl; Ω)` is not onto** for every nonempty open `Ω ⊆ ℝ³`. -/
theorem hessianMaximalData_not_surjective (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ¬ Function.Surjective ((hessianMaximalData 𝕜 hΩ).domainData.S 0 1) := by
  obtain ⟨χ, hχ, hχ0⟩ := exists_isTest_univ_ne_zero (Fin 3 → ℝ) 𝕜
  obtain ⟨N, hN⟩ := hessianSMat_leftInv (𝕜 := 𝕜) 0 le_rfl
  have hψ : IsTestField Set.univ fun l x => fderiv ℝ χ x (coordDir l) := fun l =>
    hχ.fderiv_apply _
  refine (hessianBGG 𝕜).not_surjective_maximalData_domainS hessianSMat hessianS_apply_eq hΩ hne
    hN (isHomogeneous_vecOp (𝕜 := 𝕜) 1 (0 + 1)) (isHomogeneous_vecOp 3 0) one_pos hψ
    ((hessianS_anticomm 0 _ fun l => (hψ l).contDiff).trans ?_) fun h => ?_
  · change -(ofMatrix hessS1).apply ((gradOp 3 3).apply _) = 0
    funext a
    rw [Pi.neg_apply, ofMatrix_hessS1_apply, gradOp_grad_swap hχ (a.2 + 1), sub_self, neg_zero]
    rfl
  · change (gradOp 3 3).apply _ = 0 at h
    exact hχ.fderiv_fderiv_ne_zero hχ0 0 0 (funext fun x => by
      simpa [gradOp_apply] using congrFun (congrFun h ((0, 0) : Fin 3 × Fin 3)) x)

theorem elasticityMaximalData_not_surjective (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ¬ Function.Surjective ((elasticityMaximalData 𝕜 hΩ).domainData.S 1 2) := by
  obtain ⟨χ, hχ, hχ0⟩ := exists_isTest_univ_ne_zero (Fin 3 → ℝ) 𝕜
  obtain ⟨N, hN⟩ := elasticitySMat_leftInv (𝕜 := 𝕜) 1 le_rfl
  have hg : IsTestField Set.univ fun l x => fderiv ℝ χ x (coordDir l) := fun l =>
    hχ.fderiv_apply _
  have hψ := (ofMatrix (elS0 (𝕜 := 𝕜))).isTestField_apply hg
  have hcurl := curlOp_elS0 (𝕜 := 𝕜) fun l x => fderiv ℝ χ x (coordDir l)
  refine (elasticityBGG 𝕜).not_surjective_maximalData_domainS elasticitySMat elasticityS_apply_eq
    hΩ hne hN (isHomogeneous_vecOp (𝕜 := 𝕜) 3 (1 + 1)) (isHomogeneous_vecOp 3 1) one_pos hψ ?_
    fun h => ?_
  · change (divOp 3 3).apply ((ofMatrix elS1).apply _) = 0
    rw [divOp_elS1 fun a => (hψ a).contDiff, hcurl]
    funext i
    rw [Pi.neg_apply, ofMatrix_elS2_apply, Pi.neg_apply, Pi.neg_apply, ofMatrix_elS1_apply,
      ofMatrix_elS1_apply, gradOp_grad_swap hχ (i + 2)]
    fin_cases i <;> simp
  · change (curlOp 3).apply ((ofMatrix elS0).apply _) = 0 at h
    rw [hcurl] at h
    refine hχ.fderiv_fderiv_ne_zero hχ0 1 0 (funext fun x => ?_)
    have h01 := congrFun (congrFun h ((0, 1) : Fin 3 × Fin 3)) x
    simpa [ofMatrix_elS1_apply, gradOp_apply] using h01

theorem divDivMaximalData_not_surjective (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ¬ Function.Surjective ((divDivMaximalData 𝕜 hΩ).domainData.S 2 3) := by
  obtain ⟨χ, hχ, hχ0⟩ := exists_isTest_univ_ne_zero (Fin 3 → ℝ) 𝕜
  obtain ⟨N, hN⟩ := divDivSMat_leftInv (𝕜 := 𝕜) 2 le_rfl
  have hψ : IsTestField Set.univ fun a : Fin 1 × Fin 3 => if a.2 = 0 then χ else 0 := fun a => by
    by_cases h : a.2 = 0 <;> simp [h, hχ, IsTest.zero]
  refine (divDivBGG 𝕜).not_surjective_maximalData_domainS divDivSMat divDivS_apply_eq hΩ hne hN
    (isHomogeneous_vecOp (𝕜 := 𝕜) 3 (2 + 1)) (isHomogeneous_vecOp 1 2) one_pos hψ
    (ConstCoeffOp.apply_eq_zero_of_isEmpty _ _
      (Or.inr (isEmpty_vecIdx 3 (k := 2 + 1 + 1) (Or.inr (by decide)))))
    fun h => hχ.fderiv_apply_ne_zero hχ0 (v := coordDir 0) (by simp) (funext fun x => ?_)
  have h0 := congrFun (congrFun h (0 : Fin 1)) x
  change (divOp 3 1).apply _ 0 x = 0 at h0
  simpa [divOp_apply, Fin.sum_univ_three] using h0

theorem hessianMaximalData_not_injSurjWith (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {J : ℤ}
    (hJ : J ≤ 0) (t : ∀ i j, (hessianMaximalData 𝕜 hΩ).H.domainSpace j →ₗ[𝕜]
      (hessianMaximalData 𝕜 hΩ).Ht.domainSpace i) :
    ¬ (hessianMaximalData 𝕜 hΩ).domainData.InjSurjWith J t := fun h =>
  hessianMaximalData_not_surjective hΩ hne fun w => ⟨t 0 (0 + 1) w, h.S_t' hJ w⟩

theorem elasticityMaximalData_not_injSurjWith (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {J : ℤ}
    (hJ : J ≤ 1) (t : ∀ i j, (elasticityMaximalData 𝕜 hΩ).H.domainSpace j →ₗ[𝕜]
      (elasticityMaximalData 𝕜 hΩ).Ht.domainSpace i) :
    ¬ (elasticityMaximalData 𝕜 hΩ).domainData.InjSurjWith J t := fun h =>
  elasticityMaximalData_not_surjective hΩ hne fun w => ⟨t 1 (1 + 1) w, h.S_t' hJ w⟩

theorem divDivMaximalData_not_injSurjWith (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {J : ℤ}
    (hJ : J ≤ 2) (t : ∀ i j, (divDivMaximalData 𝕜 hΩ).H.domainSpace j →ₗ[𝕜]
      (divDivMaximalData 𝕜 hΩ).Ht.domainSpace i) :
    ¬ (divDivMaximalData 𝕜 hΩ).domainData.InjSurjWith J t := fun h =>
  divDivMaximalData_not_surjective hΩ hne fun w => ⟨t 2 (2 + 1) w, h.S_t' hJ w⟩

end Instances

end Feec.Domain
