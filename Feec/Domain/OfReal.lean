module

public import Feec.Domain.RegularDecomposition

/-!
# Real-coefficient operators on `𝕜`-valued fields

A constant-coefficient operator with real coefficients acts on `𝕜`-valued fields, and the regular
decompositions and finite-dimensional cohomology of maximal complexes of such operators pass to `𝕜`.

## Main results

* `ConstCoeffComplex.HasRegularDecomposition.ofReal`: the regular decompositions pass to `𝕜`.
* `ConstCoeffComplex.finiteDimensional_cohomology_ofReal`: so does finite-dimensional cohomology.
-/

open MeasureTheory
open scoped InnerProductSpace ContDiff

@[expose] public noncomputable section

namespace Feec.Domain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type*} [RCLike 𝕜]
  {ι κ : Type*}

/-! ### Real-coefficient operators -/

namespace ConstCoeffOp

variable (𝕜) in
/-- A real-coefficient operator acting on `𝕜`-valued fields (the coefficients cast to `𝕜`). -/
def ofReal (A : ConstCoeffOp E ℝ ι κ) : ConstCoeffOp E 𝕜 ι κ where
  coeff j i := (A.coeff j i).map fun t => (t.1, (t.2 : 𝕜))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem ofReal_real (A : ConstCoeffOp E ℝ ι κ) : A.ofReal ℝ = A := by
  obtain ⟨c⟩ := A
  simp [ofReal]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem formalAdj_ofReal (A : ConstCoeffOp E ℝ ι κ) :
    (A.ofReal 𝕜).formalAdj = A.formalAdj.ofReal 𝕜 := by
  simp only [ofReal, formalAdj, adjEntry, List.map_map]
  congr 1
  funext i j
  refine List.map_congr_left fun t _ => ?_
  simp

theorem clm_ofReal_apply {𝕜₁ 𝕜₂ : Type*} [RCLike 𝕜₁] [RCLike 𝕜₂] [Fintype ι]
    (A : ConstCoeffOp E ℝ ι κ) (L : 𝕜₁ →L[ℝ] 𝕜₂) {f : ι → E → 𝕜₁}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (j : κ) (x : E) :
    L ((A.ofReal 𝕜₁).apply f j x) = (A.ofReal 𝕜₂).apply (fun i y => L (f i y)) j x := by
  simp only [apply, applyEntry, ofReal, List.map_map, map_sum, map_list_sum]
  refine Finset.sum_congr rfl fun i _ => congrArg List.sum (List.map_congr_left fun t _ => ?_)
  simp only [Function.comp_apply, ← RCLike.real_smul_eq_coe_mul, map_smul,
    iterDeriv_comp_clm L (hf i)]

theorem IsComplexPair.ofReal {μ : Type*} [Fintype ι] [Fintype κ] {A : ConstCoeffOp E ℝ ι κ}
    {B : ConstCoeffOp E ℝ κ μ} (h : A.IsComplexPair B) :
    (A.ofReal 𝕜).IsComplexPair (B.ofReal 𝕜) := by
  intro f hf
  have key : ∀ L : 𝕜 →L[ℝ] ℝ, ∀ j x, L ((B.ofReal 𝕜).apply ((A.ofReal 𝕜).apply f) j x) = 0 := by
    intro L j x
    have hA : (fun i y => L ((A.ofReal 𝕜).apply f i y)) = A.apply fun i y => L (f i y) := by
      funext i y; rw [clm_ofReal_apply A L hf, ofReal_real]
    rw [clm_ofReal_apply B L ((A.ofReal 𝕜).contDiff_apply hf), ofReal_real, hA,
      h (fun i y => L (f i y)) fun i => L.contDiff.comp (hf i)]
    rfl
  funext j x
  exact RCLike.ext (by simpa using key RCLike.reCLM j x) (by simpa using key RCLike.imCLM j x)

end ConstCoeffOp

variable (𝕜) in
/-- A complex of real-coefficient operators acting on `𝕜`-valued fields. -/
def ConstCoeffComplex.ofReal (C : ConstCoeffComplex E ℝ) : ConstCoeffComplex E 𝕜 where
  ι := C.ι
  A k := (C.A k).ofReal 𝕜
  comp k := (C.comp k).ofReal

/-! ### The maximal realizations -/

namespace ConstCoeffOp

variable [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] {Ω : Set E} [Fintype ι] [Fintype κ]

theorem ofRealCLM_mem_maximal_domain (hΩ : IsOpen Ω) (A : ConstCoeffOp E ℝ ι κ)
    (p : (A.maximal Ω).domain) :
    ∃ hp : L2F.ofRealCLM 𝕜 (p : L2F ℝ Ω ι) ∈ ((A.ofReal 𝕜).maximal Ω).domain,
      (A.ofReal 𝕜).maximal Ω ⟨_, hp⟩ = L2F.ofRealCLM 𝕜 (A.maximal Ω p) := by
  have key : ∀ φ : κ → E → 𝕜, ∀ hφ : IsTestField Ω φ,
      ⟪L2F.ofRealCLM 𝕜 (A.maximal Ω p), testField hφ⟫_𝕜 =
        ⟪L2F.ofRealCLM 𝕜 (p : L2F ℝ Ω ι),
          testField ((A.ofReal 𝕜).formalAdj.isTestField_apply hφ)⟫_𝕜 := by
    intro φ hφ
    have e : ∀ L : 𝕜 →L[ℝ] ℝ, L2F.mapCLM L (testField ((A.ofReal 𝕜).formalAdj.isTestField_apply hφ))
        = testField (A.formalAdj.isTestField_apply (hφ.comp_clm L)) := fun L => by
      rw [L2F.mapCLM_testField]
      refine testField_congr _ _ (funext₂ fun j x => ?_)
      rw [formalAdj_ofReal, clm_ofReal_apply _ L fun i => (hφ i).contDiff, ofReal_real]
    rw [← L2F.ofRealCLM_re_add_im (testField hφ),
      ← L2F.ofRealCLM_re_add_im (testField ((A.ofReal 𝕜).formalAdj.isTestField_apply hφ))]
    simp only [inner_add_right, inner_smul_right, L2F.inner_ofRealCLM, e]
    simp only [L2F.mapCLM_testField, A.maximal_inner_testField hΩ p]
  exact ⟨((A.ofReal 𝕜).mem_maximal_domain_iff hΩ).2 ⟨_, key⟩,
    (A.ofReal 𝕜).maximal_apply_eq hΩ ⟨_, _⟩ key⟩

theorem reCLM_mem_maximal_domain (hΩ : IsOpen Ω) (A : ConstCoeffOp E ℝ ι κ)
    (u : ((A.ofReal 𝕜).maximal Ω).domain) :
    ∃ hu : L2F.reCLM (u : L2F 𝕜 Ω ι) ∈ (A.maximal Ω).domain,
      A.maximal Ω ⟨_, hu⟩ = L2F.reCLM ((A.ofReal 𝕜).maximal Ω u) := by
  have key : ∀ ψ : κ → E → ℝ, ∀ hψ : IsTestField Ω ψ,
      ⟪L2F.reCLM ((A.ofReal 𝕜).maximal Ω u), testField hψ⟫_ℝ =
        ⟪L2F.reCLM (u : L2F 𝕜 Ω ι), testField (A.formalAdj.isTestField_apply hψ)⟫_ℝ := by
    intro ψ hψ
    have e : L2F.ofRealCLM 𝕜 (testField (A.formalAdj.isTestField_apply hψ)) =
        testField ((A.ofReal 𝕜).formalAdj.isTestField_apply (hψ.comp_clm
          RCLike.ofRealCLM)) := by
      rw [L2F.mapCLM_testField]
      refine testField_congr _ _ (funext₂ fun j x => ?_)
      rw [formalAdj_ofReal, ← clm_ofReal_apply _ _ fun i => (hψ i).contDiff, ofReal_real]
    rw [L2F.inner_reCLM, L2F.inner_reCLM, e, L2F.mapCLM_testField,
      (A.ofReal 𝕜).maximal_inner_testField hΩ u]
  exact ⟨(A.mem_maximal_domain_iff hΩ).2 ⟨_, key⟩, A.maximal_apply_eq hΩ ⟨_, _⟩ key⟩

theorem imCLM_mem_maximal_domain (hΩ : IsOpen Ω) (A : ConstCoeffOp E ℝ ι κ)
    (u : ((A.ofReal 𝕜).maximal Ω).domain) :
    ∃ hu : L2F.imCLM (u : L2F 𝕜 Ω ι) ∈ (A.maximal Ω).domain,
      A.maximal Ω ⟨_, hu⟩ = L2F.imCLM ((A.ofReal 𝕜).maximal Ω u) := by
  obtain ⟨hu, e⟩ := reCLM_mem_maximal_domain hΩ A (-((RCLike.I : 𝕜) • u))
  rw [LinearPMap.map_neg, LinearPMap.map_smul] at e
  simp only [L2F.imCLM_eq_reCLM]
  exact ⟨hu, e⟩

end ConstCoeffOp

/-! ### `H¹` fields -/

section FieldH1

variable [Fintype ι] {n : ℕ} {Ω : Set (Fin n → ℝ)}

omit [Fintype ι] in
theorem fieldGradOp_ofReal : (fieldGradOp ℝ n ι).ofReal 𝕜 = fieldGradOp 𝕜 n ι := by
  classical
  simp only [ConstCoeffOp.ofReal, fieldGradOp]
  congr 1
  funext ij i
  split_ifs <;> simp

theorem ofRealCLM_mem_fieldH1 (hΩ : IsOpen Ω) {w : L2F ℝ Ω ι} (hw : w ∈ fieldH1 ℝ Ω ι) :
    L2F.ofRealCLM 𝕜 w ∈ fieldH1 𝕜 Ω ι := by
  rw [fieldH1, ← fieldGradOp_ofReal]
  exact (ConstCoeffOp.ofRealCLM_mem_maximal_domain hΩ _ ⟨w, hw⟩).1

end FieldH1

/-! ### Complexes of real-coefficient operators -/

namespace ConstCoeffComplex

/-- **The `H¹`-regular decompositions pass from `ℝ` to `𝕜`.** -/
theorem HasRegularDecomposition.ofReal {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {C : ConstCoeffComplex (Fin n → ℝ) ℝ} {J : ℤ} (h : C.HasRegularDecomposition Ω J) :
    (C.ofReal 𝕜).HasRegularDecomposition Ω J := by
  intro i hi (u : L2F 𝕜 Ω (C.ι (i + 1))) hu
  obtain ⟨hre, -⟩ := ConstCoeffOp.reCLM_mem_maximal_domain hΩ (C.A (i + 1)) ⟨u, hu⟩
  obtain ⟨him, -⟩ := ConstCoeffOp.imCLM_mem_maximal_domain hΩ (C.A (i + 1)) ⟨u, hu⟩
  obtain ⟨p, hp⟩ := h i hi _ hre
  obtain ⟨q, hq⟩ := h i hi _ him
  obtain ⟨hp', ep⟩ := ConstCoeffOp.ofRealCLM_mem_maximal_domain (𝕜 := 𝕜) hΩ (C.A i) p
  obtain ⟨hq', eq⟩ := ConstCoeffOp.ofRealCLM_mem_maximal_domain (𝕜 := 𝕜) hΩ (C.A i) q
  refine ⟨⟨_, hp'⟩ + (RCLike.I : 𝕜) • ⟨_, hq'⟩, ?_⟩
  change u - ((C.A i).ofReal 𝕜).maximal Ω (⟨_, hp'⟩ + (RCLike.I : 𝕜) • ⟨_, hq'⟩) ∈
    fieldH1 𝕜 Ω (C.ι (i + 1))
  rw [LinearPMap.map_add, LinearPMap.map_smul, ep, eq]
  have e : u - (L2F.ofRealCLM 𝕜 ((C.A i).maximal Ω p) +
        (RCLike.I : 𝕜) • L2F.ofRealCLM 𝕜 ((C.A i).maximal Ω q)) =
      L2F.ofRealCLM 𝕜 (L2F.reCLM u - (C.A i).maximal Ω p) +
        (RCLike.I : 𝕜) • L2F.ofRealCLM 𝕜 (L2F.imCLM u - (C.A i).maximal Ω q) := by
    conv_lhs => rw [← L2F.ofRealCLM_re_add_im u]
    rw [map_sub, map_sub, smul_sub]; abel
  rw [e]
  exact add_mem (ofRealCLM_mem_fieldH1 hΩ hp) (Submodule.smul_mem _ _ (ofRealCLM_mem_fieldH1 hΩ hq))

variable [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] {Ω : Set E}

/-- **Finite-dimensional cohomology of the maximal complex passes from `ℝ` to `𝕜`.** -/
theorem finiteDimensional_cohomology_ofReal (C : ConstCoeffComplex E ℝ) (hΩ : IsOpen Ω) (i : ℤ)
    [FiniteDimensional ℝ ((C.maximalComplex hΩ).cohomology i)] :
    FiniteDimensional 𝕜 (((C.ofReal 𝕜).maximalComplex hΩ).cohomology i) := by
  have hre := maximalComplex_comm hΩ hΩ (C := C.ofReal 𝕜) (C' := C)
    (T := fun k => L2F.reCLM (𝕜 := 𝕜) (Ω := Ω) (ι := C.ι k))
    fun k x => ConstCoeffOp.reCLM_mem_maximal_domain hΩ (C.A k) x
  have him := maximalComplex_comm hΩ hΩ (C := C.ofReal 𝕜) (C' := C)
    (T := fun k => L2F.imCLM (𝕜 := 𝕜) (Ω := Ω) (ι := C.ι k))
    fun k x => ConstCoeffOp.imCLM_mem_maximal_domain hΩ (C.A k) x
  have hof := maximalComplex_comm hΩ hΩ (C := C) (C' := C.ofReal 𝕜)
    (T := fun k => L2F.ofRealCLM 𝕜 (Ω := Ω) (ι := C.ι k))
    fun k x => ConstCoeffOp.ofRealCLM_mem_maximal_domain hΩ (C.A k) x
  let re := fun k => (L2F.reCLM (𝕜 := 𝕜) (Ω := Ω) (ι := C.ι k)).toLinearMap
  let im := fun k => (L2F.imCLM (𝕜 := 𝕜) (Ω := Ω) (ι := C.ι k)).toLinearMap
  let of := fun k => (L2F.ofRealCLM 𝕜 (Ω := Ω) (ι := C.ι k)).toLinearMap
  refine HilbertComplex.finiteDimensional_cohomology_of_sum_smul_eq_id
    (H := C.maximalComplex hΩ) (H' := (C.ofReal 𝕜).maximalComplex hΩ) ![re i, im i] ![of i, of i]
    ![1, RCLike.I] ?_ ?_ ?_ fun x _ => ?_
  · refine Fin.forall_fin_two.2 ⟨fun _ hx => ?_, fun _ hx => ?_⟩
    · exact HilbertComplex.apply_mem_cycles (T := re) hre hx
    · exact HilbertComplex.apply_mem_cycles (T := im) him hx
  · refine Fin.forall_fin_two.2 ⟨fun _ hx => ?_, fun _ hx => ?_⟩
    · exact HilbertComplex.apply_mem_boundaries (T := re) hre hx
    · exact HilbertComplex.apply_mem_boundaries (T := im) him hx
  · refine Fin.forall_fin_two.2 ⟨fun _ hx => ?_, fun _ hx => ?_⟩
    · exact HilbertComplex.apply_mem_boundaries (T := of) hof hx
    · exact HilbertComplex.apply_mem_boundaries (T := of) hof hx
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul]
  exact L2F.ofRealCLM_re_add_im (x : L2F 𝕜 Ω (C.ι i))

end ConstCoeffComplex

/-! ### The de Rham complexes in vector proxies -/

theorem vecOp_ofReal (m : ℕ) : ∀ k, (vecOp ℝ m k).ofReal 𝕜 = vecOp 𝕜 m k
  | .ofNat (_ + 3) | .negSucc _ => rfl
  | .ofNat 0 | .ofNat 1 | .ofNat 2 => by
    simp only [vecOp, ConstCoeffOp.ofReal, gradOp, curlOp, divOp]
    congr 1
    funext a b
    split_ifs <;> simp

theorem deRhamVec_ofReal (m : ℕ) : (deRhamVec ℝ m).ofReal 𝕜 = deRhamVec 𝕜 m := by
  simp only [ConstCoeffComplex.ofReal, deRhamVec, vecOp_ofReal]

end Feec.Domain
