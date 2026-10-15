module

public import Feec.Ch4.WholeIdent
public import Feec.Ch4.BoxReduce

/-!
# Real-valued fields on `ℝ³`: Prop 4.17 within real fields

`Feec.Ch4.Whole` states Prop 4.17 on `ℝ³` for complex-valued fields (viewed as a real Hilbert
space). Physical fields are real. On the Fourier side a field `f` is real iff
`𝓕 f (-ξ) = conj (𝓕 f ξ)`. This file shows that the whole-space complex restricts to real fields
and that Prop 4.17 holds there, with existence of solutions.

## Main results

* `refl`: the real-linear isometric involution `(J A)(ξ) = conj (A (-ξ))` on `L²(ℝ³_ξ; ℂᴾ)`
  (`refl_refl`, `inner_refl`). Its fixed points are the Fourier transforms of real fields:
  `fieldFourierW_conj` (`𝓕 (conj f) = J (𝓕 f)`) and **`fourier_mem_fix_iff`**
  (`J (𝓕 f) = 𝓕 f` iff `f(x)` is real for a.e. `x`).
* `realRefl`: `J` packaged as a `Feec.Box.Refl3` (the three reflections all equal to `J`), so
  that the restriction machinery of `Feec.Ch4.BoxReduce` applies.
* `intertwines_mulOp`: a multiplier whose symbol satisfies `m(ξ) (conj v) = conj (m(-ξ) v)`
  commutes with `J`; this holds for `grad` and `curl` (`intertwines_grad`, `intertwines_curl`).
  `J` preserves `L²(TSD)` (`refl_mem_L2TSD`).
* `realComplex`: the whole-space complex `H¹(V) → H(curl; M) → L²(M)` restricted to real fields
  (`Feec.Box.resComplex`).
* **`real_prop_4_17_whole`**, **`real_prop_4_17_whole_exists`**: Prop 4.17 for `realComplex`,
  with constraint spaces `L²(TSD) ∩ real`, and existence and uniqueness of solutions for real TSD
  data in `H(curl)`.

Scope: Prop 4.17 is proved for the restricted complex, whose state space consists of real fields.
That the Stone group of the full complex `Feec.Whole.wholeComplex` maps real data to real states
is not formalized; it would follow from identifying the wave operator of `realComplex` with the
restriction of that of `wholeComplex`.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17)
* Mathlib, `Mathlib.Analysis.Fourier.LpSpace` (Plancherel)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory LinearPMap Set Filter

namespace Feec.WholeReal

open Feec.Torus Feec.Whole Feec.Box HilbertComplex2 Constraints

section Refl

variable (P : Type*) [Fintype P]

/-- Entrywise complex conjugation on `ℂᴾ`, a real-linear map. -/
def conjE : EuclideanSpace ℂ P →L[ℝ] EuclideanSpace ℂ P :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 fun p => conj (v p)
      map_add' := fun u v => by ext p; simp
      map_smul' := fun r v => by ext p; simp [Complex.real_smul] }

variable {P}

theorem conjE_apply (v : EuclideanSpace ℂ P) (p : P) : conjE P v p = conj (v p) := rfl

theorem conjE_conjE (v : EuclideanSpace ℂ P) : conjE P (conjE P v) = v := by
  ext p; simp [conjE_apply]

theorem conjE_smul (c : ℂ) (v : EuclideanSpace ℂ P) : conjE P (c • v) = conj c • conjE P v := by
  ext p; simp [conjE_apply]

theorem inner_conjE (u v : EuclideanSpace ℂ P) : ⟪conjE P u, conjE P v⟫ = ⟪u, v⟫ := by
  simp only [real_inner_eq_re_inner, PiLp.inner_apply, conjE_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp

theorem measurePreserving_neg :
    MeasurePreserving (fun ξ : Freq => -ξ) volume volume :=
  Measure.measurePreserving_neg volume

theorem ae_neg {p : Freq → Prop} (h : ∀ᵐ ξ ∂(volume : Measure Freq), p ξ) :
    ∀ᵐ ξ ∂(volume : Measure Freq), p (-ξ) :=
  measurePreserving_neg.quasiMeasurePreserving.ae h

variable (P) in
/-- **The reality involution** `(J A)(ξ) = conj (A (-ξ))` on `L²(ℝ³_ξ; ℂᴾ)`; its fixed points are
the Fourier transforms of real fields (`fourier_mem_fix_iff`). -/
def refl : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq) →L[ℝ]
    Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq) :=
  ((conjE P).compLpL 2 volume).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (fun ξ : Freq => -ξ) measurePreserving_neg).toContinuousLinearMap

theorem coeFn_refl (A : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq)) :
    refl P A =ᵐ[volume] fun ξ => conjE P (A (-ξ)) := by
  filter_upwards [(conjE P).coeFn_compLp (Lp.compMeasurePreserving _ measurePreserving_neg A),
    Lp.coeFn_compMeasurePreserving A measurePreserving_neg] with ξ h1 h2
  change ((conjE P).compLp (Lp.compMeasurePreserving _ measurePreserving_neg A) :
    Freq → EuclideanSpace ℂ P) ξ = _
  rw [h1, h2]; rfl

theorem refl_refl (A : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq)) :
    refl P (refl P A) = A := by
  refine Lp.ext ?_
  filter_upwards [coeFn_refl (refl P A), ae_neg (coeFn_refl A)] with ξ h1 h2
  rw [h1, h2, neg_neg, conjE_conjE]

theorem inner_refl (A B : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq)) :
    ⟪refl P A, refl P B⟫ = ⟪A, B⟫ := by
  rw [L2.inner_def, L2.inner_def]
  have : ∫ ξ, ⟪refl P A ξ, refl P B ξ⟫ = ∫ ξ, ⟪A (-ξ), B (-ξ)⟫ := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_refl A, coeFn_refl B] with ξ h1 h2
    rw [h1, h2, inner_conjE]
  rw [this]
  exact integral_neg_eq_self (fun ξ => ⟪A ξ, B ξ⟫) volume

variable (P) in
/-- `J` as a `Feec.Box.Refl3` (all three reflections equal to `J`). -/
def realRefl : Refl3 (Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq)) where
  R _ := refl P
  invol _ := refl_refl
  inner_map _ := inner_refl
  comm _ _ _ := rfl

theorem realRefl_R (i : Fin 3) : (realRefl P).R i = refl P := rfl

/-- The fixed subspace of `realRefl` is `{A | J A = A}`. -/
theorem mem_fix_iff {A : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq)} :
    A ∈ (realRefl P).fix ↔ refl P A = A :=
  ⟨fun h => h 0, fun h _ => h⟩

end Refl

section Physical

variable {P : Type*} [Fintype P]

/-- On Schwartz fields, `𝓕 (conj φ)(ξ) = conj (𝓕 φ (-ξ))`. -/
theorem fourier_conj (φ : 𝓢(Freq, EuclideanSpace ℂ P)) (ξ : Freq) :
    𝓕 (SchwartzMap.postcompCLM (conjE P) φ) ξ = conjE P (𝓕 φ (-ξ)) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  have : (SchwartzMap.postcompCLM (conjE P) φ : Freq → EuclideanSpace ℂ P) =
      fun x => conjE P (φ x) :=
    funext fun x => SchwartzMap.postcompCLM_apply (conjE P) φ x
  rw [this, Real.fourier_eq, Real.fourier_eq, ← (conjE P).integral_comp_comm]
  · congr 1; funext v
    rw [Circle.smul_def, Circle.smul_def, conjE_smul, ← Circle.coe_inv_eq_conj,
      ← AddChar.map_neg_eq_inv, inner_neg_right, neg_neg]
  · exact (Real.fourierIntegral_convergent_iff (-ξ)).2 φ.integrable

/-- **The `L²` Fourier transform intertwines conjugation and `J`**: `𝓕 (conj f) = J (𝓕 f)`. -/
theorem fieldFourierW_conj (f : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq)) :
    fieldFourierW P ((conjE P).compLp f) = refl P (fieldFourierW P f) := by
  have hc1 : Continuous fun f : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq) =>
      fieldFourierW P ((conjE P).compLp f) :=
    (fieldFourierW P).continuous.comp ((conjE P).compLpL 2 volume).continuous
  have hc2 : Continuous fun f : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq) =>
      refl P (fieldFourierW P f) :=
    (refl P).continuous.comp (fieldFourierW P).continuous
  refine DenseRange.induction_on
    (SchwartzMap.denseRange_toLpCLM (F := EuclideanSpace ℂ P) (μ := (volume : Measure Freq))
      (p := 2) ENNReal.ofNat_ne_top) f (isClosed_eq hc1 hc2) ?_
  intro φ
  simp only [SchwartzMap.toLpCLM_apply]
  have h1 : (conjE P).compLp (φ.toLp 2) = (SchwartzMap.postcompCLM (conjE P) φ).toLp 2 := by
    refine Lp.ext ?_
    filter_upwards [(conjE P).coeFn_compLp (φ.toLp 2), φ.coeFn_toLp 2 volume,
      (SchwartzMap.postcompCLM (conjE P) φ).coeFn_toLp 2 volume] with ξ h1 h2 h3
    rw [h1, h2, h3, SchwartzMap.postcompCLM_apply]
  rw [h1, fieldFourierW_toLp, fieldFourierW_toLp]
  refine Lp.ext ?_
  filter_upwards [(𝓕 (SchwartzMap.postcompCLM (conjE P) φ)).coeFn_toLp 2 volume,
    coeFn_refl ((𝓕 φ).toLp 2), ae_neg ((𝓕 φ).coeFn_toLp 2 volume)] with ξ h1 h2 h3
  rw [h1, h2, h3, fourier_conj]

/-- **Real fields.** For `f ∈ L²(ℝ³; ℂᴾ)`, `𝓕 f` is fixed by `J` (i.e. `𝓕 f (-ξ) = conj 𝓕 f (ξ)`)
iff `f(x)` is real-valued for a.e. `x`. -/
theorem fourier_mem_fix_iff (f : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq)) :
    fieldFourierW P f ∈ (realRefl P).fix ↔
      ∀ᵐ x ∂(volume : Measure Freq), ∀ p, conj (f x p) = f x p := by
  rw [mem_fix_iff, ← fieldFourierW_conj, (fieldFourierW P).injective.eq_iff]
  constructor
  · intro h
    filter_upwards [(conjE P).coeFn_compLp f] with x h1
    rw [h] at h1
    intro p
    have := congrArg (fun v : EuclideanSpace ℂ P => v p) h1
    simp only [conjE_apply] at this
    exact this.symm
  · intro h
    refine Lp.ext ?_
    filter_upwards [(conjE P).coeFn_compLp f, h] with x h1 h2
    rw [h1]
    ext p
    exact h2 p

end Physical

section Complex

/-- A multiplier with `m(ξ) (conj v) = conj (m(-ξ) v)` commutes with `J`. -/
theorem intertwines_mulOp {P Q : Type*} [Fintype P] [Fintype Q]
    {m : Freq → EuclideanSpace ℂ P →L[ℝ] EuclideanSpace ℂ Q}
    (hm : ∀ ξ v, m ξ (conjE P v) = conjE Q (m (-ξ) v)) :
    Intertwines (realRefl P) (realRefl Q) (mulOp volume m) := by
  intro i x
  have key : (fun ξ => m ξ (refl P (x : Lp (EuclideanSpace ℂ P) 2 volume) ξ)) =ᵐ[volume]
      (refl Q (mulOp volume m x) : Freq → EuclideanSpace ℂ Q) := by
    filter_upwards [coeFn_refl (x : Lp (EuclideanSpace ℂ P) 2 volume),
      coeFn_refl (mulOp volume m x), ae_neg (coeFn_mulOp volume m x)] with ξ h1 h2 h3
    rw [h1, h2, h3, hm]
  have hd : refl P (x : Lp (EuclideanSpace ℂ P) 2 volume) ∈ mulDomain volume m :=
    (Lp.memLp _).ae_eq key.symm
  exact ⟨hd, Lp.ext ((coeFn_mulOp volume m ⟨_, hd⟩).trans key)⟩

theorem freqW_neg (ξ : Freq) : freqW (-ξ) = -freqW ξ := by simp [freqW]

theorem gradSym_conj (ξ : Freq) (v : Vec3) :
    gradSym (freqW ξ) (conjE (Fin 3) v) = conjE (Fin 3 × Fin 3) (gradSym (freqW (-ξ)) v) := by
  rw [freqW_neg]
  ext ⟨a, b⟩
  simp [gradSym_apply, conjE_apply]

theorem curlSym_conj (ξ : Freq) (M : Mat3) :
    curlSym (freqW ξ) (conjE (Fin 3 × Fin 3) M) =
      conjE (Fin 3 × Fin 3) (curlSym (freqW (-ξ)) M) := by
  rw [freqW_neg]
  ext ⟨a, b⟩
  fin_cases b <;> simp [curlSym_apply, jM_apply, curlR_apply, cross, conjE_apply] <;> ring

/-- `grad` commutes with `J`. -/
theorem intertwines_grad :
    Intertwines (realRefl (Fin 3)) (realRefl (Fin 3 × Fin 3)) wholeComplex.d0 :=
  intertwines_mulOp gradSym_conj

/-- `curl` commutes with `J`. -/
theorem intertwines_curl :
    Intertwines (realRefl (Fin 3 × Fin 3)) (realRefl (Fin 3 × Fin 3)) wholeComplex.d1 :=
  intertwines_mulOp curlSym_conj

/-- `J` preserves `L²(TSD)`. -/
theorem refl_mem_L2TSD {A : Whole.L2M} (hA : A ∈ Whole.L2TSD) : refl (Fin 3 × Fin 3) A ∈ Whole.L2TSD := by
  refine Whole.mem_fibreSub.2 ?_
  filter_upwards [coeFn_refl A, ae_neg (Whole.mem_fibreSub.1 hA)] with ξ h1 h2
  rw [h1]
  rw [freqW_neg, tsd_neg] at h2
  exact conjM_mem_tsd h2

/-- **The whole-space complex on real fields**: `H¹(V) → H(curl; M) → L²(M)` on `ℝ³`, restricted
to the Fourier transforms of real fields. -/
def realComplex : HilbertComplex2 (realRefl (Fin 3)).fix (realRefl (Fin 3 × Fin 3)).fix
    (realRefl (Fin 3 × Fin 3)).fix :=
  resComplex wholeComplex (realRefl (Fin 3)) (realRefl (Fin 3 × Fin 3))
    (realRefl (Fin 3 × Fin 3)) intertwines_grad intertwines_curl

/-- `L²(TSD)` within real fields. -/
abbrev realTSD : Submodule ℝ (realRefl (Fin 3 × Fin 3)).fix :=
  Whole.L2TSD.comap (realRefl (Fin 3 × Fin 3)).fix.subtype

instance : realTSD.HasOrthogonalProjection := by
  have hc : _root_.IsClosed (realTSD : Set (realRefl (Fin 3 × Fin 3)).fix) :=
    (Whole.isClosed_fibreSub _ stronglyMeasurable_projTSD.aestronglyMeasurable).preimage
      continuous_subtype_val
  have : CompleteSpace realTSD := hc.completeSpace_coe
  infer_instance

/-- **Thesis Prop 4.17 on `ℝ³` for real fields.** For the whole-space complex restricted to real
fields (`realComplex`), every strong solution of (4.14) with data `(0, E₀, B₀)`,
`E₀, B₀ ∈ L²(TSD)` real, keeps `σ ≡ 0` and `E, B ∈ L²(TSD)` for `t ∈ [0, T]`, and `(E, B)`
solves (4.15).
See [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem real_prop_4_17_whole {T : ℝ} {E₀ B₀ : (realRefl (Fin 3 × Fin 3)).fix}
    {U : ℝ → Tot (realRefl (Fin 3)).fix (realRefl (Fin 3 × Fin 3)).fix
      (realRefl (Fin 3 × Fin 3)).fix}
    (hE₀ : E₀ ∈ realTSD) (hB₀ : B₀ ∈ realTSD)
    (hU : IsStrongSolution (-realComplex.waveOp) T (ini (realRefl (Fin 3)).fix E₀ B₀) 0 U) :
    (∀ t ∈ Icc 0 T, U t ∈ Kc (realRefl (Fin 3)).fix realTSD realTSD) ∧
      IsReducedSolution realComplex T E₀ B₀ (fun t => (tot _ _ _ (U t)).2.1)
        (fun t => (tot _ _ _ (U t)).2.2) :=
  prop_4_17_res (H := wholeComplex) (G0 := realRefl (Fin 3)) (h0 := intertwines_grad)
    (h1 := intertwines_curl) Whole.L2TSD Whole.L2TSD Whole.L2TSD_le_ker Whole.projKc_mem_domL Whole.curlW_mem_L2TSD
    Whole.adjoint_curlW_mem_L2TSD (fun _ _ hA => refl_mem_L2TSD hA) (fun _ _ hA => refl_mem_L2TSD hA)
    hE₀ hB₀ hU

/-- Real TSD data in `H(curl)` give an initial state in `D(L)` of `realComplex`. -/
theorem ini_mem_domL_real {E₀ B₀ : (realRefl (Fin 3 × Fin 3)).fix} (hE₀ : E₀ ∈ realTSD)
    (hE₀c : (E₀ : Whole.L2M) ∈ Whole.Hcurl) (hB₀c : (B₀ : Whole.L2M) ∈ Whole.Hcurl) :
    ini (realRefl (Fin 3)).fix E₀ B₀ ∈ realComplex.domL := by
  have h := (Whole.ini_mem_domL_iff_of_TSD (B₀ := (B₀ : Whole.L2M)) hE₀).2 ⟨hE₀c, hB₀c⟩
  rw [Constraints.mem_domL, tot_ini] at h
  have hm : E₀ ∈ realComplex.midDomain := mem_midDomain_res.2 h.2.1
  have ha : B₀ ∈ realComplex.d1†.domain := mem_adj1_domain_res.2 h.2.2
  have e := tot_ini (W0 := (realRefl (Fin 3)).fix) E₀ B₀
  refine (Constraints.mem_domL realComplex).2 ?_
  simp only [e]
  exact ⟨Submodule.zero_mem _, hm, ha⟩

/-- **Thesis Prop 4.17 on `ℝ³` for real fields, with existence.** For real TSD data
`E₀, B₀ ∈ L²(TSD) ∩ H(curl)`, the Hodge wave (4.14) of `realComplex` has a strong solution on
`[0, T]` (Stone's theorem for the restricted complex), unique among strong solutions; it stays in
`{0} × L²(TSD) × L²(TSD)` within real fields, and `(E, B)` solves (4.15).
See [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem real_prop_4_17_whole_exists (T : ℝ) {E₀ B₀ : (realRefl (Fin 3 × Fin 3)).fix}
    (hE₀ : E₀ ∈ realTSD) (hB₀ : B₀ ∈ realTSD) (hE₀c : (E₀ : Whole.L2M) ∈ Whole.Hcurl)
    (hB₀c : (B₀ : Whole.L2M) ∈ Whole.Hcurl) :
    ∃ U : ℝ → Tot (realRefl (Fin 3)).fix (realRefl (Fin 3 × Fin 3)).fix
        (realRefl (Fin 3 × Fin 3)).fix,
      IsStrongSolution (-realComplex.waveOp) T (ini (realRefl (Fin 3)).fix E₀ B₀) 0 U ∧
      (∀ U', IsStrongSolution (-realComplex.waveOp) T (ini (realRefl (Fin 3)).fix E₀ B₀) 0 U' →
        EqOn U' U (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, U t ∈ Kc (realRefl (Fin 3)).fix realTSD realTSD) ∧
      IsReducedSolution realComplex T E₀ B₀ (fun t => (tot _ _ _ (U t)).2.1)
        (fun t => (tot _ _ _ (U t)).2.2) :=
  prop_4_17_res_exists (H := wholeComplex) (G0 := realRefl (Fin 3)) (h0 := intertwines_grad)
    (h1 := intertwines_curl) Whole.L2TSD Whole.L2TSD Whole.L2TSD_le_ker Whole.projKc_mem_domL Whole.curlW_mem_L2TSD
    Whole.adjoint_curlW_mem_L2TSD (fun _ _ hA => refl_mem_L2TSD hA) (fun _ _ hA => refl_mem_L2TSD hA)
    T hE₀ hB₀ (ini_mem_domL_real hE₀ hE₀c hB₀c)

end Complex

end Feec.WholeReal
