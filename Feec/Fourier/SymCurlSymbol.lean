module

public import Feec.Fourier.GradCurlSymbol

/-!
# The symbol of the strong-symmetry complex (Thesis (4.16))

The complex `H²(ℂ) --grad grad--> H(curl; S) --curl--> L²(T)` of Thesis (4.16), with `S` the
symmetric and `T` the trace-free `3 × 3` matrices, has at a frequency `ξ ∈ ℝ³` the symbols
`hess_ξ c = -c ξ ξᵀ` and the row-wise curl symbol restricted to symmetric matrices, which is
trace-free (Lemma 3.5). Its adjoint complex (4.17) is `div div ← sym curl`.

## Main results

* `symSub`, `trSub`; `Sym = ↥symSub`, `Tr = ↥trSub` (Hilbert spaces with the Frobenius product).
* `hess ξ : ℂ →L Sym`, `curlS ξ : Sym →L Tr`, `curlS_hess` (`curl grad grad = 0`).
* `tsdS ξ ⊆ Sym`, `tsdT ξ ⊆ Tr`: the transverse–traceless fibres, and **`isFibreReducing`**:
  `({0}, tsdS ξ, tsdT ξ)` reduces the fibre complex at every frequency (Lemma 3.5 on the symbol
  and self-adjointness of the matrix curl).
* `symCurl : FibreComplex ℂ ℝ³ ComplexShape.fin3 (W3 ℂ Sym Tr)`, homogeneous of degrees `2` and
  `1`, with measurable fibre projections.

## References

* [QuennevilleBelair2015], §3.4 (Lemma 3.5), §4.11 (Prop 4.19, (4.16)–(4.18))
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Matrix Finset

namespace Feec.Fourier.SymCurl

open GradCurl

/-- Symmetric matrices. -/
def symSub : Submodule ℂ Mat where
  carrier := {M | ∀ a b, M (a, b) = M (b, a)}
  zero_mem' := by simp
  add_mem' := by intro M N hM hN a b; simp [hM a b, hN a b]
  smul_mem' := by intro c M hM a b; simp [hM a b]

/-- Trace-free matrices. -/
def trSub : Submodule ℂ Mat where
  carrier := {M | ∑ a, M (a, a) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro M N hM hN
    simp only [Set.mem_ofPred_eq] at hM hN ⊢
    simp [sum_add_distrib, hM, hN]
  smul_mem' := by
    intro c M hM
    simp only [Set.mem_ofPred_eq] at hM ⊢
    simp [← mul_sum, hM]

/-- The fibre `S` of symmetric matrices (a type synonym of `↥symSub`, with its Hilbert space
structure declared once, so that instance search never unfolds the submodule). -/
def Sym : Type := ↥symSub
/-- The fibre `T` of trace-free matrices. -/
def Tr : Type := ↥trSub

instance : NormedAddCommGroup Sym := inferInstanceAs (NormedAddCommGroup ↥symSub)
instance : InnerProductSpace ℂ Sym := inferInstanceAs (InnerProductSpace ℂ ↥symSub)
instance : CompleteSpace Sym := inferInstanceAs (CompleteSpace ↥symSub)
instance : FiniteDimensional ℂ Sym := inferInstanceAs (FiniteDimensional ℂ ↥symSub)
instance : NormedSpace ℝ Sym := inferInstanceAs (NormedSpace ℝ ↥symSub)
instance : IsScalarTower ℝ ℂ Sym := inferInstanceAs (IsScalarTower ℝ ℂ ↥symSub)
instance : NormedAddCommGroup Tr := inferInstanceAs (NormedAddCommGroup ↥trSub)
instance : InnerProductSpace ℂ Tr := inferInstanceAs (InnerProductSpace ℂ ↥trSub)
instance : CompleteSpace Tr := inferInstanceAs (CompleteSpace ↥trSub)
instance : FiniteDimensional ℂ Tr := inferInstanceAs (FiniteDimensional ℂ ↥trSub)
instance : NormedSpace ℝ Tr := inferInstanceAs (NormedSpace ℝ ↥trSub)
instance : IsScalarTower ℝ ℂ Tr := inferInstanceAs (IsScalarTower ℝ ℂ ↥trSub)

/-- The matrix of an element of `S`. -/
@[coe] def Sym.val (M : Sym) : Mat := Subtype.val (p := (· ∈ symSub)) M
/-- The matrix of an element of `T`. -/
@[coe] def Tr.val (M : Tr) : Mat := Subtype.val (p := (· ∈ trSub)) M

instance : CoeOut Sym Mat := ⟨Sym.val⟩
instance : CoeOut Tr Mat := ⟨Tr.val⟩

theorem Sym.val_mem (M : Sym) : (M : Mat) ∈ symSub := Subtype.property (p := (· ∈ symSub)) M
theorem Tr.val_mem (M : Tr) : (M : Mat) ∈ trSub := Subtype.property (p := (· ∈ trSub)) M

/-- The element of `S` of a symmetric matrix. -/
def Sym.mk (M : Mat) (h : M ∈ symSub) : Sym := ⟨M, h⟩
/-- The element of `T` of a trace-free matrix. -/
def Tr.mk (M : Mat) (h : M ∈ trSub) : Tr := ⟨M, h⟩

@[simp] theorem Sym.val_mk (M : Mat) (h : M ∈ symSub) : (Sym.mk M h : Mat) = M := rfl
@[simp] theorem Tr.val_mk (M : Mat) (h : M ∈ trSub) : (Tr.mk M h : Mat) = M := rfl

@[ext] theorem Sym.ext {M N : Sym} (h : (M : Mat) = N) : M = N := Subtype.ext h
@[ext] theorem Tr.ext {M N : Tr} (h : (M : Mat) = N) : M = N := Subtype.ext h

@[simp] theorem Sym.val_zero : ((0 : Sym) : Mat) = 0 := rfl
@[simp] theorem Tr.val_zero : ((0 : Tr) : Mat) = 0 := rfl

theorem Sym.inner_val (M N : Sym) : ⟪M, N⟫_ℂ = ⟪(M : Mat), (N : Mat)⟫_ℂ := rfl
theorem Tr.inner_val (M N : Tr) : ⟪M, N⟫_ℂ = ⟪(M : Mat), (N : Mat)⟫_ℂ := rfl

theorem mem_symSub {M : Mat} : M ∈ symSub ↔ ∀ a b, M (a, b) = M (b, a) := Iff.rfl

theorem mem_trSub {M : Mat} : M ∈ trSub ↔ ∑ a, M (a, a) = 0 := Iff.rfl

theorem tsd_le_symSub (ξ : Freq) : tsd ξ ≤ symSub := fun M hM a b => by
  have := congrFun (congrFun hM.1 b) a
  simpa using this

theorem tsd_le_trSub (ξ : Freq) : tsd ξ ≤ trSub := fun M hM => by
  have := hM.2.1
  change ∑ a, M (a, a) = 0
  simpa [trace] using this

/-! ### The symbols -/

/-- The Hessian symbol `hess_ξ c = -c ξ ξᵀ` (`(grad grad u)_{ab} = ∂_a ∂_b u`), as
`grad_ξ (i c ξ)`. -/
def hessM (ξ : Freq) : ℂ →L[ℂ] Mat :=
  grad ξ ∘L (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
    (WithLp.toLp 2 fun a => Complex.I * (ξ a : ℂ) : Vec))

theorem hessM_apply (ξ : Freq) (c : ℂ) (a b : Fin 3) :
    hessM ξ c (a, b) = -(c * (ξ a : ℂ) * (ξ b : ℂ)) := by
  simp only [hessM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, grad_apply, PiLp.smul_apply, smul_eq_mul]
  have : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (c * (ξ a : ℂ) * (ξ b : ℂ)) * this

theorem hessM_mem_symSub (ξ : Freq) (c : ℂ) : hessM ξ c ∈ symSub := fun a b => by
  rw [hessM_apply, hessM_apply]; ring

/-- `hess_ξ : ℂ → S`. -/
def hess (ξ : Freq) : ℂ →L[ℂ] Sym := (hessM ξ).codRestrict symSub (hessM_mem_symSub ξ)

@[simp] theorem coe_hess (ξ : Freq) (c : ℂ) : (hess ξ c : Mat) = hessM ξ c := rfl

/-- The curl symbol maps symmetric matrices to trace-free ones. Thesis: Lemma 3.5 -/
theorem curl_mem_trSub (ξ : Freq) {M : Mat} (hM : M ∈ symSub) : curl ξ M ∈ trSub := by
  have hs : ∀ c, (MatrixSymbol.symbolJet (cfreq ξ) (toMatrix M) c)ᵀ =
      MatrixSymbol.symbolJet (cfreq ξ) (toMatrix M) c := fun c => by
    ext a b; simp [MatrixSymbol.symbolJet, hM a b]
  have h := MatrixSymbol.trace_curl_of_transpose_eq hs
  change ∑ a, toMatrix (curl ξ M) a a = 0
  rw [toMatrix_curl]
  have : (Complex.I • MatrixSymbol.curlSymbol (cfreq ξ) (toMatrix M)).trace = 0 := by
    rw [trace_smul]; exact (smul_eq_zero.2 (Or.inr h))
  simpa [trace] using this

/-- `curl_ξ : S → T`. -/
def curlS (ξ : Freq) : Sym →L[ℂ] Tr :=
  (curl ξ ∘L symSub.subtypeL).codRestrict trSub fun M => curl_mem_trSub ξ M.2

@[simp] theorem coe_curlS (ξ : Freq) (M : Sym) : (curlS ξ M : Mat) = curl ξ M := rfl

/-- **`curl_ξ hess_ξ = 0`**. -/
theorem curlS_hess (ξ : Freq) (c : ℂ) : curlS ξ (hess ξ c) = 0 := by
  apply Subtype.ext
  change curl ξ (hessM ξ c) = 0
  exact curl_grad ξ _

/-! ### The transverse–traceless fibres -/

/-- The TSD fibre in `S`. -/
def tsdS (ξ : Freq) : Submodule ℂ Sym := (tsd ξ).comap symSub.subtype

/-- The TSD fibre in `T`. -/
def tsdT (ξ : Freq) : Submodule ℂ Tr := (tsd ξ).comap trSub.subtype

theorem inner_hess_eq_zero {ξ : Freq} {M : Sym} (hM : M ∈ tsdS ξ) (c : ℂ) :
    ⟪hess ξ c, M⟫_ℂ = 0 := by
  rw [Sym.inner_val, coe_hess]
  exact inner_grad_eq_zero hM _

/-- Orthogonal complements in `S` (with the inner-product module structure). -/
abbrev orthS (K : Submodule ℂ Sym) : Submodule ℂ Sym := Submodule.orthogonal (𝕜 := ℂ) (E := Sym) K

/-- Orthogonal complements in `T`. -/
abbrev orthT (K : Submodule ℂ Tr) : Submodule ℂ Tr := Submodule.orthogonal (𝕜 := ℂ) (E := Tr) K

theorem hess_mem_orthogonal (ξ : Freq) (c : ℂ) : hess ξ c ∈ orthS (tsdS ξ) := by
  rw [Submodule.mem_orthogonal (𝕜 := ℂ) (E := Sym)]
  intro M hM
  rw [← inner_conj_symm, inner_hess_eq_zero hM, map_zero]

theorem curlS_mem_tsdT {ξ : Freq} {M : Sym} (hM : M ∈ tsdS ξ) : curlS ξ M ∈ tsdT ξ :=
  curl_mem_tsd hM

theorem curlS_mem_orthogonal {ξ : Freq} {N : Sym} (hN : N ∈ orthS (tsdS ξ)) :
    curlS ξ N ∈ orthT (tsdT ξ) := by
  rw [Submodule.mem_orthogonal (𝕜 := ℂ) (E := Sym)] at hN
  rw [Submodule.mem_orthogonal (𝕜 := ℂ) (E := Tr)]
  intro P hP
  rw [Tr.inner_val, coe_curlS, ← inner_curl]
  have hcP : curl ξ P ∈ tsd ξ := curl_mem_tsd hP
  have := hN (Sym.mk (curl ξ P) (tsd_le_symSub ξ hcP)) hcP
  rwa [Sym.inner_val] at this


/-! ### Frequency dependence and the fibre complex -/

theorem hessM_smul (t : ℝ) (ξ : Freq) : hessM (t • ξ) = ((t ^ 2 : ℝ) : ℂ) • hessM ξ := by
  refine ContinuousLinearMap.ext fun c => ?_
  ext ⟨a, b⟩
  simp only [hessM_apply, _root_.smul_apply, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_pow]
  ring

theorem hess_smul (t : ℝ) (ξ : Freq) : hess (t • ξ) = ((t ^ 2 : ℝ) : ℂ) • hess ξ := by
  refine ContinuousLinearMap.ext fun c => Subtype.ext ?_
  change hessM (t • ξ) c = ((t ^ 2 : ℝ) : ℂ) • hessM ξ c
  rw [hessM_smul]; rfl

theorem curlS_smul (t : ℝ) (ξ : Freq) : curlS (t • ξ) = (t : ℂ) • curlS ξ := by
  refine ContinuousLinearMap.ext fun M => Subtype.ext ?_
  change curl (t • ξ) M = (t : ℂ) • curl ξ M
  rw [curl_smul]; rfl

theorem continuous_hessM : Continuous hessM := by
  refine continuous_clm_apply.2 fun c => ?_
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p => ?_)
  change Continuous fun ξ : Freq => hessM ξ c (p.1, p.2)
  simp only [hessM_apply]
  exact ((continuous_const.mul (Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ p.1))).mul
    (Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ p.2))).neg

theorem continuous_hess : Continuous hess := by
  refine continuous_clm_apply.2 fun c => ?_
  have h : Continuous fun ξ => hessM ξ c := continuous_hessM.clm_apply continuous_const
  exact continuous_induced_rng.2 h

theorem continuous_curlS : Continuous curlS := by
  refine continuous_clm_apply.2 fun M => ?_
  have h : Continuous fun ξ => curl ξ (M : Mat) := continuous_curl.clm_apply continuous_const
  exact continuous_induced_rng.2 h

open ShortHilbertComplex in
/-- The symbols of the strong-symmetry complex on the window `Fin 3`. -/
def sym : ∀ i j : Fin 3, Freq → W3 ℂ Sym Tr i →L[ℂ] W3 ℂ Sym Tr j
  | 0, 1 => hess
  | 1, 2 => curlS
  | _, _ => 0

open ShortHilbertComplex in
/-- **The strong-symmetry family** `ℂ --hess_ξ--> S --curl_ξ--> T` (Thesis (4.16)). -/
def symCurl : FibreComplex ℂ Freq ComplexShape.fin3 (W3 ℂ Sym Tr) where
  m := sym
  shape i j h := by
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd rfl h
  comp i j k ξ := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      first
      | exact ContinuousLinearMap.ext fun c => curlS_hess ξ c
      | exact ContinuousLinearMap.zero_comp _
      | exact ContinuousLinearMap.comp_zero _
  cont i j := by
    fin_cases i <;> fin_cases j <;>
      first | exact continuous_hess | exact continuous_curlS | exact continuous_const

@[simp] theorem symCurl_m01 (ξ : Freq) : symCurl.m 0 1 ξ = hess ξ := rfl
@[simp] theorem symCurl_m12 (ξ : Freq) : symCurl.m 1 2 ξ = curlS ξ := rfl

theorem symCurl_isHomogeneous01 : symCurl.IsHomogeneous 0 1 2 := fun t ξ _ => by
  rw [symCurl_m01, symCurl_m01, hess_smul]; rfl

theorem symCurl_isHomogeneous12 : symCurl.IsHomogeneous 1 2 1 := fun t ξ _ => by
  rw [symCurl_m12, symCurl_m12, curlS_smul, pow_one]; rfl

open ShortHilbertComplex in
/-- **The constraint fibres** `({0}, tsd ξ ∩ S, tsd ξ ∩ T)` (Thesis Prop 4.19). -/
def tsdK : ∀ i : Fin 3, Freq → Submodule ℂ (W3 ℂ Sym Tr i)
  | 0 => fun _ => ⊥
  | 1 => tsdS
  | 2 => tsdT

instance (i : Fin 3) (ξ : Freq) : (tsdK i ξ).HasOrthogonalProjection := by
  fin_cases i <;> infer_instance

/-- **`({0}, tsdS ξ, tsdT ξ)` reduces the strong-symmetry fibre complex at every frequency.**
Thesis: Lemma 3.5, Prop 4.19 -/
theorem isFibreReducing : symCurl.IsFibreReducing tsdK := by
  refine FibreComplex.IsFibreReducing.of_orthogonal (fun i j ξ => ?_) (fun i j ξ => ?_)
  · fin_cases i <;> fin_cases j
    all_goals first
      | (rintro _ ⟨v, -, rfl⟩; exact Submodule.zero_mem _)
      | (rintro _ ⟨v, hv, rfl⟩; exact curlS_mem_tsdT hv)
      | (rintro _ ⟨v, hv, rfl⟩; rw [(Submodule.mem_bot ℂ).1 hv]; simp)
  · fin_cases i <;> fin_cases j
    all_goals first
      | (rintro _ ⟨v, -, rfl⟩; exact Submodule.zero_mem _)
      | (rintro _ ⟨v, hv, rfl⟩; exact curlS_mem_orthogonal hv)
      | (rintro _ ⟨v, -, rfl⟩; exact hess_mem_orthogonal ξ v)


/-! ### Measurability of the fibre projections -/

/-- The projection onto a subspace `K ≤ U` of a subspace `U`, computed in the ambient space. -/
theorem coe_starProjection_comap {U K : Submodule ℂ Mat} (h : K ≤ U) (x : U) :
    ((Submodule.starProjection (𝕜 := ℂ) (E := U) (K.comap U.subtype) x : U) : Mat) =
      K.starProjection (x : Mat) := by
  symm
  have hmem : ((Submodule.starProjection (𝕜 := ℂ) (E := U) (K.comap U.subtype) x : U) : Mat) ∈ K := by
    have := Submodule.starProjection_apply_mem (𝕜 := ℂ) (E := U) (K.comap U.subtype) x
    exact this
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem fun w hw => ?_
  have h1 := Submodule.sub_starProjection_mem_orthogonal (𝕜 := ℂ) (E := U) (K := K.comap U.subtype) x
  have := (Submodule.mem_orthogonal' (𝕜 := ℂ) (E := U) _ _).1 h1 ⟨w, h hw⟩ hw
  rwa [Submodule.coe_inner] at this

/-- `P_{tsdS ξ} = P_S P_{tsd ξ} ι` (a continuous function of `P_{tsd ξ}`). -/
theorem starProjection_tsdS (ξ : Freq) :
    Submodule.starProjection (𝕜 := ℂ) (E := Sym) (tsdS ξ) =
      symSub.orthogonalProjectionOnto ∘L (tsd ξ).starProjection ∘L symSub.subtypeL := by
  refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
  have h1 := coe_starProjection_comap (tsd_le_symSub ξ) x
  have h2 : symSub.orthogonalProjectionOnto ((tsd ξ).starProjection (x : Mat)) =
      ⟨_, tsd_le_symSub ξ (Submodule.starProjection_apply_mem _ _)⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      ⟨_, tsd_le_symSub ξ (Submodule.starProjection_apply_mem _ _)⟩
  exact h1.trans (congrArg Subtype.val h2).symm

theorem starProjection_tsdT (ξ : Freq) :
    Submodule.starProjection (𝕜 := ℂ) (E := Tr) (tsdT ξ) =
      trSub.orthogonalProjectionOnto ∘L (tsd ξ).starProjection ∘L trSub.subtypeL := by
  refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
  have h1 := coe_starProjection_comap (tsd_le_trSub ξ) x
  have h2 : trSub.orthogonalProjectionOnto ((tsd ξ).starProjection (x : Mat)) =
      ⟨_, tsd_le_trSub ξ (Submodule.starProjection_apply_mem _ _)⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      ⟨_, tsd_le_trSub ξ (Submodule.starProjection_apply_mem _ _)⟩
  exact h1.trans (congrArg Subtype.val h2).symm

theorem aestronglyMeasurable_starProjection_tsd {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f : α → Freq} (hf : Measurable f) :
    MeasureTheory.AEStronglyMeasurable (fun a => (tsd (f a)).starProjection) μ := by
  have : ProperSpace (Mat →L[ℂ] Mat) := FiniteDimensional.proper_rclike ℂ _
  have : SecondCountableTopology (Mat →L[ℂ] Mat) := secondCountable_of_proper
  exact (measurable_starProjection_tsd.comp hf).aestronglyMeasurable

/-- The fibre projections of the strong-symmetry constraint are measurable along any measurable
frequency map. -/
theorem aestronglyMeasurable_starProjection_tsdK {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f : α → Freq} (hf : Measurable f) (i : Fin 3) :
    MeasureTheory.AEStronglyMeasurable (fun a => (tsdK i (f a)).starProjection) μ := by
  fin_cases i
  · exact MeasureTheory.aestronglyMeasurable_const (b := (⊥ : Submodule ℂ ℂ).starProjection)
  · change MeasureTheory.AEStronglyMeasurable
      (fun a => Submodule.starProjection (𝕜 := ℂ) (E := Sym) (tsdS (f a))) μ
    simp_rw [starProjection_tsdS]
    exact ((ContinuousLinearMap.compL ℂ Sym Mat Sym symSub.orthogonalProjectionOnto).continuous.comp
      ((ContinuousLinearMap.compL ℂ Sym Mat Mat).flip symSub.subtypeL).continuous
        |>.comp_aestronglyMeasurable (aestronglyMeasurable_starProjection_tsd hf))
  · change MeasureTheory.AEStronglyMeasurable
      (fun a => Submodule.starProjection (𝕜 := ℂ) (E := Tr) (tsdT (f a))) μ
    simp_rw [starProjection_tsdT]
    exact ((ContinuousLinearMap.compL ℂ Tr Mat Tr trSub.orthogonalProjectionOnto).continuous.comp
      ((ContinuousLinearMap.compL ℂ Tr Mat Mat).flip trSub.subtypeL).continuous
        |>.comp_aestronglyMeasurable (aestronglyMeasurable_starProjection_tsd hf))

theorem hess_ne_zero : symCurl.m 0 1 ≠ 0 := by
  intro h
  have h' : hess (EuclideanSpace.single 0 1) = 0 := congrFun h _
  have := congrArg (fun T : ℂ →L[ℂ] Sym => (T 1 : Mat) (0, 0)) h'
  simp [coe_hess, hessM_apply] at this

theorem curlS_ne_zero : symCurl.m 1 2 ≠ 0 := by
  intro h
  have h' : curlS (EuclideanSpace.single 0 1) = 0 := congrFun h _
  set M : Sym := ⟨EuclideanSpace.single (0, 2) 1 + EuclideanSpace.single (2, 0) 1, fun a b => by
    fin_cases a <;> fin_cases b <;> simp⟩
  have := congrArg (fun T : Sym →L[ℂ] Tr => (T M : Mat) (0, 1)) h'
  simp only [coe_curlS, _root_.zero_apply, Tr.val_zero, PiLp.zero_apply] at this
  simp [M, Sym.val, curl_apply, Fin.sum_univ_three, leviCivita3_apply] at this


/-! ### Real symbols -/

theorem entryConj_mem_symSub {M : Mat} (hM : M ∈ symSub) : entryConj M ∈ symSub := fun a b => by
  simp [hM a b]

theorem entryConj_mem_trSub {M : Mat} (hM : M ∈ trSub) : entryConj M ∈ trSub := by
  change ∑ a, conj (M (a, a)) = 0
  rw [← map_sum, (show ∑ a, M (a, a) = 0 from hM), map_zero]

/-- Entrywise conjugation on `S`. -/
def cjS : Sym →L[ℝ] Sym :=
  LinearMap.mkContinuous
    { toFun := fun M => Sym.mk (entryConj (M : Mat)) (entryConj_mem_symSub M.val_mem)
      map_add' := fun M N => Sym.ext (map_add entryConj (M : Mat) N)
      map_smul' := fun r M => Sym.ext (entryConj.map_smul r (M : Mat)) } 1 fun M => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
    change ‖entryConj (M : Mat)‖ ≤ ‖(M : Mat)‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp

/-- Entrywise conjugation on `T`. -/
def cjT : Tr →L[ℝ] Tr :=
  LinearMap.mkContinuous
    { toFun := fun M => Tr.mk (entryConj (M : Mat)) (entryConj_mem_trSub M.val_mem)
      map_add' := fun M N => Tr.ext (map_add entryConj (M : Mat) N)
      map_smul' := fun r M => Tr.ext (entryConj.map_smul r (M : Mat)) } 1 fun M => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
    change ‖entryConj (M : Mat)‖ ≤ ‖(M : Mat)‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp

@[simp] theorem coe_cjS (M : Sym) : (cjS M : Mat) = entryConj (M : Mat) := rfl
@[simp] theorem coe_cjT (M : Tr) : (cjT M : Mat) = entryConj (M : Mat) := rfl

theorem inner_conj_conj (v w : ℂ) : ⟪conj v, conj w⟫_ℂ = ⟪w, v⟫_ℂ := by
  simp [RCLike.inner_apply, mul_comm]

/-- Complex conjugation on `ℂ` as a real-linear map. -/
def cjC : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap

@[simp] theorem cjC_apply (z : ℂ) : cjC z = conj z := rfl

theorem hess_neg_cj (ξ : Freq) (c : ℂ) : hess (-ξ) (cjC c) = cjS (hess ξ c) := by
  ext ⟨a, b⟩
  simp [coe_hess, hessM_apply]

theorem curlS_neg_cj (ξ : Freq) (M : Sym) : curlS (-ξ) (cjS M) = cjT (curlS ξ M) := by
  ext1
  simp only [coe_curlS, coe_cjS, coe_cjT]
  exact curl_neg_entryConj ξ _

open ShortHilbertComplex in
/-- Conjugation on the three fibres `ℂ, S, T`. -/
def cjW3 : ∀ i : Fin 3, W3 ℂ Sym Tr i →L[ℝ] W3 ℂ Sym Tr i
  | 0 => cjC
  | 1 => cjS
  | 2 => cjT

open ShortHilbertComplex in
/-- **The strong-symmetry symbols are real.** -/
theorem symCurl_neg_cj (i j : Fin 3) (ξ : Freq) (v : W3 ℂ Sym Tr i) :
    symCurl.m i j (-ξ) (cjW3 i v) = cjW3 j (symCurl.m i j ξ v) := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact hess_neg_cj ξ v
    | exact curlS_neg_cj ξ v
    | exact (map_zero (cjW3 _)).symm

open ShortHilbertComplex in
theorem cjW3_smul : ∀ (i : Fin 3) (a : ℂ) (v : W3 ℂ Sym Tr i),
    cjW3 i (a • v) = (starRingEnd ℂ) a • cjW3 i v
  | 0, a, v => map_mul (starRingEnd ℂ) a (show ℂ from v)
  | 1, a, v => Sym.ext (entryConj_smul a (Sym.val v))
  | 2, a, v => Tr.ext (entryConj_smul a (Tr.val v))

open ShortHilbertComplex in
theorem cjW3_cjW3 : ∀ (i : Fin 3) (v : W3 ℂ Sym Tr i), cjW3 i (cjW3 i v) = v
  | 0, v => Complex.conj_conj (show ℂ from v)
  | 1, v => Sym.ext (entryConj_entryConj (Sym.val v))
  | 2, v => Tr.ext (entryConj_entryConj (Tr.val v))

open ShortHilbertComplex in
theorem inner_cjW3 : ∀ (i : Fin 3) (v w : W3 ℂ Sym Tr i), ⟪cjW3 i v, cjW3 i w⟫_ℂ = ⟪w, v⟫_ℂ
  | 0, v, w => inner_conj_conj (show ℂ from v) (show ℂ from w)
  | 1, v, w => inner_entryConj (Sym.val v) (Sym.val w)
  | 2, v, w => inner_entryConj (Tr.val v) (Tr.val w)

end Feec.Fourier.SymCurl
