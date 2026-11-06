module

public import Solution.Defs
public import Solution.Forms
public import Feec.Instances.Maxwell

/-!
# The vector-proxy complex of the challenge

The challenge's scalar and vector fields `L2Field Ω ι` are `Feec`'s `L2F ℝ Ω ι` (`rfl`), and its
weak `grad`, `curl`, `div` are the maximal realizations of constant-coefficient operators
(`weakOp_eq`): the row-wise operators `Feec.Domain.vecOp 1` of `Feec` with the single row
dropped (`vOp`, `reindexOp`). The index types `vIdx` (`Fin 1`, `Fin 3`, `Fin 3`, `Fin 1`) carry
the complex `vC`, whose maximal complex is the unitary transport of `HΛ(Ω)` along the vector
proxies `Pq k` (`vC_maximalComplex_eq`, from
`Feec.Domain.ConstCoeffComplex.maximalComplex_eq_transport_ofMatrix` and `Feec`'s proxy identities
`Feec.Domain.vecOp_proxyMat`); `Pq` are the challenge's `proxy0`, `proxy1`, `proxy2`
(`Pq_zero`, `Pq_one`, `Pq_two`). A conforming family of `HΛ(Ω)` is carried to one of the
vector-proxy complex (`vFamily`, as `Feec.Instances.Maxwell.vecFamily`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §2 (vector proxies)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff
open Filter Topology Set LinearPMap MeasureTheory Feec.Domain

@[expose] public noncomputable section

namespace FEEC

/-! ### Reindexed constant-coefficient operators -/

section Reindex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι ι' κ κ' : Type*}

/-- `A` with its component index types reindexed along `r : ι' ≃ ι` and `s : κ' ≃ κ`. -/
def reindexOp (r : ι' ≃ ι) (s : κ' ≃ κ) (A : ConstCoeffOp E ℝ ι κ) : ConstCoeffOp E ℝ ι' κ' where
  coeff j i := A.coeff (s j) (r i)

theorem reindexOp_apply [Fintype ι] [Fintype ι'] (r : ι' ≃ ι) (s : κ' ≃ κ)
    (A : ConstCoeffOp E ℝ ι κ) (f : ι' → E → ℝ) (j : κ') :
    (reindexOp r s A).apply f j = A.apply (fun i => f (r.symm i)) (s j) := by
  funext x
  simp only [ConstCoeffOp.apply, reindexOp]
  rw [← Equiv.sum_comp r]
  simp only [Equiv.symm_apply_apply]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem formalAdj_reindexOp (r : ι' ≃ ι) (s : κ' ≃ κ) (A : ConstCoeffOp E ℝ ι κ) :
    (reindexOp r s A).formalAdj = reindexOp s r A.formalAdj := rfl

end Reindex

/-! ### The weak operators of the challenge are maximal realizations -/

variable {Ω : Set (Fin 3 → ℝ)}

/-- **A weak realization of the challenge is `Feec`'s maximal realization** of an operator `A`
whose formal adjoint acts on test fields as `Aᵗ`. -/
theorem weakOp_eq {ι κ : Type} [Fintype ι] [Fintype κ] (A : ConstCoeffOp (Fin 3 → ℝ) ℝ ι κ)
    (At : ((Fin 3 → ℝ) → κ → ℝ) → (Fin 3 → ℝ) → ι → ℝ)
    (hAt : ∀ ψ : (Fin 3 → ℝ) → κ → ℝ, (∀ j, IsTestFn Ω fun x => ψ x j) →
      ∀ x i, At ψ x i = A.formalAdj.apply (fun j y => ψ y j) i x) :
    weakOp Ω At = A.maximal Ω := by
  have hG : Submodule.span ℝ {p : L2Field Ω κ × L2Field Ω ι | ∃ ψ : (Fin 3 → ℝ) → κ → ℝ,
      (∀ j, IsTestFn Ω fun x => ψ x j) ∧ (∀ j, ⇑(p.1 j) =ᵐ[volume.restrict Ω] fun x => ψ x j) ∧
      ∀ i, ⇑(p.2 i) =ᵐ[volume.restrict Ω] fun x => At ψ x i} = A.formalAdj.testGraph Ω := by
    convert Submodule.span_eq (A.formalAdj.testGraph Ω) using 2
    ext p
    constructor
    · rintro ⟨ψ, hψ, h1, h2⟩
      set φ : κ → (Fin 3 → ℝ) → ℝ := fun j x => ψ x j
      have hφ : IsTestField Ω φ := fun j => isTest_of (hψ j)
      refine ⟨φ, hφ, Prod.ext (PiLp.ext fun j => Lp.ext ?_) (PiLp.ext fun i => Lp.ext ?_)⟩
      · filter_upwards [h1 j, coeFn_testField hφ j] with x hx hx'
        rw [hx]; exact hx'.symm
      · filter_upwards [h2 i, coeFn_testField (A.formalAdj.isTestField_apply hφ) i]
          with x hx hx'
        rw [hx, hx', hAt ψ hψ]
    · rintro ⟨φ, hφ, rfl⟩
      have hψ : ∀ j, IsTestFn Ω fun x => (fun x j => φ j x) x j := fun j => isTestFn_of (hφ j)
      refine ⟨fun x j => φ j x, hψ, fun j => ?_, fun i => ?_⟩
      · filter_upwards [coeFn_testField hφ j] with x hx
        rw [hx]
      · filter_upwards [coeFn_testField (A.formalAdj.isTestField_apply hφ) i] with x hx
        rw [hx, hAt _ hψ]
  unfold weakOp ConstCoeffOp.maximal ConstCoeffOp.minimal
  rw [hG]

/-! ### The index types and operators of the vector-proxy complex -/

/-- The component index types of the vector-proxy complex: scalars (`Fin 1`) in degrees `0`, `3`,
vectors (`Fin 3`) in degrees `1`, `2`. -/
abbrev vIdx : ℤ → Type
  | .ofNat 0 => Fin 1
  | .ofNat 1 => Fin 3
  | .ofNat 2 => Fin 3
  | .ofNat 3 => Fin 1
  | .ofNat (_ + 4) => Empty
  | .negSucc _ => Empty

instance instFintypeVIdx : ∀ k, Fintype (vIdx k)
  | .ofNat 0 => inferInstanceAs (Fintype (Fin 1))
  | .ofNat 1 => inferInstanceAs (Fintype (Fin 3))
  | .ofNat 2 => inferInstanceAs (Fintype (Fin 3))
  | .ofNat 3 => inferInstanceAs (Fintype (Fin 1))
  | .ofNat (_ + 4) => inferInstanceAs (Fintype Empty)
  | .negSucc _ => inferInstanceAs (Fintype Empty)

instance instDecidableEqVIdx : ∀ k, DecidableEq (vIdx k)
  | .ofNat 0 => inferInstanceAs (DecidableEq (Fin 1))
  | .ofNat 1 => inferInstanceAs (DecidableEq (Fin 3))
  | .ofNat 2 => inferInstanceAs (DecidableEq (Fin 3))
  | .ofNat 3 => inferInstanceAs (DecidableEq (Fin 1))
  | .ofNat (_ + 4) => inferInstanceAs (DecidableEq Empty)
  | .negSucc _ => inferInstanceAs (DecidableEq Empty)

/-- `Feec`'s row-wise index types with the single row dropped: `vIdx k ≃ vecIdx 1 k`. -/
def vEquiv : ∀ k : ℤ, vIdx k ≃ vecIdx 1 k
  | .ofNat 0 => Equiv.refl _
  | .ofNat 1 => (Equiv.uniqueProd (Fin 3) (Fin 1)).symm
  | .ofNat 2 => (Equiv.uniqueProd (Fin 3) (Fin 1)).symm
  | .ofNat 3 => Equiv.refl _
  | .ofNat (_ + 4) => Equiv.refl _
  | .negSucc _ => Equiv.refl _

/-- The operators `grad`, `curl`, `div` of the vector-proxy complex. -/
def vOp (k : ℤ) : ConstCoeffOp (Fin 3 → ℝ) ℝ (vIdx k) (vIdx (k + 1)) :=
  reindexOp (vEquiv k) (vEquiv (k + 1)) (vecOp ℝ 1 k)

/-- `vOp` is `Feec`'s `vecOp 1` up to the index types. -/
theorem vOp_apply (k : ℤ) (f : vIdx k → (Fin 3 → ℝ) → ℝ) (j : vIdx (k + 1)) :
    (vOp k).apply f j = (vecOp ℝ 1 k).apply (fun i => f ((vEquiv k).symm i)) (vEquiv (k + 1) j) :=
  reindexOp_apply _ _ _ f j

/-- **The vector-proxy complex** `grad`, `curl`, `div` on `ℝ³` with the index types `vIdx`. -/
def vC : ConstCoeffComplex (Fin 3 → ℝ) ℝ where
  ι := vIdx
  A := vOp
  comp k f hf := by
    funext j
    rw [vOp_apply]
    have : (fun i => (vOp k).apply f ((vEquiv (k + 1)).symm i)) =
        (vecOp ℝ 1 k).apply fun i => f ((vEquiv k).symm i) := by
      funext i
      rw [vOp_apply, Equiv.apply_symm_apply]
    rw [this, vecOp_comp 1 k _ fun i => hf _]
    rfl

instance (k : ℤ) : DecidableEq (vC.ι k) := inferInstanceAs (DecidableEq (vIdx k))

/-! ### The vector proxies -/

/-- The proxy matrices: `Feec`'s `proxyMat` with the single row dropped. -/
def Qm (k : ℤ) : Matrix (vIdx k) (formIdx 3 k) ℝ :=
  signedPerm (vEquiv k) (fun _ => 1) * proxyMat k

theorem Qm_mul_transpose (k : ℤ) : Qm k * (Qm k).transpose = 1 := by
  rw [Qm, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (proxyMat k),
    proxyMat_mul_transpose, Matrix.one_mul]
  exact signedPerm_mul_transpose _ fun _ => mul_one 1

theorem transpose_mul_Qm (k : ℤ) : (Qm k).transpose * Qm k = 1 := by
  rw [Qm, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (signedPerm _ _).transpose,
    transpose_mul_signedPerm _ fun _ => mul_one 1, Matrix.one_mul]
  exact transpose_mul_proxyMat k

/-- **`vC` is intertwined with the de Rham complex by the proxy matrices** (`Feec`'s
`vecOp_proxyMat`, reindexed). -/
theorem vOp_Qm (k : ℤ) (f : formIdx 3 k → (Fin 3 → ℝ) → ℝ) :
    (vOp k).apply ((ConstCoeffOp.ofMatrix (Qm k)).apply f) =
      (ConstCoeffOp.ofMatrix (Qm (k + 1))).apply ((extDerivOp ℝ 3 k).apply f) := by
  rw [Qm, Qm, ← ConstCoeffOp.ofMatrix_apply_ofMatrix, ← ConstCoeffOp.ofMatrix_apply_ofMatrix,
    ofMatrix_signedPerm_apply, ofMatrix_signedPerm_apply]
  funext j
  rw [vOp_apply]
  simp only [one_smul, Equiv.apply_symm_apply]
  exact congrFun (vecOp_proxyMat k f) _

/-- The vector proxy `L²Λᵏ(Ω) ≃ L²(Ω; ℝ^{vIdx k})`, a unitary map. -/
def Pq (k : ℤ) : L2F ℝ Ω (formIdx 3 k) ≃ₗᵢ[ℝ] L2F ℝ Ω (vIdx k) where
  toLinearEquiv := (L2F.ofMatrixEquiv (Qm k) (Qm k).transpose (Qm_mul_transpose k)
    (transpose_mul_Qm k)).toLinearEquiv
  norm_map' := L2F.norm_ofMatrixCLM (by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact transpose_mul_Qm k)

theorem Pq_apply (k : ℤ) (u : L2F ℝ Ω (formIdx 3 k)) : Pq k u = L2F.ofMatrixCLM (Qm k) u := rfl

/-- **The maximal vector-proxy complex is the unitary transport of `HΛ(Ω)`** along `Pq`. -/
theorem vC_maximalComplex_eq (hΩ : IsOpen Ω) :
    vC.maximalComplex hΩ = ((deRham ℝ 3).maximalComplex hΩ).map Pq :=
  ConstCoeffComplex.maximalComplex_eq_transport_ofMatrix (deRham ℝ 3) vC Qm
    (fun k => (Qm k).transpose) Qm_mul_transpose transpose_mul_Qm hΩ fun k f _ => vOp_Qm k f

theorem isChainIso_Pq (hΩ : IsOpen Ω) :
    Feec.HilbertComplex.IsChainIso (vC.maximalComplex hΩ) ((deRham ℝ 3).maximalComplex hΩ)
      fun k => (Pq k).toContinuousLinearEquiv.symm := by
  rw [vC_maximalComplex_eq hΩ]
  exact (Feec.HilbertComplex.isChainIso_transport _ _).symm

/-- **The vector proxies of a conforming family** `F` of `HΛ(Ω)`: the subcomplexes `Pq Vₕ` of the
vector-proxy complex with the cochain projections `Pq πₕ Pq⁻¹`. -/
def vFamily (hΩ : IsOpen Ω) {κ : Type*}
    (F : Feec.HilbertComplex.ConformingFamily ((deRham ℝ 3).maximalComplex hΩ) κ) :
    Feec.HilbertComplex.ConformingFamily (vC.maximalComplex hΩ) κ :=
  haveI : ∀ h i, FiniteDimensional ℝ (((isChainIso_Pq hΩ).comapSub (F.V h)).V i) :=
    fun h i => haveI := F.finiteDimensional h
      (isChainIso_Pq hΩ).finiteDimensional_comapSub _ i
  (isChainIso_Pq hΩ).comapFamily F (fun h => (isChainIso_Pq hΩ).comapSub (F.V h))
    (fun _ _ _ => Iff.rfl) (M := 1) (M' := 1)
    (fun k => (Pq k).symm.toLinearIsometry.norm_toContinuousLinearMap_le)
    (fun k => (Pq k).toLinearIsometry.norm_toContinuousLinearMap_le)

theorem mem_vFamily_V_iff (hΩ : IsOpen Ω) {κ : Type*}
    (F : Feec.HilbertComplex.ConformingFamily ((deRham ℝ 3).maximalComplex hΩ) κ) (h : κ)
    (k : ℤ) (u : L2F ℝ Ω (vIdx k)) :
    u ∈ ((vFamily hΩ F).V h).V k ↔ (Pq k).symm u ∈ (F.V h).V k := Iff.rfl

/-! ### The challenge's operators and proxies -/

/-- **The weak gradient** is the maximal realization of `vOp 0`. -/
theorem grad_eq : grad Ω = (vOp 0).maximal Ω := by
  refine weakOp_eq _ _ fun ψ _ x i => ?_
  rw [show (vOp 0).formalAdj = reindexOp (vEquiv 1) (vEquiv 0) (gradOp 3 1).formalAdj from rfl,
    reindexOp_apply, gradOp_formalAdj_apply]
  rfl

/-- **The weak curl** is the maximal realization of `vOp 1`. -/
theorem curl_eq : curl Ω = (vOp 1).maximal Ω := by
  refine weakOp_eq _ _ fun ψ _ x i => ?_
  rw [show (vOp 1).formalAdj = reindexOp (vEquiv 2) (vEquiv 1) (curlOp 1).formalAdj from rfl,
    reindexOp_apply, curlOp_formalAdj_apply, curlOp_apply]
  rfl

/-- **The weak divergence** is the maximal realization of `vOp 2`. -/
theorem div_eq : div Ω = (vOp 2).maximal Ω := by
  refine weakOp_eq _ _ fun ψ _ x i => ?_
  rw [show (vOp 2).formalAdj = reindexOp (vEquiv 3) (vEquiv 2) (divOp 3 1).formalAdj from rfl,
    reindexOp_apply, divOp_formalAdj_apply]
  rfl

/-- The Maxwell window `H¹(Ω) --grad--> H(curl, Ω) --curl--> L²(Ω; ℝ³)` of the vector-proxy
complex: its first differential is the weak gradient, -/
theorem window_d_zero (hΩ : IsOpen Ω) :
    ((vC.maximalComplex hΩ).window 0 3).d 0 1 = grad Ω :=
  (vC.maximalComplex_d hΩ 0).trans grad_eq.symm

/-- its second differential is the weak curl, -/
theorem window_d_one (hΩ : IsOpen Ω) :
    ((vC.maximalComplex hΩ).window 0 3).d 1 2 = curl Ω :=
  (vC.maximalComplex_d hΩ 1).trans curl_eq.symm

/-- and the differential after the window is the weak divergence. -/
theorem d_two (hΩ : IsOpen Ω) :
    (vC.maximalComplex hΩ).d (0 + ((2 : Fin 3) : ℤ)) (0 + ((2 : Fin 3) : ℤ) + 1) = div Ω :=
  (vC.maximalComplex_d hΩ 2).trans div_eq.symm

theorem ofMatrixCLM_signedPerm_apply {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (e : κ ≃ ι) (ε : κ → ℝ) (u : L2F ℝ Ω ι) (a : κ) :
    L2F.ofMatrixCLM (signedPerm e ε) u a = ε a • u (e a) := by
  rw [L2F.ofMatrixCLM_apply]
  simp [signedPerm]

theorem Pq_apply' (k : ℤ) (u : L2F ℝ Ω (formIdx 3 k)) (a : vIdx k) :
    Pq k u a = proxySgn k (vEquiv k a) • u (proxyIdx k (vEquiv k a)) := by
  rw [Pq_apply, Qm, ← L2F.ofMatrixCLM_ofMatrixCLM, ofMatrixCLM_signedPerm_apply, one_smul,
    proxyMat, ofMatrixCLM_signedPerm_apply]

/-- `Pq 0` is the challenge's `proxy0`. -/
theorem Pq_zero (u : L2Form Ω 0) : Pq 0 u = proxy0 u :=
  PiLp.ext fun a => (Pq_apply' 0 u a).trans (one_smul ℝ _)

/-- `Pq 1` is the challenge's `proxy1`. -/
theorem Pq_one (u : L2Form Ω 1) : Pq 1 u = proxy1 u :=
  PiLp.ext fun a => (Pq_apply' 1 u a).trans (one_smul ℝ _)

/-- `Pq 2` is the challenge's `proxy2`. -/
theorem Pq_two (u : L2Form Ω 2) : Pq 2 u = proxy2 u := by
  refine PiLp.ext fun a => (Pq_apply' 2 u a).trans ?_
  change ((Feec.Koszul.Proxy3.vec2Sign a : ℤ) : ℝ) • u ⟨{a}ᶜ, _⟩ = (-1 : ℝ) ^ (a : ℕ) • u ⟨Finset.univ.erase a, _⟩
  have hs : ({a}ᶜ : Finset (Fin 3)) = Finset.univ.erase a := by
    ext b; simp [eq_comm]
  congr 1
  · fin_cases a <;> simp [Feec.Koszul.Proxy3.vec2Sign]
  · exact congrArg u (Subtype.ext hs)

/-! ### The Maxwell window and its strong solutions -/

/-- The total space `L²(Ω) × L²(Ω; ℝ³) × L²(Ω; ℝ³)` of the Maxwell window (an `ℓ²` sum). -/
abbrev MX (Ω : Set (Fin 3 → ℝ)) : Type := PiLp 2 fun i : Fin 3 => L2F ℝ Ω (vC.ι (0 + (i : ℤ)))

/-- The point `(σ, E, B)` of the total space. -/
def pack (σ : L2Field Ω (Fin 1)) (E B : L2Field Ω (Fin 3)) : MX Ω :=
  WithLp.toLp 2 (Fin.cons σ (Fin.cons E (Fin.cons B finZeroElim)))

section Pack

variable (σ : L2Field Ω (Fin 1)) (E B : L2Field Ω (Fin 3))

@[simp] theorem pack_zero : pack σ E B 0 = σ := rfl

@[simp] theorem pack_one : pack σ E B 1 = E := rfl

@[simp] theorem pack_two : pack σ E B 2 = B := rfl

end Pack

theorem pack_eta (x : MX Ω) : pack (x 0) (x 1) (x 2) = x :=
  PiLp.ext fun i => by fin_cases i <;> rfl

theorem norm_sq_MX (x : MX Ω) : ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 + ‖x 2‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]

theorem hasDerivWithinAt_pack {s : Set ℝ} {t : ℝ} {σ : ℝ → L2Field Ω (Fin 1)}
    {E B : ℝ → L2Field Ω (Fin 3)} {σ' : L2Field Ω (Fin 1)} {E' B' : L2Field Ω (Fin 3)}
    (hσ : HasDerivWithinAt σ σ' s t) (hE : HasDerivWithinAt E E' s t)
    (hB : HasDerivWithinAt B B' s t) :
    HasDerivWithinAt (fun t => pack (σ t) (E t) (B t)) (pack σ' E' B') s t := by
  have h : HasDerivWithinAt (fun t => WithLp.ofLp (pack (σ t) (E t) (B t)))
      (WithLp.ofLp (pack σ' E' B')) s t := by
    refine hasDerivWithinAt_pi.2 fun i => ?_
    fin_cases i
    exacts [hσ, hE, hB]
  exact (PiLp.continuousLinearEquiv 2 ℝ _).symm.hasFDerivAt.comp_hasDerivWithinAt t h

theorem hasDerivWithinAt_apply_MX {s : Set ℝ} {t : ℝ} {U : ℝ → MX Ω} {U' : MX Ω}
    (h : HasDerivWithinAt U U' s t) (i : Fin 3) :
    HasDerivWithinAt (fun t => U t i) (U' i) s t := by
  have h' := (PiLp.proj (𝕜 := ℝ) 2 (fun i : Fin 3 => L2F ℝ Ω (vC.ι (0 + (i : ℤ)))) i
    ).hasFDerivAt.comp_hasDerivWithinAt t h
  exact h'

theorem tendsto_pack {σ : ℕ → L2Field Ω (Fin 1)} {E B : ℕ → L2Field Ω (Fin 3)}
    {σ₀ : L2Field Ω (Fin 1)} {E₀ B₀ : L2Field Ω (Fin 3)} (hσ : Tendsto σ atTop (𝓝 σ₀))
    (hE : Tendsto E atTop (𝓝 E₀)) (hB : Tendsto B atTop (𝓝 B₀)) :
    Tendsto (fun N => pack (σ N) (E N) (B N)) atTop (𝓝 (pack σ₀ E₀ B₀)) := by
  have h : Tendsto (fun N => WithLp.ofLp (pack (σ N) (E N) (B N))) atTop
      (𝓝 (WithLp.ofLp (pack σ₀ E₀ B₀))) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    fin_cases i
    exacts [hσ, hE, hB]
  exact ((PiLp.continuousLinearEquiv 2 ℝ _).symm.continuous.tendsto _).comp h

theorem tendsto_apply_MX {l : Filter ℕ} {U : ℕ → MX Ω} {x : MX Ω} (h : Tendsto U l (𝓝 x))
    (i : Fin 3) : Tendsto (fun N => U N i) l (𝓝 (x i)) :=
  ((PiLp.proj (𝕜 := ℝ) 2 _ i).continuous.tendsto _).comp h

theorem tendstoUniformlyOn_apply_MX {κ : Type*} {l : Filter κ} {s : Set ℝ}
    {U : κ → ℝ → MX Ω} {V : ℝ → MX Ω} (h : TendstoUniformlyOn U V l s) (i : Fin 3) :
    TendstoUniformlyOn (fun N t => U N t i) (fun t => V t i) l s := by
  have h' := (PiLp.proj (𝕜 := ℝ) 2 (fun i : Fin 3 => L2F ℝ Ω (vC.ι (0 + (i : ℤ)))) i
    ).uniformContinuous.comp_tendstoUniformlyOn h
  exact h'

theorem apply_eq_of_mem_graph {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] {T : E →ₗ.[ℝ] F} (x : T.domain) {y : F} (h : ((x : E), y) ∈ T.graph) :
    T x = y := by
  obtain ⟨z, hz, hTz⟩ := (LinearPMap.mem_graph_iff T).1 h
  simp only at hz hTz
  rw [← hTz]
  exact congrArg T (Subtype.ext hz.symm)

theorem mem_domain_of_mem_graph {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] {T : E →ₗ.[ℝ] F} {x : E} {y : F} (h : (x, y) ∈ T.graph) : x ∈ T.domain := by
  obtain ⟨z, hz, -⟩ := (LinearPMap.mem_graph_iff T).1 h
  simp only at hz
  exact hz ▸ z.2

variable (hΩ : IsOpen Ω)

/-- The Maxwell window `H¹(Ω) → H(curl, Ω) → L²(Ω; ℝ³)` of the vector-proxy complex. -/
abbrev Win : Feec.HilbertComplex ℝ (ComplexShape.window 3) fun i : Fin 3 => L2F ℝ Ω (vC.ι (0 + i)) :=
  (vC.maximalComplex hΩ).window 0 3

theorem grad_eq_window : grad Ω = (Win hΩ).d 0 1 := (window_d_zero hΩ).symm

theorem curl_eq_window : curl Ω = (Win hΩ).d 1 2 := (window_d_one hΩ).symm

/-- **Strong solutions of the Hodge wave equation of the Maxwell window are strong solutions of
Maxwell's equations** (`wave_apply_fin3_zero`, `_one`, `_two`). -/
theorem isMaxwellSolution_of {T : ℝ} {U : ℝ → MX Ω}
    (hU : Feec.Evolution.IsStrongSolution (Win hΩ).wave (Icc 0 T) 0 U) :
    IsMaxwellSolution Ω T (fun t => U t 0) (fun t => U t 1) (fun t => U t 2) := by
  intro t ht
  obtain ⟨v, hv, hd⟩ := hU.deriv t ht
  rw [Pi.zero_apply, add_zero] at hd
  obtain ⟨y, hy, hLy⟩ := (LinearPMap.mem_graph_iff _).1 hv
  simp only at hy hLy
  have h0 : v 0 = -((Win hΩ).d 0 1)† ⟨U t 1, hy ▸ y.2.2 1 0⟩ := by
    rw [← hLy, Feec.HilbertComplex.wave_apply_fin3_zero]; congr 3; exact congrFun (congrArg _ hy) 1
  have h1 : v 1 = (Win hΩ).d 0 1 ⟨U t 0, hy ▸ y.2.1 0 1⟩ -
      ((Win hΩ).d 1 2)† ⟨U t 2, hy ▸ y.2.2 2 1⟩ := by
    rw [← hLy, Feec.HilbertComplex.wave_apply_fin3_one]
    congr 3 <;> exact congrFun (congrArg _ hy) _
  have h2 : v 2 = (Win hΩ).d 1 2 ⟨U t 1, hy ▸ y.2.1 1 2⟩ := by
    rw [← hLy, Feec.HilbertComplex.wave_apply_fin3_two]; congr 2; exact congrFun (congrArg _ hy) 1
  refine ⟨v 0, v 1, v 2, (Win hΩ).d 0 1 ⟨U t 0, hy ▸ y.2.1 0 1⟩,
    ((Win hΩ).d 1 2)† ⟨U t 2, hy ▸ y.2.2 2 1⟩, hasDerivWithinAt_apply_MX hd 0, hasDerivWithinAt_apply_MX hd 1,
    hasDerivWithinAt_apply_MX hd 2, ?_,
    ?_, ?_, h1, ?_⟩
  · rw [grad_eq_window hΩ]
    exact (LinearPMap.mem_graph_iff _).2 ⟨⟨U t 1, hy ▸ y.2.2 1 0⟩, rfl, by
      rw [h0]; exact (neg_neg _).symm⟩
  · rw [grad_eq_window hΩ]
    exact (LinearPMap.mem_graph_iff _).2 ⟨⟨U t 0, hy ▸ y.2.1 0 1⟩, rfl, rfl⟩
  · rw [curl_eq_window hΩ]
    exact (LinearPMap.mem_graph_iff _).2 ⟨⟨U t 2, hy ▸ y.2.2 2 1⟩, rfl, rfl⟩
  · rw [curl_eq_window hΩ]
    exact (LinearPMap.mem_graph_iff _).2 ⟨⟨U t 1, hy ▸ y.2.1 1 2⟩, rfl, h2.symm⟩

/-- **Strong solutions of Maxwell's equations are strong solutions of the Hodge wave equation of
the Maxwell window.** -/
theorem isStrongSolution_of {T : ℝ} {σ : ℝ → L2Field Ω (Fin 1)} {E B : ℝ → L2Field Ω (Fin 3)}
    (h : IsMaxwellSolution Ω T σ E B) :
    Feec.Evolution.IsStrongSolution (Win hΩ).wave (Icc 0 T) 0
      fun t => pack (σ t) (E t) (B t) := by
  refine Feec.Evolution.IsStrongSolution.of_deriv fun t ht => ?_
  obtain ⟨σ', E', B', g, c, hσ, hE, hB, h1, h2, h3, h4, h5⟩ := h t ht
  rw [grad_eq_window hΩ] at h1 h2
  rw [curl_eq_window hΩ] at h3 h5
  have hx : pack (σ t) (E t) (B t) ∈ (Win hΩ).wave.domain :=
    Feec.HilbertComplex.mem_wave_domain_fin3 (Win hΩ) (mem_domain_of_mem_graph h2)
      (mem_domain_of_mem_graph h5) (mem_domain_of_mem_graph h1) (mem_domain_of_mem_graph h3)
  refine ⟨pack σ' E' B', (LinearPMap.mem_graph_iff _).2 ⟨⟨_, hx⟩, rfl, ?_⟩, ?_⟩
  · change (Win hΩ).wave ⟨_, hx⟩ = pack σ' E' B'
    rw [← pack_eta ((Win hΩ).wave ⟨_, hx⟩)]
    congr 1
    · rw [Feec.HilbertComplex.wave_apply_fin3_zero (Win hΩ) ⟨_, hx⟩,
        apply_eq_of_mem_graph _ h1]
      exact neg_neg _
    · rw [Feec.HilbertComplex.wave_apply_fin3_one (Win hΩ) ⟨_, hx⟩, apply_eq_of_mem_graph _ h2,
        apply_eq_of_mem_graph _ h3]
      exact h4.symm
    · rw [Feec.HilbertComplex.wave_apply_fin3_two (Win hΩ) ⟨_, hx⟩, apply_eq_of_mem_graph _ h5]
  · rw [Pi.zero_apply, add_zero]
    exact hasDerivWithinAt_pack hσ hE hB

/-! ### Galerkin solutions -/

theorem totalD_win_zero (x : (Win hΩ).totalD.domain) : ((Win hΩ).totalD x) 0 = 0 := by
  rw [Feec.HilbertComplex.totalD_apply]
  exact Finset.sum_eq_zero fun i _ => (Win hΩ).apply_eq_zero_of_not_rel (by simp) _

theorem totalD_win_one (x : (Win hΩ).totalD.domain) :
    ((Win hΩ).totalD x) 1 = (Win hΩ).d 0 1 ⟨(x : MX Ω) 0, x.2 0 1⟩ := by
  rw [Feec.HilbertComplex.totalD_apply, Fin.sum_univ_three,
    (Win hΩ).apply_eq_zero_of_not_rel (i := 1) (j := 1) (by simp),
    (Win hΩ).apply_eq_zero_of_not_rel (i := 2) (j := 1) (by simp), add_zero, add_zero]

theorem totalD_win_two (x : (Win hΩ).totalD.domain) :
    ((Win hΩ).totalD x) 2 = (Win hΩ).d 1 2 ⟨(x : MX Ω) 1, x.2 1 2⟩ := by
  rw [Feec.HilbertComplex.totalD_apply, Fin.sum_univ_three,
    (Win hΩ).apply_eq_zero_of_not_rel (i := 0) (j := 2) (by simp),
    (Win hΩ).apply_eq_zero_of_not_rel (i := 2) (j := 2) (by simp)]
  simp only [zero_add, add_zero]

theorem inner_MX (z w : MX Ω) : ⟪z, w⟫_ℝ = ⟪z 0, w 0⟫_ℝ + ⟪z 1, w 1⟫_ℝ + ⟪z 2, w 2⟫_ℝ := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]

/-- **The wave form of the Maxwell window**: `a((σ, E, B), (τ, F, G)) = ⟪grad τ, E⟫ + ⟪curl F, B⟫ -
⟪F, grad σ⟫ - ⟪G, curl E⟫`. -/
theorem waveForm_win (x y : (Win hΩ).totalD.domain) :
    Feec.HodgeWave.waveForm (Win hΩ).totalD ((Win hΩ).totalD.toGraphSpace x)
        ((Win hΩ).totalD.toGraphSpace y) =
      ⟪(Win hΩ).d 0 1 ⟨(y : MX Ω) 0, y.2 0 1⟩, (x : MX Ω) 1⟫_ℝ +
        ⟪(Win hΩ).d 1 2 ⟨(y : MX Ω) 1, y.2 1 2⟩, (x : MX Ω) 2⟫_ℝ -
        ⟪(y : MX Ω) 1, (Win hΩ).d 0 1 ⟨(x : MX Ω) 0, x.2 0 1⟩⟫_ℝ -
        ⟪(y : MX Ω) 2, (Win hΩ).d 1 2 ⟨(x : MX Ω) 1, x.2 1 2⟩⟫_ℝ := by
  rw [Feec.HodgeWave.waveForm_apply]
  simp only [LinearPMap.graphSnd_toGraphSpace, LinearPMap.graphFst_toGraphSpace]
  rw [inner_MX, inner_MX, totalD_win_zero, totalD_win_one, totalD_win_two, totalD_win_zero,
    totalD_win_one, totalD_win_two]
  simp only [inner_zero_left, inner_zero_right, zero_add]
  ring

theorem graph_val {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] {T : E →ₗ.[ℝ] F} {x : E} (hx : x ∈ T.domain) {y : F} (h : (x, y) ∈ T.graph) :
    T ⟨x, hx⟩ = y := by
  obtain ⟨z, hz, hTz⟩ := (LinearPMap.mem_graph_iff T).1 h
  exact (congrArg T (Subtype.ext hz.symm)).trans hTz

theorem mem_grad_graph {p : L2Field Ω (Fin 1) × L2Field Ω (Fin 3)} :
    p ∈ (grad Ω).graph ↔ p ∈ ((Win hΩ).d 0 1).graph := by
  rw [grad_eq_window hΩ]; exact Iff.rfl

theorem mem_curl_graph {p : L2Field Ω (Fin 3) × L2Field Ω (Fin 3)} :
    p ∈ (curl Ω).graph ↔ p ∈ ((Win hΩ).d 1 2).graph := by
  rw [curl_eq_window hΩ]; exact Iff.rfl

set_option maxHeartbeats 1000000 in
/-- **The semi-discrete Maxwell equation in components**: for `ξ = (σ, E, B)`, `ψ = (τ, F, G)` in
the graph space and `v = (σ', E', B')`, `⟪ψ, v⟫ + a(ξ, ψ) = ⟪τ, σ'⟫ + ⟪F, E'⟫ + ⟪G, B'⟫ +
⟪grad τ, E⟫ + ⟪curl F, B⟫ - ⟪F, grad σ⟫ - ⟪G, curl E⟫`. -/
theorem galerkin_eq (ξ ψ : (Win hΩ).totalD.GraphSpace) (v : MX Ω) {σ τ σ' : L2Field Ω (Fin 1)}
    {E B F G E' B' : L2Field Ω (Fin 3)} (hξ : (Win hΩ).totalD.graphFst ξ = pack σ E B)
    (hψ : (Win hΩ).totalD.graphFst ψ = pack τ F G) (hv : v = pack σ' E' B')
    {gξ gψ cξ cψ : L2Field Ω (Fin 3)} (hgξ : (σ, gξ) ∈ (grad Ω).graph)
    (hgψ : (τ, gψ) ∈ (grad Ω).graph) (hcξ : (E, cξ) ∈ (curl Ω).graph)
    (hcψ : (F, cψ) ∈ (curl Ω).graph) :
    ⟪(Win hΩ).totalD.graphFst ψ, v⟫_ℝ + Feec.HodgeWave.waveForm (Win hΩ).totalD ξ ψ =
      ⟪τ, σ'⟫_ℝ + ⟪F, E'⟫_ℝ + ⟪G, B'⟫_ℝ + ⟪gψ, E⟫_ℝ + ⟪cψ, B⟫_ℝ - ⟪F, gξ⟫_ℝ - ⟪G, cξ⟫_ℝ := by
  subst hv
  obtain ⟨x, rfl, -, -⟩ := (Win hΩ).totalD.exists_toGraphSpace_eq ξ
  obtain ⟨y, rfl, -, -⟩ := (Win hΩ).totalD.exists_toGraphSpace_eq ψ
  rw [LinearPMap.graphFst_toGraphSpace] at hξ hψ
  have h0 : ((x : MX Ω) 0, gξ) ∈ ((Win hΩ).d 0 1).graph := by
    rw [show (x : MX Ω) 0 = σ from congrArg (fun z : MX Ω => z 0) hξ]
    exact (mem_grad_graph hΩ).1 hgξ
  have h1 : ((y : MX Ω) 0, gψ) ∈ ((Win hΩ).d 0 1).graph := by
    rw [show (y : MX Ω) 0 = τ from congrArg (fun z : MX Ω => z 0) hψ]
    exact (mem_grad_graph hΩ).1 hgψ
  have h2 : ((x : MX Ω) 1, cξ) ∈ ((Win hΩ).d 1 2).graph := by
    rw [show (x : MX Ω) 1 = E from congrArg (fun z : MX Ω => z 1) hξ]
    exact (mem_curl_graph hΩ).1 hcξ
  have h3 : ((y : MX Ω) 1, cψ) ∈ ((Win hΩ).d 1 2).graph := by
    rw [show (y : MX Ω) 1 = F from congrArg (fun z : MX Ω => z 1) hψ]
    exact (mem_curl_graph hΩ).1 hcψ
  rw [waveForm_win, LinearPMap.graphFst_toGraphSpace, inner_MX, graph_val _ h0, graph_val _ h1,
    graph_val _ h2, graph_val _ h3, hξ, hψ]
  rw [show ∀ a b c d e f g : ℝ, a + b + c + (d + e - f - g) = a + b + c + d + e - f - g from
    fun _ _ _ _ _ _ _ => by ring]
  rfl

/-- `galerkin_eq` as the Galerkin equation of the challenge. -/
theorem galerkin_iff (ξ ψ : (Win hΩ).totalD.GraphSpace) (v : MX Ω) {σ τ σ' : L2Field Ω (Fin 1)}
    {E B F G E' B' : L2Field Ω (Fin 3)} (hξ : (Win hΩ).totalD.graphFst ξ = pack σ E B)
    (hψ : (Win hΩ).totalD.graphFst ψ = pack τ F G) (hv : v = pack σ' E' B')
    {gξ gψ cξ cψ : L2Field Ω (Fin 3)} (hgξ : (σ, gξ) ∈ (grad Ω).graph)
    (hgψ : (τ, gψ) ∈ (grad Ω).graph) (hcξ : (E, cξ) ∈ (curl Ω).graph)
    (hcψ : (F, cψ) ∈ (curl Ω).graph) :
    ⟪(Win hΩ).totalD.graphFst ψ, v⟫_ℝ + Feec.HodgeWave.waveForm (Win hΩ).totalD ξ ψ = 0 ↔
      ⟪σ', τ⟫_ℝ + ⟪E', F⟫_ℝ + ⟪B', G⟫_ℝ = ⟪gξ, F⟫_ℝ + ⟪cξ, G⟫_ℝ - ⟪E, gψ⟫_ℝ - ⟪B, cψ⟫_ℝ := by
  rw [galerkin_eq hΩ ξ ψ v hξ hψ hv hgξ hgψ hcξ hcψ, real_inner_comm τ, real_inner_comm F E',
    real_inner_comm G B', real_inner_comm gψ, real_inner_comm cψ, real_inner_comm gξ,
    real_inner_comm cξ]
  constructor <;> intro h <;> linarith

variable {κ : Type*} (G : Feec.HilbertComplex.ConformingFamily (vC.maximalComplex hΩ) κ)

theorem mem_Kh_iff (N : κ) (v : (Win hΩ).totalD.GraphSpace) :
    v ∈ (Feec.Instances.Maxwell.feec G 0).Kh N ↔
      (Win hΩ).totalD.graphFst v 0 ∈ (G.V N).V 0 ∧ (Win hΩ).totalD.graphFst v 1 ∈ (G.V N).V 1 ∧
        (Win hΩ).totalD.graphFst v 2 ∈ (G.V N).V 2 :=
  ⟨fun h => ⟨h 0, h 1, h 2⟩, fun h i => by fin_cases i; exacts [h.1, h.2.1, h.2.2]⟩

/-- The point `(x, 𝐝 x)` of the graph space for `x` with components in the subcomplex. -/
def liftV (N : κ) {x : MX Ω} (h0 : x 0 ∈ (G.V N).V 0) (h1 : x 1 ∈ (G.V N).V 1)
    (h2 : x 2 ∈ (G.V N).V 2) : (Win hΩ).totalD.GraphSpace :=
  (Win hΩ).totalD.toGraphSpace ⟨x, fun i j => by
    fin_cases i
    exacts [(G.V N).le_domain _ _ h0, (G.V N).le_domain _ _ h1, (G.V N).le_domain _ _ h2]⟩

/-- **Semi-discrete solutions of the Hodge wave equation of the Maxwell window are Galerkin
solutions of Maxwell's equations.** -/
theorem galerkin_of_semidiscrete {N : κ} {A₀ : Set (L2Field Ω (Fin 1))}
    {A₁ A₂ : Set (L2Field Ω (Fin 3))} (h₀ : ∀ u, u ∈ A₀ ↔ u ∈ (G.V N).V 0)
    (h₁ : ∀ u, u ∈ A₁ ↔ u ∈ (G.V N).V 1) (h₂ : ∀ u, u ∈ A₂ ↔ u ∈ (G.V N).V 2) {T : ℝ}
    {ξ ξ' : ℝ → (Win hΩ).totalD.GraphSpace}
    (hξ : Feec.HodgeWave.IsSemidiscreteSolution ((Feec.Instances.Maxwell.feec G 0).Kh N)
      (Icc 0 T) ξ ξ') :
    IsMaxwellGalerkin Ω A₀ A₁ A₂ T (fun t => (Win hΩ).totalD.graphFst (ξ t) 0)
      (fun t => (Win hΩ).totalD.graphFst (ξ t) 1) (fun t => (Win hΩ).totalD.graphFst (ξ t) 2) := by
  intro t ht
  obtain ⟨m0, m1, m2⟩ := (mem_Kh_iff hΩ G N _).1 (hξ.mem t ht)
  have hd : HasDerivWithinAt (fun t => (Win hΩ).totalD.graphFst (ξ t))
      ((Win hΩ).totalD.graphFst (ξ' t)) (Icc 0 T) t :=
    ((Win hΩ).totalD.graphFst.hasFDerivAt).comp_hasDerivWithinAt t (hξ.deriv t ht)
  refine ⟨(h₀ _).2 m0, (h₁ _).2 m1, (h₂ _).2 m2, _, _, _, hasDerivWithinAt_apply_MX hd 0,
    hasDerivWithinAt_apply_MX hd 1, hasDerivWithinAt_apply_MX hd 2,
    fun τ hτ F hF G' hG gσ gτ cE cF hgσ hgτ hcE hcF => ?_⟩
  have hdom : pack τ F G' ∈ (Win hΩ).totalD.domain := fun i j => by
    fin_cases i
    exacts [(G.V N).le_domain _ _ ((h₀ _).1 hτ), (G.V N).le_domain _ _ ((h₁ _).1 hF),
      (G.V N).le_domain _ _ ((h₂ _).1 hG)]
  have hψK : (Win hΩ).totalD.toGraphSpace ⟨pack τ F G', hdom⟩ ∈
      (Feec.Instances.Maxwell.feec G 0).Kh N := (mem_Kh_iff hΩ G N _).2 (by
    rw [LinearPMap.graphFst_toGraphSpace]
    exact ⟨(h₀ _).1 hτ, (h₁ _).1 hF, (h₂ _).1 hG⟩)
  exact (galerkin_iff hΩ (ξ t) _ ((Win hΩ).totalD.graphFst (ξ' t)) (pack_eta _).symm
    (LinearPMap.graphFst_toGraphSpace _ _) (pack_eta _).symm hgσ hgτ hcE hcF).1
    (hξ.eq t ht _ hψK)

theorem mem_grad_domain {u : L2Field Ω (Fin 1)} :
    u ∈ (grad Ω).domain ↔ u ∈ ((Win hΩ).d 0 1).domain := by
  rw [grad_eq_window hΩ]; exact Iff.rfl

theorem mem_curl_domain {u : L2Field Ω (Fin 3)} :
    u ∈ (curl Ω).domain ↔ u ∈ ((Win hΩ).d 1 2).domain := by
  rw [curl_eq_window hΩ]; exact Iff.rfl

set_option maxHeartbeats 1000000 in
/-- **Galerkin solutions of Maxwell's equations are semi-discrete solutions of the Hodge wave
equation of the Maxwell window**, through the lift `x ↦ (x, 𝐝 x)` of the orthogonal projection
onto `Xₕ = Vₕ⁰ × Vₕ¹ × Vₕ²`. -/
theorem semidiscrete_of_galerkin {N : κ} {A₀ : Set (L2Field Ω (Fin 1))}
    {A₁ A₂ : Set (L2Field Ω (Fin 3))} (h₀ : ∀ u, u ∈ A₀ ↔ u ∈ (G.V N).V 0)
    (h₁ : ∀ u, u ∈ A₁ ↔ u ∈ (G.V N).V 1) (h₂ : ∀ u, u ∈ A₂ ↔ u ∈ (G.V N).V 2) {T : ℝ}
    {σ : ℝ → L2Field Ω (Fin 1)} {E B : ℝ → L2Field Ω (Fin 3)}
    (h : IsMaxwellGalerkin Ω A₀ A₁ A₂ T σ E B) :
    ∃ ξ ξ' : ℝ → (Win hΩ).totalD.GraphSpace,
      Feec.HodgeWave.IsSemidiscreteSolution ((Feec.Instances.Maxwell.feec G 0).Kh N) (Icc 0 T)
        ξ ξ' ∧ ∀ t ∈ Icc 0 T, (Win hΩ).totalD.graphFst (ξ t) = pack (σ t) (E t) (B t) := by
  classical
  set Fc := Feec.Instances.Maxwell.feec G 0
  set X := Feec.HilbertComplex.totalSub (Fc.V N).V
  have : FiniteDimensional ℝ X := inferInstanceAs (FiniteDimensional ℝ (Fc.Xh N))
  have : CompleteSpace X := FiniteDimensional.complete ℝ X
  have : X.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace X
  have hX : ∀ {τ : L2Field Ω (Fin 1)} {F G' : L2Field Ω (Fin 3)}, τ ∈ A₀ → F ∈ A₁ → G' ∈ A₂ →
      pack τ F G' ∈ X := fun hτ hF hG i => by
    fin_cases i
    exacts [(h₀ _).1 hτ, (h₁ _).1 hF, (h₂ _).1 hG]
  let L : _ →L[ℝ] (Win hΩ).totalD.GraphSpace := Fc.liftXh N ∘L X.orthogonalProjectionOnto
  have hL : ∀ u, (Win hΩ).totalD.graphFst (L u) = X.starProjection u := fun u => rfl
  choose hm0 hm1 hm2 σ' E' B' hσ hE hB heq using h
  refine ⟨fun t => L (pack (σ t) (E t) (B t)), fun t => if ht : t ∈ Icc 0 T then
    L (pack (σ' t ht) (E' t ht) (B' t ht)) else 0, ⟨fun t _ => Fc.liftXh_mem N _,
    fun t ht => ?_, fun t ht ψ hψ => ?_⟩, fun t ht => ?_⟩
  · simp only [ht, ↓reduceDIte]
    exact L.hasFDerivAt.comp_hasDerivWithinAt t
      (hasDerivWithinAt_pack (hσ t ht) (hE t ht) (hB t ht))
  · have hψX : (Win hΩ).totalD.graphFst ψ ∈ X := hψ
    obtain ⟨m0, m1, m2⟩ := (mem_Kh_iff hΩ G N ψ).1 hψ
    have hτ : ((Win hΩ).totalD.graphFst ψ 0 : L2Field Ω (Fin 1)) ∈ A₀ := (h₀ _).2 m0
    have hF : ((Win hΩ).totalD.graphFst ψ 1 : L2Field Ω (Fin 3)) ∈ A₁ := (h₁ _).2 m1
    have hG : ((Win hΩ).totalD.graphFst ψ 2 : L2Field Ω (Fin 3)) ∈ A₂ := (h₂ _).2 m2
    have dσ := (mem_grad_domain hΩ).2 ((G.V N).le_domain 0 1 ((h₀ _).1 (hm0 t ht)))
    have dτ := (mem_grad_domain hΩ).2 ((G.V N).le_domain 0 1 m0)
    have dE := (mem_curl_domain hΩ).2 ((G.V N).le_domain 1 2 ((h₁ _).1 (hm1 t ht)))
    have dF := (mem_curl_domain hΩ).2 ((G.V N).le_domain 1 2 m1)
    have key := heq t ht _ hτ _ hF _ hG _ _ _ _ (LinearPMap.mem_graph _ ⟨_, dσ⟩)
      (LinearPMap.mem_graph _ ⟨_, dτ⟩) (LinearPMap.mem_graph _ ⟨_, dE⟩)
      (LinearPMap.mem_graph _ ⟨_, dF⟩)
    simp only [ht, ↓reduceDIte]
    rw [hL, ← Submodule.inner_starProjection_left_eq_right X,
      (Submodule.starProjection_eq_self_iff (K := X)).2 hψX]
    refine (galerkin_iff hΩ _ ψ _ ?_ (pack_eta _).symm rfl (LinearPMap.mem_graph _ ⟨_, dσ⟩)
      (LinearPMap.mem_graph _ ⟨_, dτ⟩) (LinearPMap.mem_graph _ ⟨_, dE⟩)
      (LinearPMap.mem_graph _ ⟨_, dF⟩)).2 key
    rw [hL]
    exact (Submodule.starProjection_eq_self_iff (K := X)).2 (hX (hm0 t ht) (hm1 t ht) (hm2 t ht))
  · rw [hL]
    exact (Submodule.starProjection_eq_self_iff (K := X)).2 (hX (hm0 t ht) (hm1 t ht) (hm2 t ht))

/-! ### The vector proxies of the finite element spaces, the Gauss laws -/

section Spaces

variable {κ : Type*} (F : Feec.HilbertComplex.ConformingFamily ((deRham ℝ 3).maximalComplex hΩ) κ)
  (h : κ)

theorem mem_proxy0_iff {A : Set (L2Form Ω 0)} (hA : ∀ w, w ∈ A ↔ w ∈ (F.V h).V 0)
    (u : L2Field Ω (Fin 1)) : u ∈ proxy0 '' A ↔ u ∈ ((vFamily hΩ F).V h).V 0 := by
  rw [mem_vFamily_V_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [← Pq_zero, LinearIsometryEquiv.symm_apply_apply]
    exact (hA w).1 hw
  · intro hu
    exact ⟨_, (hA _).2 hu, by rw [← Pq_zero, LinearIsometryEquiv.apply_symm_apply]⟩

theorem mem_proxy1_iff {A : Set (L2Form Ω 1)} (hA : ∀ w, w ∈ A ↔ w ∈ (F.V h).V 1)
    (u : L2Field Ω (Fin 3)) : u ∈ proxy1 '' A ↔ u ∈ ((vFamily hΩ F).V h).V 1 := by
  rw [mem_vFamily_V_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [← Pq_one, LinearIsometryEquiv.symm_apply_apply]
    exact (hA w).1 hw
  · intro hu
    exact ⟨_, (hA _).2 hu, by rw [← Pq_one, LinearIsometryEquiv.apply_symm_apply]⟩

theorem mem_proxy2_iff {A : Set (L2Form Ω 2)} (hA : ∀ w, w ∈ A ↔ w ∈ (F.V h).V 2)
    (u : L2Field Ω (Fin 3)) : u ∈ proxy2 '' A ↔ u ∈ ((vFamily hΩ F).V h).V 2 := by
  rw [mem_vFamily_V_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [← Pq_two, LinearIsometryEquiv.symm_apply_apply]
    exact (hA w).1 hw
  · intro hu
    exact ⟨_, (hA _).2 hu, by rw [← Pq_two, LinearIsometryEquiv.apply_symm_apply]⟩

end Spaces

theorem div_eq_d : div Ω = (vC.maximalComplex hΩ).d 2 3 :=
  ((vC.maximalComplex_d hΩ 2).trans div_eq.symm).symm

theorem mem_div_graph {p : L2Field Ω (Fin 3) × L2Field Ω (Fin 1)} :
    p ∈ (div Ω).graph ↔ p ∈ ((vC.maximalComplex hΩ).d 2 3).graph := by
  rw [div_eq_d hΩ]; exact Iff.rfl

theorem mem_div_domain {u : L2Field Ω (Fin 3)} :
    u ∈ (div Ω).domain ↔ u ∈ ((vC.maximalComplex hΩ).d 2 3).domain := by
  rw [div_eq_d hΩ]; exact Iff.rfl

theorem mem_grad_adj_graph {p : L2Field Ω (Fin 3) × L2Field Ω (Fin 1)} :
    p ∈ (grad Ω)†.graph ↔ p ∈ ((Win hΩ).d 0 1)†.graph := by
  rw [grad_eq_window hΩ]; exact Iff.rfl

theorem mem_grad_adj_domain {u : L2Field Ω (Fin 3)} :
    u ∈ (grad Ω)†.domain ↔ u ∈ ((Win hΩ).d 0 1)†.domain := by
  rw [grad_eq_window hΩ]; exact Iff.rfl

theorem mem_curl_adj_domain {u : L2Field Ω (Fin 3)} :
    u ∈ (curl Ω)†.domain ↔ u ∈ ((Win hΩ).d 1 2)†.domain := by
  rw [curl_eq_window hΩ]; exact Iff.rfl

theorem mem_graph_zero_iff {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] {T : E →ₗ.[ℝ] F} {x : E} : (x, (0 : F)) ∈ T.graph ↔ x ∈ T.ker := by
  rw [LinearPMap.mem_graph_iff, LinearPMap.mem_ker_iff]
  constructor <;> rintro ⟨y, h1, h2⟩ <;> exact ⟨y, h1.symm, h2⟩

/-- **The Gauss laws of the challenge**: `σ = 0`, `grad* E = 0`, `div B = 0` is the Gauss-law
constraint of the Maxwell window (`Feec.Instances.Maxwell.mem_gauss`). -/
theorem mem_windowGauss_iff (x : MX Ω) :
    x ∈ Feec.Instances.Maxwell.windowGauss (vC.maximalComplex hΩ) 0 ↔
      (x 0 : L2Field Ω (Fin 1)) = 0 ∧ ((x 1 : L2Field Ω (Fin 3)), 0) ∈ (grad Ω)†.graph ∧
        ((x 2 : L2Field Ω (Fin 3)), 0) ∈ (div Ω).graph := by
  rw [Feec.Instances.Maxwell.mem_gauss]
  refine and_congr Iff.rfl (and_congr ⟨fun h => (mem_grad_adj_graph hΩ).2 (mem_graph_zero_iff.2 h),
    fun h => mem_graph_zero_iff.1 ((mem_grad_adj_graph hΩ).1 h)⟩
    ⟨fun h => (mem_div_graph hΩ).2 (mem_graph_zero_iff.2 h),
    fun h => mem_graph_zero_iff.1 ((mem_div_graph hΩ).1 h)⟩)

end FEEC
