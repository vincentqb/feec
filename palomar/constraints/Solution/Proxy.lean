module

public import Solution.Wave
public import Solution.Wedge
public import Feec.Counterexamples.BoundedBGG
public import Feec.Domain.VectorProxy

/-!
# The electric and magnetic fields of the challenge as `Feec`'s matrix fields

On an open `Ω ⊆ ℝ³`, the electric field `E_{ab} = (uₐ)_{dx_b}` of a vector `1`-form and the
magnetic field `B_{ai} = (-1)ⁱ (ρₐ)_{{i}ᶜ}` of a vector `2`-form are unitary maps
`L²(Ω; Λ¹ ⊗ ℝ³), L²(Ω; Λ² ⊗ ℝ³) ≃ L²(Ω; ℝ³ˣ³)` (`fieldE`, `fieldB`), the matrix fields of
`Feec.Models.BoundedDomain`. Row by row they are the vector proxies of `Feec.Domain.proxy`, so
they intertwine `d` with the row-wise curl (`curlOp_rowMat`, `Feec.Domain.curlOp_proxyMat`), and
`ConstCoeffOp.minimal_ofMatrixCLM_of_comm` carries `H̊Λ¹(Ω)³` and `d_min` into `H̊(curl, Ω; ℝ³ˣ³)`
and `curl_min` (`fieldE_mem_curl_minimal`). The Gauss law of the challenge is `Feec`'s weak
divergence against test fields (`isDivFree_iff`), and TSD in its sense is `Feec`'s `L²(TSD)`
(`isTSD_iff`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §2 (vector proxies)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace ContDiff
open Set MeasureTheory

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.Models.BoundedDomain
open Feec.Koszul.Proxy3 (vec1 vec2 vec2_apply vec2Sign)

variable {Ω : Set (Fin 3 → ℝ)}

/-! ### The index equivalences and the fields -/

/-- `b ↦ dx_b`. -/
def f1 (b : Fin 3) : FormIdx 3 1 := ⟨{b}, by simp⟩
/-- `i ↦ dx_{{i}ᶜ}`. -/
def f2 (i : Fin 3) : FormIdx 3 2 := ⟨Finset.univ.erase i, by simp⟩

theorem f1_bijective : Function.Bijective f1 := by decide
theorem f2_bijective : Function.Bijective f2 := by decide

/-- `Fin 3 ≃ FormIdx 3 1`, `b ↦ dx_b`. -/
def ix1 : Fin 3 ≃ FormIdx 3 1 := Equiv.ofBijective f1 f1_bijective
/-- `Fin 3 ≃ FormIdx 3 2`, `i ↦ dx_{{i}ᶜ}`. -/
def ix2 : Fin 3 ≃ FormIdx 3 2 := Equiv.ofBijective f2 f2_bijective

/-- The sign `(-1)ⁱ` of the Hodge star `⋆dxᵢ = (-1)ⁱ dx_{{i}ᶜ}`. -/
def sgn3 (i : Fin 3) : ℝ := (-1) ^ (i : ℕ)

theorem sgn3_mul_self (i : Fin 3) : sgn3 i * sgn3 i = 1 := by
  rw [sgn3, ← pow_add, ← two_mul, pow_mul]; norm_num

theorem norm_sq_piLp {ι : Type*} [Fintype ι] {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)]
    (x : PiLp 2 F) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]

/-- **The electric field** `L²(Ω; Λ¹ ⊗ ℝ³) ≃ L²(Ω; ℝ³ˣ³)`, `E_{ab} = (uₐ)_{dx_b}`. -/
def fieldE : L2Vec Ω 1 ≃ₗᵢ[ℝ] L2F ℝ Ω Ix where
  toFun u := WithLp.toLp 2 fun p => u p.1 (ix1 p.2)
  invFun E := WithLp.toLp 2 fun a => WithLp.toLp 2 fun s => E (a, ix1.symm s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv u := PiLp.ext fun a => PiLp.ext fun s => by simp
  right_inv E := PiLp.ext fun p => by simp
  norm_map' u := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [norm_sq_piLp, norm_sq_piLp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [norm_sq_piLp]
    exact Fintype.sum_equiv ix1 _ _ fun _ => rfl

/-- The magnetic field as a linear equivalence. -/
def fieldBₗ : L2Vec Ω 2 ≃ₗ[ℝ] L2F ℝ Ω Ix where
  toFun ρ := WithLp.toLp 2 fun p => sgn3 p.2 • ρ p.1 (ix2 p.2)
  invFun B := WithLp.toLp 2 fun a => WithLp.toLp 2 fun t => sgn3 (ix2.symm t) • B (a, ix2.symm t)
  map_add' x y := PiLp.ext fun p => by simp [smul_add]
  map_smul' c x := PiLp.ext fun p => by simp [smul_comm c]
  left_inv ρ := PiLp.ext fun a => PiLp.ext fun s => by
    simp [smul_smul, sgn3_mul_self]
  right_inv B := PiLp.ext fun p => by simp [smul_smul, sgn3_mul_self]

/-- **The magnetic field** `L²(Ω; Λ² ⊗ ℝ³) ≃ L²(Ω; ℝ³ˣ³)`, `B_{ai} = (-1)ⁱ (ρₐ)_{{i}ᶜ}`. -/
def fieldB : L2Vec Ω 2 ≃ₗᵢ[ℝ] L2F ℝ Ω Ix where
  toLinearEquiv := fieldBₗ
  norm_map' ρ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [norm_sq_piLp, norm_sq_piLp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [norm_sq_piLp]
    refine Fintype.sum_equiv ix2 _ _ fun i => ?_
    change ‖sgn3 i • ρ a (ix2 i)‖ ^ 2 = _
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, show sgn3 i ^ 2 = 1 by
      rw [_root_.sq, sgn3_mul_self], one_mul]

theorem fieldE_apply (u : L2Vec Ω 1) (a b : Fin 3) : fieldE u (a, b) = mat1 u a b := rfl

theorem fieldB_apply (ρ : L2Vec Ω 2) (a i : Fin 3) : fieldB ρ (a, i) = mat2 ρ a i := rfl

/-- The matrix field of an array of `L²` functions. -/
def toIx (E : Fin 3 → Fin 3 → Lp ℝ 2 (volume.restrict Ω)) : L2F ℝ Ω Ix :=
  WithLp.toLp 2 fun p => E p.1 p.2

theorem toIx_mat1 (u : L2Vec Ω 1) : toIx (mat1 u) = fieldE u := rfl
theorem toIx_mat2 (ρ : L2Vec Ω 2) : toIx (mat2 ρ) = fieldB ρ := rfl

/-! ### TSD -/

theorem isTest_single {ψ : (Fin 3 → ℝ) → ℝ} (hψ : IsTestFn Ω ψ) (a : Fin 3) :
    IsTestField Ω (fun i => if i = a then ψ else 0) := fun i => by
  by_cases h : i = a
  · simp only [h, ite_true]; exact isTest_of hψ
  · simp only [h, ite_false]; exact IsTest.zero

/-- **The Gauss law of the challenge is `Feec`'s weak divergence**, against test fields. -/
theorem isDivFree_iff (E : Fin 3 → Fin 3 → Lp ℝ 2 (volume.restrict Ω)) :
    IsDivFree E ↔ ∀ φ : Fin 3 → R3 → ℝ, IsTestField Ω φ →
      ∑ ij : Ix, ∫ x, toIx E ij x * _root_.partialDeriv ij.2 (φ ij.1) x ∂volume.restrict Ω =
        0 := by
  refine ⟨fun h φ hφ => ?_, fun h a ψ hψ => ?_⟩
  · rw [Fintype.sum_prod_type]
    exact Finset.sum_eq_zero fun a _ => h a (φ a) (isTestFn_of (hφ a))
  · have e := h _ (isTest_single hψ a)
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a] at e
    · simp [toIx] at e; exact e
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      simp [hb]
    · simp

/-- **TSD in the sense of the challenge is `Feec`'s `L²(TSD)`.** -/
theorem isTSD_iff (E : Fin 3 → Fin 3 → Lp ℝ 2 (volume.restrict Ω)) :
    IsTSD E ↔ toIx E ∈ tsd Ω := by
  rw [mem_tsd]
  exact and_congr Iff.rfl (and_congr Iff.rfl ((isDivFree_iff E).trans
    (forall₂_congr fun φ hφ => by rw [inner_grad_testField _ hφ])))

/-! ### The curl -/

/-- The row `a` of the electric field: `(M₁ u)_{ib} = [i = a] u_{dx_b}`. -/
def matE (a : Fin 3) : Matrix Ix (FormIdx 3 1) ℝ := fun p s =>
  if p.1 = a ∧ s = ix1 p.2 then 1 else 0

/-- The row `a` of the magnetic field: `(M₂ ρ)_{ik} = [i = a] (-1)ᵏ ρ_{{k}ᶜ}`. -/
def matB (a : Fin 3) : Matrix Ix (FormIdx 3 2) ℝ :=
  fun p t => if p.1 = a ∧ t = ix2 p.2 then sgn3 p.2 else 0

/-- Embedding of a vector as the row `a` of a matrix. -/
def rowMat (a : Fin 3) : Matrix Ix (Fin 1 × Fin 3) ℝ := fun p q =>
  if p.1 = a ∧ p.2 = q.2 then 1 else 0

theorem ofMatrix_rowMat_apply (a : Fin 3) (g : Fin 1 × Fin 3 → R3 → ℝ) :
    (ConstCoeffOp.ofMatrix (rowMat a) : ConstCoeffOp R3 ℝ _ _).apply g =
      fun p => if p.1 = a then g (0, p.2) else 0 := by
  funext p x
  rw [ConstCoeffOp.ofMatrix_apply]
  by_cases h : p.1 = a
  · simp [rowMat, h, Fintype.sum_prod_type]
  · simp [rowMat, h]

theorem curlOp_rowMat (a : Fin 3) (g : Fin 1 × Fin 3 → R3 → ℝ) :
    (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).apply
        ((ConstCoeffOp.ofMatrix (rowMat a) : ConstCoeffOp R3 ℝ _ _).apply g) =
      (ConstCoeffOp.ofMatrix (rowMat a) : ConstCoeffOp R3 ℝ _ _).apply
        ((curlOp 1 : ConstCoeffOp R3 ℝ _ _).apply g) := by
  rw [ofMatrix_rowMat_apply, ofMatrix_rowMat_apply]
  funext p x
  obtain ⟨i, k⟩ := p
  rw [curlOp_apply]
  by_cases h : i = a
  · simp only [h, ite_true]
    rw [curlOp_apply]
  · simp [h]

theorem ofMatrix_matE_apply (a : Fin 3) (f : FormIdx 3 1 → R3 → ℝ) :
    (ConstCoeffOp.ofMatrix (matE a) : ConstCoeffOp R3 ℝ _ _).apply f =
      (ConstCoeffOp.ofMatrix (rowMat a) : ConstCoeffOp R3 ℝ _ _).apply
        ((ConstCoeffOp.ofMatrix (proxyMat 1) : ConstCoeffOp R3 ℝ _ _).apply f) := by
  rw [ofMatrix_rowMat_apply, ofMatrix_proxyMat_one]
  funext p x
  rw [ConstCoeffOp.ofMatrix_apply]
  by_cases h : p.1 = a
  · simp [matE, h, vec1, ix1, f1, formExt]
  · simp [matE, h]

theorem ofMatrix_matB_apply (a : Fin 3) (f : FormIdx 3 2 → R3 → ℝ) :
    (ConstCoeffOp.ofMatrix (matB a) : ConstCoeffOp R3 ℝ _ _).apply f =
      (ConstCoeffOp.ofMatrix (rowMat a) : ConstCoeffOp R3 ℝ _ _).apply
        ((ConstCoeffOp.ofMatrix (proxyMat 2) : ConstCoeffOp R3 ℝ _ _).apply f) := by
  rw [ofMatrix_rowMat_apply, ofMatrix_proxyMat_two]
  funext p x
  rw [ConstCoeffOp.ofMatrix_apply]
  by_cases h : p.1 = a
  · simp only [matB, h, true_and, ite_true, vec2_apply]
    obtain ⟨i, k⟩ := p
    fin_cases k <;> simp [ix2, f2, sgn3, vec2Sign, formExt, Finset.compl_singleton]
  · simp [matB, h]

/-- **The rows of the fields intertwine `d` and the row-wise curl.** -/
theorem curlOp_matE (a : Fin 3) (f : FormIdx 3 1 → R3 → ℝ) :
    (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).apply
        ((ConstCoeffOp.ofMatrix (matE a) : ConstCoeffOp R3 ℝ _ _).apply f) =
      (ConstCoeffOp.ofMatrix (matB a) : ConstCoeffOp R3 ℝ _ _).apply
        ((extDerivOp ℝ 3 1).apply f) := by
  rw [ofMatrix_matE_apply, ofMatrix_matB_apply, curlOp_rowMat]
  exact congrArg _ (curlOp_proxyMat f)

theorem ofMatrixCLM_matE_apply (a : Fin 3) (v : L2Form Ω 1) (p : Ix) :
    L2F.ofMatrixCLM (matE a) v p = if p.1 = a then v (ix1 p.2) else 0 := by
  rw [L2F.ofMatrixCLM_apply]
  by_cases h : p.1 = a
  · simp [matE, h]
  · simp [matE, h]

theorem ofMatrixCLM_matB_apply (a : Fin 3) (w : L2Form Ω 2) (p : Ix) :
    L2F.ofMatrixCLM (matB a) w p = if p.1 = a then sgn3 p.2 • w (ix2 p.2) else 0 := by
  rw [L2F.ofMatrixCLM_apply]
  by_cases h : p.1 = a
  · simp [matB, h]
  · simp [matB, h]

theorem fieldE_eq_sum (u : L2Vec Ω 1) : fieldE u = ∑ a, L2F.ofMatrixCLM (matE a) (u a) := by
  refine PiLp.ext fun p => ?_
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [ofMatrixCLM_matE_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

theorem fieldB_eq_sum (ρ : L2Vec Ω 2) : fieldB ρ = ∑ a, L2F.ofMatrixCLM (matB a) (ρ a) := by
  refine PiLp.ext fun p => ?_
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [ofMatrixCLM_matB_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

/-- **`H̊Λ¹(Ω)³` lies in `H̊(curl, Ω; ℝ³ˣ³)`, with `curl_min E = B(d_min u)`.** -/
theorem fieldE_mem_curl_minimal (hΩ : IsOpen Ω) (u : (vecOpC (dMin Ω 1)).domain) :
    (fieldE (u : L2Vec Ω 1), fieldB (vecOpC (dMin Ω 1) u)) ∈
      ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).graph := by
  rw [fieldE_eq_sum, fieldB_eq_sum]
  rw [show ∀ (x : Fin 3 → L2F ℝ Ω Ix) (y : Fin 3 → L2F ℝ Ω Ix),
      (∑ a, x a, ∑ a, y a) = ∑ a, (x a, y a) from fun x y => by
    ext <;> simp [Prod.fst_sum, Prod.snd_sum]]
  refine Submodule.sum_mem _ fun a _ => ?_
  have hu : (u : L2Vec Ω 1) a ∈ ((extDerivOp ℝ 3 1).minimal Ω).domain := by
    rw [← dMin_eq]; exact u.2 a
  obtain ⟨h, e⟩ := ConstCoeffOp.minimal_ofMatrixCLM_of_comm hΩ (A := curlOp 3)
    (fun f _ => curlOp_matE a f) ⟨_, hu⟩
  have e' : (vecOpC (dMin Ω 1) u : L2Vec Ω 2) a = (extDerivOp ℝ 3 1).minimal Ω ⟨_, hu⟩ :=
    LinearPMap.apply_of_eq' (dMin_eq Ω 1) ⟨_, u.2 a⟩
  rw [e', ← e]
  exact LinearPMap.mem_graph _ ⟨_, h⟩

end FEEC
