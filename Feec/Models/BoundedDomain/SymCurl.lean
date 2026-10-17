module

public import Feec.Models.BoundedDomain.GradCurl
public import Feec.Domain.Constrained

/-!
# The Hessian–curl complex on a bounded domain (thesis complex (4.16))

On an open `Ω ⊆ ℝ³` let `L²(Ω; S)` and `L²(Ω; T)` be the symmetric and the trace-free matrix
fields (`symSub`, `trSub`). The thesis' complex (4.16) for Prop 4.19 is
`H̊²(Ω) --grad grad--> H̊(curl, Ω; S) --curl--> L²(Ω; T)`, the realizations of the Hessian and of
the row-wise curl along the embeddings `L²(Ω) ↪ L²(Ω; 𝕜^{Unit})`, `L²(S), L²(T) ↪ L²(Ω; 𝕜³ˣ³)`
(`Feec.Domain.ConstCoeffOp.minimalVia`): `hessCurl`. The complex with the dual boundary
conditions, `H̊(sym curl, Ω; T) --sym curl--> H̊(div div, Ω; S) --div div--> L²(Ω)`, is
`symCurlDivDiv`.

The constrained test fields are dense (`denseVia_symSub`, `denseVia_trSub`, `denseVia_scalar`:
the symmetric and deviatoric parts are self-adjoint projections preserving test fields), and the
curl of a symmetric field is trace-free (`trace_curl_eq_zero_of_symm`).

`H̊(curl, S) ⊆ H̊(curl, M)` with the same curl (`Feec.Domain.ConstCoeffOp.minimalVia_graph_map`),
so the zero-mean theorem of `Feec.Models.BoundedDomain.GradCurl` applies to symmetric TSD fields,
and **TSD propagation fails for (4.16)** on every nonempty bounded open `Ω` (`not_propagates_sym`,
the bounded-domain refutation of thesis Prop 4.19).

## References

* [QuennevilleBelair2015], §4.11 (Prop 4.19, complex (4.16)); [Arnold2018], §8 (Hessian and
  div-div complexes)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ContDiff Matrix ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology Feec.Domain

namespace Feec.Models.BoundedDomain

variable {𝕜 : Type*} [RCLike 𝕜] {Ω : Set R3}

/-! ## Symmetric and trace-free fields -/

variable (𝕜 Ω) in
/-- `L²(Ω; S)`: symmetric matrix fields. -/
def symSub : Submodule 𝕜 (L2F 𝕜 Ω Ix) where
  carrier := {B | ∀ i j, B (i, j) = B (j, i)}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} ha hb i j => by
    simp only [mem_ofPred_eq, PiLp.add_apply] at ha hb ⊢
    rw [ha i j, hb i j]
  smul_mem' := fun r B hB i j => by
    simp only [mem_ofPred_eq, PiLp.smul_apply] at hB ⊢
    rw [hB i j]

variable (𝕜 Ω) in
/-- `L²(Ω; T)`: trace-free matrix fields. -/
def trSub : Submodule 𝕜 (L2F 𝕜 Ω Ix) where
  carrier := {B | ∑ i, B (i, i) = 0}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [mem_ofPred_eq, PiLp.add_apply, Finset.sum_add_distrib] at ha hb ⊢
    rw [ha, hb, add_zero]
  smul_mem' := fun r B hB => by
    simp only [mem_ofPred_eq, PiLp.smul_apply, ← Finset.smul_sum] at hB ⊢
    rw [hB, smul_zero]

theorem mem_symSub {B : L2F 𝕜 Ω Ix} : B ∈ symSub 𝕜 Ω ↔ ∀ i j, B (i, j) = B (j, i) := Iff.rfl

theorem mem_trSub {B : L2F 𝕜 Ω Ix} : B ∈ trSub 𝕜 Ω ↔ ∑ i, B (i, i) = 0 := Iff.rfl

theorem isClosed_symSub : IsClosed (symSub 𝕜 Ω : Set (L2F 𝕜 Ω Ix)) := by
  have e : (symSub 𝕜 Ω : Set (L2F 𝕜 Ω Ix)) =
      ⋂ i : Fin 3, ⋂ j : Fin 3, {B : L2F 𝕜 Ω Ix | B (i, j) = B (j, i)} := by
    ext B
    simp [mem_symSub]
  rw [e]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (L2F.continuous_apply (i, j)) (L2F.continuous_apply (j, i))

theorem isClosed_trSub : IsClosed (trSub 𝕜 Ω : Set (L2F 𝕜 Ω Ix)) :=
  isClosed_eq (continuous_finsetSum Finset.univ fun i _ => L2F.continuous_apply (i, i))
    continuous_const

instance : CompleteSpace (symSub 𝕜 Ω) := isClosed_symSub.completeSpace_coe

instance : CompleteSpace (trSub 𝕜 Ω) := isClosed_trSub.completeSpace_coe

/-! ## The symmetric and deviatoric projections -/

/-- A field-level continuous linear map assembled from its components. -/
def matCLM (M : Ix → Ix → 𝕜) : L2F 𝕜 Ω Ix →L[𝕜] L2F 𝕜 Ω Ix :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : Ix => L2 𝕜 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun ij => ∑ kl, M ij kl • PiLp.proj 2 (fun _ : Ix => L2 𝕜 Ω) kl)

theorem matCLM_apply (M : Ix → Ix → 𝕜) (u : L2F 𝕜 Ω Ix) (ij : Ix) :
    matCLM M u ij = ∑ kl, M ij kl • u kl := by
  simp [matCLM]

/-- `matCLM` acts pointwise on test fields. -/
theorem matCLM_testField (M : Ix → Ix → 𝕜) {Φ : Ix → R3 → 𝕜} (hΦ : IsTestField Ω Φ) :
    ∃ hΨ : IsTestField Ω (fun ij x => ∑ kl, M ij kl * Φ kl x),
      matCLM M (testField hΦ) = testField hΨ := by
  have hΨ : IsTestField Ω (fun ij x => ∑ kl, M ij kl * Φ kl x) := fun ij =>
    IsTest.sum _ fun kl _ => (hΦ kl).const_mul _
  refine ⟨hΨ, (WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_)⟩
  rw [matCLM_apply]
  have h1 := Lp.coeFn_fun_finsetSum (μ := volume.restrict Ω) Finset.univ
    (fun kl => M ij kl • testField hΦ kl)
  filter_upwards [h1, coeFn_testField hΨ ij,
    ae_all_iff.2 fun kl => Lp.coeFn_smul (M ij kl) (testField hΦ kl),
    ae_all_iff.2 fun kl => coeFn_testField hΦ kl] with x h1 h2 h3 h4
  rw [h1, h2]
  refine Finset.sum_congr rfl fun kl _ => ?_
  rw [h3 kl, Pi.smul_apply, h4 kl, smul_eq_mul]

theorem inner_matCLM (M : Ix → Ix → 𝕜) (hM : ∀ ij kl, M kl ij = conj (M ij kl))
    (u v : L2F 𝕜 Ω Ix) : ⟪matCLM M u, v⟫_𝕜 = ⟪u, matCLM M v⟫_𝕜 := by
  rw [L2F.inner_def, L2F.inner_def]
  simp only [matCLM_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ij _ => Finset.sum_congr rfl fun kl _ => ?_
  rw [hM]
  simp

/-- The symmetric part `(B + Bᵀ)/2`. -/
def symProj : L2F 𝕜 Ω Ix →L[𝕜] L2F 𝕜 Ω Ix := matCLM (symMat 3)

/-- The deviatoric part `B - ⅓ (tr B) I`. -/
def devMat : Ix → Ix → 𝕜 := fun ij kl =>
  (if kl = ij then 1 else 0) - (if ij.1 = ij.2 ∧ kl.1 = kl.2 then 1 / 3 else 0)

def devProj : L2F 𝕜 Ω Ix →L[𝕜] L2F 𝕜 Ω Ix := matCLM devMat

theorem symProj_apply (u : L2F 𝕜 Ω Ix) (ij : Ix) :
    symProj u ij = (1 / 2 : 𝕜) • (u ij + u (ij.2, ij.1)) := by
  rw [symProj, matCLM_apply]
  simp only [symMat, add_div, add_smul, Finset.sum_add_distrib, ite_div, zero_div, ite_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, smul_add]

theorem devProj_apply (u : L2F 𝕜 Ω Ix) (ij : Ix) :
    devProj u ij = u ij - (if ij.1 = ij.2 then (1 / 3 : 𝕜) • ∑ k, u (k, k) else 0) := by
  rw [devProj, matCLM_apply]
  simp only [devMat, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  split_ifs with h
  · rw [Fintype.sum_prod_type, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [h, Finset.sum_ite_eq]
  · simp [h]

theorem symProj_mem (u : L2F 𝕜 Ω Ix) : symProj u ∈ symSub 𝕜 Ω := fun i j => by
  rw [symProj_apply, symProj_apply, add_comm]

theorem symProj_eq_self {u : L2F 𝕜 Ω Ix} (hu : u ∈ symSub 𝕜 Ω) : symProj u = u :=
  (WithLp.ext_iff 2).2 (funext fun ij => by
    rw [symProj_apply, ← hu ij.1 ij.2, ← two_smul 𝕜, smul_smul]
    norm_num)

theorem devProj_mem (u : L2F 𝕜 Ω Ix) : devProj u ∈ trSub 𝕜 Ω := by
  rw [mem_trSub]
  simp only [devProj_apply, ite_true, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul]
  norm_num

theorem devProj_eq_self {u : L2F 𝕜 Ω Ix} (hu : u ∈ trSub 𝕜 Ω) : devProj u = u :=
  (WithLp.ext_iff 2).2 (funext fun ij => by
    rw [devProj_apply, mem_trSub.1 hu]
    simp)

theorem inner_symProj (u v : L2F 𝕜 Ω Ix) : ⟪symProj u, v⟫_𝕜 = ⟪u, symProj v⟫_𝕜 :=
  inner_matCLM _ (fun ij kl => by
    simp only [symMat, map_div₀, map_add, apply_ite (starRingEnd 𝕜), map_one, map_zero,
      map_ofNat]
    congr 2
    · exact if_congr eq_comm rfl rfl
    · exact if_congr ⟨fun h => by rw [h], fun h => by rw [h]⟩ rfl rfl) u v

theorem inner_devProj (u v : L2F 𝕜 Ω Ix) : ⟪devProj u, v⟫_𝕜 = ⟪u, devProj v⟫_𝕜 :=
  inner_matCLM _ (fun ij kl => by
    simp only [devMat]
    split_ifs <;> simp_all [map_ofNat]) u v

/-! ## Density of constrained test fields -/

theorem denseVia_symSub (hΩ : IsOpen Ω) :
    ConstCoeffOp.DenseVia (symSub 𝕜 Ω).subtypeₗᵢ := by
  refine ConstCoeffOp.denseVia_of_proj hΩ _ symProj (fun y => symProj_eq_self y.2) inner_symProj
    fun ψ hψ => ?_
  obtain ⟨hψ', e⟩ := matCLM_testField (symMat 3) hψ
  exact ⟨_, hψ', ⟨_, symProj_mem (testField hψ)⟩, e, e⟩

theorem denseVia_trSub (hΩ : IsOpen Ω) :
    ConstCoeffOp.DenseVia (trSub 𝕜 Ω).subtypeₗᵢ := by
  refine ConstCoeffOp.denseVia_of_proj hΩ _ devProj (fun y => devProj_eq_self y.2) inner_devProj
    fun ψ hψ => ?_
  obtain ⟨hψ', e⟩ := matCLM_testField devMat hψ
  exact ⟨_, hψ', ⟨_, devProj_mem (testField hψ)⟩, e, e⟩

theorem denseVia_scalar (hΩ : IsOpen Ω) : ConstCoeffOp.DenseVia (L2.toL2F 𝕜 Ω) := by
  intro y hy
  refine (L2.toL2F 𝕜 Ω).injective ?_
  rw [map_zero]
  refine L2F.eq_zero_of_forall_inner_testField hΩ _ fun ψ hψ => ?_
  have := hy ψ hψ (testField hψ ()) ((WithLp.ext_iff 2).2 (funext fun _ => rfl))
  rw [← (L2.toL2F 𝕜 Ω).inner_map_map] at this
  rw [← inner_conj_symm, show testField hψ = L2.toL2F 𝕜 Ω (testField hψ ()) from
    (WithLp.ext_iff 2).2 (funext fun _ => rfl), this, map_zero]


/-! ## Pointwise identities -/

/-- The Hessian is symmetric (Schwarz). -/
theorem hessOp_apply_swap {h : Unit → R3 → 𝕜} (hh : ∀ u, ContDiff ℝ ∞ (h u)) (i j : Fin 3) :
    (hessOp 3 : ConstCoeffOp R3 𝕜 _ _).apply h (i, j) =
      (hessOp 3 : ConstCoeffOp R3 𝕜 _ _).apply h (j, i) := by
  funext x
  rw [hessOp_apply, hessOp_apply]
  exact fderiv_fderiv_comm ((hh ()).of_le (by simp)) _ _ x

/-- The curl of a pointwise symmetric field is trace-free. -/
theorem trace_curl_eq_zero_of_symm {Φ : Ix → R3 → 𝕜} (hs : ∀ i j, Φ (i, j) = Φ (j, i))
    (x : R3) : ∑ i, (curlOp 3 : ConstCoeffOp R3 𝕜 _ _).apply Φ (i, i) x = 0 := by
  simp only [Fin.sum_univ_three, curlOp_apply]
  simp only [Fin.isValue, Fin.reduceAdd]
  rw [hs 0 2, hs 0 1, hs 1 2]
  ring

/-- The sum of the diagonal components of a test field is the class of the pointwise sum. -/
theorem sum_diag_testField {Φ : Ix → R3 → 𝕜} (hΦ : IsTestField Ω Φ) :
    ∑ i, testField hΦ (i, i) = toL2 (IsTest.sum Finset.univ fun i _ => hΦ (i, i)) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_fun_finsetSum (μ := volume.restrict Ω) Finset.univ
      (fun i => testField hΦ (i, i)), coeFn_toL2 (IsTest.sum Finset.univ fun i _ => hΦ (i, i)),
    ae_all_iff.2 fun i => coeFn_testField hΦ (i, i)] with x h1 h2 h3
  rw [h1, h2]
  exact Finset.sum_congr rfl fun i _ => h3 i

theorem testField_mem_trSub {Φ : Ix → R3 → 𝕜} (hΦ : IsTestField Ω Φ)
    (htr : ∀ x, ∑ i, Φ (i, i) x = 0) : testField hΦ ∈ trSub 𝕜 Ω := by
  rw [mem_trSub, sum_diag_testField]
  rw [toL2_congr _ IsTest.zero (funext htr)]
  exact toL2_zero

theorem testField_mem_symSub {Φ : Ix → R3 → 𝕜} (hΦ : IsTestField Ω Φ)
    (hs : ∀ i j, Φ (i, j) = Φ (j, i)) : testField hΦ ∈ symSub 𝕜 Ω := fun i j => by
  simp only [testField_apply]
  exact toL2_congr _ _ (hs i j)

/-- The Hessian maps scalar test functions to symmetric test fields. -/
theorem hess_mapsTo (φ : Unit → R3 → 𝕜) (hφ : IsTestField Ω φ) (x : L2 𝕜 Ω)
    (_ : L2.toL2F 𝕜 Ω x = testField hφ) :
    ∃ y : symSub 𝕜 Ω, ((symSub 𝕜 Ω).subtypeₗᵢ y : L2F 𝕜 Ω Ix) =
      testField ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ) :=
  ⟨⟨_, testField_mem_symSub _ (hessOp_apply_swap fun u => (hφ u).contDiff)⟩, rfl⟩

/-- `curl` maps symmetric test fields to trace-free test fields (Lemma 3.5). -/
theorem curl_mapsTo (hΩ : IsOpen Ω) (Φ : Ix → R3 → 𝕜) (hΦ : IsTestField Ω Φ)
    (x : symSub 𝕜 Ω) (hx : ((symSub 𝕜 Ω).subtypeₗᵢ x : L2F 𝕜 Ω Ix) = testField hΦ) :
    ∃ y : trSub 𝕜 Ω, ((trSub 𝕜 Ω).subtypeₗᵢ y : L2F 𝕜 Ω Ix) =
      testField ((curlOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hΦ) := by
  obtain ⟨hΨ, e⟩ := matCLM_testField (Ω := Ω) (symMat 3) hΦ
  have hsym : testField hΦ = testField hΨ := by
    rw [← e, ← hx]
    exact (symProj_eq_self x.2).symm
  have hcurl : testField ((curlOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hΦ) =
      testField ((curlOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hΨ) := by
    rw [← (curlOp 3 : ConstCoeffOp R3 𝕜 _ _).minimal_testField hΩ hΦ,
      ← (curlOp 3 : ConstCoeffOp R3 𝕜 _ _).minimal_testField hΩ hΨ]
    congr 1
    exact Subtype.ext hsym
  have hmem : testField ((curlOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hΦ) ∈ trSub 𝕜 Ω := by
    rw [hcurl]
    refine testField_mem_trSub _ fun y => trace_curl_eq_zero_of_symm (fun i j => ?_) y
    funext z
    simp only [symMat, add_div, add_mul, ite_div, zero_div, ite_mul, zero_mul,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  exact ⟨⟨_, hmem⟩, rfl⟩

/-! ## The complex (4.16) -/

variable (𝕜) in
/-- **The thesis' complex (4.16)** `H̊²(Ω) --grad grad--> H̊(curl, Ω; S) --curl--> L²(Ω; T)`:
the realizations of the Hessian and of the curl along the scalar and the symmetric/trace-free
embeddings. Thesis: Prop 4.19 -/
def hessCurl (hΩ : IsOpen Ω) : ShortHilbertComplex 𝕜 (L2 𝕜 Ω) (symSub 𝕜 Ω) (trSub 𝕜 Ω) where
  d₀ := (hessOp 3).minimalVia (L2.toL2F 𝕜 Ω) (symSub 𝕜 Ω).subtypeₗᵢ
  d₁ := (curlOp 3).minimalVia (symSub 𝕜 Ω).subtypeₗᵢ (trSub 𝕜 Ω).subtypeₗᵢ
  dense₀ := (hessOp 3).dense_minimalVia_domain_of _ _ (denseVia_symSub hΩ) (denseVia_scalar hΩ)
    hess_mapsTo
  dense₁ := (curlOp 3).dense_minimalVia_domain_of _ _ (denseVia_trSub hΩ) (denseVia_symSub hΩ)
    (curl_mapsTo hΩ)
  closed₀ := (hessOp 3).isClosed_minimalVia _ _ (denseVia_symSub hΩ)
  closed₁ := (curlOp 3).isClosed_minimalVia _ _ (denseVia_trSub hΩ)
  mapsTo := ConstCoeffOp.minimalVia_mapsTo _ _ _ _ isComplexPair_hess_curl (denseVia_symSub hΩ)
    (denseVia_trSub hΩ)
  comp := ConstCoeffOp.minimalVia_comp _ _ _ _ isComplexPair_hess_curl (denseVia_symSub hΩ)
    (denseVia_trSub hΩ)

/-- **`H̊(curl, S) ⊆ H̊(curl, M)`** with the same curl. -/
theorem hessCurl_d₁_graph_map (hΩ : IsOpen Ω) (x : (hessCurl 𝕜 hΩ).d₁.domain) :
    (((x : symSub 𝕜 Ω) : L2F 𝕜 Ω Ix), (((hessCurl 𝕜 hΩ).d₁ x : trSub 𝕜 Ω) : L2F 𝕜 Ω Ix)) ∈
      ((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).minimal Ω).graph :=
  (curlOp 3).minimalVia_graph_map _ _ hΩ (denseVia_trSub hΩ) x

/-- **`D(d₁†) = H(sym curl, T)`** for (4.16): weak curl against symmetric test fields. -/
theorem mem_adjoint_hessCurl_d₁_domain_iff (hΩ : IsOpen Ω) {v : trSub 𝕜 Ω} :
    v ∈ (hessCurl 𝕜 hΩ).d₁†.domain ↔ ∃ w : symSub 𝕜 Ω,
      ∀ p ∈ (curlOp 3 : ConstCoeffOp R3 𝕜 _ _).testGraphVia (symSub 𝕜 Ω).subtypeₗᵢ
        (trSub 𝕜 Ω).subtypeₗᵢ, ⟪w, p.1⟫_𝕜 = ⟪v, p.2⟫_𝕜 :=
  (curlOp 3).mem_adjoint_minimalVia_domain_iff _ _ (denseVia_trSub hΩ) (hessCurl 𝕜 hΩ).dense₁

/-- **`D(d₀†) = H(div div, S)`** for (4.16): weak double divergence against test functions. -/
theorem mem_adjoint_hessCurl_d₀_domain_iff (hΩ : IsOpen Ω) {v : symSub 𝕜 Ω} :
    v ∈ (hessCurl 𝕜 hΩ).d₀†.domain ↔ ∃ w : L2 𝕜 Ω,
      ∀ p ∈ (hessOp 3 : ConstCoeffOp R3 𝕜 _ _).testGraphVia (L2.toL2F 𝕜 Ω)
        (symSub 𝕜 Ω).subtypeₗᵢ, ⟪w, p.1⟫_𝕜 = ⟪v, p.2⟫_𝕜 :=
  (hessOp 3).mem_adjoint_minimalVia_domain_iff _ _ (denseVia_symSub hΩ) (hessCurl 𝕜 hΩ).dense₀

/-! ## Failure of TSD propagation for (4.16): Prop 4.19 on bounded domains -/

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

variable (Ω) in
/-- `L²(TSD)` inside `L²(S)`. -/
def tsdS : Submodule ℝ (symSub ℝ Ω) := (tsd Ω).comap (symSub ℝ Ω).subtype

instance : (tsdS Ω).HasOrthogonalProjection := by
  have : CompleteSpace (tsdS Ω) :=
    (isClosed_tsd.preimage continuous_subtype_val).completeSpace_coe
  infer_instance

variable (Ω) in
/-- `L²(TSD)` inside `L²(T)`. -/
def tsdT : Submodule ℝ (trSub ℝ Ω) := (tsd Ω).comap (trSub ℝ Ω).subtype

instance : (tsdT Ω).HasOrthogonalProjection := by
  have : CompleteSpace (tsdT Ω) :=
    (isClosed_tsd.preimage continuous_subtype_val).completeSpace_coe
  infer_instance

/-- `⟪-diag(1, -1, 0), Φ⟫ = ⟪β, curl Φ⟫` for every test field `Φ`: `curl β = -diag(1, -1, 0)`
weakly. -/
theorem inner_betaL2_curl (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Φ : Ix → R3 → ℝ}
    (hΦ : IsTestField Ω Φ) :
    ⟪-constField hΩ hb diagA, testField hΦ⟫_ℝ =
      ⟪betaL2 hΩ hb, testField ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply hΦ)⟫_ℝ := by
  obtain ⟨hβM, hβv⟩ := betaL2_mem_adjoint hΩ hb (gradCurl ℝ hΩ) le_rfl
  have h := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).adjoint_minimal_inner_testField hΩ ⟨_, hβM⟩ hΦ
  rw [← hβv]
  exact h

/-- `β ∈ D(d₁†)` for every complex with `d₁ ⊆ curl` on `H̊(curl, S)`, with
`d₁† β = -diag(1, -1, 0)`. -/
theorem betaT_mem_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {W₀ : Type*}
    [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    (S : ShortHilbertComplex ℝ W₀ (symSub ℝ Ω) (trSub ℝ Ω)) (hd₁ : S.d₁ ≤ (hessCurl ℝ hΩ).d₁) :
    ∃ h : (⟨_, (betaL2_mem_tsd hΩ hb).2.1⟩ : trSub ℝ Ω) ∈ S.d₁†.domain,
      S.d₁† ⟨_, h⟩ = -(⟨_, (constField_mem_tsd hΩ hb diagA_transpose diagA_trace).1⟩ :
        symSub ℝ Ω) := by
  set β : trSub ℝ Ω := ⟨_, (betaL2_mem_tsd hΩ hb).2.1⟩
  set G : symSub ℝ Ω := ⟨_, (constField_mem_tsd hΩ hb diagA_transpose diagA_trace).1⟩
  have key : ∀ p ∈ (curlOp 3 : ConstCoeffOp R3 ℝ _ _).testGraphVia (symSub ℝ Ω).subtypeₗᵢ
      (trSub ℝ Ω).subtypeₗᵢ, ⟪-G, p.1⟫_ℝ = ⟪β, p.2⟫_ℝ := by
    rintro ⟨x, y⟩ ⟨Φ, hΦ, h1, h2⟩
    have e1 : ((x : symSub ℝ Ω) : L2F ℝ Ω Ix) = testField hΦ := h1
    have e2 : ((y : trSub ℝ Ω) : L2F ℝ Ω Ix) = testField
        ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply hΦ) := h2
    change ⟪((-G : symSub ℝ Ω) : L2F ℝ Ω Ix), (x : L2F ℝ Ω Ix)⟫_ℝ =
      ⟪((β : trSub ℝ Ω) : L2F ℝ Ω Ix), (y : L2F ℝ Ω Ix)⟫_ℝ
    rw [e1, e2, Submodule.coe_neg]
    exact inner_betaL2_curl hΩ hb hΦ
  have hβ1 : β ∈ (hessCurl ℝ hΩ).d₁†.domain := (mem_adjoint_hessCurl_d₁_domain_iff hΩ).2 ⟨-G, key⟩
  have hle := LinearPMap.adjoint_le_adjoint_of_le S.dense₁ hd₁
  refine ⟨hle.1 hβ1, ?_⟩
  rw [← hle.2 (x := ⟨β, hβ1⟩) (y := ⟨β, hle.1 hβ1⟩) rfl]
  exact (curlOp 3).adjoint_minimalVia_apply_eq _ _ (denseVia_trSub hΩ) (hessCurl ℝ hΩ).dense₁
    ⟨β, hβ1⟩ key

set_option maxHeartbeats 800000 in
/-- **TSD data do not propagate for the complex (4.16)** (the conclusion of thesis Prop 4.19
fails on every nonempty bounded open `Ω ⊆ ℝ³`): for every short complex
`W₀ → L²(Ω; S) → L²(Ω; T)` with `d₁ ⊆ curl` on `H̊(curl, S)`, the TSD datum `(0, 0, β)` lies in
`D(L) ∩ K`, `K = {0} × L²(TSD) × L²(TSD)`, and every strong solution from it leaves `K` at once.
Thesis: Prop 4.19 -/
theorem not_propagates_sym (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {W₀ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    (S : ShortHilbertComplex ℝ W₀ (symSub ℝ Ω) (trSub ℝ Ω))
    (hd₁ : S.d₁ ≤ (hessCurl ℝ hΩ).d₁) :
    ∃ U₀ ∈ S.wave.domain,
      U₀ ∈ HilbertComplex.totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsdS Ω)
        (tsdT Ω)) ∧
      ∀ T > 0, ∀ U : ℝ → PiLp 2 (ShortHilbertComplex.W3 W₀ (symSub ℝ Ω) (trSub ℝ Ω)), U 0 = U₀ →
        Evolution.IsStrongSolution S.wave (Icc 0 T) 0 U →
          ∃ t ∈ Icc 0 T, U t ∉ HilbertComplex.totalSub
            (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsdS Ω) (tsdT Ω)) := by
  obtain ⟨hβS, hβSv⟩ := betaT_mem_adjoint hΩ hb S hd₁
  let β : trSub ℝ Ω := ⟨_, (betaL2_mem_tsd hΩ hb).2.1⟩
  let G : symSub ℝ Ω := ⟨_, (constField_mem_tsd hΩ hb diagA_transpose diagA_trace).1⟩
  let U₀ : PiLp 2 (ShortHilbertComplex.W3 W₀ (symSub ℝ Ω) (trSub ℝ Ω)) :=
    WithLp.toLp 2 (Pi.single (M := ShortHilbertComplex.W3 W₀ (symSub ℝ Ω) (trSub ℝ Ω)) 2 β)
  have h0 : (U₀ 0 : W₀) = 0 := rfl
  have h1 : (U₀ 1 : symSub ℝ Ω) = 0 := by
    simp only [U₀]
    rfl
  have h2 : (U₀ 2 : trSub ℝ Ω) = β := rfl
  have hD : U₀ ∈ S.wave.domain := by
    rw [S.mem_wave_domain, h0, h1, h2]
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, Submodule.zero_mem _, hβS⟩
  have hK : U₀ ∈ HilbertComplex.totalSub
      (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsdS Ω) (tsdT Ω)) :=
    ShortHilbertComplex.single_two_mem_totalSub_family3 (⊥ : Submodule ℝ W₀) (tsdS Ω) (tsdT Ω)
      (v := β) (Submodule.mem_comap.2 (betaL2_mem_tsd hΩ hb))
  refine ⟨U₀, hD, hK, fun T hT U hU0 hU => ?_⟩
  have hG : G ∈ (tsdS Ω ⊓ S.d₁.domain)ᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro z ⟨hzK, hzD⟩
    have hzM := hessCurl_d₁_graph_map hΩ ⟨z, hd₁.1 hzD⟩
    rw [Submodule.coe_inner]
    exact inner_constField_eq_zero hΩ hb diagA ⟨hzK, LinearPMap.mem_domain_of_mem_graph hzM⟩
  have hne0 : ⟪G, S.d₁† ⟨β, hβS⟩⟫_ℝ ≠ 0 := by
    rw [hβSv, inner_neg_right, Submodule.coe_inner, real_inner_comm, inner_constField]
    simp only [integral_constField, Fintype.sum_prod_type, Fin.sum_univ_three]
    have hpos := volume_real_pos hΩ hb hne
    simp [diagA]
    positivity
  obtain ⟨t, ht, hnot⟩ := S.not_propagates_of_inner_ne_zero hG ⟨β, hβS⟩ hne0 hT hU
    (by rw [hU0]; exact h0) (by rw [hU0]; exact h2)
  exact ⟨t, ht, fun hmem => hnot (hmem 1)⟩

end Feec.Models.BoundedDomain
