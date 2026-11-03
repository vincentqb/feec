module

public import Feec.Models.BoundedDomain.Density
public import Feec.Domain.Constrained
public import Feec.HilbertComplex.ShortDual

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

Dualizing `symCurlDivDiv` (`Feec.ShortHilbertComplex.dual`) gives the complex with the
maximal boundary conditions, `H²(Ω) --grad grad--> H(curl, Ω; S) --curl--> L²(Ω; T)`
(`hessCurlMax`); the minimal operators are restrictions of the maximal ones
(`hessCurl_d₀_le_hessCurlMax_d₀`, `hessCurl_d₁_le_hessCurlMax_d₁`), and smooth fields up to the
boundary lie in the maximal domains with their classical values (`smooth_mem_hessCurlMax_d₀`,
`smoothField_mem_hessCurlMax_d₁`, `smoothField_mem_adjoint_hessCurl_d₁`).

The pieces of [QuennevilleBelair2015], Lemma 3.5 for (4.16): `curl` maps `L²(TSD) ∩ H̊(curl, S)`
into `L²(TSD) ∩ L²(T)` (`hessCurl_d₁_mem_tsdT`), `curl†` maps `L²(TSD) ∩ D(curl†)` into
`L²(TSD) ∩ L²(S)` (`adjoint_hessCurl_d₁_mem_tsdS`), and a field of `L²(TSD)` with a weak curl
in `L²(TSD)` has a symmetric curl (`symm_of_weakCurl_tsd`). The divergence-free constraint
propagates ([QuennevilleBelair2015], Prop. 4.16: `hessCurl_divFree_propagates`) and the reduced
system is well posed ([QuennevilleBelair2015], Prop. 4.18:
`hessCurl_existsUnique_reducedSolution`).

`H̊(curl, S) ⊆ H̊(curl, M)` with the same curl (`Feec.Domain.ConstCoeffOp.minimalVia_graph_map`),
so the zero-mean theorem of `Feec.Models.BoundedDomain.GradCurl` applies to symmetric TSD fields,
and **TSD propagation fails for (4.16)** on every nonempty bounded open `Ω` for the constraint
spaces `tsdS`, `tsdT` (`Feec.Counterexamples.BoundedSymTSD.tsd_not_propagates`, the bounded-domain
refutation of thesis Prop 4.19).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Lemma 3.5, Prop. 4.16, Prop. 4.18, §4.11 (Prop. 4.19, complex (4.16))
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], §8 (Hessian and div-div complexes)

Bibliography: [references.bib](../../../docs/references.bib)
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
embeddings. [QuennevilleBelair2015], Prop 4.19 -/
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

/-! ## The constraint spaces of (4.16) -/

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

/-! ## The complex with the dual boundary conditions, and its dual -/

section DualComplex

variable {𝕜 : Type*} [RCLike 𝕜] {Ω : Set R3}

/-- `sym curl` maps trace-free test fields to symmetric test fields. -/
theorem symCurl_mapsTo (φ : Ix → R3 → 𝕜) (hφ : IsTestField Ω φ) (x : trSub 𝕜 Ω)
    (_ : ((trSub 𝕜 Ω).subtypeₗᵢ x : L2F 𝕜 Ω Ix) = testField hφ) :
    ∃ y : symSub 𝕜 Ω, ((symSub 𝕜 Ω).subtypeₗᵢ y : L2F 𝕜 Ω Ix) =
      testField ((symCurlOp : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ) :=
  ⟨⟨_, testField_mem_symSub _ fun i j => funext fun z => by
    rw [symCurlOp_apply, symCurlOp_apply, add_comm]⟩, rfl⟩

/-- `div div` maps symmetric test fields to scalar test functions. -/
theorem divdiv_mapsTo (Ψ : Ix → R3 → 𝕜) (hΨ : IsTestField Ω Ψ) (x : symSub 𝕜 Ω)
    (_ : ((symSub 𝕜 Ω).subtypeₗᵢ x : L2F 𝕜 Ω Ix) = testField hΨ) :
    ∃ y : L2 𝕜 Ω, L2.toL2F 𝕜 Ω y =
      testField ((divdivOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hΨ) :=
  ⟨testField ((divdivOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hΨ) (),
    (WithLp.ext_iff 2).2 (funext fun _ => rfl)⟩

variable (𝕜) in
/-- **The complex with the dual boundary conditions**
`H̊(sym curl, Ω; T) --sym curl--> H̊(div div, Ω; S) --div div--> L²(Ω)`: the realizations of
`sym curl` and `div div` along the trace-free, symmetric and scalar embeddings (the adjoint
complex (4.17) with the boundary conditions moved to it). [QuennevilleBelair2015], (4.17) -/
def symCurlDivDiv (hΩ : IsOpen Ω) : ShortHilbertComplex 𝕜 (trSub 𝕜 Ω) (symSub 𝕜 Ω) (L2 𝕜 Ω) where
  d₀ := symCurlOp.minimalVia (trSub 𝕜 Ω).subtypeₗᵢ (symSub 𝕜 Ω).subtypeₗᵢ
  d₁ := (divdivOp 3).minimalVia (symSub 𝕜 Ω).subtypeₗᵢ (L2.toL2F 𝕜 Ω)
  dense₀ := symCurlOp.dense_minimalVia_domain_of _ _ (denseVia_symSub hΩ) (denseVia_trSub hΩ)
    symCurl_mapsTo
  dense₁ := (divdivOp 3).dense_minimalVia_domain_of _ _ (denseVia_scalar hΩ) (denseVia_symSub hΩ)
    divdiv_mapsTo
  closed₀ := symCurlOp.isClosed_minimalVia _ _ (denseVia_symSub hΩ)
  closed₁ := (divdivOp 3).isClosed_minimalVia _ _ (denseVia_scalar hΩ)
  mapsTo := ConstCoeffOp.minimalVia_mapsTo _ _ _ _ isComplexPair_symCurl_divdiv
    (denseVia_symSub hΩ) (denseVia_scalar hΩ)
  comp := ConstCoeffOp.minimalVia_comp _ _ _ _ isComplexPair_symCurl_divdiv
    (denseVia_symSub hΩ) (denseVia_scalar hΩ)

variable (𝕜) in
/-- **The complex (4.16) with the boundary conditions printed in Prop 4.19**
`H²(Ω) --grad grad--> H(curl, Ω; S) --curl--> L²(Ω; T)` (no boundary conditions): the dual of
`symCurlDivDiv`, `d₀ = (div div)†`, `d₁ = (sym curl)†`. Its adjoints are `div div` on
`H̊(div div, S)` and `sym curl` on `H̊(sym curl, T)` (`adjoint_hessCurlMax_d₀`,
`adjoint_hessCurlMax_d₁`), so its wave operator has the data space
`H² × (H(curl, S) ∩ H̊(div div, S)) × H̊(sym curl, T)` of the statement of Prop 4.19.
[QuennevilleBelair2015], Prop. 4.19 (§4.11) -/
abbrev hessCurlMax (hΩ : IsOpen Ω) : ShortHilbertComplex 𝕜 (L2 𝕜 Ω) (symSub 𝕜 Ω) (trSub 𝕜 Ω) :=
  (symCurlDivDiv 𝕜 hΩ).dual

theorem adjoint_hessCurlMax_d₀ (hΩ : IsOpen Ω) :
    (hessCurlMax 𝕜 hΩ).d₀† = (symCurlDivDiv 𝕜 hΩ).d₁ :=
  (symCurlDivDiv 𝕜 hΩ).adjoint_dual_d₀

theorem adjoint_hessCurlMax_d₁ (hΩ : IsOpen Ω) :
    (hessCurlMax 𝕜 hΩ).d₁† = (symCurlDivDiv 𝕜 hΩ).d₀ :=
  (symCurlDivDiv 𝕜 hΩ).adjoint_dual_d₁

/-- **`D(d₀) = H²(Ω)`** for `hessCurlMax` (no boundary condition): `f` has a weak Hessian in
`L²(S)`, tested against symmetric test fields. -/
theorem mem_hessCurlMax_d₀_domain_iff (hΩ : IsOpen Ω) {f : L2 𝕜 Ω} :
    f ∈ (hessCurlMax 𝕜 hΩ).d₀.domain ↔ ∃ H : symSub 𝕜 Ω,
      ∀ p ∈ (divdivOp 3 : ConstCoeffOp R3 𝕜 _ _).testGraphVia (symSub 𝕜 Ω).subtypeₗᵢ
        (L2.toL2F 𝕜 Ω), ⟪H, p.1⟫_𝕜 = ⟪f, p.2⟫_𝕜 :=
  (divdivOp 3).mem_adjoint_minimalVia_domain_iff _ _ (denseVia_scalar hΩ)
    (symCurlDivDiv 𝕜 hΩ).dense₁

/-- **`D(d₁) = H(curl, S)`** for `hessCurlMax` (no boundary condition): `E` has a weak curl in
`L²(T)`, tested against trace-free test fields. -/
theorem mem_hessCurlMax_d₁_domain_iff (hΩ : IsOpen Ω) {E : symSub 𝕜 Ω} :
    E ∈ (hessCurlMax 𝕜 hΩ).d₁.domain ↔ ∃ C : trSub 𝕜 Ω,
      ∀ p ∈ (symCurlOp : ConstCoeffOp R3 𝕜 _ _).testGraphVia (trSub 𝕜 Ω).subtypeₗᵢ
        (symSub 𝕜 Ω).subtypeₗᵢ, ⟪C, p.1⟫_𝕜 = ⟪E, p.2⟫_𝕜 :=
  symCurlOp.mem_adjoint_minimalVia_domain_iff _ _ (denseVia_symSub hΩ) (symCurlDivDiv 𝕜 hΩ).dense₀

/-- The value of `d₀` of `hessCurlMax` is the weak Hessian. -/
theorem hessCurlMax_d₀_apply_eq (hΩ : IsOpen Ω) (f : (hessCurlMax 𝕜 hΩ).d₀.domain)
    {H : symSub 𝕜 Ω} (hH : ∀ p ∈ (divdivOp 3 : ConstCoeffOp R3 𝕜 _ _).testGraphVia
      (symSub 𝕜 Ω).subtypeₗᵢ (L2.toL2F 𝕜 Ω), ⟪H, p.1⟫_𝕜 = ⟪(f : L2 𝕜 Ω), p.2⟫_𝕜) :
    (hessCurlMax 𝕜 hΩ).d₀ f = H :=
  (divdivOp 3 : ConstCoeffOp R3 𝕜 _ _).adjoint_minimalVia_apply_eq (symSub 𝕜 Ω).subtypeₗᵢ
    (L2.toL2F 𝕜 Ω) (denseVia_scalar hΩ) (symCurlDivDiv 𝕜 hΩ).dense₁ f hH

/-- The value of `d₁` of `hessCurlMax` is the weak curl. -/
theorem hessCurlMax_d₁_apply_eq (hΩ : IsOpen Ω) (E : (hessCurlMax 𝕜 hΩ).d₁.domain)
    {C : trSub 𝕜 Ω} (hC : ∀ p ∈ (symCurlOp : ConstCoeffOp R3 𝕜 _ _).testGraphVia
      (trSub 𝕜 Ω).subtypeₗᵢ (symSub 𝕜 Ω).subtypeₗᵢ, ⟪C, p.1⟫_𝕜 = ⟪(E : symSub 𝕜 Ω), p.2⟫_𝕜) :
    (hessCurlMax 𝕜 hΩ).d₁ E = C :=
  (symCurlOp : ConstCoeffOp R3 𝕜 _ _).adjoint_minimalVia_apply_eq (trSub 𝕜 Ω).subtypeₗᵢ
    (symSub 𝕜 Ω).subtypeₗᵢ (denseVia_symSub hΩ) (symCurlDivDiv 𝕜 hΩ).dense₀ E hC

end DualComplex

/-! ## Comparison of the two placements of the boundary conditions -/

section Compare

variable {𝕜 : Type*} [RCLike 𝕜] {Ω : Set R3}

/-- Symmetric fields pair with `sym M` as with `M`. -/
theorem inner_symProj_of_mem (E : symSub 𝕜 Ω) (u : L2F 𝕜 Ω Ix) :
    ⟪(E : L2F 𝕜 Ω Ix), symProj u⟫_𝕜 = ⟪(E : L2F 𝕜 Ω Ix), u⟫_𝕜 := by
  rw [← inner_symProj, symProj_eq_self E.2]

/-- `sym curl φ = sym (curl φ)` on test fields. -/
theorem testField_symCurl {φ : Ix → R3 → 𝕜} (hφ : IsTestField Ω φ) :
    testField ((symCurlOp : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ) =
      symProj (testField ((curlOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ)) := by
  obtain ⟨hΨ, e⟩ := matCLM_testField (Ω := Ω) (symMat 3) ((curlOp 3).isTestField_apply hφ)
  rw [symProj, e]
  exact testField_congr _ _ (funext fun ij => funext fun x => by rw [symCurlOp,
      ConstCoeffOp.postComp_apply])

/-- **`H̊(curl, S) ⊆ H(curl, S)`**: the curl of (4.16) is a restriction of the weak curl of the
complex with the printed boundary conditions. -/
theorem hessCurl_d₁_le_hessCurlMax_d₁ (hΩ : IsOpen Ω) :
    (hessCurl 𝕜 hΩ).d₁ ≤ (hessCurlMax 𝕜 hΩ).d₁ := by
  have key : ∀ u : (hessCurl 𝕜 hΩ).d₁.domain,
      ∀ p ∈ (symCurlOp : ConstCoeffOp R3 𝕜 _ _).testGraphVia (trSub 𝕜 Ω).subtypeₗᵢ
        (symSub 𝕜 Ω).subtypeₗᵢ, ⟪(hessCurl 𝕜 hΩ).d₁ u, p.1⟫_𝕜 = ⟪(u : symSub 𝕜 Ω), p.2⟫_𝕜 := by
    rintro u ⟨x, y⟩ ⟨φ, hφ, h1, h2⟩
    simp only at h1 h2
    obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff _).1 (hessCurl_d₁_graph_map hΩ u)
    simp only at hz1 hz2
    have e := (curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).closure_testGraph_inner_testField
      ((curlOp 3).mem_closure_minimal hΩ z) hφ
    have ec : testField ((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).formalAdj.isTestField_apply hφ) =
        testField ((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).isTestField_apply hφ) :=
      testField_congr _ _ (curlOp_formalAdj_apply φ)
    rw [ec] at e
    have e' : ⟪(((hessCurl 𝕜 hΩ).d₁ u : trSub 𝕜 Ω) : L2F 𝕜 Ω Ix), testField hφ⟫_𝕜 =
        ⟪((u : symSub 𝕜 Ω) : L2F 𝕜 Ω Ix),
          testField ((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).isTestField_apply hφ)⟫_𝕜 := by
      rw [← hz2, ← hz1]; exact e
    rw [Submodule.coe_inner, Submodule.coe_inner, show (x : L2F 𝕜 Ω Ix) = testField hφ from h1,
      show (y : L2F 𝕜 Ω Ix) = testField ((symCurlOp : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ)
        from h2, e', testField_symCurl hφ, inner_symProj_of_mem]
  refine ⟨fun u hu => ?_, ?_⟩
  · have hk := key ⟨u, hu⟩
    exact (mem_hessCurlMax_d₁_domain_iff hΩ).2 ⟨_, hk⟩
  · intro x y hxy
    have hk := key x
    have hmem : (x : symSub 𝕜 Ω) ∈ (hessCurlMax 𝕜 hΩ).d₁.domain :=
      (mem_hessCurlMax_d₁_domain_iff hΩ).2 ⟨_, hk⟩
    have e := (symCurlOp : ConstCoeffOp R3 𝕜 _ _).adjoint_minimalVia_apply_eq
      (trSub 𝕜 Ω).subtypeₗᵢ (symSub 𝕜 Ω).subtypeₗᵢ (denseVia_symSub hΩ)
      (symCurlDivDiv 𝕜 hΩ).dense₀ ⟨_, hmem⟩ hk
    have hy : y = ⟨(x : symSub 𝕜 Ω), hmem⟩ := Subtype.ext hxy.symm
    subst hy
    exact e.symm

/-- **`H̊²(Ω) ⊆ H²(Ω)`**: the Hessian of (4.16) is a restriction of the weak Hessian. -/
theorem hessCurl_d₀_le_hessCurlMax_d₀ (hΩ : IsOpen Ω) :
    (hessCurl 𝕜 hΩ).d₀ ≤ (hessCurlMax 𝕜 hΩ).d₀ := by
  have key : ∀ u : (hessCurl 𝕜 hΩ).d₀.domain,
      ∀ p ∈ (divdivOp 3 : ConstCoeffOp R3 𝕜 _ _).testGraphVia (symSub 𝕜 Ω).subtypeₗᵢ
        (L2.toL2F 𝕜 Ω), ⟪(hessCurl 𝕜 hΩ).d₀ u, p.1⟫_𝕜 = ⟪(u : L2 𝕜 Ω), p.2⟫_𝕜 := by
    rintro u ⟨x, y⟩ ⟨Ψ, hΨ, h1, h2⟩
    simp only at h1 h2
    obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff _).1
      ((hessOp 3).minimalVia_graph_map _ _ hΩ (denseVia_symSub hΩ) u)
    simp only at hz1 hz2
    have e := (hessOp 3 : ConstCoeffOp R3 𝕜 Unit Ix).closure_testGraph_inner_testField
      ((hessOp 3).mem_closure_minimal hΩ z) hΨ
    have ec : testField ((hessOp 3 : ConstCoeffOp R3 𝕜 Unit Ix).formalAdj.isTestField_apply hΨ) =
        testField ((divdivOp 3 : ConstCoeffOp R3 𝕜 Ix Unit).isTestField_apply hΨ) :=
      testField_congr _ _ (by rw [hessOp_formalAdj])
    rw [ec] at e
    have e' : ⟪(((hessCurl 𝕜 hΩ).d₀ u : symSub 𝕜 Ω) : L2F 𝕜 Ω Ix), testField hΨ⟫_𝕜 =
        ⟪L2.toL2F 𝕜 Ω (u : L2 𝕜 Ω),
          testField ((divdivOp 3 : ConstCoeffOp R3 𝕜 Ix Unit).isTestField_apply hΨ)⟫_𝕜 := by
      have h := e
      rw [hz2, hz1] at h
      exact h
    rw [Submodule.coe_inner, show (x : L2F 𝕜 Ω Ix) = testField hΨ from h1, e', ← h2,
      LinearIsometry.inner_map_map]
  refine ⟨fun u hu => (mem_hessCurlMax_d₀_domain_iff hΩ).2 ⟨_, key ⟨u, hu⟩⟩, ?_⟩
  intro x y hxy
  have hk := key x
  have hmem : (x : L2 𝕜 Ω) ∈ (hessCurlMax 𝕜 hΩ).d₀.domain :=
    (mem_hessCurlMax_d₀_domain_iff hΩ).2 ⟨_, hk⟩
  have e := (divdivOp 3 : ConstCoeffOp R3 𝕜 _ _).adjoint_minimalVia_apply_eq
    (symSub 𝕜 Ω).subtypeₗᵢ (L2.toL2F 𝕜 Ω) (denseVia_scalar hΩ) (symCurlDivDiv 𝕜 hΩ).dense₁
    ⟨_, hmem⟩ hk
  have hy : y = ⟨(x : L2 𝕜 Ω), hmem⟩ := Subtype.ext hxy.symm
  subst hy
  exact e.symm

/-- `H̊(sym curl, T) ⊆ H(sym curl, T)` with the same `sym curl`: `d₁†` of the printed
placement is a restriction of `d₁†` of (4.16). -/
theorem adjoint_hessCurlMax_d₁_le (hΩ : IsOpen Ω) :
    (hessCurlMax 𝕜 hΩ).d₁† ≤ (hessCurl 𝕜 hΩ).d₁† :=
  LinearPMap.adjoint_le_adjoint_of_le (hessCurl 𝕜 hΩ).dense₁ (hessCurl_d₁_le_hessCurlMax_d₁ hΩ)

/-- `H̊(div div, S) ⊆ H(div div, S)` with the same `div div`. -/
theorem adjoint_hessCurlMax_d₀_le (hΩ : IsOpen Ω) :
    (hessCurlMax 𝕜 hΩ).d₀† ≤ (hessCurl 𝕜 hΩ).d₀† :=
  LinearPMap.adjoint_le_adjoint_of_le (hessCurl 𝕜 hΩ).dense₀ (hessCurl_d₀_le_hessCurlMax_d₀ hΩ)

/-- **`ker (grad grad)† = H(div div, S, 0)`** for (4.16): `B ⊥ ∇²φ` for every test function `φ`
(no boundary condition). -/
theorem mem_ker_adjoint_hessCurl_d₀_iff (hΩ : IsOpen Ω) {B : symSub 𝕜 Ω} :
    B ∈ (hessCurl 𝕜 hΩ).d₀†.ker ↔ ∀ (φ : Unit → R3 → 𝕜) (hφ : IsTestField Ω φ),
      ⟪(B : L2F 𝕜 Ω Ix), testField ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ)⟫_𝕜 =
        0 := by
  constructor
  · intro hB φ hφ
    obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 hB
    subst hy
    obtain ⟨y', hy'⟩ := hess_mapsTo φ hφ (testField hφ ())
      ((WithLp.ext_iff 2).2 (funext fun _ => rfl))
    have hp : ((testField hφ () : L2 𝕜 Ω), y') ∈ (hessCurl 𝕜 hΩ).d₀.graph :=
      (hessOp 3).mem_graph_minimalVia _ _ (denseVia_symSub hΩ)
        ⟨φ, hφ, (WithLp.ext_iff 2).2 (funext fun _ => rfl), hy'⟩
    have e := LinearPMap.adjoint_inner_of_mem_graph (hessCurl 𝕜 hΩ).dense₀ y hp
    simp only at e
    rw [hy0, inner_zero_left, Submodule.coe_inner] at e
    rw [← hy']
    exact e.symm
  · intro hB
    have key : ∀ p ∈ (hessOp 3 : ConstCoeffOp R3 𝕜 _ _).testGraphVia (L2.toL2F 𝕜 Ω)
        (symSub 𝕜 Ω).subtypeₗᵢ, ⟪(0 : L2 𝕜 Ω), p.1⟫_𝕜 = ⟪B, p.2⟫_𝕜 := by
      rintro ⟨x, y⟩ ⟨φ, hφ, -, h2⟩
      rw [inner_zero_left]
      change 0 = ⟪((B : symSub 𝕜 Ω) : L2F 𝕜 Ω Ix), ((symSub 𝕜 Ω).subtypeₗᵢ y)⟫_𝕜
      rw [h2, hB φ hφ]
    have hmem := (mem_adjoint_hessCurl_d₀_domain_iff hΩ).2 ⟨0, key⟩
    exact LinearPMap.mem_ker_iff.2 ⟨⟨B, hmem⟩, rfl,
      (hessOp 3).adjoint_minimalVia_apply_eq _ _ (denseVia_symSub hΩ) (hessCurl 𝕜 hΩ).dense₀ _ key⟩

/-- Symmetric test fields lie in `D(d₁) ∩ D(d₀†)` of (4.16). -/
theorem testField_mem_hessCurl_d₁_domain (hΩ : IsOpen Ω) {Φ : Ix → R3 → 𝕜}
    (hΦ : IsTestField Ω Φ) (hs : ∀ i j, Φ (i, j) = Φ (j, i)) :
    (⟨testField hΦ, testField_mem_symSub hΦ hs⟩ : symSub 𝕜 Ω) ∈ (hessCurl 𝕜 hΩ).d₁.domain := by
  obtain ⟨y, hy⟩ := curl_mapsTo hΩ Φ hΦ ⟨_, testField_mem_symSub hΦ hs⟩ rfl
  exact LinearPMap.mem_domain_of_mem_graph
    ((curlOp 3).mem_graph_minimalVia _ _ (denseVia_trSub hΩ) ⟨Φ, hΦ, rfl, hy⟩)

theorem testField_mem_adjoint_hessCurl_d₀ (hΩ : IsOpen Ω) {Φ : Ix → R3 → 𝕜}
    (hΦ : IsTestField Ω Φ) (hs : ∀ i j, Φ (i, j) = Φ (j, i)) :
    (⟨testField hΦ, testField_mem_symSub hΦ hs⟩ : symSub 𝕜 Ω) ∈ (hessCurl 𝕜 hΩ).d₀†.domain := by
  refine (mem_adjoint_hessCurl_d₀_domain_iff hΩ).2
    ⟨testField ((divdivOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hΦ) (), ?_⟩
  rintro ⟨x, y⟩ ⟨φ, hφ, h1, h2⟩
  simp only at h1 h2
  rw [← (L2.toL2F 𝕜 Ω).inner_map_map, h1, Submodule.coe_inner]
  change ⟪testField ((divdivOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hΦ), testField hφ⟫_𝕜 =
    ⟪testField hΦ, (symSub 𝕜 Ω).subtypeₗᵢ y⟫_𝕜
  rw [h2, ← inner_conj_symm (testField hΦ),
    (hessOp 3 : ConstCoeffOp R3 𝕜 _ _).inner_testField_apply_testField hφ hΦ,
    inner_conj_symm, testField_congr ((hessOp 3 : ConstCoeffOp R3 𝕜 _
        _).formalAdj.isTestField_apply hΦ)
      ((divdivOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hΦ) (by rw [hessOp_formalAdj])]

/-- Symmetric test fields lie in `D(d₁) ∩ D(d₀†) = H(curl, S) ∩ H̊(div div, S)` of the printed
placement. -/
theorem testField_mem_hessCurlMax_d₁_domain (hΩ : IsOpen Ω) {Φ : Ix → R3 → 𝕜}
    (hΦ : IsTestField Ω Φ) (hs : ∀ i j, Φ (i, j) = Φ (j, i)) :
    (⟨testField hΦ, testField_mem_symSub hΦ hs⟩ : symSub 𝕜 Ω) ∈ (hessCurlMax 𝕜 hΩ).d₁.domain :=
  (hessCurl_d₁_le_hessCurlMax_d₁ hΩ).1 (testField_mem_hessCurl_d₁_domain hΩ hΦ hs)

theorem testField_mem_adjoint_hessCurlMax_d₀ (hΩ : IsOpen Ω) {Φ : Ix → R3 → 𝕜}
    (hΦ : IsTestField Ω Φ) (hs : ∀ i j, Φ (i, j) = Φ (j, i)) :
    (⟨testField hΦ, testField_mem_symSub hΦ hs⟩ : symSub 𝕜 Ω) ∈ (hessCurlMax 𝕜 hΩ).d₀†.domain := by
  rw [adjoint_hessCurlMax_d₀]
  obtain ⟨y, hy⟩ := divdiv_mapsTo Φ hΦ ⟨_, testField_mem_symSub hΦ hs⟩ rfl
  exact LinearPMap.mem_domain_of_mem_graph
    ((divdivOp 3).mem_graph_minimalVia _ _ (denseVia_scalar hΩ) ⟨Φ, hΦ, rfl, hy⟩)

end Compare

/-! ## Real fields: pointwise identities -/

section Pointwise

/-- The symmetric part `(Ψ + Ψᵀ)/2` of a matrix field. -/
def symF (Ψ : Ix → R3 → ℝ) : Ix → R3 → ℝ := fun ij x => (Ψ ij x + Ψ (ij.2, ij.1) x) / 2

theorem symF_swap (Ψ : Ix → R3 → ℝ) (i j : Fin 3) : symF Ψ (i, j) = symF Ψ (j, i) := by
  funext x
  simp only [symF]
  ring

theorem continuous_symF {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, Continuous (Ψ ij)) (ij : Ix) :
    Continuous (symF Ψ ij) :=
  ((hΨ ij).add (hΨ _)).div_const 2

/-- The scalar field `g I`. -/
def diagOf (g : R3 → ℝ) : Ix → R3 → ℝ := fun ij => if ij.1 = ij.2 then g else 0

theorem diagOf_swap (g : R3 → ℝ) (i j : Fin 3) : diagOf g (i, j) = diagOf g (j, i) := by
  simp only [diagOf, eq_comm]

theorem isTestField_diagOf {Ω : Set R3} {g : R3 → ℝ} (hg : IsTest Ω g) :
    IsTestField Ω (diagOf g) := fun ij => by
  unfold diagOf; split_ifs; exacts [hg, IsTest.zero]

/-- `curl (g I) = skewOf (-∇g)` is skew. -/
theorem curlM_diagOf (g : R3 → ℝ) (ij : Ix) (x : R3) :
    curlM (diagOf g) ij x = skewOf (fun i y => -partialDeriv i g y) ij x := by
  obtain ⟨a, b⟩ := ij
  simp only [curlM, diagOf, skewOf, pd_ite_zero]
  fin_cases a <;> fin_cases b <;> simp

/-- `∂_k ((f + g)/2) = (∂_k f + ∂_k g)/2`. -/
theorem pd_avg {f g : R3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (k : Fin 3)
    (x : R3) : partialDeriv k (fun y => (f y + g y) / 2) x =
      (partialDeriv k f x + partialDeriv k g x) / 2 := by
  have : (fun y => (f y + g y) / 2) = fun y => (1 / 2 : ℝ) * (f + g) y := by
    funext y
    simp only [Pi.add_apply]
    ring
  rw [this, partialDeriv_const_mul ((hf.add hg) _), partialDeriv_add' hf hg, Pi.add_apply]
  ring

/-- `curl sym ∇ψ = ½ (∇ curl ψ)ᵀ` (rows `½ ∂_a curl ψ`). -/
theorem curlM_symF_gradM {ψ : Fin 3 → R3 → ℝ} (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (ab : Ix)
    (x : R3) : curlM (symF (gradM ψ)) ab x = (partialDeriv ab.1 (fun y =>
      partialDeriv (ab.2 + 1) (ψ (ab.2 + 2)) y - partialDeriv (ab.2 + 2)
        (ψ (ab.2 + 1)) y) x) / 2 := by
  obtain ⟨a, b⟩ := ab
  have hd : ∀ c i, Differentiable ℝ (partialDeriv c (ψ i)) := fun c i =>
    ((hψ i).partialDeriv_infty c).differentiable (by simp)
  have h2 : ∀ i, ContDiff ℝ 2 (ψ i) := fun i => (hψ i).of_le (by simp)
  have hS : ∀ c, symF (gradM ψ) (a, c) = fun y => (partialDeriv c (ψ a) y +
    partialDeriv a (ψ c) y) / 2 :=
    fun c => rfl
  simp only [curlM]
  rw [hS, hS, pd_avg (hd _ _) (hd _ _), pd_avg (hd _ _) (hd _ _)]
  rw [partialDeriv_sub (hd _ _ _) (hd _ _ _), partialDeriv_comm (h2 a) (b + 1) (b + 2),
    partialDeriv_comm (h2 (b + 2)) (b + 1) a, partialDeriv_comm (h2 (b + 1)) (b + 2) a]
  ring

/-- The trace-free part `dev Ψ = Ψ - ⅓ (tr Ψ) I` of a matrix field. -/
def devF (Ψ : Ix → R3 → ℝ) : Ix → R3 → ℝ := fun ij x =>
  Ψ ij x - diagOf (fun y => (∑ k, Ψ (k, k) y) / 3) ij x

theorem devF_trace (Ψ : Ix → R3 → ℝ) (x : R3) : ∑ i, devF Ψ (i, i) x = 0 := by
  simp only [devF, diagOf, Fin.sum_univ_three]
  simp
  ring

theorem isTestField_devF {Ω : Set R3} {Ψ : Ix → R3 → ℝ} (hΨ : IsTestField Ω Ψ) :
    IsTestField Ω (devF Ψ) := by
  have hg : IsTest Ω (fun y => (∑ k, Ψ (k, k) y) / 3) := by
    have h := (((hΨ (0, 0)).add (hΨ (1, 1))).add (hΨ (2, 2))).const_mul (1 / 3 : ℝ)
    convert h using 1
    funext y
    simp only [Fin.sum_univ_three, Pi.add_apply]
    ring
  exact fun ij => (hΨ ij).sub (isTestField_diagOf hg ij)

/-- `curl dev Ψ = curl Ψ - curl (⅓ (tr Ψ) I)`. -/
theorem curlM_devF {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, Differentiable ℝ (Ψ ij))
    (hg : Differentiable ℝ fun y => (∑ k, Ψ (k, k) y) / 3) (ij : Ix) (x : R3) :
    curlM (devF Ψ) ij x =
      curlM Ψ ij x - curlM (diagOf fun y => (∑ k, Ψ (k, k) y) / 3) ij x := by
  have hd : ∀ ij, Differentiable ℝ (diagOf (fun y => (∑ k, Ψ (k, k) y) / 3) ij) := by
    intro ij
    unfold diagOf
    split_ifs
    exacts [hg, differentiable_const 0]
  have e : ∀ ij, devF Ψ ij = Ψ ij - diagOf (fun y => (∑ k, Ψ (k, k) y) / 3) ij := fun _ => rfl
  simp only [curlM, e, partialDeriv_sub' (hΨ _) (hd _), Pi.sub_apply]
  ring

end Pointwise

/-! ## Real fields: smooth symmetric and trace-free fields on a bounded domain -/

section Smooth

variable {Ω : Set R3}

theorem smoothField_mem_symSub (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Ψ : Ix → R3 → ℝ}
    (hΨ : ∀ ij, Continuous (Ψ ij)) (hs : ∀ i j, Ψ (i, j) = Ψ (j, i)) :
    smoothField hΩ hb Ψ hΨ ∈ symSub ℝ Ω := fun i j => by
  refine Lp.ext ?_
  filter_upwards [coeFn_smoothField hΩ hb Ψ hΨ (i, j), coeFn_smoothField hΩ hb Ψ hΨ (j, i)]
    with x h1 h2
  rw [h1, h2, hs]

theorem smoothField_mem_trSub (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Ψ : Ix → R3 → ℝ}
    (hΨ : ∀ ij, Continuous (Ψ ij)) (htr : ∀ x, ∑ i, Ψ (i, i) x = 0) :
    smoothField hΩ hb Ψ hΨ ∈ trSub ℝ Ω := by
  rw [mem_trSub]
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_fun_finsetSum (μ := volume.restrict Ω) Finset.univ
      (fun i => smoothField hΩ hb Ψ hΨ (i, i)),
    ae_all_iff.2 fun i => coeFn_smoothField hΩ hb Ψ hΨ (i, i),
    Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x h0 h1 h2
  rw [h0, h2]
  simp only [Pi.zero_apply]
  rw [Finset.sum_congr rfl fun i _ => h1 i]
  exact htr x

/-- `smoothField` depends only on the field. -/
theorem smoothField_congr {hΩ : IsOpen Ω} {hb : Bornology.IsBounded Ω} {ι : Type*}
    {Ψ Ψ' : ι → R3 → ℝ} (hΨ : ∀ i, Continuous (Ψ i)) (hΨ' : ∀ i, Continuous (Ψ' i))
    (h : Ψ = Ψ') : smoothField hΩ hb Ψ hΨ = smoothField hΩ hb Ψ' hΨ' := by
  subst h; rfl

/-- `sym` of a smooth field is the smooth field of its symmetric part. -/
theorem symProj_smoothField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {F : Ix → R3 → ℝ}
    (hF : ∀ ij, Continuous (F ij)) :
    symProj (smoothField hΩ hb F hF) = smoothField hΩ hb (symF F) (continuous_symF hF) := by
  refine (WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_)
  have e := symProj_apply (smoothField hΩ hb F hF) ij
  change (symProj (smoothField hΩ hb F hF)) ij = _ at e
  change ((symProj (smoothField hΩ hb F hF)) ij : R3 → ℝ) =ᵐ[volume.restrict Ω]
    (smoothField hΩ hb (symF F) (continuous_symF hF) ij : R3 → ℝ)
  rw [e]
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (smoothField hΩ hb F hF ij +
      smoothField hΩ hb F hF (ij.2, ij.1)),
    Lp.coeFn_add (smoothField hΩ hb F hF ij) (smoothField hΩ hb F hF (ij.2, ij.1)),
    coeFn_smoothField hΩ hb F hF ij, coeFn_smoothField hΩ hb F hF (ij.2, ij.1),
    coeFn_smoothField hΩ hb (symF F) (continuous_symF hF) ij] with x h1 h2 h3 h4 h5
  rw [h1, Pi.smul_apply, h2, Pi.add_apply, h3, h4, h5, smul_eq_mul]
  simp only [symF]
  ring

/-- Symmetric fields pair with `Ψ` as with its symmetric part. -/
theorem sum_integral_mul_symF (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {v : L2F ℝ Ω Ix}
    (hv : v ∈ symSub ℝ Ω) {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, Continuous (Ψ ij)) :
    ∑ ij, ∫ x, v ij x * symF Ψ ij x ∂volume.restrict Ω =
      ∑ ij, ∫ x, v ij x * Ψ ij x ∂volume.restrict Ω := by
  rw [← inner_smoothField hΩ hb _ (continuous_symF hΨ), ← inner_smoothField hΩ hb _ hΨ,
    ← symProj_smoothField, ← inner_symProj, symProj_eq_self hv]

/-- Green's formula for the curl against a `C¹` field with no boundary condition. -/
theorem inner_testField_curl_smoothField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {φ : Ix → R3 → ℝ} (hφ : IsTestField Ω φ) {Ψ : Ix → R3 → ℝ}
    (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) :
    ⟪testField ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply hφ),
        smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous)⟫_ℝ =
      ⟪testField hφ, smoothField hΩ hb (curlM Ψ) (continuous_curlM hΨ)⟫_ℝ := by
  have m2 : ∀ ij, MemLp ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.apply Ψ ij) 2
      (volume.restrict Ω) := fun ij => by
    rw [← curlM_eq_formalAdj_apply]
    exact memLp_of_continuous hΩ.measurableSet hb (continuous_curlM hΨ ij)
  have e := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).inner_testField_apply (N := 1) curlOp_isOrderLE hφ
    hΨ (fun ij => memLp_of_continuous hΩ.measurableSet hb (hΨ ij).continuous) m2
  refine e.trans (congrArg _ ((WithLp.ext_iff 2).2 (funext fun ij => ?_)))
  exact MemLp.toLp_congr (m2 ij) (memLp_of_continuous hΩ.measurableSet hb
    (continuous_curlM hΨ ij)) (Eventually.of_forall fun x => by rw [← curlM_eq_formalAdj_apply])

/-- Green's formula for `div div` against a smooth function with no boundary condition:
`⟪div div Ψ, φ⟫ = ⟪Ψ, ∇²φ⟫`. -/
theorem inner_testField_divdiv_smoothField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {Ψ : Ix → R3 → ℝ} (hΨ : IsTestField Ω Ψ) {φ : R3 → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ⟪testField ((divdivOp 3 : ConstCoeffOp R3 ℝ Ix Unit).isTestField_apply hΨ),
        smoothField hΩ hb (fun _ : Unit => φ) (fun _ => hφ.continuous)⟫_ℝ =
      ⟪testField hΨ, hessL2 hΩ hb hφ⟫_ℝ := by
  have hh : ∀ ij, (divdivOp 3 : ConstCoeffOp R3 ℝ Ix Unit).formalAdj.apply (fun _ => φ) ij =
      hessField φ ij := fun ij => by
    rw [divdivOp_formalAdj]
    funext x
    rw [hessOp_apply]
    rfl
  have m2 : ∀ ij, MemLp ((divdivOp 3 : ConstCoeffOp R3 ℝ Ix Unit).formalAdj.apply (fun _ => φ) ij)
      2 (volume.restrict Ω) := fun ij => by
    rw [hh]
    exact memLp_of_continuous hΩ.measurableSet hb (contDiff_hessField hφ ij).continuous
  have e := (divdivOp 3 : ConstCoeffOp R3 ℝ Ix Unit).inner_testField_apply (N := 2)
    divdivOp_isOrderLE hΨ (fun _ => hφ.of_le (by simp))
    (fun _ => memLp_of_continuous hΩ.measurableSet hb hφ.continuous) m2
  refine e.trans (congrArg _ ((WithLp.ext_iff 2).2 (funext fun ij => ?_)))
  exact MemLp.toLp_congr (m2 ij) (memLp_of_continuous hΩ.measurableSet hb
    (contDiff_hessField hφ ij).continuous) (Eventually.of_forall fun x => by rw [hh])

end Smooth

/-! ## Real fields: smooth fields in the domains -/

section Domains

variable {Ω : Set R3}

/-- **`C¹` trace-free fields lie in `D(d₁†) = H(sym curl, T)`** for (4.16) (no boundary
condition), with `d₁† Ψ = sym curl Ψ`. -/
theorem smoothField_mem_adjoint_hessCurl_d₁ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) (htr : ∀ x, ∑ i, Ψ (i, i) x = 0) :
    ∃ h : (⟨smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous),
        smoothField_mem_trSub hΩ hb _ htr⟩ : trSub ℝ Ω) ∈ (hessCurl ℝ hΩ).d₁†.domain,
      (((hessCurl ℝ hΩ).d₁† ⟨_, h⟩ : symSub ℝ Ω) : L2F ℝ Ω Ix) =
        smoothField hΩ hb (symF (curlM Ψ)) (continuous_symF (continuous_curlM hΨ)) := by
  set w : symSub ℝ Ω := ⟨smoothField hΩ hb (symF (curlM Ψ)) (continuous_symF (continuous_curlM hΨ)),
    smoothField_mem_symSub hΩ hb _ (symF_swap (curlM Ψ))⟩
  have key : ∀ p ∈ (curlOp 3 : ConstCoeffOp R3 ℝ _ _).testGraphVia (symSub ℝ Ω).subtypeₗᵢ
      (trSub ℝ Ω).subtypeₗᵢ, ⟪w, p.1⟫_ℝ = ⟪(⟨smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous),
        smoothField_mem_trSub hΩ hb _ htr⟩ : trSub ℝ Ω), p.2⟫_ℝ := by
    rintro ⟨x, y⟩ ⟨Φ, hΦ, h1, h2⟩
    simp only at h1 h2
    rw [Submodule.coe_inner, Submodule.coe_inner]
    change ⟪smoothField hΩ hb (symF (curlM Ψ)) (continuous_symF (continuous_curlM hΨ)),
        (x : L2F ℝ Ω Ix)⟫_ℝ = ⟪smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous),
        (y : L2F ℝ Ω Ix)⟫_ℝ
    rw [← symProj_smoothField, inner_symProj, symProj_eq_self x.2,
      show (x : L2F ℝ Ω Ix) = testField hΦ from h1,
      show (y : L2F ℝ Ω Ix) = testField ((curlOp 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hΦ)
        from h2, real_inner_comm _ (smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous)),
      inner_testField_curl_smoothField hΩ hb hΦ hΨ]
    exact real_inner_comm _ _
  have hmem := (mem_adjoint_hessCurl_d₁_domain_iff hΩ).2 ⟨w, key⟩
  exact ⟨hmem, congrArg Subtype.val ((curlOp 3 : ConstCoeffOp R3 ℝ _ _).adjoint_minimalVia_apply_eq
    _ _ (denseVia_trSub hΩ) (hessCurl ℝ hΩ).dense₁ ⟨_, hmem⟩ key)⟩

/-- **`C¹` symmetric fields lie in `D(d₁) = H(curl, S)`** for `hessCurlMax` (no boundary
condition: constants, linear fields, Hessians of polynomials), with `d₁ Ψ = curl Ψ`. -/
theorem smoothField_mem_hessCurlMax_d₁ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) (hs : ∀ i j, Ψ (i, j) = Ψ (j, i)) :
    ∃ h : (⟨smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous),
        smoothField_mem_symSub hΩ hb _ hs⟩ : symSub ℝ Ω) ∈ (hessCurlMax ℝ hΩ).d₁.domain,
      (((hessCurlMax ℝ hΩ).d₁ ⟨_, h⟩ : trSub ℝ Ω) : L2F ℝ Ω Ix) =
        smoothField hΩ hb (curlM Ψ) (continuous_curlM hΨ) := by
  have htr : ∀ x, ∑ i, curlM Ψ (i, i) x = 0 := fun x => by
    rw [curlM_eq_apply]; exact trace_curl_eq_zero_of_symm hs x
  set C : trSub ℝ Ω := ⟨_, smoothField_mem_trSub hΩ hb (continuous_curlM hΨ) htr⟩
  have hE : symProj (smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous)) =
      smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous) :=
    symProj_eq_self (smoothField_mem_symSub hΩ hb _ hs)
  have key : ∀ p ∈ (symCurlOp : ConstCoeffOp R3 ℝ _ _).testGraphVia (trSub ℝ Ω).subtypeₗᵢ
      (symSub ℝ Ω).subtypeₗᵢ, ⟪C, p.1⟫_ℝ = ⟪(⟨smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous),
        smoothField_mem_symSub hΩ hb _ hs⟩ : symSub ℝ Ω), p.2⟫_ℝ := by
    rintro ⟨x, y⟩ ⟨φ, hφ, h1, h2⟩
    simp only at h1 h2
    rw [Submodule.coe_inner, Submodule.coe_inner]
    change ⟪smoothField hΩ hb (curlM Ψ) (continuous_curlM hΨ), (x : L2F ℝ Ω Ix)⟫_ℝ =
      ⟪smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous), (y : L2F ℝ Ω Ix)⟫_ℝ
    rw [show (x : L2F ℝ Ω Ix) = testField hφ from h1,
      show (y : L2F ℝ Ω Ix) = testField ((symCurlOp : ConstCoeffOp R3 ℝ _ _).isTestField_apply hφ)
        from h2, testField_symCurl hφ, ← inner_symProj, hE,
      real_inner_comm _ (smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous)),
      inner_testField_curl_smoothField hΩ hb hφ hΨ]
    exact real_inner_comm _ _
  have hmem := (mem_hessCurlMax_d₁_domain_iff hΩ).2 ⟨C, key⟩
  exact ⟨hmem, congrArg Subtype.val (hessCurlMax_d₁_apply_eq hΩ ⟨_, hmem⟩ key)⟩

theorem hessL2_mem_symSub (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {φ : R3 → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : hessL2 hΩ hb hφ ∈ symSub ℝ Ω :=
  smoothField_mem_symSub hΩ hb _ fun i j => funext fun x =>
    (partialDeriv_comm (hφ.of_le (by simp)) i j x).symm

/-- **Smooth functions lie in `D(d₀) = H²(Ω)`** for `hessCurlMax` (no boundary condition: e.g.
all polynomials), with `d₀ φ = ∇²φ`. -/
theorem smooth_mem_hessCurlMax_d₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {φ : R3 → ℝ}
    (hφ : ContDiff ℝ ∞ φ) :
    ∃ h : (memLp_of_continuous hΩ.measurableSet hb hφ.continuous).toLp φ ∈
        (hessCurlMax ℝ hΩ).d₀.domain,
      (((hessCurlMax ℝ hΩ).d₀ ⟨_, h⟩ : symSub ℝ Ω) : L2F ℝ Ω Ix) = hessL2 hΩ hb hφ := by
  set H : symSub ℝ Ω := ⟨_, hessL2_mem_symSub hΩ hb hφ⟩
  have key : ∀ p ∈ (divdivOp 3 : ConstCoeffOp R3 ℝ _ _).testGraphVia (symSub ℝ Ω).subtypeₗᵢ
      (L2.toL2F ℝ Ω), ⟪H, p.1⟫_ℝ =
        ⟪(memLp_of_continuous hΩ.measurableSet hb hφ.continuous).toLp φ, p.2⟫_ℝ := by
    rintro ⟨x, y⟩ ⟨Ψ, hΨ, h1, h2⟩
    simp only at h1 h2
    rw [Submodule.coe_inner, ← (L2.toL2F ℝ Ω).inner_map_map, h2]
    change ⟪hessL2 hΩ hb hφ, (x : L2F ℝ Ω Ix)⟫_ℝ =
      ⟪smoothField hΩ hb (fun _ : Unit => φ) (fun _ => hφ.continuous), _⟫_ℝ
    rw [show (x : L2F ℝ Ω Ix) = testField hΨ from h1,
      real_inner_comm _ (smoothField hΩ hb (fun _ : Unit => φ) (fun _ => hφ.continuous)),
      inner_testField_divdiv_smoothField hΩ hb hΨ hφ]
    exact real_inner_comm _ _
  have hmem := (mem_hessCurlMax_d₀_domain_iff hΩ).2 ⟨H, key⟩
  exact ⟨hmem, congrArg Subtype.val (hessCurlMax_d₀_apply_eq hΩ ⟨_, hmem⟩ key)⟩

end Domains

/-! ## Lemma 3.5 for the complex (4.16) -/

section Lemma35

variable {Ω : Set R3}

/-- `⟪C, g I⟫ = ⟪tr C, g⟫`. -/
theorem inner_testField_diagOf (C : L2F ℝ Ω Ix) {g : R3 → ℝ} (hg : IsTest Ω g) :
    ⟪C, testField (isTestField_diagOf hg)⟫_ℝ = ⟪∑ i, C (i, i), toL2 hg⟫_ℝ := by
  rw [inner_testField_eq, sum_inner, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp only [diagOf, ite_true]
    exact integral_mul_eq_inner _ hg.memLp
  · intro j _ hj
    simp [diagOf, Ne.symm hj]
  · simp

/-- `⟪B, curl Φ⟫ = Σ ∫ B : curl Φ`. -/
theorem inner_testField_curl_eq (B : L2F ℝ Ω Ix) {Φ : Ix → R3 → ℝ} (hΦ : IsTestField Ω Φ) :
    ⟪B, testField ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply hΦ)⟫_ℝ =
      ∑ ij, ∫ x, B ij x * curlM Φ ij x ∂volume.restrict Ω := by
  rw [inner_testField_eq, curlM_eq_apply]

theorem isTestField_symF {Ψ : Ix → R3 → ℝ} (hΨ : IsTestField Ω Ψ) : IsTestField Ω (symF Ψ) :=
  fun ij => by
    have h := ((hΨ ij).add (hΨ (ij.2, ij.1))).const_mul (1 / 2 : ℝ)
    convert h using 1
    funext x
    simp only [symF, Pi.add_apply]
    ring

/-- `sym` of a test field is the test field of its symmetric part. -/
theorem symProj_testField {Ψ : Ix → R3 → ℝ} (hΨ : IsTestField Ω Ψ) :
    symProj (testField hΨ) = testField (isTestField_symF hΨ) := by
  obtain ⟨hΨ', e⟩ := matCLM_testField (Ω := Ω) (symMat 3) hΨ
  rw [symProj, e]
  refine testField_congr _ _ (funext fun ij => funext fun z => ?_)
  simp only [symMat, symF, add_div, add_mul, ite_div, zero_div, ite_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, one_div]
  ring

theorem isTestField_gradM {ψ : Fin 3 → R3 → ℝ} (hψ : IsTestField Ω ψ) :
    IsTestField Ω (gradM ψ) := fun ij => (hψ ij.1).fderiv_apply _

/-- **`L²(TSD) ⊆ ker (grad grad)† = H(div div, S, 0)`** for (4.16) (row-wise divergence-free
fields are `div div`-free). -/
theorem tsdS_le_ker (hΩ : IsOpen Ω) : tsdS Ω ≤ (hessCurl ℝ hΩ).d₀†.ker := fun B hB =>
  (mem_ker_adjoint_hessCurl_d₀_iff hΩ).2 fun φ hφ => by
    have hψ : IsTestField Ω fun i : Fin 3 => fun y => fderiv ℝ (φ ()) y (coordDir i) :=
      fun i => (hφ ()).fderiv_apply _
    have e : testField ((hessOp 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hφ) =
        testField ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hψ) :=
      testField_congr _ _ (funext fun ij => funext fun x => by rw [hessOp_apply, gradOp_apply])
    rw [e]
    exact hB.2.2 _ hψ

/-- The weak identity of `curl_min` against test fields: `⟪curl u, Φ⟫ = ⟪u, curl Φ⟫`. -/
theorem inner_minimal_curl_testField (hΩ : IsOpen Ω)
    (u : ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain) (Φ : Ix → R3 → ℝ)
    (hΦ : IsTestField Ω Φ) :
    ⟪(curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω u, testField hΦ⟫_ℝ =
      ⟪(u : L2F ℝ Ω Ix), testField ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply
          hΦ)⟫_ℝ := by
  have e := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).closure_testGraph_inner_testField
    ((curlOp 3).mem_closure_minimal hΩ u) hΦ
  rwa [testField_congr _ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply hΦ)
    (curlOp_formalAdj_apply Φ)] at e

/-- **The curl of a symmetric field in `H̊(curl)` is trace-free**: test against `Ψ = g I`, whose
curl is skew, so `∫ tr (curl u) g = ∫ u : curl (g I) = 0`. Part of [QuennevilleBelair2015],
Lemma 3.5 (§3.4). -/
theorem trace_minimal_curl_eq_zero (hΩ : IsOpen Ω)
    (u : ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain)
    (hu : ∀ i j, (u : L2F ℝ Ω Ix) (i, j) = (u : L2F ℝ Ω Ix) (j, i)) :
    ∑ i, ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω u : L2F ℝ Ω Ix) (i, i) = 0 := by
  refine L2.eq_zero_of_forall_inner_toL2 hΩ _ fun g hg => ?_
  rw [← inner_testField_diagOf _ hg, inner_minimal_curl_testField hΩ u _ (isTestField_diagOf hg),
    inner_testField_curl_eq _ (isTestField_diagOf hg)]
  simp only [curlM_diagOf]
  exact sum_integral_mul_skewOf_eq_zero hu _

/-- **Lemma 3.5 for `curl_min`**: `curl (L²(TSD) ∩ H̊(curl)) ⊆ L²(TSD)` (symmetric by
`curl_symm_of_mem_tsd`; trace-free as `curl (g I)` is skew, `trace_minimal_curl_eq_zero`;
divergence-free as `curl ∘ grad = 0`). [QuennevilleBelair2015], Lemma 3.5 (§3.4) -/
theorem minimal_curl_mem_tsd (hΩ : IsOpen Ω)
    (u : ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain) (hu : (u : L2F ℝ Ω Ix) ∈ tsd Ω) :
    (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω u ∈ tsd Ω := by
  have hid := inner_minimal_curl_testField hΩ u
  refine ⟨curl_symm_of_mem_tsd hΩ u hu, trace_minimal_curl_eq_zero hΩ u hu.1, fun φ hφ => ?_⟩
  rw [hid, testField_congr _ IsTestField.zero
    (isComplexPair_grad_curl φ fun i => (hφ i).contDiff), testField_zero, inner_zero_right]

/-- **`curl (H̊(curl, S) ∩ L²(TSD)) ⊆ L²(TSD)`** for (4.16) (Lemma 3.5, the thesis' third
itemized check in the proof of Prop 4.19). [QuennevilleBelair2015], Lemma 3.5, Prop. 4.19 -/
theorem hessCurl_d₁_mem_tsdT (hΩ : IsOpen Ω) (u : (hessCurl ℝ hΩ).d₁.domain)
    (hu : (u : symSub ℝ Ω) ∈ tsdS Ω) : (hessCurl ℝ hΩ).d₁ u ∈ tsdT Ω := by
  obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff _).1 (hessCurl_d₁_graph_map hΩ u)
  simp only at hz1 hz2
  have h := minimal_curl_mem_tsd hΩ z (by rw [hz1]; exact hu)
  rw [hz2] at h
  exact h

/-- The adjoint identity of (4.16) against symmetric test fields: `⟪d₁† ρ, Φ⟫ = ⟪ρ, curl Φ⟫`. -/
theorem adjoint_hessCurl_d₁_inner_testField (hΩ : IsOpen Ω) (ρ : (hessCurl ℝ hΩ).d₁†.domain)
    {Φ : Ix → R3 → ℝ} (hΦ : IsTestField Ω Φ) (hs : ∀ i j, Φ (i, j) = Φ (j, i)) :
    ⟪(((hessCurl ℝ hΩ).d₁† ρ : symSub ℝ Ω) : L2F ℝ Ω Ix), testField hΦ⟫_ℝ =
      ⟪((ρ : trSub ℝ Ω) : L2F ℝ Ω Ix),
        testField ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply hΦ)⟫_ℝ := by
  obtain ⟨y, hy⟩ := curl_mapsTo hΩ Φ hΦ ⟨_, testField_mem_symSub hΦ hs⟩ rfl
  have hp : ((⟨testField hΦ, testField_mem_symSub hΦ hs⟩ : symSub ℝ Ω), y) ∈
      (hessCurl ℝ hΩ).d₁.graph :=
    (curlOp 3).mem_graph_minimalVia _ _ (denseVia_trSub hΩ) ⟨Φ, hΦ, rfl, hy⟩
  have e := LinearPMap.adjoint_inner_of_mem_graph (hessCurl ℝ hΩ).dense₁ ρ hp
  simp only at e
  rw [Submodule.coe_inner, Submodule.coe_inner] at e
  rw [← hy]
  exact e

/-- **`curl† (H(sym curl, T) ∩ L²(TSD)) ⊆ L²(TSD)`** for (4.16) (Lemma 3.5): `d₁† ρ` is
symmetric, trace-free (`⟪d₁† ρ, g I⟫ = ⟪ρ, curl (g I)⟫ = 0`, `curl (g I)` skew) and
divergence-free (`⟪d₁† ρ, ∇ψ⟫ = ⟪ρ, curl sym ∇ψ⟫ = ½ ⟪ρ, (∇ curl ψ)ᵀ⟫ = 0`).
[QuennevilleBelair2015], Lemma 3.5, Prop. 4.19 -/
theorem adjoint_hessCurl_d₁_mem_tsdS (hΩ : IsOpen Ω) (ρ : (hessCurl ℝ hΩ).d₁†.domain)
    (hρ : (ρ : trSub ℝ Ω) ∈ tsdT Ω) : (hessCurl ℝ hΩ).d₁† ρ ∈ tsdS Ω := by
  have hDs : ∀ i j, (((hessCurl ℝ hΩ).d₁† ρ : symSub ℝ Ω) : L2F ℝ Ω Ix) (i, j) =
      (((hessCurl ℝ hΩ).d₁† ρ : symSub ℝ Ω) : L2F ℝ Ω Ix) (j, i) := ((hessCurl ℝ hΩ).d₁† ρ).2
  have hρt : ((ρ : trSub ℝ Ω) : L2F ℝ Ω Ix) ∈ tsd Ω := hρ
  have hρs := hρt.1
  show (((hessCurl ℝ hΩ).d₁† ρ : symSub ℝ Ω) : L2F ℝ Ω Ix) ∈ tsd Ω
  refine ⟨hDs, ?_, fun ψ hψ => ?_⟩
  · refine L2.eq_zero_of_forall_inner_toL2 hΩ _ fun g hg => ?_
    rw [← inner_testField_diagOf _ hg,
      adjoint_hessCurl_d₁_inner_testField hΩ ρ (isTestField_diagOf hg) (diagOf_swap g),
      inner_testField_curl_eq _ (isTestField_diagOf hg)]
    simp only [curlM_diagOf]
    exact sum_integral_mul_skewOf_eq_zero hρs _
  · have hG := isTestField_gradM hψ
    have hSG := isTestField_symF hG
    have e0 : testField ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hψ) =
        testField hG :=
      testField_congr _ _ (funext fun ij => funext fun x => by rw [gradOp_apply]; rfl)
    have hψ' : ∀ i, ContDiff ℝ ∞ (ψ i) := fun i => (hψ i).contDiff
    set w : Fin 3 → R3 → ℝ := fun b y => partialDeriv (b + 1) (ψ (b + 2)) y -
      partialDeriv (b + 2) (ψ (b + 1)) y
    have hw : IsTestField Ω w := fun b => ((hψ _).fderiv_apply _).sub ((hψ _).fderiv_apply _)
    have hdiv := hρt.2.2 w hw
    rw [inner_grad_testField _ hw] at hdiv
    rw [e0, ← inner_symProj_of_mem, symProj_testField hG,
      adjoint_hessCurl_d₁_inner_testField hΩ ρ hSG (symF_swap _), inner_testField_curl_eq _ hSG]
    simp only [curlM_symF_gradM hψ', mul_div_assoc', integral_div, ← Finset.sum_div]
    rw [div_eq_zero_iff]
    left
    rw [← hdiv]
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun jk => ?_
    obtain ⟨j, k⟩ := jk
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, w]
    rw [hρs j k]

/-- **Lemma 3.5 (symmetry part), weak form with no boundary condition**: if `B ∈ L²(TSD)` and
`C` satisfies `∫ C : Ψ = ∫ B : curl Ψ` for the trace-free test fields `Ψ = e_j × ψ`, then `C` is
symmetric. [QuennevilleBelair2015], Lemma 3.5 (§3.4) -/
theorem symm_of_weakCurl_tsd (hΩ : IsOpen Ω) {B C : L2F ℝ Ω Ix} (hB : B ∈ tsd Ω)
    (h : ∀ ψ : Fin 3 → R3 → ℝ, IsTestField Ω ψ →
      ∑ ij, ∫ x, C ij x * skewOf ψ ij x ∂volume.restrict Ω =
        ∑ ij, ∫ x, B ij x * curlM (skewOf ψ) ij x ∂volume.restrict Ω) (j k : Fin 3) :
    C (j, k) = C (k, j) := by
  have key : ∀ m : Fin 3, C (m + 2, m + 1) = C (m + 1, m + 2) := by
    intro m
    refine L2_ext_of_integral hΩ fun g hg => ?_
    let ψ : Fin 3 → R3 → ℝ := fun i => if i = m then g else 0
    have hψ : IsTestField Ω ψ := fun i => by
      by_cases hi : i = m
      · simpa [ψ, hi] using hg
      · simpa [ψ, hi] using (IsTest.zero : IsTest Ω (0 : R3 → ℝ))
    have e := h ψ hψ
    rw [sum_integral_mul_curlM_skewOf_eq_zero hB hψ] at e
    fin_cases m <;>
      simp [ψ, skewOf, Fintype.sum_prod_type, Fin.sum_univ_three, integral_neg] at e ⊢ <;>
      linarith
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  simp only [Fin.isValue, Fin.reduceAdd] at k0 k1 k2
  fin_cases j <;> fin_cases k <;> simp [k0, k1, k2]

end Lemma35

/-! ## What propagates for (4.16): Props 4.16 and 4.18 -/

section Propagation

variable {𝕜 : Type*} [RCLike 𝕜] {Ω : Set R3}

/-- **Prop 4.16 for the complex (4.16) on `Ω`** (unconditional): for data `(0, E₀, B₀) ∈ D(L)`
with `div div E₀ = 0` weakly (e.g. TSD data, `tsdS_le_ker`), the Hodge wave equation has a
classical solution on `[a, b]`, unique among strong solutions, and for all `t`: `σ(t) = 0` and
`div div E(t) = 0` weakly (`⟪E(t), ∇²φ⟫ = 0` for every test function `φ`). An instance of
`Feec.ShortHilbertComplex.reducingSubcomplex_divFreeSub`. [QuennevilleBelair2015], Prop. 4.16 -/
theorem hessCurl_divFree_propagates (hΩ : IsOpen Ω)
    {U₀ : PiLp 2 (ShortHilbertComplex.W3 (L2 𝕜 Ω) (symSub 𝕜 Ω) (trSub 𝕜 Ω))}
    (hU₀ : U₀ ∈ (hessCurl 𝕜 hΩ).wave.domain) (h0 : (U₀ 0 : L2 𝕜 Ω) = 0)
    (h1 : (U₀ 1 : symSub 𝕜 Ω) ∈ (hessCurl 𝕜 hΩ).d₀†.ker) (a b : ℝ) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution (hessCurl 𝕜 hΩ).wave (Icc a b) 0 U ∧
      (∀ t ∈ Icc a b, (U t 0 : L2 𝕜 Ω) = 0 ∧ ∀ (φ : Unit → R3 → 𝕜) (hφ : IsTestField Ω φ),
        ⟪Subtype.val (U t 1 : symSub 𝕜 Ω),
          testField ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ)⟫_𝕜 = 0) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution (hessCurl 𝕜 hΩ).wave (Icc a b) 0 V →
        EqOn V U (Icc a b) := by
  have hred := (hessCurl 𝕜 hΩ).reducingSubcomplex_divFreeSub ⊤ fun _ => Submodule.mem_top
  obtain ⟨U, hU0, hU, hK, huniq⟩ := hred.existsUnique_mem hU₀
    ((ShortHilbertComplex.mem_totalSub_divFreeSub _).2
      ⟨h0, h1, Submodule.mem_top (x := (U₀ 2 : trSub 𝕜 Ω))⟩)
    (Evolution.ForcingClass.admissible_zero _ a b) fun _ _ => Submodule.zero_mem _
  refine ⟨U, hU0, hU, fun t ht => ?_, huniq⟩
  obtain ⟨h0', h1', -⟩ := (ShortHilbertComplex.mem_totalSub_divFreeSub _).1 (hK t ht)
  exact ⟨h0', (mem_ker_adjoint_hessCurl_d₀_iff hΩ).1 h1'⟩

/-- **Prop 4.18 for the complex (4.16) on `Ω`** (unconditional): for `E₀ ∈ H̊(curl, S)` with
`div div E₀ = 0` and `B₀ ∈ H(sym curl, T)`, the reduced system `Ė = -sym curl B`, `Ḃ = curl E`
has a solution, unique among strong solutions, `div div E = 0` for all time, and `(0, E, B)`
solves the Hodge wave equation. An instance of
`Feec.ShortHilbertComplex.existsUnique_reducedSolution_divFree`.
[QuennevilleBelair2015], Prop. 4.18 -/
theorem hessCurl_existsUnique_reducedSolution (hΩ : IsOpen Ω) {E₀ : symSub 𝕜 Ω}
    {B₀ : trSub 𝕜 Ω} (hE₀ : E₀ ∈ (hessCurl 𝕜 hΩ).d₁.domain)
    (hE₀k : E₀ ∈ (hessCurl 𝕜 hΩ).d₀†.ker) (hB₀ : B₀ ∈ (hessCurl 𝕜 hΩ).d₁†.domain) (a b : ℝ) :
    ∃ E B, E a = E₀ ∧ B a = B₀ ∧ (hessCurl 𝕜 hΩ).IsReducedSolution (Icc a b) E B ∧
      (∀ t ∈ Icc a b, E t ∈ (hessCurl 𝕜 hΩ).d₀†.ker) ∧
      Evolution.IsStrongSolution (hessCurl 𝕜 hΩ).wave (Icc a b) 0
        (fun t => ShortHilbertComplex.mk3 0 (E t) (B t)) ∧
      ∀ E' B', E' a = E₀ → B' a = B₀ → (hessCurl 𝕜 hΩ).IsReducedSolution (Icc a b) E' B' →
        EqOn E' E (Icc a b) ∧ EqOn B' B (Icc a b) :=
  (hessCurl 𝕜 hΩ).existsUnique_reducedSolution_divFree hE₀ hE₀k hB₀ a b

end Propagation

end Feec.Models.BoundedDomain
