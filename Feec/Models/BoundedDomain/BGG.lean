module

public import Feec.Models.BoundedDomain.Hessian

/-!
# The BGG weak-symmetry complex (5.1) on a bounded domain

The complex (5.1) of the weakly symmetric formulation of [QuennevilleBelair2015], Ch. 6 on an open
`Ω ⊆ ℝ³` with the boundary conditions of §6.3,
`L²(Ω) ⊇ H̊²(Ω) --grad grad--> H̊(curl, Ω; 𝕜³ˣ³) --(S₁, curl)--> L²(Ω; 𝕜³) × L²(Ω; 𝕜³ˣ³)`.

## Main results

* `mem_bggComplex_d₁_graph_iff`: `D(d₁) = H̊(curl, M)` and `d₁ u = (S₁ u, curl u)`.
* `bggComplex_divFree_propagates`: `σ ≡ 0` and `div div u ≡ 0` propagate.
* `bggComplex_weakEqs_of_isStrongSolution`: strong solutions solve the weak system (6.1).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ContDiff ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology Feec.Domain

namespace Feec.Models.BoundedDomain

variable {𝕜 : Type*} [RCLike 𝕜] {Ω : Set R3}

variable (𝕜 Ω) in
/-- The top space `L²(Ω; 𝕜³) × L²(Ω; 𝕜³ˣ³)` of (5.1). -/
abbrev W2B := WithLp 2 (L2F 𝕜 Ω (Fin 3) × L2F 𝕜 Ω Ix)

variable (𝕜 Ω) in
/-- The BGG map `S₁ = 2 vskw`, `(S₁ u)ᵢ = u_{i+1,i+2} - u_{i+2,i+1}`. -/
def skwL : L2F 𝕜 Ω Ix →L[𝕜] L2F 𝕜 Ω (Fin 3) :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : Fin 3 => L2 𝕜 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      PiLp.proj (𝕜 := 𝕜) 2 (fun _ : Ix => L2 𝕜 Ω) (i + 1, i + 2) -
        PiLp.proj (𝕜 := 𝕜) 2 (fun _ : Ix => L2 𝕜 Ω) (i + 2, i + 1))

theorem skwL_apply (u : L2F 𝕜 Ω Ix) (i : Fin 3) :
    skwL 𝕜 Ω u i = u (i + 1, i + 2) - u (i + 2, i + 1) := rfl

theorem skwL_eq_zero_of_mem_symSub {u : L2F 𝕜 Ω Ix} (hu : u ∈ symSub 𝕜 Ω) : skwL 𝕜 Ω u = 0 :=
  (WithLp.ext_iff 2).2 (funext fun i => by rw [skwL_apply, hu (i + 1) (i + 2), sub_self]; rfl)

variable (𝕜 Ω) in
/-- The isometry `L²(Ω; 𝕜³) × L²(Ω; 𝕜³ˣ³) ≃ L²(Ω; 𝕜^{3 ⊕ 3×3})`. -/
def bggJ : W2B 𝕜 Ω →ₗᵢ[𝕜] L2F 𝕜 Ω (Fin 3 ⊕ Ix) :=
  (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := 𝕜) 2 fun _ : Fin 3 ⊕ Ix => L2 𝕜 Ω).symm.toLinearIsometry

@[simp] theorem bggJ_inl (w : W2B 𝕜 Ω) (i : Fin 3) :
    bggJ 𝕜 Ω w (.inl i) = (WithLp.ofLp w).1 i := rfl

@[simp] theorem bggJ_inr (w : W2B 𝕜 Ω) (ik : Ix) :
    bggJ 𝕜 Ω w (.inr ik) = (WithLp.ofLp w).2 ik := rfl

theorem bggJ_surjective : Function.Surjective (bggJ 𝕜 Ω) :=
  (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := 𝕜) 2 fun _ : Fin 3 ⊕ Ix => L2 𝕜 Ω).symm.surjective

theorem denseVia_bggJ (hΩ : IsOpen Ω) : ConstCoeffOp.DenseVia (bggJ 𝕜 Ω) :=
  ConstCoeffOp.denseVia_of_surjective hΩ _ bggJ_surjective

theorem toL2_sub {f g : R3 → 𝕜} (hf : IsTest Ω f) (hg : IsTest Ω g) :
    toL2 (hf.sub hg) = toL2 hf - toL2 hg := by
  refine Lp.ext ?_
  filter_upwards [coeFn_toL2 (hf.sub hg), coeFn_toL2 hf, coeFn_toL2 hg,
    Lp.coeFn_sub (toL2 hf) (toL2 hg)] with x h1 h2 h3 h4
  rw [h1, h4, Pi.sub_apply, Pi.sub_apply, h2, h3]

theorem bggJ_testField {φ : Ix → R3 → 𝕜} (hφ : IsTestField Ω φ) :
    bggJ 𝕜 Ω (WithLp.toLp 2 (skwL 𝕜 Ω (testField hφ),
      testField ((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).isTestField_apply hφ))) =
      testField ((skwCurlOp : ConstCoeffOp R3 𝕜 Ix (Fin 3 ⊕ Ix)).isTestField_apply hφ) := by
  refine (WithLp.ext_iff 2).2 (funext fun j => ?_)
  rcases j with i | ik
  · change skwL 𝕜 Ω (testField hφ) i = _
    rw [skwL_apply, testField_apply, testField_apply, testField_apply, ← toL2_sub]
    exact toL2_congr _ _ (funext fun x => (skwCurlOp_apply_inl φ i x).symm)
  · rfl

theorem skwCurl_mapsTo (φ : Ix → R3 → 𝕜) (hφ : IsTestField Ω φ) (x : L2F 𝕜 Ω Ix)
    (_ : (LinearIsometry.id : L2F 𝕜 Ω Ix →ₗᵢ[𝕜] L2F 𝕜 Ω Ix) x = testField hφ) : ∃ y : W2B 𝕜 Ω,
        bggJ 𝕜 Ω y =
      testField ((skwCurlOp : ConstCoeffOp R3 𝕜 Ix (Fin 3 ⊕ Ix)).isTestField_apply hφ) :=
  ⟨_, bggJ_testField hφ⟩

variable (𝕜) in
/-- The complex (5.1) with the boundary conditions of [QuennevilleBelair2015], §6.3. -/
def bggComplex (hΩ : IsOpen Ω) : ShortHilbertComplex 𝕜 (L2 𝕜 Ω) (L2F 𝕜 Ω Ix) (W2B 𝕜 Ω) where
  d₀ := hessMin 𝕜 hΩ
  d₁ := skwCurlOp.minimalVia LinearIsometry.id (bggJ 𝕜 Ω)
  dense₀ := dense_hessMin_domain hΩ
  dense₁ := skwCurlOp.dense_minimalVia_domain_of _ _ (denseVia_bggJ hΩ) (denseVia_id hΩ)
    skwCurl_mapsTo
  closed₀ := isClosed_hessMin hΩ
  closed₁ := skwCurlOp.isClosed_minimalVia _ _ (denseVia_bggJ hΩ)
  mapsTo := ConstCoeffOp.minimalVia_mapsTo _ _ _ _ isComplexPair_hess_skwCurl (denseVia_id hΩ)
    (denseVia_bggJ hΩ)
  comp := ConstCoeffOp.minimalVia_comp _ _ _ _ isComplexPair_hess_skwCurl (denseVia_id hΩ)
    (denseVia_bggJ hΩ)

@[simp] theorem bggComplex_d₀ (hΩ : IsOpen Ω) : (bggComplex 𝕜 hΩ).d₀ = hessMin 𝕜 hΩ := rfl

/-- `(u, w)` lies in the graph of `d₁` iff `(u, w₂)` lies in the graph of `curl_min` and
`w₁ = S₁ u`. -/
theorem mem_bggComplex_d₁_graph_iff (hΩ : IsOpen Ω) {u : L2F 𝕜 Ω Ix} {w : W2B 𝕜 Ω} :
    (u, w) ∈ (bggComplex 𝕜 hΩ).d₁.graph ↔
      (u, (WithLp.ofLp w).2) ∈ ((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).minimal Ω).graph ∧
        (WithLp.ofLp w).1 = skwL 𝕜 Ω u := by
  have hG : (bggComplex 𝕜 hΩ).d₁.graph =
      ((skwCurlOp : ConstCoeffOp R3 𝕜 Ix (Fin 3 ⊕ Ix)).testGraphVia LinearIsometry.id
        (bggJ 𝕜 Ω)).topologicalClosure :=
    skwCurlOp.minimalVia_graph _ _ (denseVia_bggJ hΩ)
  have hc : (((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).minimal Ω).graph : Set (L2F 𝕜 Ω Ix × L2F 𝕜 Ω
      Ix)) =
      closure ((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).testGraph Ω : Set _) := by
    rw [(curlOp 3).minimal_graph hΩ, Submodule.topologicalClosure_coe]
  let e := WithLp.prodContinuousLinearEquiv 2 𝕜 (L2F 𝕜 Ω (Fin 3)) (L2F 𝕜 Ω Ix)
  have he : ∀ w : W2B 𝕜 Ω, e w = WithLp.ofLp w := fun _ => rfl
  constructor
  · intro h
    rw [← SetLike.mem_coe, hG, Submodule.topologicalClosure_coe] at h
    let S : Set (L2F 𝕜 Ω Ix × W2B 𝕜 Ω) := {p |
      (p.1, (WithLp.ofLp p.2).2) ∈ ((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).minimal Ω).graph ∧
        (WithLp.ofLp p.2).1 = skwL 𝕜 Ω p.1}
    have hS : IsClosed S :=
      ((curlOp 3).isClosed_minimal hΩ |>.preimage
        (continuous_fst.prodMk (continuous_snd.comp (e.continuous.comp continuous_snd)))).inter
      (isClosed_eq (continuous_fst.comp (e.continuous.comp continuous_snd))
        ((skwL 𝕜 Ω).continuous.comp continuous_fst))
    have hsub : ((skwCurlOp : ConstCoeffOp R3 𝕜 Ix (Fin 3 ⊕ Ix)).testGraphVia LinearIsometry.id
        (bggJ 𝕜 Ω) : Set (L2F 𝕜 Ω Ix × W2B 𝕜 Ω)) ⊆ S := by
      rintro ⟨x, y⟩ ⟨φ, hφ, h1, h2⟩
      simp only at h1 h2
      have hy : y = WithLp.toLp 2 (skwL 𝕜 Ω (testField hφ),
          testField ((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).isTestField_apply hφ)) :=
        (bggJ 𝕜 Ω).injective (h2.trans (bggJ_testField hφ).symm)
      have hx : x = testField hφ := h1
      subst hx hy
      exact ⟨(curlOp 3).testField_mem_graph_minimal hΩ hφ, rfl⟩
    exact closure_minimal hsub hS h
  · rintro ⟨h1, h2⟩
    let S : Set (L2F 𝕜 Ω Ix × L2F 𝕜 Ω Ix) := {p |
      (p.1, WithLp.toLp 2 (skwL 𝕜 Ω p.1, p.2)) ∈ (bggComplex 𝕜 hΩ).d₁.graph}
    have hS : IsClosed S :=
      ((bggComplex 𝕜 hΩ).closed₁).preimage (continuous_fst.prodMk
        (e.symm.continuous.comp (((skwL 𝕜 Ω).continuous.comp continuous_fst).prodMk
          continuous_snd)))
    have hsub : ((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).testGraph Ω :
        Set (L2F 𝕜 Ω Ix × L2F 𝕜 Ω Ix)) ⊆ S := by
      rintro _ ⟨φ, hφ, rfl⟩
      exact skwCurlOp.mem_graph_minimalVia _ _ (denseVia_bggJ hΩ)
        ⟨φ, hφ, rfl, bggJ_testField hφ⟩
    have hm : (u, (WithLp.ofLp w).2) ∈ S := by
      rw [← SetLike.mem_coe, hc] at h1
      exact closure_minimal hsub hS h1
    have hw : w = WithLp.toLp 2 (skwL 𝕜 Ω u, (WithLp.ofLp w).2) := by
      rw [← h2]
    rw [hw]
    exact hm

theorem bggComplex_d₁_apply (hΩ : IsOpen Ω) (u : (bggComplex 𝕜 hΩ).d₁.domain) :
    ((u : L2F 𝕜 Ω Ix), (WithLp.ofLp ((bggComplex 𝕜 hΩ).d₁ u)).2) ∈
        ((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).minimal Ω).graph ∧
      (WithLp.ofLp ((bggComplex 𝕜 hΩ).d₁ u)).1 = skwL 𝕜 Ω u :=
  (mem_bggComplex_d₁_graph_iff hΩ).1 ((bggComplex 𝕜 hΩ).d₁.mem_graph u)

theorem bggComplex_d₁_domain (hΩ : IsOpen Ω) :
    (bggComplex 𝕜 hΩ).d₁.domain = ((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).minimal Ω).domain := by
  ext u
  constructor
  · intro hu
    exact LinearPMap.mem_domain_of_mem_graph (bggComplex_d₁_apply hΩ ⟨u, hu⟩).1
  · intro hu
    exact LinearPMap.mem_domain_of_mem_graph ((mem_bggComplex_d₁_graph_iff hΩ
      (w := WithLp.toLp 2 (skwL 𝕜 Ω u, (curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).minimal Ω ⟨u, hu⟩))).2
        ⟨((curlOp 3).minimal Ω).mem_graph ⟨u, hu⟩, rfl⟩)

theorem bggComplex_d₁_snd (hΩ : IsOpen Ω) (u : (bggComplex 𝕜 hΩ).d₁.domain) :
    (WithLp.ofLp ((bggComplex 𝕜 hΩ).d₁ u)).2 =
      (curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).minimal Ω ⟨u, (bggComplex_d₁_domain (𝕜 := 𝕜) hΩ)
          ▸ u.2⟩ := by
  obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff _).1 (bggComplex_d₁_apply hΩ u).1
  rw [← hz2]
  congr 1
  exact Subtype.ext hz1

theorem mem_ker_adjoint_bggComplex_d₀_iff (hΩ : IsOpen Ω) {B : L2F 𝕜 Ω Ix} :
    B ∈ (bggComplex 𝕜 hΩ).d₀†.ker ↔ ∀ (φ : Unit → R3 → 𝕜) (hφ : IsTestField Ω φ),
      ⟪B, testField ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ)⟫_𝕜 = 0 :=
  mem_ker_divdivMax_iff hΩ

theorem tsd_le_ker_bgg (hΩ : IsOpen Ω) : tsd Ω ≤ (bggComplex ℝ hΩ).d₀†.ker := fun B hB =>
  (mem_ker_adjoint_bggComplex_d₀_iff hΩ).2 fun φ hφ => by
    have hψ : IsTestField Ω fun i : Fin 3 => fun y => fderiv ℝ (φ ()) y (coordDir i) :=
      fun i => (hφ ()).fderiv_apply _
    have e : testField ((hessOp 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hφ) =
        testField ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hψ) :=
      testField_congr _ _ (funext fun ij => funext fun x => by rw [hessOp_apply, gradOp_apply])
    rw [e]
    exact hB.2.2 _ hψ

theorem smoothPair_mem_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {W₀ : Type*}
    [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (W2B ℝ Ω)) (hd₁ : S.d₁ ≤ (bggComplex ℝ hΩ).d₁)
    (m : L2F ℝ Ω (Fin 3)) {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) :
    ∃ h : WithLp.toLp 2 (m, smoothField hΩ hb Ψ fun ij => (hΨ ij).continuous) ∈ S.d₁†.domain,
      S.d₁† ⟨_, h⟩ = ContinuousLinearMap.adjoint (skwL ℝ Ω) m +
        smoothField hΩ hb (curlM Ψ) (continuous_curlM hΨ) := by
  have key : ∀ u : S.d₁.domain,
      ⟪ContinuousLinearMap.adjoint (skwL ℝ Ω) m + smoothField hΩ hb (curlM Ψ) (continuous_curlM hΨ),
        (u : L2F ℝ Ω Ix)⟫_ℝ =
        ⟪WithLp.toLp 2 (m, smoothField hΩ hb Ψ fun ij => (hΨ ij).continuous), S.d₁ u⟫_ℝ := by
    intro u
    have hu : S.d₁ u = (bggComplex ℝ hΩ).d₁ ⟨u, hd₁.1 u.2⟩ := hd₁.2 rfl
    obtain ⟨hc, hs⟩ := bggComplex_d₁_apply hΩ ⟨u, hd₁.1 u.2⟩
    obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff _).1 hc
    simp only at hz1 hz2
    have e := minimal_curl_identity hΩ hb z hΨ
    rw [hz2, hz1] at e
    rw [hu, WithLp.prod_inner_apply, inner_add_left, ContinuousLinearMap.adjoint_inner_left, hs]
    congr 1
    rw [real_inner_comm, inner_smoothField, WithLp.ofLp_toLp, real_inner_comm, inner_smoothField]
    exact e.symm
  have hmem := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq S.dense₁ ⟨_, hmem⟩ key⟩

/-- For `(0, E₀, ρ₀) ∈ D(L)` with `div div E₀ = 0`, the Hodge wave equation of (5.1) has a unique
classical solution, with `σ ≡ 0`, `div div u ≡ 0`. [QuennevilleBelair2015], Prop 4.16 (adapted) -/
theorem bggComplex_divFree_propagates (hΩ : IsOpen Ω)
    {U₀ : PiLp 2 (ShortHilbertComplex.W3 (L2 𝕜 Ω) (L2F 𝕜 Ω Ix) (W2B 𝕜 Ω))}
    (hU₀ : U₀ ∈ (bggComplex 𝕜 hΩ).wave.domain) (h0 : (U₀ 0 : L2 𝕜 Ω) = 0)
    (h1 : (U₀ 1 : L2F 𝕜 Ω Ix) ∈ (bggComplex 𝕜 hΩ).d₀†.ker) (a b : ℝ) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution (bggComplex 𝕜 hΩ).wave (Icc a b) 0 U ∧
      (∀ t ∈ Icc a b, (U t 0 : L2 𝕜 Ω) = 0 ∧ ∀ (φ : Unit → R3 → 𝕜) (hφ : IsTestField Ω φ),
        ⟪(U t 1 : L2F 𝕜 Ω Ix),
          testField ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ)⟫_𝕜 = 0) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution (bggComplex 𝕜 hΩ).wave (Icc a b) 0 V →
        EqOn V U (Icc a b) := by
  have hred := (bggComplex 𝕜 hΩ).reducingSubcomplex_divFreeSub ⊤ fun _ => Submodule.mem_top
  obtain ⟨U, hU0, hU, hK, huniq⟩ := hred.existsUnique_mem hU₀
    ((ShortHilbertComplex.mem_totalSub_divFreeSub _).2
      ⟨h0, h1, Submodule.mem_top (x := (U₀ 2 : W2B 𝕜 Ω))⟩)
    (Evolution.ForcingClass.admissible_zero _ a b) fun _ _ => Submodule.zero_mem _
  refine ⟨U, hU0, hU, fun t ht => ?_, huniq⟩
  obtain ⟨h0', h1', -⟩ := (ShortHilbertComplex.mem_totalSub_divFreeSub _).1 (hK t ht)
  exact ⟨h0', (mem_ker_adjoint_bggComplex_d₀_iff hΩ).1 h1'⟩

section Weak

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- A strong solution of the Hodge wave equation of (5.1) solves the weak system (6.1) with `f = 0`.
[QuennevilleBelair2015], (6.1) (adapted) -/
theorem bggComplex_weakEqs_of_isStrongSolution (hΩ : IsOpen Ω) {I : Set ℝ}
    {U : ℝ → PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ Ω) (L2F ℝ Ω Ix) (W2B ℝ Ω))}
    (hU : Evolution.IsStrongSolution (bggComplex ℝ hΩ).wave I 0 U) {t : ℝ} (ht : t ∈ I) :
    ∃ (hσ : (U t 0 : L2 ℝ Ω) ∈ (hessMin ℝ hΩ).domain)
      (hu : (U t 1 : L2F ℝ Ω Ix) ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain)
      (σ' : L2 ℝ Ω) (u' : L2F ℝ Ω Ix) (ρ' : W2B ℝ Ω),
      HasDerivWithinAt U (ShortHilbertComplex.mk3 σ' u' ρ') I t ∧
      (∀ τ : (hessMin ℝ hΩ).domain,
        ⟪σ', (τ : L2 ℝ Ω)⟫_ℝ + ⟪(U t 1 : L2F ℝ Ω Ix), hessMin ℝ hΩ τ⟫_ℝ = 0) ∧
      (∀ v : ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain,
        ⟪u', (v : L2F ℝ Ω Ix)⟫_ℝ - ⟪hessMin ℝ hΩ ⟨_, hσ⟩, (v : L2F ℝ Ω Ix)⟫_ℝ +
          ⟪(WithLp.ofLp (U t 2 : W2B ℝ Ω)).1, skwL ℝ Ω v⟫_ℝ +
          ⟪(WithLp.ofLp (U t 2 : W2B ℝ Ω)).2, (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω v⟫_ℝ =
          0) ∧
      (WithLp.ofLp ρ').1 = skwL ℝ Ω (U t 1 : L2F ℝ Ω Ix) ∧
      (WithLp.ofLp ρ').2 = (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω ⟨_, hu⟩ := by
  obtain ⟨hσ, hu, σ', u', ρ', hd, ha, hb', hc⟩ :=
    (bggComplex ℝ hΩ).weakEqs_of_isStrongSolution hU ht
  have hu' : (U t 1 : L2F ℝ Ω Ix) ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain := by
    rw [← bggComplex_d₁_domain hΩ]; exact hu
  refine ⟨hσ, hu', σ', u', ρ', hd, fun τ => ?_, fun v => ?_, ?_, ?_⟩
  · have h : ⟪σ', (τ : L2 ℝ Ω)⟫_ℝ = -⟪(U t 1 : L2F ℝ Ω Ix), hessMin ℝ hΩ τ⟫_ℝ := ha τ
    rw [h, neg_add_cancel]
  · have hv : (v : L2F ℝ Ω Ix) ∈ (bggComplex ℝ hΩ).d₁.domain := by
      rw [bggComplex_d₁_domain hΩ]; exact v.2
    have h : ⟪u', (v : L2F ℝ Ω Ix)⟫_ℝ - ⟪hessMin ℝ hΩ ⟨_, hσ⟩, (v : L2F ℝ Ω Ix)⟫_ℝ +
        (⟪(WithLp.ofLp (U t 2 : W2B ℝ Ω)).1, (WithLp.ofLp ((bggComplex ℝ hΩ).d₁ ⟨_, hv⟩)).1⟫_ℝ +
          ⟪(WithLp.ofLp (U t 2 : W2B ℝ Ω)).2,
            (WithLp.ofLp ((bggComplex ℝ hΩ).d₁ ⟨_, hv⟩)).2⟫_ℝ) = 0 := hb' ⟨_, hv⟩
    rw [(bggComplex_d₁_apply hΩ ⟨_, hv⟩).2, bggComplex_d₁_snd hΩ ⟨_, hv⟩] at h
    linear_combination h
  · rw [hc]; exact (bggComplex_d₁_apply hΩ ⟨_, hu⟩).2
  · rw [hc, bggComplex_d₁_snd hΩ ⟨_, hu⟩]

end Weak

end Feec.Models.BoundedDomain
