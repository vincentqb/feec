module

public import Feec.Counterexamples.BoundedDomainTSD
public import Feec.Models.BoundedDomain.SymCurl
public import Feec.Models.BoundedDomain.InvariantCore

/-!
# Bounded domains: TSD constraints for the Hessian–curl complex (thesis Prop 4.19 refuted)

On an open `Ω ⊆ ℝ³` the thesis' complex (4.16) for Prop 4.19 is the Hessian–curl complex
`H̊²(Ω) --grad grad--> H̊(curl, Ω; S) --curl--> L²(Ω; T)` (`Feec.Models.BoundedDomain.hessCurl`),
with constraint spaces `L²(TSD) ∩ L²(S)` and `L²(TSD) ∩ L²(T)`
(`Feec.Models.BoundedDomain.tsdS`, `tsdT`). Since `H̊(curl, S) ⊆ H̊(curl)` with the same curl,
the zero-mean theorem applies, and on every nonempty bounded open `Ω` the projection hypothesis
(`exists_projTSD_not_mem_domain`, `not_isReducing_tsd`) and the density hypothesis
(`not_dense_tsdS_inter`) of Prop 4.19 fail, and TSD data do **not**
propagate for any short complex with `d₁ ⊆ curl` on `H̊(curl, S)` (`tsd_not_propagates`), from
the same datum `(0, 0, β)` as for the grad–curl complex (`Feec.Counterexamples.BoundedDomainTSD`).

The obstruction is quantified: a datum that propagates for every such complex must have its
electric field in `L²(TSD₀)` (`mem_tsd₀_of_propagates`), the invariant core
`K* = {0} × S₁* × S₂*` of `K = {0} × tsdS × tsdT` has `S₁* ⊆ L²(TSD₀)` and an infinite-dimensional
`S₂*` (`invariantCore_tsd`, `not_finiteDimensional_obstruction`), and `diagnosis` records which
hypotheses of Prop. 4.19 fail.

For the complex with the maximal boundary conditions (`Feec.Models.BoundedDomain.hessCurlMax`,
`H²(Ω) → H(curl, S) → L²(T)`) the same hypotheses fail (`not_dense_hessCurlMax`,
`not_starProjection_mem_wave_domain_hessCurlMax`, `not_isReducing_tsd_hessCurlMax`), although the
divergence-free constraint propagates (`hessCurlMax_divFree_propagates`) and `curl` maps TSD fields
to TSD fields (`hessCurlMax_d₁_mem_tsdT`); `tsdS ⊄ ker (grad grad)†` here, so the constraint
space is `tsdSKer = tsdS ∩ ker (grad grad)†`, and the invariant core of
`K = {0} × tsdSKer × tsdT` is computed in `invariantCore_tsdSKer` (`diagnosis_hessCurlMax`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10–4.11 (Prop. 4.16, Prop. 4.17, Prop. 4.19, complex (4.16))
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], §8 (Hessian and div-div complexes)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ContDiff Matrix ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology Feec.Domain Feec.Models.BoundedDomain

namespace Feec.Counterexamples.BoundedSymTSD

variable {Ω : Set R3}

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-! ### The projection and density hypotheses of Prop 4.19 -/

theorem diagA_symm (i j : Fin 3) : BoundedDomainTSD.diagA i j = BoundedDomainTSD.diagA j i := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The constant field `diag(1, -1, 0)` as an element of `L²(TSD) ∩ L²(S)`. -/
def constS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : symSub ℝ Ω :=
  ⟨_, (BoundedDomainTSD.constField_mem_tsd hΩ hb BoundedDomainTSD.diagA_transpose
    BoundedDomainTSD.diagA_trace).1⟩

theorem constS_mem_tsdS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : constS hΩ hb ∈ tsdS Ω :=
  BoundedDomainTSD.constField_mem_tsd hΩ hb BoundedDomainTSD.diagA_transpose
    BoundedDomainTSD.diagA_trace

/-- Fields of `L²(TSD) ∩ H̊(curl, S)` are orthogonal to `diag(1, -1, 0)`. -/
theorem inner_constS_eq_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {z : symSub ℝ Ω}
    (hzK : z ∈ tsdS Ω) (hzD : z ∈ (hessCurl ℝ hΩ).d₁.domain) : ⟪z, constS hΩ hb⟫_ℝ = 0 := by
  have hzM := hessCurl_d₁_graph_map hΩ ⟨z, hzD⟩
  rw [Submodule.coe_inner]
  exact BoundedDomainTSD.inner_constField_eq_zero hΩ hb BoundedDomainTSD.diagA
    ⟨hzK, LinearPMap.mem_domain_of_mem_graph hzM⟩

/-- **The projection hypothesis of Prop 4.19 fails** on every nonempty bounded open `Ω`: for the
symmetric test field `Φ = g · diag(1, -1, 0)` (any bump `g ≥ 0`, `g ≠ 0`), the projection of `Φ`
onto `L²(TSD) ∩ L²(S)` is not in `H̊(curl, S)`. [QuennevilleBelair2015], Prop 4.19 -/
theorem exists_projTSD_not_mem_domain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : ∃ (Φ : Ix → R3 → ℝ) (hΦ : IsTestField Ω Φ)
      (hs : ∀ i j, Φ (i, j) = Φ (j, i)),
      (tsdS Ω).starProjection ⟨testField hΦ, testField_mem_symSub hΦ hs⟩ ∉
        (hessCurl ℝ hΩ).d₁.domain := by
  obtain ⟨g, hg, hgpos⟩ := BoundedDomainTSD.exists_isTest_integral_pos hΩ hne
  let Φ : Ix → R3 → ℝ := fun ij x => BoundedDomainTSD.diagA ij.1 ij.2 * g x
  have hΦ : IsTestField Ω Φ := fun ij => hg.const_mul (BoundedDomainTSD.diagA ij.1 ij.2)
  have hs : ∀ i j, Φ (i, j) = Φ (j, i) := fun i j => by
    funext x; simp only [Φ, diagA_symm i j]
  refine ⟨Φ, hΦ, hs, fun hP => ?_⟩
  set Φs : symSub ℝ Ω := ⟨testField hΦ, testField_mem_symSub hΦ hs⟩
  have h1 : ⟪(tsdS Ω).starProjection Φs, constS hΩ hb⟫_ℝ = ⟪Φs, constS hΩ hb⟫_ℝ := by
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (constS_mem_tsdS hΩ hb)]
  have h2 := inner_constS_eq_zero hΩ hb (Submodule.starProjection_apply_mem _ _) hP
  have hI : ∀ ij : Ix, ∫ x, testField hΦ ij x ∂volume.restrict Ω =
      BoundedDomainTSD.diagA ij.1 ij.2 * ∫ x, g x ∂volume.restrict Ω := fun ij => by
    rw [← integral_const_mul]
    exact integral_congr_ae (coeFn_testField hΦ ij)
  rw [h1, Submodule.coe_inner] at h2
  change ⟪testField hΦ, BoundedDomainTSD.constField hΩ hb BoundedDomainTSD.diagA⟫_ℝ = 0 at h2
  rw [BoundedDomainTSD.inner_constField] at h2
  simp only [hI, Fintype.sum_prod_type, Fin.sum_univ_three] at h2
  simp [BoundedDomainTSD.diagA] at h2
  linarith

/-- **`L²(TSD) ∩ H̊(curl, S)` is not dense in `L²(TSD) ∩ L²(S)`** (the density hypothesis of
Prop 4.19 fails): `diag(1, -1, 0)` is orthogonal to it. [QuennevilleBelair2015], Prop 4.19 -/
theorem not_dense_tsdS_inter (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    constS hΩ hb ∈ tsdS Ω ∧ constS hΩ hb ∉
      closure ((tsdS Ω : Set (symSub ℝ Ω)) ∩ (hessCurl ℝ hΩ).d₁.domain) := by
  refine ⟨constS_mem_tsdS hΩ hb, fun hcl => ?_⟩
  have hsub : (tsdS Ω : Set (symSub ℝ Ω)) ∩ (hessCurl ℝ hΩ).d₁.domain ⊆
      (fun z => ⟪z, constS hΩ hb⟫_ℝ) ⁻¹' {0} := fun z ⟨hK, hD⟩ => inner_constS_eq_zero hΩ hb hK hD
  have h0 := closure_minimal hsub (isClosed_singleton.preimage
    (continuous_id.inner continuous_const)) hcl
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at h0
  have h0' : ((constS hΩ hb : symSub ℝ Ω) : L2F ℝ Ω Ix) = 0 := by
    rw [inner_self_eq_zero.1 h0]; rfl
  exact BoundedDomainTSD.constField_diagA_ne_zero hΩ hb hne h0'

/-- **`K = {0} × (L²(TSD) ∩ L²(S)) × S₂` does not reduce the wave operator** (the projection
hypothesis `P_K D(L) ⊆ D(L)` of Prop 4.19 fails) for every short complex
`W₀ → L²(S) → W₂` with `D(d₁) ⊆ H̊(curl, S)` containing the symmetric test fields in
`D(d₁) ∩ D(d₀†)`, on every nonempty bounded open `Ω`. [QuennevilleBelair2015], Prop 4.19 -/
theorem not_isReducing_tsd (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {W₀ W₂ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [CompleteSpace W₂]
    (S : ShortHilbertComplex ℝ W₀ (symSub ℝ Ω) W₂) (S₂ : Submodule ℝ W₂)
    [S₂.HasOrthogonalProjection] (hd₁ : S.d₁.domain ≤ (hessCurl ℝ hΩ).d₁.domain)
    (htest : ∀ (Φ : Ix → R3 → ℝ) (hΦ : IsTestField Ω Φ) (hs : ∀ i j, Φ (i, j) = Φ (j, i)),
      (⟨testField hΦ, testField_mem_symSub hΦ hs⟩ : symSub ℝ Ω) ∈ S.d₁.domain ∧
        (⟨testField hΦ, testField_mem_symSub hΦ hs⟩ : symSub ℝ Ω) ∈ S.d₀†.domain) :
    ¬ S.wave.IsReducing
      (HilbertComplex.totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsdS Ω) S₂)) := by
  intro hred
  obtain ⟨Φ, hΦ, hs, hnot⟩ := exists_projTSD_not_mem_domain hΩ hb hne
  let x : PiLp 2 (ShortHilbertComplex.W3 W₀ (symSub ℝ Ω) W₂) :=
    WithLp.toLp 2 (Pi.single (M := ShortHilbertComplex.W3 W₀ (symSub ℝ Ω) W₂) 1
      (⟨testField hΦ, testField_mem_symSub hΦ hs⟩ : symSub ℝ Ω))
  have hx0 : (x 0 : W₀) = 0 := rfl
  have hx1 : (x 1 : symSub ℝ Ω) = ⟨testField hΦ, testField_mem_symSub hΦ hs⟩ := rfl
  have hx2 : (x 2 : W₂) = 0 := rfl
  have hxD : x ∈ S.wave.domain := by
    rw [S.mem_wave_domain, hx0, hx1, hx2]
    exact ⟨Submodule.zero_mem _, (htest Φ hΦ hs).1, (htest Φ hΦ hs).2, Submodule.zero_mem _⟩
  have hP := hred.proj_mem ⟨x, hxD⟩
  rw [S.mem_wave_domain] at hP
  have h1 := hP.2.1
  rw [HilbertComplex.totalSub_starProjection_apply] at h1
  exact hnot (hd₁ h1)

/-- `⟪-diag(1, -1, 0), Φ⟫ = ⟪β, curl Φ⟫` for every test field `Φ`: `curl β = -diag(1, -1, 0)`
weakly. -/
theorem inner_betaL2_curl (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Φ : Ix → R3 → ℝ}
    (hΦ : IsTestField Ω Φ) :
    ⟪-BoundedDomainTSD.constField hΩ hb BoundedDomainTSD.diagA, testField hΦ⟫_ℝ =
      ⟪BoundedDomainTSD.betaL2 hΩ hb,
        testField ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply hΦ)⟫_ℝ := by
  obtain ⟨hβM, hβv⟩ := BoundedDomainTSD.betaL2_mem_adjoint hΩ hb (gradCurl ℝ hΩ) le_rfl
  have h := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).adjoint_minimal_inner_testField hΩ ⟨_, hβM⟩ hΦ
  rw [← hβv]
  exact h

/-- `β ∈ D(d₁†)` for every complex with `d₁ ⊆ curl` on `H̊(curl, S)`, with
`d₁† β = -diag(1, -1, 0)`. -/
theorem betaT_mem_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {W₀ : Type*}
    [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    (S : ShortHilbertComplex ℝ W₀ (symSub ℝ Ω) (trSub ℝ Ω)) (hd₁ : S.d₁ ≤ (hessCurl ℝ hΩ).d₁) :
    ∃ h : (⟨_, (BoundedDomainTSD.betaL2_mem_tsd hΩ hb).2.1⟩ : trSub ℝ Ω) ∈ S.d₁†.domain,
      S.d₁† ⟨_, h⟩ = -(⟨_, (BoundedDomainTSD.constField_mem_tsd hΩ hb
        BoundedDomainTSD.diagA_transpose BoundedDomainTSD.diagA_trace).1⟩ :
        symSub ℝ Ω) := by
  set β : trSub ℝ Ω := ⟨_, (BoundedDomainTSD.betaL2_mem_tsd hΩ hb).2.1⟩
  set G : symSub ℝ Ω := ⟨_, (BoundedDomainTSD.constField_mem_tsd hΩ hb
    BoundedDomainTSD.diagA_transpose BoundedDomainTSD.diagA_trace).1⟩
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
[QuennevilleBelair2015], Prop 4.19 -/
theorem tsd_not_propagates (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
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
  let β : trSub ℝ Ω := ⟨_, (BoundedDomainTSD.betaL2_mem_tsd hΩ hb).2.1⟩
  let G : symSub ℝ Ω := ⟨_, (BoundedDomainTSD.constField_mem_tsd hΩ hb
    BoundedDomainTSD.diagA_transpose BoundedDomainTSD.diagA_trace).1⟩
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
      (v := β) (Submodule.mem_comap.2 (BoundedDomainTSD.betaL2_mem_tsd hΩ hb))
  refine ⟨U₀, hD, hK, fun T hT U hU0 hU => ?_⟩
  have hG : G ∈ (tsdS Ω ⊓ S.d₁.domain)ᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro z ⟨hzK, hzD⟩
    have hzM := hessCurl_d₁_graph_map hΩ ⟨z, hd₁.1 hzD⟩
    rw [Submodule.coe_inner]
    exact BoundedDomainTSD.inner_constField_eq_zero hΩ hb BoundedDomainTSD.diagA
      ⟨hzK, LinearPMap.mem_domain_of_mem_graph hzM⟩
  have hne0 : ⟪G, S.d₁† ⟨β, hβS⟩⟫_ℝ ≠ 0 := by
    rw [hβSv, inner_neg_right, Submodule.coe_inner, real_inner_comm,
      BoundedDomainTSD.inner_constField]
    simp only [BoundedDomainTSD.integral_constField, Fintype.sum_prod_type, Fin.sum_univ_three]
    have hpos := BoundedDomainTSD.volume_real_pos hΩ hb hne
    simp [BoundedDomainTSD.diagA]
    positivity
  obtain ⟨t, ht, hnot⟩ := S.not_propagates_of_inner_ne_zero hG ⟨β, hβS⟩ hne0 hT hU
    (by rw [hU0]; exact h0) (by rw [hU0]; exact h2)
  exact ⟨t, ht, fun hmem => hnot (hmem 1)⟩

/-! ### Named fields: `diag(1, -1, 0)` and `β` in `L²(S)`, `L²(T)` -/

/-- `diag(1, -1, 0)` as an element of `L²(TSD) ∩ L²(T)`. -/
def constT (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : trSub ℝ Ω :=
  ⟨_, (BoundedDomainTSD.constField_mem_tsd hΩ hb BoundedDomainTSD.diagA_transpose
    BoundedDomainTSD.diagA_trace).2.1⟩

theorem constT_mem_tsdT (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : constT hΩ hb ∈ tsdT Ω :=
  BoundedDomainTSD.constField_mem_tsd hΩ hb BoundedDomainTSD.diagA_transpose
    BoundedDomainTSD.diagA_trace

theorem constT_ne_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    constT hΩ hb ≠ 0 := fun h =>
  BoundedDomainTSD.constField_diagA_ne_zero hΩ hb hne (congrArg Subtype.val h)

/-- `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)` as an element of `L²(TSD) ∩ L²(T)`. -/
def betaT (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : trSub ℝ Ω :=
  ⟨_, (BoundedDomainTSD.betaL2_mem_tsd hΩ hb).2.1⟩

theorem betaT_mem_tsdT (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : betaT hΩ hb ∈ tsdT Ω :=
  BoundedDomainTSD.betaL2_mem_tsd hΩ hb

theorem betaField_symm (i j : Fin 3) :
    BoundedDomainTSD.betaField (i, j) = BoundedDomainTSD.betaField (j, i) := by
  fin_cases i <;> fin_cases j <;> rfl

/-- `β` as a symmetric field (an element of `L²(S)`). -/
def betaS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : symSub ℝ Ω :=
  ⟨_, (BoundedDomainTSD.betaL2_mem_tsd hΩ hb).1⟩

/-! ### The obstruction `L²(TSD₀)` for `H̊(curl, S)` -/

/-- `L²(TSD) ∩ H̊(curl, S) ⊆ L²(TSD₀)` (orthogonal to every gradient, weakly `E n = 0`). -/
theorem mem_tsd₀_of_mem_domain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {E : symSub ℝ Ω}
    (hE : E ∈ tsdS Ω) (hD : E ∈ (hessCurl ℝ hΩ).d₁.domain) :
    (E : L2F ℝ Ω Ix) ∈ tsd₀ Ω hΩ hb :=
  inf_le_tsd₀ hΩ hb ⟨hE, LinearPMap.mem_domain_of_mem_graph (hessCurl_d₁_graph_map hΩ ⟨E, hD⟩)⟩

/-- **Zero mean on `H̊(curl, S) ∩ L²(TSD)`**: `∫_Ω E = 0`. -/
theorem integral_eq_zero_of_mem_tsdS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {E : symSub ℝ Ω} (hE : E ∈ tsdS Ω) (hD : E ∈ (hessCurl ℝ hΩ).d₁.domain) (a b : Fin 3) :
    ∫ x, (E : L2F ℝ Ω Ix) (a, b) x ∂volume.restrict Ω = 0 :=
  integral_eq_zero_of_mem_tsd₀ hΩ hb (mem_tsd₀_of_mem_domain hΩ hb hE hD) a b

/-- `cl (L²(TSD) ∩ D(d₁)) ⊆ L²(TSD₀)` for every complex with `D(d₁) ⊆ H̊(curl, S)`. -/
theorem closure_le_tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {D : Submodule ℝ (symSub ℝ Ω)}
    (hD : D ≤ (hessCurl ℝ hΩ).d₁.domain) {E : symSub ℝ Ω}
    (hE : E ∈ (tsdS Ω ⊓ D).topologicalClosure) : (E : L2F ℝ Ω Ix) ∈ tsd₀ Ω hΩ hb := by
  have hcl : IsClosed ((tsd₀ Ω hΩ hb).comap (symSub ℝ Ω).subtype : Set (symSub ℝ Ω)) :=
    (isClosed_tsd₀ hΩ hb).preimage continuous_subtype_val
  exact Submodule.topologicalClosure_minimal (tsdS Ω ⊓ D)
    (t := (tsd₀ Ω hΩ hb).comap (symSub ℝ Ω).subtype)
    (fun F (hF : F ∈ tsdS Ω ⊓ D) => mem_tsd₀_of_mem_domain hΩ hb hF.1 (hD hF.2)) hcl hE

/-- **A necessary condition for TSD propagation** (the thesis' `Ė(0)` argument): for every short
complex `W₀ → L²(S) → W₂` with `D(d₁) ⊆ H̊(curl, S)`, if a strong solution from `(0, E₀, B₀)`
keeps its electric field in `L²(TSD)` on `[0, T]`, `T > 0`, then `E₀ ∈ L²(TSD₀)` and
`d₁† B₀ ∈ L²(TSD₀)` (weakly `E₀ n = 0` and `(d₁† B₀) n = 0` on `∂Ω`). -/
theorem mem_tsd₀_of_propagates (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {W₀ W₂ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [CompleteSpace W₂]
    (S : ShortHilbertComplex ℝ W₀ (symSub ℝ Ω) W₂) (hd₁ : S.d₁.domain ≤ (hessCurl ℝ hΩ).d₁.domain)
    {T : ℝ} (hT : 0 < T) {U : ℝ → PiLp 2 (ShortHilbertComplex.W3 W₀ (symSub ℝ Ω) W₂)}
    (hU : Evolution.IsStrongSolution S.wave (Icc 0 T) 0 U) (h0 : (U 0 0 : W₀) = 0)
    (hK : ∀ t ∈ Icc 0 T, (U t 1 : symSub ℝ Ω) ∈ tsdS Ω) :
    Subtype.val (U 0 1 : symSub ℝ Ω) ∈ tsd₀ Ω hΩ hb ∧
      ∃ hB : (U 0 2 : W₂) ∈ S.d₁†.domain, Subtype.val (S.d₁† ⟨_, hB⟩) ∈ tsd₀ Ω hΩ hb := by
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hD := (S.mem_wave_domain).1 (hU.mem_domain h0T)
  refine ⟨mem_tsd₀_of_mem_domain hΩ hb (hK 0 h0T) (hd₁ hD.2.1), ?_⟩
  obtain ⟨hB, hm⟩ := S.adjoint_mem_closure_of_propagates hT hU h0 hK
  exact ⟨hB, closure_le_tsd₀ hΩ hb hd₁ hm⟩

/-! ### The magnetic projection hypothesis of Prop 4.19 fails -/

open BoundedDomainTSD in
/-- The fields `E_t` (trace-free, curl-free) and `B_t = P_{L²(TSD)} E_t` in `D(d₁†)` for (4.16),
with `d₁† E_t = 0` and `d₁† B_t = curl B_t`. -/
theorem exists_gradFld_symFld (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ) :
    ∃ (E : trSub ℝ Ω) (B : trSub ℝ Ω) (hE : E ∈ (hessCurl ℝ hΩ).d₁†.domain)
      (hB : B ∈ (hessCurl ℝ hΩ).d₁†.domain), (hessCurl ℝ hΩ).d₁† ⟨E, hE⟩ = 0 ∧
      (tsdT Ω).starProjection E = B ∧
      (((hessCurl ℝ hΩ).d₁† ⟨B, hB⟩ : symSub ℝ Ω) : L2F ℝ Ω Ix) = curlSymFldL2 hΩ hb t ∧
      (E : L2F ℝ Ω Ix) = gradFldL2 hΩ hb t := by
  have hgE : ∀ ij, ContDiff ℝ 1 (gradFld t ij) := fun ij =>
    (contDiff_gradFld t ij).of_le (by simp)
  have hsB : ∀ ij, ContDiff ℝ 1 (symFld t ij) := fun ij =>
    (contDiff_symFld t ij).of_le (by simp)
  have htrE : ∀ x, ∑ i, gradFld t (i, i) x = 0 := fun x => by
    simp [gradFld, Fin.sum_univ_three]
  have htrB : ∀ x, ∑ i, symFld t (i, i) x = 0 := fun x => by
    simp [symFld_diag]
  obtain ⟨hE, hE'⟩ := smoothField_mem_adjoint_hessCurl_d₁ (Ψ := gradFld t) hΩ hb hgE htrE
  obtain ⟨hB, hB'⟩ := smoothField_mem_adjoint_hessCurl_d₁ (Ψ := symFld t) hΩ hb hsB htrB
  refine ⟨_, _, hE, hB, Subtype.ext ?_, ?_, ?_, rfl⟩
  · rw [hE']
    exact smoothField_eq_zero hΩ hb _ fun ij x _ => by simp [symF, curlM_gradFld]
  · refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := tsdT Ω)
      (show (symFldL2 hΩ hb t : L2F ℝ Ω Ix) ∈ tsd Ω from by
        have := (tsd Ω).starProjection_apply_mem (gradFldL2 hΩ hb t)
        rwa [starProjection_gradFld hΩ hb t] at this) fun w hw => ?_
    rw [Submodule.coe_inner, Submodule.coe_sub]
    have h := (tsd Ω).sub_starProjection_mem_orthogonal (gradFldL2 hΩ hb t)
    rw [starProjection_gradFld hΩ hb t] at h
    exact (Submodule.mem_orthogonal' _ _).1 h _ hw
  · rw [hB']
    refine smoothField_congr _ _ ?_
    funext ij x
    obtain ⟨i, k⟩ := ij
    simp only [symF, curlM_symFld]
    fin_cases i <;> fin_cases k <;> simp

/-- **The second projection hypothesis of Prop 4.19 is false** on every nonempty bounded open
`Ω ⊆ ℝ³`: `P_{L²(TSD)}` does not map `H(sym curl, T) = D(d₁†)` into itself, for (4.16).
Otherwise `ρ ↦ d₁† (P ρ)` is bounded on the graph of `d₁†` (closed graph theorem,
`LinearPMap.exists_norm_apply_le_of_mapsTo`), but the curl-free trace-free `E_t` have
`P E_t = B_t` and `‖sym curl B_t‖ = (t/√2) ‖E_t‖`.
[QuennevilleBelair2015], Prop. 4.19 (§4.11), second conjecture -/
theorem not_starProjection_mem_adjoint_domain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    ¬ ∀ B ∈ (hessCurl ℝ hΩ).d₁†.domain, (tsdT Ω).starProjection B ∈ (hessCurl ℝ hΩ).d₁†.domain := by
  intro hyp
  obtain ⟨C, hC⟩ := LinearPMap.exists_norm_apply_le_of_mapsTo
    (LinearPMap.adjoint_isClosed (hessCurl ℝ hΩ).dense₁) (tsdT Ω).starProjection
    fun x => hyp _ x.2
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 2 * |C| + 1 := ⟨_, rfl⟩
  obtain ⟨E, B, hE, hB, hAE, hPE, hAB, hEv⟩ := exists_gradFld_symFld hΩ hb t
  have h := hC ⟨E, hE⟩
  have e1 : (⟨(tsdT Ω).starProjection E, hyp _ hE⟩ : (hessCurl ℝ hΩ).d₁†.domain) = ⟨B, hB⟩ :=
    Subtype.ext hPE
  rw [e1, hAE] at h
  have hn1 : ‖(hessCurl ℝ hΩ).d₁† ⟨B, hB⟩‖ = ‖BoundedDomainTSD.curlSymFldL2 hΩ hb t‖ := by
    rw [← hAB]; rfl
  have hn2 : ‖(((⟨E, hE⟩ : (hessCurl ℝ hΩ).d₁†.domain) : trSub ℝ Ω), (0 : symSub ℝ Ω))‖ =
      ‖BoundedDomainTSD.gradFldL2 hΩ hb t‖ := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _), ← hEv]; rfl
  rw [hn1, hn2] at h
  have h1 := BoundedDomainTSD.norm_sq_curlSymFld hΩ hb t
  have h2 := BoundedDomainTSD.norm_sq_gradFld hΩ hb hne t
  have hC0 : C * ‖BoundedDomainTSD.gradFldL2 hΩ hb t‖ ≤ |C| * ‖BoundedDomainTSD.gradFldL2 hΩ
      hb t‖ :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
  have hsq : t ^ 2 / 2 * ‖BoundedDomainTSD.gradFldL2 hΩ hb t‖ ^ 2 ≤
      (|C| * ‖BoundedDomainTSD.gradFldL2 hΩ hb t‖) ^ 2 := by
    rw [← h1]
    exact pow_le_pow_left₀ (norm_nonneg _) (h.trans hC0) 2
  have : t ^ 2 / 2 ≤ |C| ^ 2 := by
    rw [mul_pow] at hsq
    exact le_of_mul_le_mul_right hsq h2
  rw [ht] at this
  nlinarith [abs_nonneg C]

/-- **Both parts of the magnetic projection hypothesis fail** for (4.16) and every closed `S₁`:
`P_{L²(TSD)} D(d₁†) ⊄ D(d₁†)`, and `P_K D(L) ⊄ D(L)` for `K = {0} × S₁ × L²(TSD)`.
[QuennevilleBelair2015], Prop. 4.19 (§4.11) -/
theorem not_projection_magnetic (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (S₁ : Submodule ℝ (symSub ℝ Ω)) [S₁.HasOrthogonalProjection] :
    (¬ ∀ B ∈ (hessCurl ℝ hΩ).d₁†.domain, (tsdT Ω).starProjection B ∈
      (hessCurl ℝ hΩ).d₁†.domain) ∧
      ¬ ∀ x ∈ (hessCurl ℝ hΩ).wave.domain, (HilbertComplex.totalSub
        (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω)) S₁ (tsdT Ω))).starProjection x ∈
          (hessCurl ℝ hΩ).wave.domain := by
  refine ⟨not_starProjection_mem_adjoint_domain hΩ hb hne, fun hPD => ?_⟩
  refine not_starProjection_mem_adjoint_domain hΩ hb hne fun B hB => ?_
  have hx := ShortHilbertComplex.inj₂_mem_wave_domain (S := hessCurl ℝ hΩ) hB
  have h := (((hessCurl ℝ hΩ).mem_wave_domain).1 (hPD _ hx)).2.2.2
  rwa [HilbertComplex.totalSub_starProjection_apply] at h

/-! ### Diagnosis -/

/-- **Diagnosis of Prop 4.19 on bounded domains** for the complex (4.16), on every nonempty
bounded open `Ω ⊆ ℝ³`, with `S₁ = S₂ = L²(TSD)`: the invariance hypotheses hold (Lemma 3.5:
`L²(TSD) ⊆ ker d₀†`, `d₁ (D(d₁) ∩ L²(TSD)) ⊆ L²(TSD)`, `d₁† (D(d₁†) ∩ L²(TSD)) ⊆ L²(TSD)`), while
the projection hypothesis fails through the electric slot and independently through the
magnetic slot. [QuennevilleBelair2015], Prop. 4.19 (§4.11) -/
theorem diagnosis (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    tsdS Ω ≤ (hessCurl ℝ hΩ).d₀†.ker ∧
      (∀ u : (hessCurl ℝ hΩ).d₁.domain, (u : symSub ℝ Ω) ∈ tsdS Ω →
        (hessCurl ℝ hΩ).d₁ u ∈ tsdT Ω) ∧
      (∀ ρ : (hessCurl ℝ hΩ).d₁†.domain, (ρ : trSub ℝ Ω) ∈ tsdT Ω →
        (hessCurl ℝ hΩ).d₁† ρ ∈ tsdS Ω) ∧
      ¬ (hessCurl ℝ hΩ).wave.IsReducing (HilbertComplex.totalSub
        (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω)) (tsdS Ω) (tsdT Ω))) ∧
      ¬ ∀ B ∈ (hessCurl ℝ hΩ).d₁†.domain, (tsdT Ω).starProjection B ∈
        (hessCurl ℝ hΩ).d₁†.domain := by
  refine ⟨tsdS_le_ker hΩ, hessCurl_d₁_mem_tsdT hΩ, adjoint_hessCurl_d₁_mem_tsdS hΩ,
    not_isReducing_tsd hΩ hb hne (hessCurl ℝ hΩ) (tsdT Ω) le_rfl fun Φ hΦ hs => ⟨?_, ?_⟩,
    not_starProjection_mem_adjoint_domain hΩ hb hne⟩
  · exact testField_mem_hessCurl_d₁_domain hΩ hΦ hs
  · exact testField_mem_adjoint_hessCurl_d₀ hΩ hΦ hs

/-! ### The corrected Prop 4.19: the invariant core `K*` of (4.16) -/

section InvariantCore

variable {W₀ W₂ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [CompleteSpace W₂]

/-- **The electric slot of `K*` lies in `L²(TSD₀)`** for every short complex `W₀ → L²(S) → W₂`
with `D(d₁) ⊆ H̊(curl, S)`, `K = {0} × L²(TSD) × S₂`. -/
theorem invariantCore₁_le_tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (S : ShortHilbertComplex ℝ W₀ (symSub ℝ Ω) W₂)
    (hd₁ : S.d₁.domain ≤ (hessCurl ℝ hΩ).d₁.domain) (S₂ : Submodule ℝ W₂)
    [S₂.HasOrthogonalProjection] {u : symSub ℝ Ω} (hu : u ∈ S.invariantCore₁ (tsdS Ω) S₂) :
    (u : L2F ℝ Ω Ix) ∈ tsd₀ Ω hΩ hb := by
  have hcl := ShortHilbertComplex.mem_closure_wave_domain_inter_coreSub
    (ShortHilbertComplex.mem_invariantCore₁.1 hu)
  let π : PiLp 2 (ShortHilbertComplex.W3 W₀ (symSub ℝ Ω) W₂) →L[ℝ] L2F ℝ Ω Ix :=
    (symSub ℝ Ω).subtypeL.comp
      (PiLp.proj 2 (fun i => ShortHilbertComplex.W3 W₀ (symSub ℝ Ω) W₂ i) 1)
  have := map_mem_closure π.continuous hcl (t := (tsd₀ Ω hΩ hb : Set (L2F ℝ Ω Ix)))
    fun y ⟨hyD, hyK⟩ => by
      obtain ⟨-, h1, -⟩ := ShortHilbertComplex.mem_coreSub_iff.1 hyK
      exact mem_tsd₀_of_mem_domain hΩ hb (ShortHilbertComplex.invariantCore₁_le h1)
        (hd₁ ((S.mem_wave_domain).1 hyD).2.1)
  rwa [(isClosed_tsd₀ hΩ hb).closure_eq] at this

/-- `diag(1, -1, 0) ∉ S₁*`. -/
theorem constS_not_mem_invariantCore₁ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (S : ShortHilbertComplex ℝ W₀ (symSub ℝ Ω) W₂)
    (hd₁ : S.d₁.domain ≤ (hessCurl ℝ hΩ).d₁.domain) (S₂ : Submodule ℝ W₂)
    [S₂.HasOrthogonalProjection] : constS hΩ hb ∉ S.invariantCore₁ (tsdS Ω) S₂ := fun hm =>
  BoundedDomainTSD.constField_diagA_not_mem_tsd₀ hΩ hb hne
    (invariantCore₁_le_tsd₀ hΩ hb S hd₁ S₂ hm)

/-- `β ∉ S₂*` for every complex `W₀ → L²(S) → L²(T)` with `d₁ ⊆ curl` on `H̊(curl, S)`:
`d₁† β = -diag(1, -1, 0) ∉ L²(TSD₀)`. -/
theorem betaT_not_mem_invariantCore₂ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (S : ShortHilbertComplex ℝ W₀ (symSub ℝ Ω) (trSub ℝ Ω))
    (hd₁ : S.d₁ ≤ (hessCurl ℝ hΩ).d₁) (S₂ : Submodule ℝ (trSub ℝ Ω))
    [S₂.HasOrthogonalProjection] : betaT hΩ hb ∉ S.invariantCore₂ (tsdS Ω) S₂ := by
  intro hm
  obtain ⟨h, hv⟩ := betaT_mem_adjoint hΩ hb S hd₁
  have h1 := ShortHilbertComplex.adjoint_mem_invariantCore₁ (S := S) ⟨_, h⟩ hm
  rw [hv] at h1
  have h2 := invariantCore₁_le_tsd₀ hΩ hb S hd₁.1 S₂ h1
  refine BoundedDomainTSD.constField_diagA_not_mem_tsd₀ hΩ hb hne ?_
  simpa using (tsd₀ Ω hΩ hb).neg_mem h2

/-- `sym curl` of a `C¹` trace-free curl-free field vanishes: such a field is a stationary
magnetic datum of (4.16). -/
theorem mem_invariantCore₂_of_curl_eq_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (S₁ : Submodule ℝ (symSub ℝ Ω)) [S₁.HasOrthogonalProjection] {Ψ : Ix → R3 → ℝ}
    (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) (htr : ∀ x, ∑ i, Ψ (i, i) x = 0)
    (hc : ∀ ij x, curlM Ψ ij x = 0)
    (hK : (⟨smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous),
      smoothField_mem_trSub hΩ hb _ htr⟩ : trSub ℝ Ω) ∈ tsdT Ω) :
    (⟨smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous),
      smoothField_mem_trSub hΩ hb _ htr⟩ : trSub ℝ Ω) ∈
        (hessCurl ℝ hΩ).invariantCore₂ S₁ (tsdT Ω) := by
  obtain ⟨h, e⟩ := smoothField_mem_adjoint_hessCurl_d₁ (Ψ := Ψ) hΩ hb hΨ htr
  refine ShortHilbertComplex.mem_invariantCore₂_of_eq_zero (S := hessCurl ℝ hΩ) ⟨_, h⟩ hK
    (Subtype.ext ?_)
  rw [e]
  exact smoothField_eq_zero hΩ hb _ fun ij x _ => by simp [symF, hc]

/-- **`diag(1, -1, 0)` is a nonzero stationary magnetic datum**: `constT ∈ S₂*`. -/
theorem constT_mem_invariantCore₂ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (S₁ : Submodule ℝ (symSub ℝ Ω)) [S₁.HasOrthogonalProjection] :
    constT hΩ hb ∈ (hessCurl ℝ hΩ).invariantCore₂ S₁ (tsdT Ω) :=
  mem_invariantCore₂_of_curl_eq_zero hΩ hb S₁ (Ψ := fun ij _ => BoundedDomainTSD.diagA ij.1 ij.2)
    (fun _ => contDiff_const)
    (fun _ => by simpa [Matrix.trace] using BoundedDomainTSD.diagA_trace)
    (fun ij x => by simp [curlM, pd]) (constT_mem_tsdT hΩ hb)

/-- **Hessians of harmonic functions are stationary magnetic data**: `∇²h ∈ S₂*`. -/
theorem hessL2_mem_invariantCore₂ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (S₁ : Submodule ℝ (symSub ℝ Ω)) [S₁.HasOrthogonalProjection] {h : R3 → ℝ}
    (hh : ContDiff ℝ ∞ h) (hΔ : ∀ x, lap h x = 0) :
    (⟨hessL2 hΩ hb hh, smoothField_mem_trSub hΩ hb _ hΔ⟩ : trSub ℝ Ω) ∈
      (hessCurl ℝ hΩ).invariantCore₂ S₁ (tsdT Ω) :=
  mem_invariantCore₂_of_curl_eq_zero hΩ hb S₁ (Ψ := hessField h)
    (fun ij => (contDiff_hessField hh ij).of_le (by simp)) hΔ
    (fun ij x => by
      rw [hessField_eq_gradM]
      exact curlM_gradM (fun i => (contDiff_pd_top hh i).of_le (by simp)) ij x)
    (hessL2_mem_tsd hΩ hb hh fun x _ => hΔ x)

/-- **The stationary part of `S₂*` is infinite-dimensional** for (4.16) on a nonempty bounded
open `Ω`: it contains the independent harmonic Hessians `∇²(e^{-n x₁} cos(n x₂))`. -/
theorem not_finiteDimensional_invariantCore₂ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (S₁ : Submodule ℝ (symSub ℝ Ω)) [S₁.HasOrthogonalProjection] :
    ¬ FiniteDimensional ℝ ((hessCurl ℝ hΩ).invariantCore₂ S₁ (tsdT Ω)) := by
  intro hfin
  let v : ℕ → (hessCurl ℝ hΩ).invariantCore₂ S₁ (tsdT Ω) := fun n =>
    ⟨_, hessL2_mem_invariantCore₂ hΩ hb S₁ (contDiff_expCos ((n : ℝ) + 1)) (lap_expCos _)⟩
  have hli : LinearIndependent ℝ v :=
    LinearIndependent.of_comp ((trSub ℝ Ω).subtype ∘ₗ Submodule.subtype _)
      (linearIndependent_hessL2_expCos hΩ hb hne)
  exact Module.Finite.not_linearIndependent_of_infinite v hli

/-- **Corrected Prop 4.19 on bounded domains** for the complex (4.16)
`H̊² → H̊(curl, S) → L²(T)` and `K = {0} × L²(TSD) × L²(TSD)`, with `K*` the invariant core of `K`
under the wave group:
1. `K* = {0} × S₁* × S₂*` with `S₁* ⊆ L²(TSD₀)` and `S₂* ⊆ L²(TSD)`;
2. `{0} × S₁* × S₂*` is a reducing subcomplex, and the largest one inside `K`;
3. strictness: `diag(1, -1, 0) ∈ L²(TSD) \ S₁*`, `β ∈ L²(TSD) \ S₂*`; `diag(1, -1, 0) ∈ S₂*` is a
   nonzero stationary datum, and `S₂*` is infinite-dimensional;
4. every `U₀ ∈ D(L) ∩ K*` has on every `[0, T]` a classical solution, unique among strong
   solutions, staying in `K* ⊆ K`.
The only elements of `K*` exhibited are stationary. [QuennevilleBelair2015], Prop. 4.19, corrected -/
theorem invariantCore_tsd (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    (hessCurl ℝ hΩ).coreSub (tsdS Ω) (tsdT Ω) = HilbertComplex.totalSub
        (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω))
          ((hessCurl ℝ hΩ).invariantCore₁ (tsdS Ω) (tsdT Ω))
          ((hessCurl ℝ hΩ).invariantCore₂ (tsdS Ω) (tsdT Ω))) ∧
      (∀ u ∈ (hessCurl ℝ hΩ).invariantCore₁ (tsdS Ω) (tsdT Ω),
        (u : L2F ℝ Ω Ix) ∈ tsd₀ Ω hΩ hb) ∧
      (hessCurl ℝ hΩ).invariantCore₂ (tsdS Ω) (tsdT Ω) ≤ tsdT Ω ∧
      (hessCurl ℝ hΩ).toHilbertComplex.ReducingSubcomplex
        (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω))
          ((hessCurl ℝ hΩ).invariantCore₁ (tsdS Ω) (tsdT Ω))
          ((hessCurl ℝ hΩ).invariantCore₂ (tsdS Ω) (tsdT Ω))) ∧
      (∀ (S₁' : Submodule ℝ (symSub ℝ Ω)) (S₂' : Submodule ℝ (trSub ℝ Ω))
        [S₁'.HasOrthogonalProjection] [S₂'.HasOrthogonalProjection], S₁' ≤ tsdS Ω →
        S₂' ≤ tsdT Ω → (hessCurl ℝ hΩ).wave.IsReducing (HilbertComplex.totalSub
          (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω)) S₁' S₂')) →
        S₁' ≤ (hessCurl ℝ hΩ).invariantCore₁ (tsdS Ω) (tsdT Ω) ∧
          S₂' ≤ (hessCurl ℝ hΩ).invariantCore₂ (tsdS Ω) (tsdT Ω)) ∧
      constS hΩ hb ∈ tsdS Ω ∧ constS hΩ hb ∉ (hessCurl ℝ hΩ).invariantCore₁ (tsdS Ω) (tsdT Ω) ∧
      betaT hΩ hb ∈ tsdT Ω ∧ betaT hΩ hb ∉ (hessCurl ℝ hΩ).invariantCore₂ (tsdS Ω) (tsdT Ω) ∧
      constT hΩ hb ∈ (hessCurl ℝ hΩ).invariantCore₂ (tsdS Ω) (tsdT Ω) ∧ constT hΩ hb ≠ 0 ∧
      ¬ FiniteDimensional ℝ ((hessCurl ℝ hΩ).invariantCore₂ (tsdS Ω) (tsdT Ω)) ∧
      ∀ U₀ ∈ (hessCurl ℝ hΩ).wave.domain, U₀ ∈ (hessCurl ℝ hΩ).coreSub (tsdS Ω) (tsdT Ω) →
        ∀ T : ℝ, ∃ U, U 0 = U₀ ∧
          Evolution.IsClassicalSolution (hessCurl ℝ hΩ).wave (Icc 0 T) 0 U ∧
          (∀ t ∈ Icc 0 T, U t ∈ (hessCurl ℝ hΩ).coreSub (tsdS Ω) (tsdT Ω)) ∧
          ∀ V, V 0 = U₀ → Evolution.IsStrongSolution (hessCurl ℝ hΩ).wave (Icc 0 T) 0 V →
            EqOn V U (Icc 0 T) :=
  ⟨ShortHilbertComplex.coreSub_eq,
    fun _ hu => invariantCore₁_le_tsd₀ hΩ hb (hessCurl ℝ hΩ) le_rfl (tsdT Ω) hu,
    ShortHilbertComplex.invariantCore₂_le,
    ShortHilbertComplex.reducingSubcomplex_coreSub (tsdS_le_ker hΩ),
    fun _ _ _ _ h₁ h₂ hred => ShortHilbertComplex.le_invariantCore_of_isReducing h₁ h₂ hred,
    constS_mem_tsdS hΩ hb, constS_not_mem_invariantCore₁ hΩ hb hne (hessCurl ℝ hΩ) le_rfl _,
    betaT_mem_tsdT hΩ hb, betaT_not_mem_invariantCore₂ hΩ hb hne (hessCurl ℝ hΩ) le_rfl _,
    constT_mem_invariantCore₂ hΩ hb _, constT_ne_zero hΩ hb hne,
    not_finiteDimensional_invariantCore₂ hΩ hb hne _,
    fun _ hU₀ hK T => ShortHilbertComplex.existsUnique_mem_coreSub hU₀ hK 0 T⟩

/-- **When does `K*` of (4.16) contain a moving datum?** For the Hessian–curl complex and
`K = {0} × L²(TSD) ∩ L²(S) × L²(TSD) ∩ L²(T)`, under a complete set of eigenvectors of `L²`
(`hD`, the hypothesis of `Feec.Models.BoundedDomain.gradCurl_coreSub_spectral`): forward
invariance is equivalent to membership in `K*`; `K*` is stationary iff `S₁* ⊆ ker d₁`; `K*`
contains a non-stationary datum iff `d₁† d₁ u = ω² u` has a nonzero solution
`u ∈ L²(TSD) ∩ D(d₁)` with `d₁ u ∈ D(d₁†)`, `ω > 0` (`d₁ u ∈ L²(TSD)` is automatic,
`hessCurl_d₁_mem_tsdT`); and every such `u` lies in `S₁*`, has `u ∈ L²(TSD₀)`, and moves. -/
theorem hessCurl_coreSub_spectral (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hD : (hessCurl ℝ hΩ).EigenDense) :
    (∀ x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ Ω) (symSub ℝ Ω) (trSub ℝ Ω)),
      (∀ t, 0 ≤ t → (hessCurl ℝ hΩ).toHilbertComplex.waveGroup.S t x ∈
        HilbertComplex.totalSub (ShortHilbertComplex.family3 ⊥ (tsdS Ω) (tsdT Ω))) ↔
          x ∈ (hessCurl ℝ hΩ).coreSub (tsdS Ω) (tsdT Ω)) ∧
    ((hessCurl ℝ hΩ).coreSub (tsdS Ω) (tsdT Ω) ≤
        (hessCurl ℝ hΩ).stationary ↔
      ∀ v ∈ (hessCurl ℝ hΩ).invariantCore₁ (tsdS Ω) (tsdT Ω),
        ∃ h1 : v ∈ (hessCurl ℝ hΩ).d₁.domain, (hessCurl ℝ hΩ).d₁ ⟨v, h1⟩ = 0) ∧
    (¬ (hessCurl ℝ hΩ).coreSub (tsdS Ω) (tsdT Ω) ≤
        (hessCurl ℝ hΩ).stationary ↔
      ∃ w : ℝ, 0 < w ∧ ∃ v : symSub ℝ Ω, v ≠ 0 ∧ v ∈ tsdS Ω ∧ (hessCurl ℝ hΩ).IsEigenfield w v) ∧
    (∀ w : ℝ, 0 < w → ∀ v : symSub ℝ Ω, v ∈ tsdS Ω → (hessCurl ℝ hΩ).IsEigenfield w v →
          v ∈ (hessCurl ℝ hΩ).invariantCore₁ (tsdS Ω) (tsdT Ω) ∧
            (v : L2F ℝ Ω Ix) ∈ tsd₀ Ω hΩ hb ∧
            (v ≠ 0 → ShortHilbertComplex.inj₁ (𝕜 := ℝ) (L2 ℝ Ω) (symSub ℝ Ω) (trSub ℝ Ω)
              v ∉ (hessCurl ℝ hΩ).stationary)) := by
  have H :=
    ShortHilbertComplex.coreSub_spectral (S := hessCurl ℝ hΩ) (S₁ := tsdS Ω) (S₂ := tsdT Ω)
      (tsdS_le_ker hΩ) hD
  refine ⟨H.1, H.2.1, ?_, fun w hw v hv hE => ?_⟩
  · rw [H.2.2]
    refine exists_congr fun w => and_congr_right fun _ => exists_congr fun v =>
        and_congr_right fun _ => and_congr_right fun hv => ?_
    unfold ShortHilbertComplex.IsEigenfield
    exact exists_congr fun h1 => exists_congr fun _ =>
      ⟨And.right, And.intro (hessCurl_d₁_mem_tsdT hΩ ⟨v, h1⟩ hv)⟩
  obtain ⟨hv1, hv3, e⟩ := hE
  obtain ⟨h2, e2⟩ := LinearPMap.exists_apply_eq_zero_of_mem_ker (tsdS_le_ker hΩ hv)
  obtain ⟨-, hm, hns⟩ := ShortHilbertComplex.eigenfield_mem_invariantCore₁
    (S := hessCurl ℝ hΩ) (S₂ := tsdT Ω) hw hv hv1 h2 e2 hv3
    (hessCurl_d₁_mem_tsdT hΩ ⟨v, hv1⟩ hv) e
  exact ⟨hm, invariantCore₁_le_tsd₀ hΩ hb (hessCurl ℝ hΩ) le_rfl (tsdT Ω) hm, hns⟩

end InvariantCore

/-! ### The density obstruction is infinite-dimensional -/

/-- **The obstruction in `L²(S)` is infinite-dimensional**: on a nonempty bounded open `Ω`, the
part of `L²(TSD) ∩ L²(S)` orthogonal to `L²(TSD₀)` contains the independent harmonic Hessians;
since `H̊(curl, S) ∩ L²(TSD) ⊆ L²(TSD₀)`, the orthogonal complement of the closure of
`H̊(curl, S) ∩ L²(TSD)` in `L²(TSD) ∩ L²(S)` is infinite-dimensional: no finite-dimensional
correction makes the density conjecture of Prop 4.19 true.
[QuennevilleBelair2015], Prop. 4.19 (§4.11), density conjecture -/
theorem not_finiteDimensional_obstruction (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    ¬ FiniteDimensional ℝ (tsdS Ω ⊓ ((tsd₀ Ω hΩ hb).comap (symSub ℝ Ω).subtype)ᗮ :
        Submodule ℝ (symSub ℝ Ω)) ∧
      ¬ FiniteDimensional ℝ (tsdS Ω ⊓ (Submodule.span ℝ
        (closure ((tsdS Ω : Set (symSub ℝ Ω)) ∩ (hessCurl ℝ hΩ).d₁.domain)))ᗮ :
          Submodule ℝ (symSub ℝ Ω)) := by
  have hmem : ∀ n : ℕ, (⟨hessL2 hΩ hb (contDiff_expCos ((n : ℝ) + 1)),
      hessL2_mem_symSub hΩ hb (contDiff_expCos ((n : ℝ) + 1))⟩ : symSub ℝ Ω) ∈
      tsdS Ω ⊓ ((tsd₀ Ω hΩ hb).comap (symSub ℝ Ω).subtype)ᗮ := fun n => by
    refine ⟨hessL2_mem_tsd hΩ hb (contDiff_expCos ((n : ℝ) + 1)) fun x _ => lap_expCos _ x,
      (Submodule.mem_orthogonal' _ _).2 fun u hu => ?_⟩
    rw [Submodule.coe_inner]
    have ho := gradL2_mem_orthogonal_tsd₀ hΩ hb
      (φ := fun i => pd i (expCos ((n : ℝ) + 1)))
      (fun i => (contDiff_pd_top (contDiff_expCos _) i).of_le (by simp))
    exact (Submodule.mem_orthogonal' _ _).1 ho _ hu
  have hle : (tsdS Ω ⊓ ((tsd₀ Ω hΩ hb).comap (symSub ℝ Ω).subtype)ᗮ : Submodule ℝ (symSub ℝ Ω)) ≤
      tsdS Ω ⊓ (Submodule.span ℝ
        (closure ((tsdS Ω : Set (symSub ℝ Ω)) ∩ (hessCurl ℝ hΩ).d₁.domain)))ᗮ := by
    refine inf_le_inf_left _ (Submodule.orthogonal_le (Submodule.span_le.2 ?_))
    refine closure_minimal (fun E hE => mem_tsd₀_of_mem_domain hΩ hb hE.1 hE.2) ?_
    exact (isClosed_tsd₀ hΩ hb).preimage continuous_subtype_val
  have h1 : ¬ FiniteDimensional ℝ (tsdS Ω ⊓ ((tsd₀ Ω hΩ hb).comap (symSub ℝ Ω).subtype)ᗮ :
      Submodule ℝ (symSub ℝ Ω)) := by
    intro hfin
    let v : ℕ → (tsdS Ω ⊓ ((tsd₀ Ω hΩ hb).comap (symSub ℝ Ω).subtype)ᗮ :
      Submodule ℝ (symSub ℝ Ω)) := fun n => ⟨_, hmem n⟩
    have hli : LinearIndependent ℝ v :=
      LinearIndependent.of_comp ((symSub ℝ Ω).subtype ∘ₗ Submodule.subtype _)
        (linearIndependent_hessL2_expCos hΩ hb hne)
    exact Module.Finite.not_linearIndependent_of_infinite v hli
  exact ⟨h1, fun hfin => h1 (Submodule.finiteDimensional_of_le hle)⟩

/-! ### Prop 4.19 with the boundary conditions as printed (`hessCurlMax`) -/

section Printed

/-- The quadratic monomial `x_a x_b`. -/
def quadF (a b : Fin 3) : R3 → ℝ := fun y => y a * y b

theorem contDiff_quadF (a b : Fin 3) : ContDiff ℝ ∞ (quadF a b) :=
  (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) a).mul (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) b)

theorem differentiable_coord (a : Fin 3) : Differentiable ℝ fun y : R3 => y a :=
  differentiable_apply (𝕜 := ℝ) a

theorem pd_quadF (a b k : Fin 3) :
    pd k (quadF a b) = fun y => (if k = a then 1 else 0) * y b + (if k = b then 1 else 0) * y
        a := by
  funext y
  change pd k (fun y => y a * y b) y = _
  rw [pd_mul (differentiable_coord a y) (differentiable_coord b y), pd_coord, pd_coord]
  ring

/-- `∇²(x_a x_b) = e_a e_bᵀ + e_b e_aᵀ`. -/
theorem hessField_quadF (a b : Fin 3) (ij : Ix) (x : R3) :
    hessField (quadF a b) ij x = (if ij = (a, b) then 1 else 0) + (if ij = (b, a) then 1
        else 0) := by
  obtain ⟨i, j⟩ := ij
  simp only [hessField, pd_quadF]
  change pd j ((fun y => (if i = a then (1 : ℝ) else 0) * y b) +
    (fun y => (if i = b then (1 : ℝ) else 0) * y a)) x = _
  rw [pd_add ((differentiable_coord b).const_mul _) ((differentiable_coord a).const_mul _),
    pd_const_mul (differentiable_coord b), pd_const_mul (differentiable_coord a), pd_coord,
    pd_coord]
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

/-- **Zero mean of `ker d₀†`** for the printed placement: every `E ⊥ ∇² H²` has
`∫_Ω E = 0` (tested against `∇²(x_a x_b)`): the boundary condition of `H̊(div div, S)`. -/
theorem integral_eq_zero_of_mem_ker_hessCurlMax (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {E : symSub ℝ Ω} (hE : E ∈ (hessCurlMax ℝ hΩ).d₀†.ker) (a b : Fin 3) :
    ∫ x, (E : L2F ℝ Ω Ix) (a, b) x ∂volume.restrict Ω = 0 := by
  obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 hE
  subst hy
  obtain ⟨hq, eq⟩ := smooth_mem_hessCurlMax_d₀ hΩ hb (contDiff_quadF a b)
  have e := LinearPMap.adjoint_isFormalAdjoint (hessCurlMax ℝ hΩ).dense₀ y ⟨_, hq⟩
  rw [hy0, inner_zero_left, Submodule.coe_inner, eq, hessL2, inner_smoothField] at e
  have hc : ∀ ij : Ix, ∫ x, ((y : symSub ℝ Ω) : L2F ℝ Ω Ix) ij x * hessField (quadF a b) ij x
      ∂volume.restrict Ω = (∫ x, ((y : symSub ℝ Ω) : L2F ℝ Ω Ix) ij x ∂volume.restrict Ω) *
        ((if ij = (a, b) then 1 else 0) + (if ij = (b, a) then 1 else 0)) := fun ij => by
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hessField_quadF]
  simp only [hc, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at e
  have hs : ((y : symSub ℝ Ω) : L2F ℝ Ω Ix) (b, a) = ((y : symSub ℝ Ω) : L2F ℝ Ω Ix) (a, b) :=
    (y : symSub ℝ Ω).2 b a
  rw [hs] at e
  linarith

/-- **`L²(TSD) ∩ H̊(div div, S) ⊆ ker (div div)`**: `d₀†` of the printed placement extends to
the `d₀†` of (4.16), which kills `L²(TSD)`. -/
theorem mem_ker_of_mem_tsdS (hΩ : IsOpen Ω) {E : symSub ℝ Ω} (hE : E ∈ tsdS Ω)
    (hD : E ∈ (hessCurlMax ℝ hΩ).d₀†.domain) : E ∈ (hessCurlMax ℝ hΩ).d₀†.ker := by
  obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 (tsdS_le_ker hΩ hE)
  refine LinearPMap.mem_ker_iff.2 ⟨⟨E, hD⟩, rfl, ?_⟩
  rw [← hy0]
  exact (adjoint_hessCurlMax_d₀_le (𝕜 := ℝ) hΩ).2 hy

/-- **Every TSD field in `H̊(div div, S)` has zero mean**: the boundary condition of
`H̊(div div, S)` replaces that of `H̊(curl, S)` in the zero-mean obstruction. -/
theorem integral_eq_zero_of_mem_tsdS_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {E : symSub ℝ Ω} (hE : E ∈ tsdS Ω) (hD : E ∈ (hessCurlMax ℝ hΩ).d₀†.domain) (a b : Fin 3) :
    ∫ x, (E : L2F ℝ Ω Ix) (a, b) x ∂volume.restrict Ω = 0 :=
  integral_eq_zero_of_mem_ker_hessCurlMax hΩ hb (mem_ker_of_mem_tsdS hΩ hE hD) a b

theorem inner_constS_eq_zero_of_ker (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {E : symSub ℝ Ω} (hE : E ∈ (hessCurlMax ℝ hΩ).d₀†.ker) : ⟪E, constS hΩ hb⟫_ℝ = 0 := by
  rw [Submodule.coe_inner]
  change ⟪(E : L2F ℝ Ω Ix), BoundedDomainTSD.constField hΩ hb BoundedDomainTSD.diagA⟫_ℝ = 0
  rw [BoundedDomainTSD.inner_constField]
  exact Finset.sum_eq_zero fun ij _ => by
    rw [integral_eq_zero_of_mem_ker_hessCurlMax hΩ hb hE, mul_zero]

/-- **`L²(TSD) ⊄ H̊(div div, S)`**: the constant TSD field `diag(1, -1, 0)` is not in
`D(d₀†)` of the printed placement. -/
theorem constS_not_mem_adjoint_hessCurlMax_d₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : constS hΩ hb ∉ (hessCurlMax ℝ hΩ).d₀†.domain := fun hD => by
  have h := integral_eq_zero_of_mem_tsdS_adjoint hΩ hb (constS_mem_tsdS hΩ hb) hD 0 0
  change ∫ x, BoundedDomainTSD.constField hΩ hb BoundedDomainTSD.diagA (0, 0) x
    ∂volume.restrict Ω = 0 at h
  rw [BoundedDomainTSD.integral_constField] at h
  have := BoundedDomainTSD.volume_real_pos hΩ hb hne
  simp [BoundedDomainTSD.diagA] at h
  exact this.ne' h

theorem not_tsdS_le_ker_hessCurlMax (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : ¬ tsdS Ω ≤ (hessCurlMax ℝ hΩ).d₀†.ker := fun h => by
  obtain ⟨y, hy, -⟩ := LinearPMap.mem_ker_iff.1 (h (constS_mem_tsdS hΩ hb))
  exact constS_not_mem_adjoint_hessCurlMax_d₀ hΩ hb hne (hy ▸ y.2)

/-- For the symmetric test field `Φ = g · diag(1, -1, 0)` (`g ≥ 0` a bump, `g ≠ 0`),
`⟪P_{L²(TSD)} Φ, diag(1, -1, 0)⟫ ≠ 0`. -/
theorem exists_inner_starProjection_constS_ne_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : ∃ (Φ : Ix → R3 → ℝ) (hΦ : IsTestField Ω Φ)
      (hs : ∀ i j, Φ (i, j) = Φ (j, i)),
      ⟪(tsdS Ω).starProjection ⟨testField hΦ, testField_mem_symSub hΦ hs⟩, constS hΩ hb⟫_ℝ ≠ 0 := by
  obtain ⟨g, hg, hgpos⟩ := BoundedDomainTSD.exists_isTest_integral_pos hΩ hne
  let Φ : Ix → R3 → ℝ := fun ij x => BoundedDomainTSD.diagA ij.1 ij.2 * g x
  have hΦ : IsTestField Ω Φ := fun ij => hg.const_mul (BoundedDomainTSD.diagA ij.1 ij.2)
  have hs : ∀ i j, Φ (i, j) = Φ (j, i) := fun i j => by
    funext x; simp only [Φ, diagA_symm i j]
  refine ⟨Φ, hΦ, hs, fun h0 => ?_⟩
  rw [Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.2 (constS_mem_tsdS hΩ hb), Submodule.coe_inner] at h0
  change ⟪testField hΦ, BoundedDomainTSD.constField hΩ hb BoundedDomainTSD.diagA⟫_ℝ = 0 at h0
  have hI : ∀ ij : Ix, ∫ x, testField hΦ ij x ∂volume.restrict Ω =
      BoundedDomainTSD.diagA ij.1 ij.2 * ∫ x, g x ∂volume.restrict Ω := fun ij => by
    rw [← integral_const_mul]
    exact integral_congr_ae (coeFn_testField hΦ ij)
  rw [BoundedDomainTSD.inner_constField] at h0
  simp only [hI, Fintype.sum_prod_type, Fin.sum_univ_three] at h0
  simp [BoundedDomainTSD.diagA] at h0
  linarith

/-- **The projection hypothesis of Prop 4.19 fails also with the boundary conditions of its
statement** (`hessCurlMax`, `D(L) = H² × (H(curl, S) ∩ H̊(div div, S)) × H̊(sym curl, T)`), on
every nonempty bounded open `Ω ⊆ ℝ³` and for every `S₂`: `P_K D(L) ⊄ D(L)` for
`K = {0} × L²(TSD) × S₂`, since `P_{L²(TSD)} (g · diag(1, -1, 0))` has nonzero mean.
[QuennevilleBelair2015], Prop. 4.19 (§4.11), first conjecture, data space as printed -/
theorem not_starProjection_mem_wave_domain_hessCurlMax (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) (S₂ : Submodule ℝ (trSub ℝ Ω))
    [S₂.HasOrthogonalProjection] :
    ¬ ∀ x ∈ (hessCurlMax ℝ hΩ).wave.domain, (HilbertComplex.totalSub
      (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω)) (tsdS Ω) S₂)).starProjection x ∈
        (hessCurlMax ℝ hΩ).wave.domain := by
  intro hPD
  obtain ⟨Φ, hΦ, hs, hne0⟩ := exists_inner_starProjection_constS_ne_zero hΩ hb hne
  have hx := ShortHilbertComplex.inj₁_mem_wave_domain (S := hessCurlMax ℝ hΩ)
    (testField_mem_hessCurlMax_d₁_domain hΩ hΦ hs) (testField_mem_adjoint_hessCurlMax_d₀ hΩ hΦ hs)
  have h := ((hessCurlMax ℝ hΩ).mem_wave_domain.1 (hPD _ hx)).2.2.1
  rw [HilbertComplex.totalSub_starProjection_apply] at h
  exact hne0 (inner_constS_eq_zero_of_ker hΩ hb
    (mem_ker_of_mem_tsdS hΩ (Submodule.starProjection_apply_mem _ _) h))

/-- The reducing form: `{0} × L²(TSD) × S₂` does not reduce the wave operator of `hessCurlMax`. -/
theorem not_isReducing_tsd_hessCurlMax (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (S₂ : Submodule ℝ (trSub ℝ Ω)) [S₂.HasOrthogonalProjection] :
    ¬ (hessCurlMax ℝ hΩ).wave.IsReducing (HilbertComplex.totalSub
      (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω)) (tsdS Ω) S₂)) := fun h =>
  not_starProjection_mem_wave_domain_hessCurlMax hΩ hb hne S₂ fun x hx => h.proj_mem ⟨x, hx⟩

/-- **The density hypothesis of Prop 4.19 fails also with the boundary conditions of its
statement**: `H(curl, S) ∩ H̊(div div, S) ∩ L²(TSD)` is not dense in `L²(TSD)`;
`diag(1, -1, 0)` is not in its closure. [QuennevilleBelair2015], Prop. 4.19 (§4.11) -/
theorem not_dense_hessCurlMax (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    constS hΩ hb ∈ tsdS Ω ∧ constS hΩ hb ∉ closure ((tsdS Ω : Set (symSub ℝ Ω)) ∩
      ((hessCurlMax ℝ hΩ).d₁.domain ⊓ (hessCurlMax ℝ hΩ).d₀†.domain : Submodule ℝ (symSub
          ℝ Ω))) := by
  refine ⟨constS_mem_tsdS hΩ hb, fun hcl => ?_⟩
  have hsub : (tsdS Ω : Set (symSub ℝ Ω)) ∩
      ((hessCurlMax ℝ hΩ).d₁.domain ⊓ (hessCurlMax ℝ hΩ).d₀†.domain : Submodule ℝ (symSub ℝ Ω)) ⊆
        (fun z => ⟪z, constS hΩ hb⟫_ℝ) ⁻¹' {0} := fun z ⟨hK, hD⟩ =>
    inner_constS_eq_zero_of_ker hΩ hb (mem_ker_of_mem_tsdS hΩ hK hD.2)
  have h0 := closure_minimal hsub (isClosed_singleton.preimage
    (continuous_id.inner continuous_const)) hcl
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at h0
  have h0' : ((constS hΩ hb : symSub ℝ Ω) : L2F ℝ Ω Ix) = 0 := by
    rw [inner_self_eq_zero.1 h0]; rfl
  exact BoundedDomainTSD.constField_diagA_ne_zero hΩ hb hne h0'

/-- `diag(1, -1, 0) ∈ H(curl, S)` with `curl diag(1, -1, 0) = 0`. -/
theorem constS_mem_hessCurlMax_d₁ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∃ h : constS hΩ hb ∈ (hessCurlMax ℝ hΩ).d₁.domain, (hessCurlMax ℝ hΩ).d₁ ⟨_, h⟩ = 0 := by
  obtain ⟨h, e⟩ := smoothField_mem_hessCurlMax_d₁ (Ψ := fun ij _ => BoundedDomainTSD.diagA ij.1
      ij.2)
    hΩ hb (fun _ => contDiff_const) fun i j => by rw [diagA_symm i j]
  exact ⟨h, Subtype.ext (e.trans (smoothField_eq_zero hΩ hb _ fun ij x _ => by simp [curlM, pd]))⟩

/-- **The obstruction behind the refutation for (4.16) does not apply to the printed
placement**: `⟪sym curl B, diag(1, -1, 0)⟫ = 0` for every `B ∈ H̊(sym curl, T)`. -/
theorem inner_adjoint_hessCurlMax_d₁_constS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (B : (hessCurlMax ℝ hΩ).d₁†.domain) : ⟪(hessCurlMax ℝ hΩ).d₁† B, constS hΩ hb⟫_ℝ = 0 := by
  obtain ⟨h, e⟩ := constS_mem_hessCurlMax_d₁ hΩ hb
  have := LinearPMap.adjoint_isFormalAdjoint (hessCurlMax ℝ hΩ).dense₁ B ⟨_, h⟩
  rw [this, e, inner_zero_right]

/-- **Prop 4.16 for the printed placement, and the zero mean propagates** (unconditional): for
TSD data `(0, E₀, B₀) ∈ D(L)` the Hodge wave equation has a classical solution, unique among
strong solutions, and for all `t`: `σ(t) = 0`, `E(t) ∈ ker d₀†` and `∫_Ω E(t) = 0`. So the
zero-mean obstruction is propagated and does not refute Prop 4.19 here.
[QuennevilleBelair2015], Prop. 4.16 -/
theorem hessCurlMax_divFree_propagates (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {U₀ : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ Ω) (symSub ℝ Ω) (trSub ℝ Ω))}
    (hU₀ : U₀ ∈ (hessCurlMax ℝ hΩ).wave.domain) (h0 : (U₀ 0 : L2 ℝ Ω) = 0)
    (h1 : (U₀ 1 : symSub ℝ Ω) ∈ tsdS Ω) (T : ℝ) :
    ∃ U, U 0 = U₀ ∧ Evolution.IsClassicalSolution (hessCurlMax ℝ hΩ).wave (Icc 0 T) 0 U ∧
      (∀ t ∈ Icc 0 T, (U t 0 : L2 ℝ Ω) = 0 ∧
        (U t 1 : symSub ℝ Ω) ∈ (hessCurlMax ℝ hΩ).d₀†.ker ∧
        ∀ a b, ∫ x, Subtype.val (U t 1 : symSub ℝ Ω) (a, b) x ∂volume.restrict Ω = 0) ∧
      ∀ V, V 0 = U₀ → Evolution.IsStrongSolution (hessCurlMax ℝ hΩ).wave (Icc 0 T) 0 V →
        EqOn V U (Icc 0 T) := by
  have hk := mem_ker_of_mem_tsdS hΩ h1 ((hessCurlMax ℝ hΩ).mem_wave_domain.1 hU₀).2.2.1
  have hred := (hessCurlMax ℝ hΩ).reducingSubcomplex_divFreeSub ⊤ fun _ => Submodule.mem_top
  obtain ⟨U, hU0, hU, hK, huniq⟩ := hred.existsUnique_mem hU₀
    ((ShortHilbertComplex.mem_totalSub_divFreeSub _).2
      ⟨h0, hk, Submodule.mem_top (x := (U₀ 2 : trSub ℝ Ω))⟩)
    (Evolution.ForcingClass.admissible_zero _ 0 T) fun _ _ => Submodule.zero_mem _
  refine ⟨U, hU0, hU, fun t ht => ?_, huniq⟩
  obtain ⟨h0', h1', -⟩ := (ShortHilbertComplex.mem_totalSub_divFreeSub _).1 (hK t ht)
  exact ⟨h0', h1', integral_eq_zero_of_mem_ker_hessCurlMax hΩ hb h1'⟩

/-- The adjoint identity of `d₁ = (sym curl)†` against trace-free test fields:
`⟪d₁ E, Φ⟫ = ⟪E, curl Φ⟫`. -/
theorem hessCurlMax_d₁_inner_testField (hΩ : IsOpen Ω) (E : (hessCurlMax ℝ hΩ).d₁.domain)
    {Φ : Ix → R3 → ℝ} (hΦ : IsTestField Ω Φ) (htr : testField hΦ ∈ trSub ℝ Ω) :
    ⟪(((hessCurlMax ℝ hΩ).d₁ E : trSub ℝ Ω) : L2F ℝ Ω Ix), testField hΦ⟫_ℝ =
      ⟪((E : symSub ℝ Ω) : L2F ℝ Ω Ix),
        testField ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply hΦ)⟫_ℝ := by
  obtain ⟨y, hy⟩ := symCurl_mapsTo Φ hΦ ⟨_, htr⟩ rfl
  have hp : ((⟨testField hΦ, htr⟩ : trSub ℝ Ω), y) ∈ (symCurlDivDiv ℝ hΩ).d₀.graph :=
    symCurlOp.mem_graph_minimalVia _ _ (denseVia_symSub hΩ) ⟨Φ, hΦ, rfl, hy⟩
  have e := LinearPMap.adjoint_inner_of_mem_graph (T := (symCurlDivDiv ℝ hΩ).d₀)
    (symCurlDivDiv ℝ hΩ).dense₀ E hp
  simp only at e
  rw [Submodule.coe_inner, Submodule.coe_inner] at e
  change ⟪(((hessCurlMax ℝ hΩ).d₁ E : trSub ℝ Ω) : L2F ℝ Ω Ix), testField hΦ⟫_ℝ =
    ⟪((E : symSub ℝ Ω) : L2F ℝ Ω Ix), (symSub ℝ Ω).subtypeₗᵢ y⟫_ℝ at e
  rw [e, hy, testField_symCurl hΦ, inner_symProj_of_mem]

/-- For trace-free `C`, `⟪C, dev Φ⟫ = ⟪C, Φ⟫`. -/
theorem inner_testField_devF {C : L2F ℝ Ω Ix} (hC : ∑ i, C (i, i) = 0) {G : Ix → R3 → ℝ}
    (hG : IsTestField Ω G) : ⟪C, testField (isTestField_devF hG)⟫_ℝ = ⟪C, testField hG⟫_ℝ := by
  have hg : IsTest Ω (fun y => (∑ k, G (k, k) y) / 3) := by
    have h := (((hG (0, 0)).add (hG (1, 1))).add (hG (2, 2))).const_mul (1 / 3 : ℝ)
    convert h using 1
    funext y
    simp only [Fin.sum_univ_three, Pi.add_apply]
    ring
  have hd := inner_testField_diagOf C hg
  rw [hC, inner_zero_left, inner_testField_eq] at hd
  rw [inner_testField_eq, inner_testField_eq]
  have e : ∀ ij : Ix, ∫ x, C ij x * devF G ij x ∂volume.restrict Ω =
      ∫ x, C ij x * G ij x ∂volume.restrict Ω -
        ∫ x, C ij x * diagOf (fun y => (∑ k, G (k, k) y) / 3) ij x ∂volume.restrict Ω := by
    intro ij
    rw [← integral_sub (integrable_mul _ (hG ij).memLp)
      (integrable_mul _ (isTestField_diagOf hg ij).memLp)]
    congr 1
    ext x
    simp only [devF]
    ring
  rw [Finset.sum_congr rfl fun ij _ => e ij, Finset.sum_sub_distrib, hd, sub_zero]

/-- **`curl (H(curl, S) ∩ L²(TSD)) ⊆ L²(TSD)`** for the printed placement (Lemma 3.5, no
boundary condition): `curl E` is symmetric (`symm_of_weakCurl_tsd`), trace-free, and weakly
divergence-free (`⟪curl E, ∇φ⟫ = ⟪curl E, dev ∇φ⟫ = ⟪E, curl dev ∇φ⟫ = 0`).
[QuennevilleBelair2015], Lemma 3.5, Prop. 4.19 -/
theorem hessCurlMax_d₁_mem_tsdT (hΩ : IsOpen Ω) (u : (hessCurlMax ℝ hΩ).d₁.domain)
    (hu : (u : symSub ℝ Ω) ∈ tsdS Ω) : (hessCurlMax ℝ hΩ).d₁ u ∈ tsdT Ω := by
  have hut : ((u : symSub ℝ Ω) : L2F ℝ Ω Ix) ∈ tsd Ω := hu
  have hC := ((hessCurlMax ℝ hΩ).d₁ u).2
  show (((hessCurlMax ℝ hΩ).d₁ u : trSub ℝ Ω) : L2F ℝ Ω Ix) ∈ tsd Ω
  refine ⟨fun j k => symm_of_weakCurl_tsd hΩ hut (fun ψ hψ => ?_) j k, hC, fun φ hφ => ?_⟩
  · have hS := isTestField_skewOf hψ
    have htr : testField hS ∈ trSub ℝ Ω :=
      testField_mem_trSub hS fun x => by simp [skewOf]
    have e := hessCurlMax_d₁_inner_testField hΩ u hS htr
    rw [inner_testField_eq, inner_testField_curl_eq _ hS] at e
    exact e
  · have hG := isTestField_gradM hφ
    have e0 : testField ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hφ) =
        testField hG :=
      testField_congr _ _ (funext fun ij => funext fun x => by rw [gradOp_apply]; rfl)
    have hD := isTestField_devF hG
    have htr : testField hD ∈ trSub ℝ Ω := testField_mem_trSub hD (devF_trace _)
    rw [e0, ← inner_testField_devF hC hG, hessCurlMax_d₁_inner_testField hΩ u hD htr,
      inner_testField_curl_eq _ (isTestField_devF hG)]
    have hg : Differentiable ℝ fun y => (∑ k, gradM φ (k, k) y) / 3 := by
      have hk : ∀ k, Differentiable ℝ (gradM φ (k, k)) := fun k => (hG (k, k)).differentiable
      have h := (Differentiable.fun_sum (u := Finset.univ) fun k _ => hk k).mul_const ((3 : ℝ)⁻¹)
      simpa [div_eq_mul_inv] using h
    have hcd : ∀ ij x, curlM (devF (gradM φ)) ij x =
        -skewOf (fun i y => -pd i (fun y => (∑ k, gradM φ (k, k) y) / 3) y) ij x := by
      intro ij x
      rw [curlM_devF (fun ij => (hG ij).differentiable) hg, curlM_diagOf,
        curlM_gradM (fun i => (hφ i).contDiff.of_le (by simp)), zero_sub]
    simp only [hcd, mul_neg, integral_neg, Finset.sum_neg_distrib]
    rw [sum_integral_mul_skewOf_eq_zero hut.1, neg_zero]

/-- **`sym curl (H̊(sym curl, T) ∩ L²(TSD)) ⊆ L²(TSD)`** for the printed placement (Lemma 3.5):
`d₁†` here is a restriction of `d₁†` of (4.16). -/
theorem adjoint_hessCurlMax_d₁_mem_tsdS (hΩ : IsOpen Ω) (ρ : (hessCurlMax ℝ hΩ).d₁†.domain)
    (hρ : (ρ : trSub ℝ Ω) ∈ tsdT Ω) : (hessCurlMax ℝ hΩ).d₁† ρ ∈ tsdS Ω := by
  have hle := adjoint_hessCurlMax_d₁_le (𝕜 := ℝ) hΩ
  rw [hle.2 (x := ρ) (y := ⟨_, hle.1 ρ.2⟩) rfl]
  exact adjoint_hessCurl_d₁_mem_tsdS hΩ _ hρ

/-- **`β ∉ H̊(sym curl, T)`** for the printed placement: otherwise `sym curl β = -diag(1, -1, 0)`
would pair to `0` with `diag(1, -1, 0)` (`inner_adjoint_hessCurlMax_d₁_constS`). So the datum
behind the refutation for (4.16) is not admissible here. -/
theorem betaT_not_mem_adjoint_hessCurlMax_d₁ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : betaT hΩ hb ∉ (hessCurlMax ℝ hΩ).d₁†.domain := fun hβ => by
  have hle := adjoint_hessCurlMax_d₁_le (𝕜 := ℝ) hΩ
  obtain ⟨h, hv⟩ := betaT_mem_adjoint hΩ hb (hessCurl ℝ hΩ) le_rfl
  have e := hle.2 (x := ⟨_, hβ⟩) (y := ⟨_, h⟩) rfl
  have h0 := inner_adjoint_hessCurlMax_d₁_constS hΩ hb ⟨_, hβ⟩
  rw [e, hv, inner_neg_left, neg_eq_zero, Submodule.coe_inner] at h0
  change ⟪BoundedDomainTSD.constField hΩ hb BoundedDomainTSD.diagA,
    BoundedDomainTSD.constField hΩ hb BoundedDomainTSD.diagA⟫_ℝ = 0 at h0
  rw [BoundedDomainTSD.inner_constField] at h0
  simp only [BoundedDomainTSD.integral_constField, Fintype.sum_prod_type, Fin.sum_univ_three] at h0
  have hpos := BoundedDomainTSD.volume_real_pos hΩ hb hne
  simp [BoundedDomainTSD.diagA] at h0
  linarith

/-- **The mean of a magnetic field in `H̊(sym curl, T)` is a pairing of its `sym curl`**:
`⟪B, diag(1, -1, 0)⟫ = -⟪sym curl B, β⟫` for every `B ∈ D(d₁†)` of the printed placement. -/
theorem inner_constT_eq_neg_inner_betaS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (B : (hessCurlMax ℝ hΩ).d₁†.domain) :
    ⟪(B : trSub ℝ Ω), constT hΩ hb⟫_ℝ = -⟪(hessCurlMax ℝ hΩ).d₁† B, betaS hΩ hb⟫_ℝ := by
  obtain ⟨hm, em⟩ := smoothField_mem_hessCurlMax_d₁ (Ψ := BoundedDomainTSD.betaField) hΩ hb
    (fun ij => (BoundedDomainTSD.contDiff_betaField ij).of_le (by simp)) betaField_symm
  have e := LinearPMap.adjoint_isFormalAdjoint (hessCurlMax ℝ hΩ).dense₁ B ⟨_, hm⟩
  have e' : ⟪(hessCurlMax ℝ hΩ).d₁† B, betaS hΩ hb⟫_ℝ =
      ⟪(B : trSub ℝ Ω), (hessCurlMax ℝ hΩ).d₁ ⟨_, hm⟩⟫_ℝ := e
  rw [e', Submodule.coe_inner, Submodule.coe_inner, em, BoundedDomainTSD.curl_betaL2,
      inner_neg_right,
    neg_neg]
  rfl

/-- **`diag(1, -1, 0) ∉ H̊(sym curl, T)`** for the printed placement, although it is a
stationary datum of (4.16) (`constT_mem_invariantCore₂`). -/
theorem constT_not_mem_adjoint_hessCurlMax_d₁ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : constT hΩ hb ∉ (hessCurlMax ℝ hΩ).d₁†.domain := fun hc => by
  have hle := adjoint_hessCurlMax_d₁_le (𝕜 := ℝ) hΩ
  obtain ⟨h0, e0⟩ := smoothField_mem_adjoint_hessCurl_d₁
    (Ψ := fun ij _ => BoundedDomainTSD.diagA ij.1 ij.2) hΩ hb (fun _ => contDiff_const)
    (fun _ => by simpa [Matrix.trace] using BoundedDomainTSD.diagA_trace)
  have hz : (hessCurlMax ℝ hΩ).d₁† ⟨_, hc⟩ = 0 := by
    rw [hle.2 (x := ⟨_, hc⟩) (y := ⟨_, h0⟩) rfl]
    refine Subtype.ext ?_
    rw [e0]
    exact smoothField_eq_zero hΩ hb _ fun ij x _ => by simp [symF, curlM, pd]
  have h1 := inner_constT_eq_neg_inner_betaS hΩ hb ⟨_, hc⟩
  rw [hz, inner_zero_left, neg_zero] at h1
  exact constT_ne_zero hΩ hb hne (inner_self_eq_zero.1 h1)

variable (Ω) in
/-- `L²(TSD) ∩ ker d₀†` for the printed placement: TSD fields that are `div div`-free with the
`H̊(div div)` boundary condition. It has the same intersection with `D(L)` as `L²(TSD)`
(`mem_ker_of_mem_tsdS`). -/
def tsdSKer (hΩ : IsOpen Ω) : Submodule ℝ (symSub ℝ Ω) := tsdS Ω ⊓ (hessCurlMax ℝ hΩ).d₀†.ker

theorem isClosed_tsdSKer (hΩ : IsOpen Ω) : IsClosed (tsdSKer Ω hΩ : Set (symSub ℝ Ω)) :=
  ((isClosed_tsd (Ω := Ω)).preimage continuous_subtype_val).inter
    (LinearPMap.isClosed_ker (LinearPMap.adjoint_isClosed (hessCurlMax ℝ hΩ).dense₀))

instance (hΩ : IsOpen Ω) : (tsdSKer Ω hΩ).HasOrthogonalProjection := by
  have : CompleteSpace (tsdSKer Ω hΩ) := (isClosed_tsdSKer hΩ).completeSpace_coe
  infer_instance

/-- `D(L) ∩ ({0} × L²(TSD) × S₂) = D(L) ∩ ({0} × (L²(TSD) ∩ ker d₀†) × S₂)`: the variant
`tsdSKer` changes no datum of Prop 4.19. -/
theorem mem_totalSub_tsdSKer_iff (hΩ : IsOpen Ω) (S₂ : Submodule ℝ (trSub ℝ Ω))
    [S₂.HasOrthogonalProjection] {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ Ω) (symSub ℝ Ω)
      (trSub ℝ Ω))} (hx : x ∈ (hessCurlMax ℝ hΩ).wave.domain) :
    x ∈ HilbertComplex.totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω))
        (tsdS Ω) S₂) ↔
      x ∈ HilbertComplex.totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω))
        (tsdSKer Ω hΩ) S₂) := by
  have hD := (hessCurlMax ℝ hΩ).mem_wave_domain.1 hx
  rw [ShortHilbertComplex.mem_totalSub_family3, ShortHilbertComplex.mem_totalSub_family3]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, ⟨h1, mem_ker_of_mem_tsdS hΩ h1 hD.2.2.1⟩, h2⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, h1.1, h2⟩

theorem constS_not_mem_tsdSKer (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    constS hΩ hb ∉ tsdSKer Ω hΩ := fun h => by
  obtain ⟨y, hy, -⟩ := LinearPMap.mem_ker_iff.1 h.2
  exact constS_not_mem_adjoint_hessCurlMax_d₀ hΩ hb hne (hy ▸ y.2)

/-- **Diagnosis of Prop 4.19 with the boundary conditions of its statement** (`hessCurlMax`),
on every nonempty bounded open `Ω ⊆ ℝ³`, for `K = {0} × L²(TSD) × L²(TSD)`:
1. `L²(TSD) ⊄ ker d₀†` (`diag(1, -1, 0) ∉ H̊(div div, S)`); it holds for `L²(TSD) ∩ ker d₀†`,
   which has the same data in `D(L)` (`mem_totalSub_tsdSKer_iff`);
2. the invariance hypotheses hold (Lemma 3.5 without boundary condition);
3. the projection hypothesis `P_K D(L) ⊆ D(L)` fails, and
   `H(curl, S) ∩ H̊(div div, S) ∩ L²(TSD)` is not dense in `L²(TSD)`;
4. the obstruction behind the refutation for (4.16) is absent:
   `⟪sym curl B, diag(1, -1, 0)⟫ = 0` for every `B ∈ H̊(sym curl, T)`.
[QuennevilleBelair2015], Prop. 4.19 (§4.11) -/
theorem diagnosis_hessCurlMax (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ¬ tsdS Ω ≤ (hessCurlMax ℝ hΩ).d₀†.ker ∧ tsdSKer Ω hΩ ≤ (hessCurlMax ℝ hΩ).d₀†.ker ∧
      (∀ u : (hessCurlMax ℝ hΩ).d₁.domain, (u : symSub ℝ Ω) ∈ tsdS Ω →
        (hessCurlMax ℝ hΩ).d₁ u ∈ tsdT Ω) ∧
      (∀ ρ : (hessCurlMax ℝ hΩ).d₁†.domain, (ρ : trSub ℝ Ω) ∈ tsdT Ω →
        (hessCurlMax ℝ hΩ).d₁† ρ ∈ tsdSKer Ω hΩ) ∧
      (¬ ∀ x ∈ (hessCurlMax ℝ hΩ).wave.domain, (HilbertComplex.totalSub
        (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω)) (tsdS Ω) (tsdT Ω))).starProjection
          x ∈ (hessCurlMax ℝ hΩ).wave.domain) ∧
      constS hΩ hb ∉ closure ((tsdS Ω : Set (symSub ℝ Ω)) ∩
        ((hessCurlMax ℝ hΩ).d₁.domain ⊓ (hessCurlMax ℝ hΩ).d₀†.domain : Submodule ℝ (symSub ℝ Ω))) ∧
      ∀ B : (hessCurlMax ℝ hΩ).d₁†.domain, ⟪(hessCurlMax ℝ hΩ).d₁† B, constS hΩ hb⟫_ℝ = 0 := by
  refine ⟨not_tsdS_le_ker_hessCurlMax hΩ hb hne, inf_le_right, hessCurlMax_d₁_mem_tsdT hΩ,
    fun ρ hρ => ⟨adjoint_hessCurlMax_d₁_mem_tsdS hΩ ρ hρ, ?_⟩,
    not_starProjection_mem_wave_domain_hessCurlMax hΩ hb hne _, (not_dense_hessCurlMax hΩ hb hne).2,
    inner_adjoint_hessCurlMax_d₁_constS hΩ hb⟩
  exact LinearPMap.mem_ker_iff.2 ⟨⟨_, (hessCurlMax ℝ hΩ).toHilbertComplex.adjoint_mapsTo 0 1 2 ρ⟩,
    rfl, (hessCurlMax ℝ hΩ).toHilbertComplex.adjoint_comp_eq_zero 0 1 2 ρ⟩

/-- **Corrected Prop 4.19 for the printed placement, maximal form** (unconditional): for the
wave group of `hessCurlMax` and `K = {0} × (L²(TSD) ∩ ker d₀†) × L²(TSD)`, the invariant core
`K* = {0} × S₁* × S₂*` is a reducing subcomplex, the largest one inside `K`, misses
`diag(1, -1, 0)`, and its data have unique solutions staying in `K* ⊆ K`. Whether `K* ≠ {0}` is
open: the stationary data found for (4.16) are not admissible here
(`constT_not_mem_adjoint_hessCurlMax_d₁`). [QuennevilleBelair2015], Prop. 4.19, corrected -/
theorem invariantCore_tsdSKer (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    (hessCurlMax ℝ hΩ).coreSub (tsdSKer Ω hΩ) (tsdT Ω) = HilbertComplex.totalSub
        (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω))
          ((hessCurlMax ℝ hΩ).invariantCore₁ (tsdSKer Ω hΩ) (tsdT Ω))
          ((hessCurlMax ℝ hΩ).invariantCore₂ (tsdSKer Ω hΩ) (tsdT Ω))) ∧
      (hessCurlMax ℝ hΩ).invariantCore₁ (tsdSKer Ω hΩ) (tsdT Ω) ≤ tsdSKer Ω hΩ ∧
      (hessCurlMax ℝ hΩ).invariantCore₂ (tsdSKer Ω hΩ) (tsdT Ω) ≤ tsdT Ω ∧
      (hessCurlMax ℝ hΩ).toHilbertComplex.ReducingSubcomplex
        (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω))
          ((hessCurlMax ℝ hΩ).invariantCore₁ (tsdSKer Ω hΩ) (tsdT Ω))
          ((hessCurlMax ℝ hΩ).invariantCore₂ (tsdSKer Ω hΩ) (tsdT Ω))) ∧
      (∀ (S₁' : Submodule ℝ (symSub ℝ Ω)) (S₂' : Submodule ℝ (trSub ℝ Ω))
        [S₁'.HasOrthogonalProjection] [S₂'.HasOrthogonalProjection], S₁' ≤ tsdSKer Ω hΩ →
        S₂' ≤ tsdT Ω → (hessCurlMax ℝ hΩ).wave.IsReducing (HilbertComplex.totalSub
          (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω)) S₁' S₂')) →
        S₁' ≤ (hessCurlMax ℝ hΩ).invariantCore₁ (tsdSKer Ω hΩ) (tsdT Ω) ∧
          S₂' ≤ (hessCurlMax ℝ hΩ).invariantCore₂ (tsdSKer Ω hΩ) (tsdT Ω)) ∧
      constS hΩ hb ∉ (hessCurlMax ℝ hΩ).invariantCore₁ (tsdSKer Ω hΩ) (tsdT Ω) ∧
      ∀ U₀ ∈ (hessCurlMax ℝ hΩ).wave.domain, U₀ ∈ (hessCurlMax ℝ hΩ).coreSub (tsdSKer Ω hΩ) (tsdT
          Ω) →
        ∀ T : ℝ, ∃ U, U 0 = U₀ ∧
          Evolution.IsClassicalSolution (hessCurlMax ℝ hΩ).wave (Icc 0 T) 0 U ∧
          (∀ t ∈ Icc 0 T, U t ∈ (hessCurlMax ℝ hΩ).coreSub (tsdSKer Ω hΩ) (tsdT Ω)) ∧
          ∀ V, V 0 = U₀ → Evolution.IsStrongSolution (hessCurlMax ℝ hΩ).wave (Icc 0 T) 0 V →
            EqOn V U (Icc 0 T) :=
  ⟨ShortHilbertComplex.coreSub_eq, ShortHilbertComplex.invariantCore₁_le,
    ShortHilbertComplex.invariantCore₂_le,
    ShortHilbertComplex.reducingSubcomplex_coreSub inf_le_right,
    fun _ _ _ _ h₁ h₂ hred => ShortHilbertComplex.le_invariantCore_of_isReducing h₁ h₂ hred,
    fun h => constS_not_mem_tsdSKer hΩ hb hne (ShortHilbertComplex.invariantCore₁_le h),
    fun _ hU₀ hK T => ShortHilbertComplex.existsUnique_mem_coreSub hU₀ hK 0 T⟩

end Printed

end Feec.Counterexamples.BoundedSymTSD
