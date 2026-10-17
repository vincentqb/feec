module

public import Feec.Counterexamples.BoundedDomainTSD
public import Feec.Models.BoundedDomain.SymCurl

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

## References

* [QuennevilleBelair2015], §4.11 (Prop 4.19, complex (4.16))
* [Arnold2018], §8 (Hessian and div-div complexes)
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
onto `L²(TSD) ∩ L²(S)` is not in `H̊(curl, S)`. Thesis: Prop 4.19 -/
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
Prop 4.19 fails): `diag(1, -1, 0)` is orthogonal to it. Thesis: Prop 4.19 -/
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
`D(d₁) ∩ D(d₀†)`, on every nonempty bounded open `Ω`. Thesis: Prop 4.19 -/
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
Thesis: Prop 4.19 -/
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

end Feec.Counterexamples.BoundedSymTSD

/-! ### Deprecated names -/

namespace Feec.Models.BoundedDomain

end Feec.Models.BoundedDomain
