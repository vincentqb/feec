module

public import Feec.Counterexamples.BoundedDomainTSD
public import Feec.Models.BoundedDomain.SymCurl

/-!
# Bounded domains: TSD constraints for the Hessian–curl complex (thesis Prop 4.19 refuted)

On an open `Ω ⊆ ℝ³` the thesis' complex (4.16) for Prop 4.19 is the Hessian–curl complex
`H̊²(Ω) --grad grad--> H̊(curl, Ω; S) --curl--> L²(Ω; T)` (`Feec.Models.BoundedDomain.hessCurl`),
with constraint spaces `L²(TSD) ∩ L²(S)` and `L²(TSD) ∩ L²(T)`
(`Feec.Models.BoundedDomain.tsdS`, `tsdT`). Since `H̊(curl, S) ⊆ H̊(curl)` with the same curl,
the zero-mean theorem applies, and on every nonempty bounded open `Ω` TSD data do **not**
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

@[deprecated (since := "2026-10-17")] alias inner_betaL2_curl :=
  Counterexamples.BoundedSymTSD.inner_betaL2_curl
@[deprecated (since := "2026-10-17")] alias betaT_mem_adjoint :=
  Counterexamples.BoundedSymTSD.betaT_mem_adjoint
@[deprecated (since := "2026-10-17")] alias not_propagates_sym :=
  Counterexamples.BoundedSymTSD.tsd_not_propagates

end Feec.Models.BoundedDomain
