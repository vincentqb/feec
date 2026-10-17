module

public import Feec.Models.BoundedDomain.SymCurl

/-!
# The minimal and maximal Hessian and double divergence on a bounded domain

On an open `Ω ⊆ ℝ³` the Hessian `grad grad : 𝕜 → 𝕜³ˣ³` and the double divergence
`div div : 𝕜³ˣ³ → 𝕜` (`Feec.Domain.hessOp`, `Feec.Domain.divdivOp`) are formal adjoints
(`Feec.Domain.divdivOp_formalAdj`). Along the scalar embedding `L²(Ω) ↪ L²(Ω; 𝕜^{Unit})`
(`Feec.Domain.L2.toL2F`) their constrained realizations are

* `hessMin`: `grad grad` on `H̊²(Ω)`, the closure on `C_c^∞(Ω)`, closed and densely defined, with
  symmetric (`hessMin_mem_symSub`) and curl-free (`hessMin_graph_curl`) values;
* `divdivMin`: `div div` on `H̊(div div, Ω)`;
* `hessMax = divdivMin†` (the weak Hessian, `H²(Ω)`) and `divdivMax = hessMin†` (the weak double
  divergence, `H(div div, Ω)`), with `hessMin ≤ hessMax`, the adjoints exchanged by von Neumann's
  `T†† = T` (`adjoint_hessMax`, `adjoint_divdivMax`), and
  `ker divdivMax = {B : ⟪B, ∇²φ⟫ = 0 for all φ ∈ C_c^∞(Ω)}` (`mem_ker_divdivMax_iff`).

The Hessian–curl complexes on symmetric fields are in `Feec.Models.BoundedDomain.SymCurl`; the
first operator of the BGG complex (5.1) is `hessMin` (`Feec.Models.BoundedDomain.BGG`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.3 (the BGG complex on a bounded domain, `H̊²`)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], §8 (Hessian and div-div
  complexes)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ContDiff ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology Feec.Domain

namespace Feec.Models.BoundedDomain

variable {𝕜 : Type*} [RCLike 𝕜] {Ω : Set R3}

/-- The identity embedding has dense test fields. -/
theorem denseVia_id (hΩ : IsOpen Ω) {κ : Type*} [Fintype κ] :
    ConstCoeffOp.DenseVia (LinearIsometry.id : L2F 𝕜 Ω κ →ₗᵢ[𝕜] L2F 𝕜 Ω κ) :=
  ConstCoeffOp.denseVia_of_surjective hΩ _ fun y => ⟨y, rfl⟩

variable (𝕜) in
/-- **The minimal Hessian** `grad grad : H̊²(Ω) → L²(Ω; 𝕜³ˣ³)`, the closure of the Hessian on
`C_c^∞(Ω)`. -/
def hessMin (_hΩ : IsOpen Ω) : L2 𝕜 Ω →ₗ.[𝕜] L2F 𝕜 Ω Ix :=
  (hessOp 3).minimalVia (L2.toL2F 𝕜 Ω) LinearIsometry.id

variable (𝕜) in
/-- **The minimal double divergence** `div div : H̊(div div, Ω) → L²(Ω)`. -/
def divdivMin (_hΩ : IsOpen Ω) : L2F 𝕜 Ω Ix →ₗ.[𝕜] L2 𝕜 Ω :=
  (divdivOp 3).minimalVia LinearIsometry.id (L2.toL2F 𝕜 Ω)

theorem isClosed_hessMin (hΩ : IsOpen Ω) : (hessMin 𝕜 hΩ).IsClosed :=
  (hessOp 3).isClosed_minimalVia _ _ (denseVia_id hΩ)

theorem isClosed_divdivMin (hΩ : IsOpen Ω) : (divdivMin 𝕜 hΩ).IsClosed :=
  (divdivOp 3).isClosed_minimalVia _ _ (denseVia_scalar hΩ)

theorem dense_hessMin_domain (hΩ : IsOpen Ω) : Dense ((hessMin 𝕜 hΩ).domain : Set (L2 𝕜 Ω)) :=
  (hessOp 3).dense_minimalVia_domain_of _ _ (denseVia_id hΩ) (denseVia_scalar hΩ)
    fun _ hφ _ _ => ⟨testField ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ), rfl⟩

theorem dense_divdivMin_domain (hΩ : IsOpen Ω) :
    Dense ((divdivMin 𝕜 hΩ).domain : Set (L2F 𝕜 Ω Ix)) :=
  (divdivOp 3).dense_minimalVia_domain_of _ _ (denseVia_scalar hΩ) (denseVia_id hΩ)
    fun _ hΨ _ _ => ⟨testField ((divdivOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hΨ) (),
      (WithLp.ext_iff 2).2 (funext fun _ => rfl)⟩

variable (𝕜) in
/-- **The maximal (weak) Hessian** on `H²(Ω)`, `(div div on H̊(div div))†`. -/
abbrev hessMax (hΩ : IsOpen Ω) : L2 𝕜 Ω →ₗ.[𝕜] L2F 𝕜 Ω Ix := (divdivMin 𝕜 hΩ)†

variable (𝕜) in
/-- **The maximal (weak) double divergence** on `H(div div, Ω)`, `(grad grad on H̊²)†`. -/
abbrev divdivMax (hΩ : IsOpen Ω) : L2F 𝕜 Ω Ix →ₗ.[𝕜] L2 𝕜 Ω := (hessMin 𝕜 hΩ)†

/-- `(hessMax)† = divdivMin` (von Neumann). -/
theorem adjoint_hessMax (hΩ : IsOpen Ω) : (hessMax 𝕜 hΩ)† = divdivMin 𝕜 hΩ :=
  LinearPMap.adjoint_adjoint _ (dense_divdivMin_domain hΩ) (isClosed_divdivMin hΩ)

/-- `(divdivMax)† = hessMin` (von Neumann). -/
theorem adjoint_divdivMax (hΩ : IsOpen Ω) : (divdivMax 𝕜 hΩ)† = hessMin 𝕜 hΩ :=
  LinearPMap.adjoint_adjoint _ (dense_hessMin_domain hΩ) (isClosed_hessMin hΩ)

/-- **`D(divdivMax) = H(div div, Ω)`**: a weak double divergence in `L²(Ω)`. -/
theorem mem_divdivMax_domain_iff (hΩ : IsOpen Ω) {B : L2F 𝕜 Ω Ix} :
    B ∈ (divdivMax 𝕜 hΩ).domain ↔ ∃ D : L2 𝕜 Ω,
      ∀ p ∈ (hessOp 3 : ConstCoeffOp R3 𝕜 _ _).testGraphVia (L2.toL2F 𝕜 Ω) LinearIsometry.id,
        ⟪D, p.1⟫_𝕜 = ⟪B, p.2⟫_𝕜 :=
  (hessOp 3).mem_adjoint_minimalVia_domain_iff _ _ (denseVia_id hΩ) (dense_hessMin_domain hΩ)

/-- **`D(hessMax) = H²(Ω)`**: a weak Hessian in `L²(Ω; 𝕜³ˣ³)`. -/
theorem mem_hessMax_domain_iff (hΩ : IsOpen Ω) {f : L2 𝕜 Ω} :
    f ∈ (hessMax 𝕜 hΩ).domain ↔ ∃ H : L2F 𝕜 Ω Ix,
      ∀ p ∈ (divdivOp 3 : ConstCoeffOp R3 𝕜 _ _).testGraphVia LinearIsometry.id (L2.toL2F 𝕜 Ω),
        ⟪H, p.1⟫_𝕜 = ⟪f, p.2⟫_𝕜 :=
  (divdivOp 3).mem_adjoint_minimalVia_domain_iff _ _ (denseVia_scalar hΩ)
    (dense_divdivMin_domain hΩ)

/-- **`H̊²(Ω) ⊆ H²(Ω)`**: the minimal Hessian is a restriction of the weak one. -/
theorem hessMin_le_hessMax (hΩ : IsOpen Ω) : hessMin 𝕜 hΩ ≤ hessMax 𝕜 hΩ := by
  have key : ∀ u : (hessMin 𝕜 hΩ).domain,
      ∀ p ∈ (divdivOp 3 : ConstCoeffOp R3 𝕜 _ _).testGraphVia LinearIsometry.id (L2.toL2F 𝕜 Ω),
        ⟪hessMin 𝕜 hΩ u, p.1⟫_𝕜 = ⟪(u : L2 𝕜 Ω), p.2⟫_𝕜 := by
    rintro u ⟨x, y⟩ ⟨Ψ, hΨ, h1, h2⟩
    simp only at h1 h2
    obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff _).1
      ((hessOp 3).minimalVia_graph_map _ _ hΩ (denseVia_id hΩ) u)
    simp only at hz1 hz2
    have e := (hessOp 3 : ConstCoeffOp R3 𝕜 Unit Ix).closure_testGraph_inner_testField
      ((hessOp 3).mem_closure_minimal hΩ z) hΨ
    have ec : testField ((hessOp 3 : ConstCoeffOp R3 𝕜 Unit Ix).formalAdj.isTestField_apply hΨ) =
        testField ((divdivOp 3 : ConstCoeffOp R3 𝕜 Ix Unit).isTestField_apply hΨ) :=
      testField_congr _ _ (by rw [hessOp_formalAdj])
    rw [ec, hz2, hz1] at e
    change ⟪hessMin 𝕜 hΩ u, x⟫_𝕜 = _
    rw [show x = testField hΨ from h1]
    exact e.trans (by rw [← h2, LinearIsometry.inner_map_map])
  refine ⟨fun u hu => (mem_hessMax_domain_iff hΩ).2 ⟨_, key ⟨u, hu⟩⟩, ?_⟩
  intro x y hxy
  have hk := key x
  have hmem : (x : L2 𝕜 Ω) ∈ (hessMax 𝕜 hΩ).domain := (mem_hessMax_domain_iff hΩ).2 ⟨_, hk⟩
  have e := (divdivOp 3 : ConstCoeffOp R3 𝕜 _ _).adjoint_minimalVia_apply_eq
    LinearIsometry.id (L2.toL2F 𝕜 Ω) (denseVia_scalar hΩ) (dense_divdivMin_domain hΩ)
    ⟨_, hmem⟩ hk
  have hy : y = ⟨(x : L2 𝕜 Ω), hmem⟩ := Subtype.ext hxy.symm
  subst hy
  exact e.symm

/-- `ker (grad grad)† = H(div div, 0)`: `B ⊥ ∇²φ` for every test function `φ`. -/
theorem mem_ker_divdivMax_iff (hΩ : IsOpen Ω) {B : L2F 𝕜 Ω Ix} :
    B ∈ (divdivMax 𝕜 hΩ).ker ↔ ∀ (φ : Unit → R3 → 𝕜) (hφ : IsTestField Ω φ),
      ⟪B, testField ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ)⟫_𝕜 = 0 := by
  constructor
  · intro hB φ hφ
    obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 hB
    subst hy
    have hp : ((testField hφ () : L2 𝕜 Ω),
        testField ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ)) ∈
          (hessMin 𝕜 hΩ).graph :=
      (hessOp 3).mem_graph_minimalVia _ _ (denseVia_id hΩ)
        ⟨φ, hφ, (WithLp.ext_iff 2).2 (funext fun _ => rfl), rfl⟩
    have e := LinearPMap.adjoint_inner_of_mem_graph (T := hessMin 𝕜 hΩ) (dense_hessMin_domain hΩ)
      y hp
    simp only at e
    rw [hy0, inner_zero_left] at e
    exact e.symm
  · intro hB
    have key : ∀ p ∈ (hessOp 3 : ConstCoeffOp R3 𝕜 _ _).testGraphVia (L2.toL2F 𝕜 Ω)
        LinearIsometry.id, ⟪(0 : L2 𝕜 Ω), p.1⟫_𝕜 = ⟪B, p.2⟫_𝕜 := by
      rintro ⟨x, y⟩ ⟨φ, hφ, -, h2⟩
      simp only at h2
      rw [inner_zero_left]
      have h2' : y = testField ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ) := h2
      change 0 = ⟪B, y⟫_𝕜
      rw [h2', hB φ hφ]
    have hmem := (mem_divdivMax_domain_iff hΩ).2 ⟨0, key⟩
    exact LinearPMap.mem_ker_iff.2 ⟨⟨B, hmem⟩, rfl,
      (hessOp 3).adjoint_minimalVia_apply_eq _ _ (denseVia_id hΩ) (dense_hessMin_domain hΩ) _ key⟩

/-- **`grad grad H̊²` consists of symmetric fields**. -/
theorem hessMin_mem_symSub (hΩ : IsOpen Ω) (u : (hessMin 𝕜 hΩ).domain) :
    hessMin 𝕜 hΩ u ∈ symSub 𝕜 Ω := by
  have hcl : IsClosed {p : L2 𝕜 Ω × L2F 𝕜 Ω Ix | p.2 ∈ symSub 𝕜 Ω} :=
    isClosed_symSub.preimage continuous_snd
  have hsub : ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).testGraphVia (L2.toL2F 𝕜 Ω) LinearIsometry.id :
      Set (L2 𝕜 Ω × L2F 𝕜 Ω Ix)) ⊆ {p | p.2 ∈ symSub 𝕜 Ω} := by
    rintro ⟨x, y⟩ ⟨φ, hφ, -, h2⟩
    simp only at h2
    have h2' : y = testField ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ) := h2
    change y ∈ symSub 𝕜 Ω
    rw [h2']
    exact testField_mem_symSub _ (hessOp_apply_swap fun u => (hφ u).contDiff)
  exact closure_minimal hsub hcl ((hessOp 3).mem_closure_minimalVia _ _ (denseVia_id hΩ) u)

/-- **`grad grad H̊² ⊆ H̊(curl)` with `curl grad grad = 0`**. -/
theorem hessMin_graph_curl (hΩ : IsOpen Ω) (u : (hessMin 𝕜 hΩ).domain) :
    (hessMin 𝕜 hΩ u, (0 : L2F 𝕜 Ω Ix)) ∈ ((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).minimal
        Ω).graph := by
  have hcl : IsClosed {p : L2 𝕜 Ω × L2F 𝕜 Ω Ix |
      (p.2, (0 : L2F 𝕜 Ω Ix)) ∈ ((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).minimal Ω).graph} :=
    ((curlOp 3).isClosed_minimal hΩ).preimage (continuous_snd.prodMk continuous_const)
  have hsub : ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).testGraphVia (L2.toL2F 𝕜 Ω) LinearIsometry.id :
      Set (L2 𝕜 Ω × L2F 𝕜 Ω Ix)) ⊆ {p | (p.2, (0 : L2F 𝕜 Ω Ix)) ∈
        ((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).minimal Ω).graph} := by
    rintro ⟨x, y⟩ ⟨φ, hφ, -, h2⟩
    simp only at h2
    have h2' : y = testField ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ) := h2
    change (y, (0 : L2F 𝕜 Ω Ix)) ∈ ((curlOp 3 : ConstCoeffOp R3 𝕜 Ix Ix).minimal Ω).graph
    rw [h2']
    have h := (curlOp 3).testField_mem_graph_minimal hΩ
      ((hessOp 3 : ConstCoeffOp R3 𝕜 _ _).isTestField_apply hφ)
    rwa [testField_congr _ IsTestField.zero
      (isComplexPair_hess_curl φ fun u => (hφ u).contDiff), testField_zero] at h
  exact closure_minimal hsub hcl ((hessOp 3).mem_closure_minimalVia _ _ (denseVia_id hΩ) u)

end Feec.Models.BoundedDomain
