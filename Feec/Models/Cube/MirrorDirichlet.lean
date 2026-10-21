module

public import Feec.Models.Cube.Mirror

/-!
# The mirror complex on the cube between the minimal and the maximal realizations

The mirror complex on `Q = (0, ½)³` (`Feec.Models.Cube.Mirror.complexQ`, the compression of the
torus complex along the mirror extensions) is a complex of genuine weak derivatives: it lies
between the **minimal** realizations `H̊¹(Q) → H̊(curl, Q)` (the bounded-domain complex with the
thesis' Dirichlet conditions, `Feec.Models.BoundedDomain.gradCurl`) and the **maximal** ones
`H¹(Q) → H(curl, Q)` (`Feec.Models.BoundedDomain.gradCurlMax`), with the same operators:

* `minimal_le_d₀`, `minimal_le_d₁`: `grad_min ≤ d₀` and `curl_min ≤ d₁`, i.e. `H̊¹(Q) ⊆ D(d₀)`
  and `H̊(curl, Q) ⊆ D(d₁)` with `d₀ = grad`, `d₁ = curl` there (the mirror extension of a test
  field is the classical extension, whose derivatives are the extensions of the derivatives,
  `Feec.Models.Cube.Mirror.grad_J_testField`, `curl_J_testField`);
* `d₀_le_maximal`, `d₁_le_maximal`: `d₀ ≤ grad_max`, `d₁ ≤ curl_max`: `d₀` is the weak gradient
  and `d₁` the weak curl on `Q` (tested against `C_c^∞(Q)`);
* by duality the adjoints are the weak `-div` and the weak `curl`, between the minimal and the
  maximal realizations of the formal adjoints (`adjoint_d₀_le`, `minimal_le_adjoint_d₀`, …);
* `mirror_domain_le_maximal`: `H̊(curl, Q) ⊆ D(d₁) ⊆ H(curl, Q)`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.2 (extension by reflection)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

namespace Feec.Models.Cube.Mirror

open Feec.Domain (IsTestField testField gradOp curlOp ConstCoeffOp)
open Feec.Models.BoundedDomain (R3 gradCurl gradCurlMax)
open Geometry (Q isOpen_Q)

/-! ### The Dirichlet complex is a restriction of the mirror complex -/

/-- **`H̊¹(Q) ⊆ D(d₀)` and `d₀ = grad` there**: the thesis' Dirichlet gradient is a restriction of
the mirror gradient. -/
theorem minimal_le_d₀ : (gradCurl ℂ isOpen_Q).d₀ ≤ complexQ.d 0 1 := by
  refine LinearPMap.le_of_le_graph ?_
  rw [Models.BoundedDomain.gradCurl_d₀, ConstCoeffOp.minimal_graph _ isOpen_Q]
  refine Submodule.topologicalClosure_minimal _ ?_ (complexQ.closed 0 1)
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨h, e⟩ := grad_J_testField hφ
  have hx : testField hφ ∈ (complexQ.d 0 1).domain := mem_complexQ_domain_iff.2 h
  refine (LinearPMap.mem_graph_iff _).2 ⟨⟨_, hx⟩, rfl, embeddingQ.J_injective 1 ?_⟩
  exact (J_complexQ_d (i := 0) (j := 1) ⟨_, hx⟩).trans e

/-- **`H̊(curl, Q) ⊆ D(d₁)` and `d₁ = curl` there**: the thesis' Dirichlet curl is a restriction of
the mirror curl. -/
theorem minimal_le_d₁ : (gradCurl ℂ isOpen_Q).d₁ ≤ complexQ.d 1 2 := by
  refine LinearPMap.le_of_le_graph ?_
  rw [Models.BoundedDomain.gradCurl_d₁, ConstCoeffOp.minimal_graph _ isOpen_Q]
  refine Submodule.topologicalClosure_minimal _ ?_ (complexQ.closed 1 2)
  rintro _ ⟨Φ, hΦ, rfl⟩
  obtain ⟨h, e⟩ := curl_J_testField hΦ
  have hx : testField hΦ ∈ (complexQ.d 1 2).domain := mem_complexQ_domain_iff.2 h
  refine (LinearPMap.mem_graph_iff _).2 ⟨⟨_, hx⟩, rfl, embeddingQ.J_injective 2 ?_⟩
  exact (J_complexQ_d (i := 1) (j := 2) ⟨_, hx⟩).trans e

/-- **The minimal realization `H̊¹(Q) → H̊(curl, Q)` is a restriction of the mirror complex on
`Q`**: `d^{min} ≤ d^{mirror}` for both differentials. -/
theorem minimal_le_mirror :
    (gradCurl ℂ isOpen_Q).d₀ ≤ complexQ.d 0 1 ∧ (gradCurl ℂ isOpen_Q).d₁ ≤ complexQ.d 1 2 :=
  ⟨minimal_le_d₀, minimal_le_d₁⟩

/-! ### The mirror complex consists of weak derivatives -/

/-- Green's formula for `d₀` against test fields: `⟪d₀ σ, Ψ⟫ = ⟪σ, -div Ψ⟫`. -/
theorem inner_d₀_testField (x : (complexQ.d 0 1).domain) {Ψ : Fin 3 × Fin 3 → R3 → ℂ}
    (hΨ : IsTestField (Q (Fin 3)) Ψ) :
    ⟪(complexQ.d 0 1 x : MQ), testField hΨ⟫_ℂ =
      ⟪((x : SpaceQ 0) : VQ), testField
        ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.isTestField_apply hΨ)⟫_ℂ := by
  obtain ⟨h, e⟩ := adjoint_grad_J_testField hΨ
  have hx' := (HilbertComplex.mem_compress_domain_iff eight_pos inner_J
    reducingSubcomplex_range).1 x.2
  have key : ⟪J 1 (complexQ.d 0 1 x), J 1 (testField hΨ)⟫_ℂ =
      ⟪J 0 x, J 0 (testField ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.isTestField_apply
        hΨ))⟫_ℂ := by
    rw [J_complexQ_d, ← e]
    have := LinearPMap.adjoint_isFormalAdjoint (Models.Torus.GradCurl.complex.dense 0 1) ⟨_, h⟩
      ⟨_, hx'⟩
    rw [← inner_conj_symm, ← this, inner_conj_symm]
  have h8 : ((8 : ℝ) : ℂ) * ⟪(complexQ.d 0 1 x : MQ), testField hΨ⟫_ℂ =
      ((8 : ℝ) : ℂ) * ⟪((x : SpaceQ 0) : VQ), testField
        ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.isTestField_apply hΨ)⟫_ℂ :=
    calc _ = ⟪J 1 (complexQ.d 0 1 x), J 1 (testField hΨ)⟫_ℂ := (inner_J 1 _ _).symm
      _ = _ := key
      _ = _ := inner_J 0 _ _
  exact mul_left_cancel₀ (by norm_num) h8

/-- Green's formula for `d₁` against test fields: `⟪d₁ E, Ψ⟫ = ⟪E, curl Ψ⟫`. -/
theorem inner_d₁_testField (x : (complexQ.d 1 2).domain) {Ψ : Fin 3 × Fin 3 → R3 → ℂ}
    (hΨ : IsTestField (Q (Fin 3)) Ψ) :
    ⟪(complexQ.d 1 2 x : MQ), testField hΨ⟫_ℂ =
      ⟪((x : SpaceQ 1) : MQ), testField
        ((curlOp 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.isTestField_apply hΨ)⟫_ℂ := by
  obtain ⟨h, e⟩ := adjoint_curl_J_testField hΨ
  have hx' := (HilbertComplex.mem_compress_domain_iff eight_pos inner_J
    reducingSubcomplex_range).1 x.2
  have key : ⟪J 2 (complexQ.d 1 2 x), J 2 (testField hΨ)⟫_ℂ =
      ⟪J 1 x, J 1 (testField ((curlOp 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.isTestField_apply
        hΨ))⟫_ℂ := by
    rw [J_complexQ_d, ← e]
    have := LinearPMap.adjoint_isFormalAdjoint (Models.Torus.GradCurl.complex.dense 1 2) ⟨_, h⟩
      ⟨_, hx'⟩
    rw [← inner_conj_symm, ← this, inner_conj_symm]
  have h8 : ((8 : ℝ) : ℂ) * ⟪(complexQ.d 1 2 x : MQ), testField hΨ⟫_ℂ =
      ((8 : ℝ) : ℂ) * ⟪((x : SpaceQ 1) : MQ), testField
        ((curlOp 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.isTestField_apply hΨ)⟫_ℂ :=
    calc _ = ⟪J 2 (complexQ.d 1 2 x), J 2 (testField hΨ)⟫_ℂ := (inner_J 2 _ _).symm
      _ = _ := key
      _ = _ := inner_J 1 _ _
  exact mul_left_cancel₀ (by norm_num) h8

/-- **`d₀` is the weak gradient on `Q`**: `D(d₀) ⊆ H¹(Q)` and `d₀ = grad` (the condition
`σ · n = 0` is in the domain). -/
theorem d₀_le_maximal : complexQ.d 0 1 ≤ (gradCurlMax ℂ isOpen_Q).d₀ := by
  refine ⟨fun x hx => (ConstCoeffOp.mem_maximal_domain_iff _ isOpen_Q).2
    ⟨_, fun Ψ hΨ => inner_d₀_testField ⟨x, hx⟩ hΨ⟩, fun x y hxy => ?_⟩
  refine (ConstCoeffOp.maximal_apply_eq _ isOpen_Q y fun Ψ hΨ => ?_).symm
  exact (inner_d₀_testField x hΨ).trans
    (congrArg (fun z : VQ => ⟪z, testField
      ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.isTestField_apply hΨ)⟫_ℂ) hxy)

/-- **`d₁` is the weak curl on `Q`**: `D(d₁) ⊆ H(curl, Q)` and `d₁ = curl`. -/
theorem d₁_le_maximal : complexQ.d 1 2 ≤ (gradCurlMax ℂ isOpen_Q).d₁ := by
  refine ⟨fun x hx => (ConstCoeffOp.mem_maximal_domain_iff _ isOpen_Q).2
    ⟨_, fun Ψ hΨ => inner_d₁_testField ⟨x, hx⟩ hΨ⟩, fun x y hxy => ?_⟩
  refine (ConstCoeffOp.maximal_apply_eq _ isOpen_Q y fun Ψ hΨ => ?_).symm
  exact (inner_d₁_testField x hΨ).trans
    (congrArg (fun z : MQ => ⟪z, testField
      ((curlOp 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.isTestField_apply hΨ)⟫_ℂ) hxy)

/-- **The mirror curl lies between the Dirichlet and the free curl**:
`H̊(curl, Q) ⊆ D(d₁) ⊆ H(curl, Q)`. -/
theorem mirror_domain_le_maximal :
    ((gradCurl ℂ isOpen_Q).d₁.domain : Set MQ) ⊆ ((complexQ.d 1 2).domain : Set (SpaceQ 1)) ∧
      ((complexQ.d 1 2).domain : Set (SpaceQ 1)) ⊆ ((gradCurlMax ℂ isOpen_Q).d₁.domain : Set MQ) :=
  ⟨fun _ hx => minimal_le_d₁.1 hx, fun _ hx => d₁_le_maximal.1 hx⟩

/-! ### The adjoints -/

/-- **`d₀†` is the weak `-div` on `Q`**: `D(d₀†) ⊆ H(div, Q)` (no boundary condition) with
`d₀† = -div`, between the minimal and the maximal realizations of `-div`. -/
theorem adjoint_d₀_le : (complexQ.d 0 1)† ≤ (gradCurl ℂ isOpen_Q).d₀† :=
  LinearPMap.adjoint_le_adjoint_of_le (gradCurl ℂ isOpen_Q).dense₀ minimal_le_d₀

theorem minimal_le_adjoint_d₀ : (gradCurlMax ℂ isOpen_Q).d₀† ≤ (complexQ.d 0 1)† :=
  LinearPMap.adjoint_le_adjoint_of_le (complexQ.dense 0 1) d₀_le_maximal

/-- **`d₁†` is the weak curl on `Q`**: `D(d₁†) ⊆ H(curl, Q)` with `d₁† = curl` (the complementary
condition `B_{ττ} = 0` is in the domain). -/
theorem adjoint_d₁_le : (complexQ.d 1 2)† ≤ (gradCurl ℂ isOpen_Q).d₁† :=
  LinearPMap.adjoint_le_adjoint_of_le (gradCurl ℂ isOpen_Q).dense₁ minimal_le_d₁

theorem minimal_le_adjoint_d₁ : (gradCurlMax ℂ isOpen_Q).d₁† ≤ (complexQ.d 1 2)† :=
  LinearPMap.adjoint_le_adjoint_of_le (complexQ.dense 1 2) d₁_le_maximal

/-- The adjoints in terms of the formal adjoints: `(-div)_min ≤ d₀† ≤ (-div)_max` and
`curl_min ≤ d₁† ≤ curl_max`. -/
theorem adjoint_sandwich :
    ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.minimal (Q (Fin 3)) ≤ (complexQ.d 0 1)† ∧
      (complexQ.d 0 1)† ≤ (gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.maximal (Q (Fin 3))) ∧
    ((curlOp 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.minimal (Q (Fin 3)) ≤ (complexQ.d 1 2)† ∧
      (complexQ.d 1 2)† ≤ (curlOp 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.maximal (Q (Fin 3))) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← Models.BoundedDomain.adjoint_gradCurlMax_d₀]; exact minimal_le_adjoint_d₀
  · rw [← Models.BoundedDomain.adjoint_gradCurl_d₀]; exact adjoint_d₀_le
  · rw [← Models.BoundedDomain.adjoint_gradCurlMax_d₁]; exact minimal_le_adjoint_d₁
  · rw [← Models.BoundedDomain.adjoint_gradCurl_d₁]; exact adjoint_d₁_le

end Feec.Models.Cube.Mirror
