module

public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Feec.Ch4.BoundedDomain

/-!
# Bounded domains, continued: `D(curl*) = H(curl)`, Bochner model, second projection hypothesis

Sequel to `Feec.Ch4.BoundedDomain` (same model: `Ω ⊆ ℝ³` open and bounded, `L2M Ω` the
`ℓ²`-sum of nine copies of `L²(Ω)`, `thesisComplex` the complex
`H̊¹(Ω; ℝ³) --grad--> H̊(curl, Ω; ℝ³ˣ³) --curl--> L²(Ω; ℝ³ˣ³)` of [QuennevilleBelair2015, §4.10]).

## Main results

1. *Adjoints* (`mem_adjoint_curlClosure_iff`, `adjoint_curlClosure_of_weakCurl`,
   `thesisComplex_adjoint_d1_iff`, `thesisComplex_adjoint_d0_iff`): for the thesis' complex,
   `D(d1*) = H(curl, M)` (fields with a weak row-wise curl in `L²`, tested against
   `C_c^∞(Ω; ℝ³ˣ³)`, no boundary condition) and `d1*` is the weak curl; `D(d0*) = H(div, M)` and
   `d0* = -div` (weak row-wise divergence).
2. *Bochner model* (`piL2Equiv`, `bochnerM`, `integral_eq_zero_bochner`): for any measure `μ` and
   finite `ι`, `L²(μ; EuclideanSpace ℝ ι) ≃ₗᵢ ⊕ₗ²_{i ∈ ι} L²(μ)` componentwise. With
   `ι = Fin 3 × Fin 3` (Frobenius norm) this identifies `L2M Ω` with the Bochner space
   `L²(Ω; ℝ³ˣ³)`, and with `ι = Fin 3` identifies `L2V Ω` with `L²(Ω; ℝ³)`. The zero-mean theorem
   behind the refutation of the first projection hypothesis is restated for Bochner fields.
3. *The second projection hypothesis of Prop 4.17 is false* (`not_projection_hyp_adjoint`,
   `HcurlM_not_projection`, `thesisComplex_not_projection_hyp2`, `not_projection_hyp_S2`,
   Bochner form `HcurlM_not_projection_bochner`): on every
   nonempty bounded open `Ω ⊆ ℝ³` (ball, cube, smooth or not),
   `P_{L²(TSD)} H(curl, M) ⊄ H(curl, M)`. Consequently the hypothesis `hPD` of
   `Feec.Constraints.prop_4_17` fails a second, independent time: through its `B`-component, for
   every choice of the `E`-constraint space `S1`. These refutations are non-constructive (closed
   graph theorem): no single `B ∈ H(curl)` with `P_{L²(TSD)} B ∉ H(curl)` is exhibited.
4. *Quantitative form* (`projection_unbounded`): for every `C` there is a smooth curl-free `E`
   with `P_{L²(TSD)} E` smooth and `‖curl P_{L²(TSD)} E‖ > C ‖E‖ = C ‖E‖_{H(curl)}`: `P_{L²(TSD)}`
   is unbounded for the `H(curl)` graph norm on smooth fields.
5. *General formula* (`starProjection_smoothField_eq`, `starProjection_grad`):
   `P_{L²(TSD)} ∇w = dev sym ∇w` for `C²` fields `w` with `div dev sym ∇w = 0`.

## The mathematics of 3

Unlike the first hypothesis (whose failure comes from the boundary condition of `H̊(curl)`), there
is no boundary condition on either side here; the obstruction is a loss of regularity. Let
`φ_t = e^{-t x₁} sin(t x₂)` (harmonic) and `w_t = (2/t) φ_t e₃`. Then
* `E_t = ∇w_t` (row 3 equal to `(-2 a_t, 2 p_t, 0)`, `a_t = e^{-t x₁} sin(t x₂)`,
  `p_t = e^{-t x₁} cos(t x₂)`) is smooth with `curl E_t = 0`, so `E_t ∈ H(curl)`;
* `B_t = sym E_t` is symmetric, trace-free (`∂₃ w₃ = 0`) and divergence-free
  (`div B_t = ½ Δw_t = 0`), so `B_t ∈ L²(TSD)`; `E_t - B_t` is skew, hence `⊥ L²(TSD)`; so
  `P_{L²(TSD)} E_t = B_t` (`starProjection_gradFld`);
* pointwise `|curl B_t|² = (t²/2) |E_t|²` (`sum_sq_curlM_symFld`): `curl B_t` costs one more
  derivative than `E_t` (it is `½ ∇ curl w_t`, rows `½ ∂_a curl w_t`).
If `P = P_{L²(TSD)}` mapped `H(curl) = D(d1*)` into itself, `E ↦ curl (P E)` would be an
everywhere-defined linear map on the Banach space `graph(d1*)` with closed graph (`d1*` is closed,
`P` continuous), hence bounded by the **closed graph theorem**:
`‖curl P E‖ ≤ C (‖E‖ + ‖curl E‖)`. For `E = E_t` this reads `(t/√2) ‖E_t‖ ≤ C ‖E_t‖`, false for
`t > √2 C`.

A single explicit counterexample (not formalized; it needs singular integrals): on the cube
`(0, 1)³`, let `φ = Re √(x₁ + i x₂)`, harmonic in the cube with `∇φ ~ ρ^{-1/2}`,
`∇²φ ~ ρ^{-3/2}` near the edge `ρ = |(x₁, x₂)| = 0`; then `E = ∇(φ e₃) ∈ H(curl)` (`curl E = 0`),
`P_{L²(TSD)} E = sym E`, but `curl (sym E) ∉ L²` since `∫ ρ^{-3} ρ dρ = ∞`.

*General form* (`starProjection_grad`, formalized for `C²` fields on `ℝ³`): if
`div dev sym ∇w = 0` in `Ω` (equivalently `Δw + ⅓ ∇ div w = 0`, a Lamé-type system), then
`P_{L²(TSD)} ∇w = dev sym ∇w`, because `∇w - dev sym ∇w = skew ∇w + ⅓ (div w) I` is orthogonal to
symmetric trace-free fields. *Heuristic* (not formalized): row-wise `curl ∇w = 0`, so
`curl sym ∇w = -curl skew ∇w`, which is `±½ (∇ curl w)ᵀ` when `div w = 0` (in general the `dev`
part adds a term in `∇ div w`); hence `curl P_{L²(TSD)} ∇w ∈ L²` asks for `∇ curl w ∈ L²`, one
derivative more than `∇w ∈ H(curl)` provides. A counterexample must therefore have
`curl w ∉ H¹` (harmonic gradients `w = ∇h` give `curl w = 0` and are *not* counterexamples). The
fields `w_t` above have `‖∇ curl w_t‖ ~ t ‖∇w_t‖`, which is what the closed-graph argument uses;
`projection_unbounded` records the resulting unboundedness without the closed graph theorem.

## Correction

[QuennevilleBelair2015, §4.10, Prop 4.17]: both projection "conjectures" are false on bounded
domains. The first (`P_{L²(TSD)} (H̊(curl) ∩ H(div)) ⊆ H̊(curl) ∩ H(div)`) by
`Feec.BoundedDomain.thesisComplex_not_projection_hyp`; the second
(`P_{L²(TSD)} H(curl) ⊆ H(curl)`) by `thesisComplex_not_projection_hyp2`. On the flat torus both
hold (`Feec.Torus`), since there `P_{L²(TSD)}` is a Fourier multiplier commuting with `curl`.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17, the complex (4.14))
* [Brezis2011] (closed graph theorem, weak derivatives)
* [AFW2010], [BruningLesch1992] (Hilbert complexes)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal ContDiff Matrix
open MeasureTheory Set Filter Topology
open scoped LinearPMap

namespace Feec.BoundedDomain

variable {Ω : Set R3}

/-! ## `D(curl*) = H(curl)` -/

/-- `C_c^∞(Ω)` is closed under subtraction. -/
theorem IsTest.sub {f g : R3 → ℝ} (hf : IsTest Ω f) (hg : IsTest Ω g) :
    IsTest Ω (fun x => f x - g x) := by
  have := hf.add (hg.const_mul (-1))
  convert this using 1
  ext x
  simp [sub_eq_add_neg]

/-- The curl of a test field is a test field. -/
theorem isTest_curlM {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Ω (Φ ij)) (ij : Ix) :
    IsTest Ω (curlM Φ ij) :=
  ((hΦ _).pdiff _).sub ((hΦ _).pdiff _)

/-- `(Φ, curl Φ)` lies in the graph of `curlClosure` for `Φ ∈ C_c^∞(Ω; ℝ³ˣ³)`. -/
theorem testField_mem_graph_curlClosure (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Ω (Φ ij)) :
    (testField hΦ, testField (isTest_curlM hΦ)) ∈ (curlClosure (Ω := Ω)).graph := by
  rw [curlClosure_graph hΩ hb]
  exact subset_closure ⟨Φ, hΦ, fun ij => ⟨coeFn_testField hΦ ij,
    coeFn_testField (isTest_curlM hΦ) ij⟩⟩

/-- On `C_c^∞(Ω; ℝ³ˣ³)`, `curlClosure` is the classical curl. -/
theorem curlClosure_testField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Ω (Φ ij)) :
    curlClosure ⟨testField hΦ, mem_domain_curlClosure.2 (testField_mem_HcurlZero hΩ hb hΦ)⟩ =
      testField (isTest_curlM hΦ) :=
  apply_eq_of_mem_graph (testField_mem_graph_curlClosure hΩ hb hΦ) _

variable (Ω) in
/-- `H(curl, Ω; ℝ³ˣ³)` (row-wise curl, **no** boundary condition): `B` has a weak curl
`C ∈ L²(Ω; ℝ³ˣ³)`, `∫ B : curl Φ = ∫ C : Φ` for all `Φ ∈ C_c^∞(Ω; ℝ³ˣ³)`. -/
def HcurlM : Set (L2M Ω) :=
  {B | ∃ C : L2M Ω, ∀ Φ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Φ ij)) →
    ∑ ij, ∫ x, B ij x * curlM Φ ij x ∂volume.restrict Ω =
      ∑ ij, ∫ x, C ij x * Φ ij x ∂volume.restrict Ω}

/-- A point of the curl graph is `(Φ, curl Φ)` as `L²` classes. -/
theorem eq_of_mem_curlGraph {u c : L2M Ω} {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Ω (Φ ij))
    (hp : ∀ ij, (u ij : R3 → ℝ) =ᵐ[volume.restrict Ω] Φ ij ∧
      (c ij : R3 → ℝ) =ᵐ[volume.restrict Ω] curlM Φ ij) :
    u = testField hΦ ∧ c = testField (isTest_curlM hΦ) :=
  ⟨(WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ((hp ij).1.trans (coeFn_testField hΦ ij).symm)),
    (WithLp.ext_iff 2).2 (funext fun ij =>
      Lp.ext ((hp ij).2.trans (coeFn_testField (isTest_curlM hΦ) ij).symm))⟩

/-- If `B` has weak curl `C`, then `B ∈ D(curl*)` and `curl* B = C`. -/
theorem adjoint_curlClosure_of_weakCurl (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {B C : L2M Ω} (hC : ∀ Φ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Φ ij)) →
      ∑ ij, ∫ x, B ij x * curlM Φ ij x ∂volume.restrict Ω =
        ∑ ij, ∫ x, C ij x * Φ ij x ∂volume.restrict Ω) :
    ∃ h : B ∈ (curlClosure (Ω := Ω))†.domain, (curlClosure (Ω := Ω))† ⟨B, h⟩ = C := by
  have key : ∀ u : (curlClosure (Ω := Ω)).domain,
      ⟪C, (u : L2M Ω)⟫ = ⟪B, curlClosure u⟫ := by
    intro u
    have hsub : curlGraph Ω ⊆
        (fun p : L2M Ω × L2M Ω => ⟪B, p.2⟫ - ⟪C, p.1⟫) ⁻¹' {0} := by
      rintro ⟨v, c⟩ ⟨Φ, hΦ, hp⟩
      obtain ⟨rfl, rfl⟩ := eq_of_mem_curlGraph hΦ hp
      simp only [mem_preimage, mem_singleton_iff, sub_eq_zero]
      rw [inner_testField, inner_testField]
      exact hC Φ hΦ
    have h := closure_minimal hsub (isClosed_singleton.preimage
      ((continuous_const.inner continuous_snd).sub (continuous_const.inner continuous_fst)))
      (mem_closure_curlClosure hΩ hb u)
    simp only [mem_preimage, mem_singleton_iff, sub_eq_zero] at h
    exact h.symm
  have hmem := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq (dense_domain_curlClosure hΩ hb) ⟨_, hmem⟩ key⟩

/-- The adjoint identity against test fields: `∫ curl* B : Φ = ∫ B : curl Φ`. -/
theorem adjoint_curlClosure_inner (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (B : (curlClosure (Ω := Ω))†.domain) {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Ω (Φ ij)) :
    ∑ ij, ∫ x, (curlClosure (Ω := Ω))† B ij x * Φ ij x ∂volume.restrict Ω =
      ∑ ij, ∫ x, B.1 ij x * curlM Φ ij x ∂volume.restrict Ω := by
  have e := LinearPMap.adjoint_isFormalAdjoint (dense_domain_curlClosure hΩ hb) B
    ⟨_, mem_domain_curlClosure.2 (testField_mem_HcurlZero hΩ hb hΦ)⟩
  simp only at e
  rw [curlClosure_testField hΩ hb hΦ, inner_testField, inner_testField] at e
  exact e

/-- **`D(curl*) = H(curl, M)`** (no boundary condition) for `curl` on `H̊(curl, M)`, and
`curl*` is the weak curl. -/
theorem mem_adjoint_curlClosure_iff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2M Ω} :
    B ∈ (curlClosure (Ω := Ω))†.domain ↔ B ∈ HcurlM Ω := by
  constructor
  · intro hB
    exact ⟨(curlClosure (Ω := Ω))† ⟨B, hB⟩, fun Φ hΦ =>
      (adjoint_curlClosure_inner hΩ hb ⟨B, hB⟩ hΦ).symm⟩
  · rintro ⟨C, hC⟩
    exact (adjoint_curlClosure_of_weakCurl hΩ hb hC).1


section ThesisAdjoints

open Feec.HilbertComplex2

/-- **`D(d1*) = H(curl, M)` for the thesis' complex** (no boundary condition): `d1 = curl` on
`H̊(curl, M)`, so `D(d1*)` is the space of fields with a weak curl in `L²`. -/
theorem thesisComplex_adjoint_d1_iff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2M Ω} :
    B ∈ (thesisComplex hΩ hb).d1†.domain ↔ B ∈ HcurlM Ω :=
  mem_adjoint_curlClosure_iff hΩ hb

/-- **`d1* = weak curl` for the thesis' complex**: if `C` is a weak curl of `B`, then
`B ∈ D(d1*)` and `d1* B = C`. -/
theorem thesisComplex_adjoint_d1_apply (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {B C : L2M Ω} (hC : ∀ Φ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Φ ij)) →
      ∑ ij, ∫ x, B ij x * curlM Φ ij x ∂volume.restrict Ω =
        ∑ ij, ∫ x, C ij x * Φ ij x ∂volume.restrict Ω) :
    ∃ h : B ∈ (thesisComplex hΩ hb).d1†.domain, (thesisComplex hΩ hb).d1† ⟨B, h⟩ = C :=
  adjoint_curlClosure_of_weakCurl hΩ hb hC

/-- **`D(d0*) = H(div, M)` for the thesis' complex** (row-wise divergence, no boundary
condition). -/
theorem thesisComplex_adjoint_d0_iff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2M Ω} :
    B ∈ (thesisComplex hΩ hb).d0†.domain ↔ B ∈ HdivM Ω :=
  mem_adjoint_gradClosure_iff hΩ hb

/-- **`d0* = -div` for the thesis' complex**: if `D` is a weak row-wise divergence of `B`, then
`B ∈ D(d0*)` and `d0* B = -D`. -/
theorem thesisComplex_adjoint_d0_apply (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {B : L2M Ω} {D : L2V Ω} (hD : ∀ φ : Fin 3 → R3 → ℝ, (∀ i, IsTest Ω (φ i)) →
      ∑ ij : Ix, ∫ x, B ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω =
        -∑ i, ∫ x, D i x * φ i x ∂volume.restrict Ω) :
    ∃ h : B ∈ (thesisComplex hΩ hb).d0†.domain, (thesisComplex hΩ hb).d0† ⟨B, h⟩ = -D :=
  adjoint_gradClosure_of_weakDiv hΩ hb hD

end ThesisAdjoints

/-! ## The Bochner model -/

section Bochner

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (ι : Type*) [Fintype ι]

/-- Componentwise map `L²(μ; ℝ^ι) → ⊕ₗ² L²(μ)`. -/
def toPiL2 : Lp (EuclideanSpace ℝ ι) 2 μ →ₗ[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 μ) :=
  (WithLp.linearEquiv 2 ℝ (ι → Lp ℝ 2 μ)).symm.toLinearMap ∘ₗ
    LinearMap.pi fun i =>
      ((EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).compLpL 2 μ).toLinearMap

variable {μ ι}

/-- The components of `toPiL2 f` are a.e. the coordinates of `f`. -/
theorem toPiL2_apply (f : Lp (EuclideanSpace ℝ ι) 2 μ) (i : ι) :
    (toPiL2 μ ι f i : α → ℝ) =ᵐ[μ] fun x => f x i := by
  change ((EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).compLp f : α → ℝ) =ᵐ[μ] _
  filter_upwards [(EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).coeFn_compLp f] with x hx
  rw [hx]
  rfl

/-- `toPiL2` preserves the `L²` inner product: `∫ ⟪f, g⟫ = Σ_i ∫ f_i g_i`. -/
theorem inner_toPiL2 (f g : Lp (EuclideanSpace ℝ ι) 2 μ) :
    ⟪toPiL2 μ ι f, toPiL2 μ ι g⟫ = ⟪f, g⟫ := by
  rw [PiLp.inner_apply, L2.inner_def]
  simp only [L2.inner_def]
  rw [← integral_finsetSum]
  · refine integral_congr_ae ?_
    have h1 := ae_all_iff.2 fun i => toPiL2_apply f i
    have h2 := ae_all_iff.2 fun i => toPiL2_apply g i
    filter_upwards [h1, h2] with x hx hy
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx i, hy i]
  · exact fun i _ => L2.integrable_inner _ _

/-- `toPiL2` is onto: assemble the components into one `L²` function. -/
theorem toPiL2_surjective : Function.Surjective (toPiL2 μ ι) := by
  intro g
  have hm : MemLp (fun x => (WithLp.toLp 2 fun i => g i x : EuclideanSpace ℝ ι)) 2 μ :=
    MemLp.of_eval_piLp fun i => Lp.memLp (g i)
  refine ⟨hm.toLp _, (WithLp.ext_iff 2).2 (funext fun i => Lp.ext ?_)⟩
  filter_upwards [toPiL2_apply (hm.toLp _) i, hm.coeFn_toLp] with x h1 h2
  rw [h1, h2]

variable (μ ι) in
/-- **`L²(μ; ℝ^ι) ≃ₗᵢ ⊕ₗ²_{i ∈ ι} L²(μ)`**: the Bochner space of `EuclideanSpace`-valued
`L²` functions is isometric to the `ℓ²`-sum of scalar `L²` spaces, componentwise. -/
def piL2Equiv : Lp (EuclideanSpace ℝ ι) 2 μ ≃ₗᵢ[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 μ) :=
  LinearIsometryEquiv.ofSurjective ((toPiL2 μ ι).isometryOfInner inner_toPiL2)
    toPiL2_surjective

/-- The components of `piL2Equiv f` are a.e. the coordinates of `f`. -/
theorem piL2Equiv_apply (f : Lp (EuclideanSpace ℝ ι) 2 μ) (i : ι) :
    (piL2Equiv μ ι f i : α → ℝ) =ᵐ[μ] fun x => f x i :=
  toPiL2_apply f i

end Bochner

/-- The Bochner space `L²(Ω; ℝ³ˣ³)` (matrices as `EuclideanSpace ℝ (Fin 3 × Fin 3)`, i.e. with
the Frobenius norm) is isometric to the model `L2M Ω`. -/
abbrev bochnerM (Ω : Set R3) : Lp (EuclideanSpace ℝ Ix) 2 (volume.restrict Ω) ≃ₗᵢ[ℝ] L2M Ω :=
  piL2Equiv (volume.restrict Ω) Ix

/-- The Bochner space `L²(Ω; ℝ³)` is isometric to the model `L2V Ω`. -/
abbrev bochnerV (Ω : Set R3) : Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume.restrict Ω) ≃ₗᵢ[ℝ] L2V Ω :=
  piL2Equiv (volume.restrict Ω) (Fin 3)

/-- **Zero mean, Bochner form** (`integral_eq_zero_of_mem_TSD_of_mem_HcurlZero` through
`bochnerM`): a Bochner field `F ∈ L²(Ω; ℝ³ˣ³)` lying in `L²(TSD) ∩ H̊(curl)` has
`∫_Ω F = 0 ∈ ℝ³ˣ³`. This is the obstruction refuting the first projection hypothesis of
[QuennevilleBelair2015, §4.10, Prop 4.17] (`thesisComplex_not_projection_hyp`). -/
theorem integral_eq_zero_bochner (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (F : Lp (EuclideanSpace ℝ Ix) 2 (volume.restrict Ω)) (hT : bochnerM Ω F ∈ TSD Ω)
    (hC : bochnerM Ω F ∈ HcurlZero Ω) : ∫ x, F x ∂volume.restrict Ω = 0 := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  have hi : Integrable (fun x => (F x : EuclideanSpace ℝ Ix)) (volume.restrict Ω) :=
    (Lp.memLp F).integrable (by norm_num)
  ext ij
  rw [eval_integral_piLp (fun i => hi.eval_piLp i)]
  rw [← integral_congr_ae (piL2Equiv_apply F ij)]
  simpa using integral_eq_zero_of_mem_TSD_of_mem_HcurlZero hΩ hb hT hC ij.1 ij.2


/-! ## The second projection hypothesis `P_{L²(TSD)} H(curl) ⊆ H(curl)` is false

The test fields `E_t = ∇((2/t) e^{-t x₁} sin(t x₂) e₃)` and `B_t = sym E_t = P_{L²(TSD)} E_t`,
with `|curl B_t| = (t/√2) |E_t|` pointwise; see the module docstring. -/

/-- `a_t(x) = e^{-t x₁} sin(t x₂)` (a harmonic function). -/
def expSin (t : ℝ) (x : R3) : ℝ := Real.exp (-t * x 0) * Real.sin (t * x 1)
/-- `p_t(x) = e^{-t x₁} cos(t x₂)` (its harmonic conjugate partner). -/
def expCos (t : ℝ) (x : R3) : ℝ := Real.exp (-t * x 0) * Real.cos (t * x 1)

/-- `∂_k f = f'(e_k)` from a Fréchet derivative. -/
theorem pd_of_hasFDerivAt {f : R3 → ℝ} {f' : R3 →L[ℝ] ℝ} {x : R3} (h : HasFDerivAt f f' x)
    (k : Fin 3) : pd k f x = f' (Pi.single k 1) := by rw [pd, h.fderiv]

/-- Partial derivatives of `a_t`. -/
theorem pd_expSin (t : ℝ) (k : Fin 3) (x : R3) :
    pd k (expSin t) x = if k = 0 then -t * expSin t x else if k = 1 then t * expCos t x else 0 := by
  have h0 := ((hasFDerivAt_apply (0 : Fin 3) x).const_mul (-t)).exp
  have h1 := ((hasFDerivAt_apply (1 : Fin 3) x).const_mul t).sin
  have h2 : HasFDerivAt (expSin t) _ x := h0.mul h1
  rw [pd_of_hasFDerivAt h2]
  fin_cases k <;> simp [expSin, expCos] <;> ring

/-- Partial derivatives of `p_t`. -/
theorem pd_expCos (t : ℝ) (k : Fin 3) (x : R3) :
    pd k (expCos t) x =
      if k = 0 then -t * expCos t x else if k = 1 then -t * expSin t x else 0 := by
  have h0 := ((hasFDerivAt_apply (0 : Fin 3) x).const_mul (-t)).exp
  have h1 := ((hasFDerivAt_apply (1 : Fin 3) x).const_mul t).cos
  have h2 : HasFDerivAt (expCos t) _ x := h0.mul h1
  rw [pd_of_hasFDerivAt h2]
  fin_cases k <;> simp [expSin, expCos] <;> ring

/-- `a_t` is smooth. -/
theorem contDiff_expSin (t : ℝ) : ContDiff ℝ ∞ (expSin t) := by unfold expSin; fun_prop

/-- `p_t` is smooth. -/
theorem contDiff_expCos (t : ℝ) : ContDiff ℝ ∞ (expCos t) := by unfold expCos; fun_prop

/-- `∂_k (-f) = -∂_k f`. -/
theorem pd_neg (f : R3 → ℝ) (k : Fin 3) (x : R3) : pd k (fun y => -f y) x = -pd k f x := by
  simp [pd]

/-- `E_t = (2/t) ∇(φ_t e₃)`, `φ_t = e^{-t x₁} sin(t x₂)`: the only nonzero row is the third,
`(-2 a_t, 2 p_t, 0)`. A curl-free field (`curlM_gradFld`). -/
def gradFld (t : ℝ) : Ix → R3 → ℝ := fun ij =>
  if ij = (2, 0) then (fun x => -(2 * expSin t x))
  else if ij = (2, 1) then (fun x => 2 * expCos t x) else 0

/-- `B_t = sym E_t`: entries `(1,3), (3,1)` equal to `-a_t` and `(2,3), (3,2)` equal to `p_t`. -/
def symFld (t : ℝ) : Ix → R3 → ℝ := fun ij =>
  if ij = (0, 2) ∨ ij = (2, 0) then (fun x => -expSin t x)
  else if ij = (1, 2) ∨ ij = (2, 1) then expCos t else 0

/-- `S_t = skew E_t = E_t - B_t`. -/
def skewFld (t : ℝ) : Ix → R3 → ℝ := fun ij =>
  if ij = (2, 0) then (fun x => -expSin t x) else if ij = (0, 2) then expSin t
  else if ij = (2, 1) then expCos t else if ij = (1, 2) then (fun x => -expCos t x) else 0

/-- `a_t` is differentiable. -/
theorem differentiable_expSin (t : ℝ) : Differentiable ℝ (expSin t) :=
  (contDiff_expSin t).differentiable (by simp)

/-- `p_t` is differentiable. -/
theorem differentiable_expCos (t : ℝ) : Differentiable ℝ (expCos t) :=
  (contDiff_expCos t).differentiable (by simp)

/-- `curl E_t = 0` (the curl of a gradient). -/
theorem curlM_gradFld (t : ℝ) (ij : Ix) (x : R3) : curlM (gradFld t) ij x = 0 := by
  obtain ⟨i, k⟩ := ij
  simp only [curlM, gradFld]
  fin_cases i <;> fin_cases k <;>
    simp [pd_neg, pd_const_mul (differentiable_expSin t), pd_const_mul (differentiable_expCos t),
      pd_expSin, pd_expCos]

/-- `curl B_t` explicitly: one derivative more than `E_t`, hence a factor `t`. -/
theorem curlM_symFld (t : ℝ) (ij : Ix) (x : R3) : curlM (symFld t) ij x =
    if ij = (0, 0) then -t * expCos t x else if ij = (0, 1) then -t * expSin t x
    else if ij = (1, 0) then -t * expSin t x else if ij = (1, 1) then t * expCos t x else 0 := by
  obtain ⟨i, k⟩ := ij
  simp only [curlM, symFld]
  fin_cases i <;> fin_cases k <;>
    simp [pd_neg, pd_expSin, pd_expCos]

/-- `div B_t = 0` (row-wise): row 3 is `½ Δ φ_t = 0`. -/
theorem div_symFld (t : ℝ) (i : Fin 3) (x : R3) : ∑ j, pd j (symFld t (i, j)) x = 0 := by
  simp only [symFld, Fin.sum_univ_three]
  fin_cases i <;> simp [pd_neg, pd_expSin, pd_expCos]

/-- `B_t` is symmetric. -/
theorem symFld_symm (t : ℝ) (i j : Fin 3) : symFld t (i, j) = symFld t (j, i) := by
  fin_cases i <;> fin_cases j <;> simp [symFld]

/-- `B_t` has zero diagonal, in particular zero trace. -/
theorem symFld_diag (t : ℝ) (i : Fin 3) : symFld t (i, i) = 0 := by
  fin_cases i <;> simp [symFld]

/-- `E_t = B_t + S_t`. -/
theorem gradFld_eq (t : ℝ) (ij : Ix) (x : R3) :
    gradFld t ij x = symFld t ij x + skewFld t ij x := by
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j <;> simp [gradFld, symFld, skewFld] <;> ring

/-- `S_t` is skew. -/
theorem skewFld_skew (t : ℝ) (i j : Fin 3) (x : R3) : skewFld t (j, i) x = -skewFld t (i, j) x := by
  fin_cases i <;> fin_cases j <;> simp [skewFld]

/-- `|E_t|² = 4 e^{-2 t x₁}` pointwise. -/
theorem sum_sq_gradFld (t : ℝ) (x : R3) :
    ∑ ij, gradFld t ij x ^ 2 = 4 * Real.exp (-(t * x 0)) ^ 2 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, gradFld, expSin, expCos]
  simp
  have := Real.sin_sq_add_cos_sq (t * x 1)
  linear_combination 4 * Real.exp (-(t * x 0)) ^ 2 * this

/-- **The key pointwise identity** `|curl B_t|² = (t²/2) |E_t|²`. -/
theorem sum_sq_curlM_symFld (t : ℝ) (x : R3) :
    ∑ ij, curlM (symFld t) ij x ^ 2 = t ^ 2 / 2 * ∑ ij, gradFld t ij x ^ 2 := by
  rw [sum_sq_gradFld]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, curlM_symFld, expSin, expCos]
  simp
  have := Real.sin_sq_add_cos_sq (t * x 1)
  linear_combination 2 * t ^ 2 * Real.exp (-(t * x 0)) ^ 2 * this

/-- `E_t` is smooth. -/
theorem contDiff_gradFld (t : ℝ) (ij : Ix) : ContDiff ℝ ∞ (gradFld t ij) := by
  unfold gradFld
  split_ifs
  exacts [(contDiff_const.mul (contDiff_expSin t)).neg, contDiff_const.mul (contDiff_expCos t),
    contDiff_const]

/-- `B_t` is smooth. -/
theorem contDiff_symFld (t : ℝ) (ij : Ix) : ContDiff ℝ ∞ (symFld t ij) := by
  unfold symFld
  split_ifs
  exacts [(contDiff_expSin t).neg, contDiff_expCos t, contDiff_const]

/-- `S_t` is smooth. -/
theorem contDiff_skewFld (t : ℝ) (ij : Ix) : ContDiff ℝ ∞ (skewFld t ij) := by
  unfold skewFld
  split_ifs
  exacts [(contDiff_expSin t).neg, contDiff_expSin t, contDiff_expCos t, (contDiff_expCos t).neg,
    contDiff_const]

/-- Continuous functions are integrable on a bounded `Ω`. -/
theorem integrable_of_continuous (hb : Bornology.IsBounded Ω) {f : R3 → ℝ} (hf : Continuous f) :
    Integrable f (volume.restrict Ω) :=
  (hf.locallyIntegrable.integrableOn_isCompact hb.isCompact_closure).mono_set subset_closure

/-- `‖Ψ‖² = ∫_Ω |Ψ|²` for a continuous matrix field. -/
theorem norm_sq_smoothField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (Ψ : Ix → R3 → ℝ)
    (hΨ : ∀ ij, Continuous (Ψ ij)) :
    ‖smoothField hΩ hb Ψ hΨ‖ ^ 2 = ∫ x, ∑ ij, Ψ ij x ^ 2 ∂volume.restrict Ω := by
  rw [← real_inner_self_eq_norm_sq, inner_smoothField,
    integral_finsetSum (f := fun ij x => Ψ ij x ^ 2) _ fun ij _ =>
      integrable_of_continuous hb ((hΨ ij).pow 2)]
  refine Finset.sum_congr rfl fun ij _ => integral_congr_ae ?_
  filter_upwards [coeFn_smoothField hΩ hb Ψ hΨ ij] with x hx
  rw [hx, sq]

/-- A continuous field vanishing identically is `0` in `L²`. -/
theorem smoothField_eq_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (Ψ : Ix → R3 → ℝ)
    (hΨ : ∀ ij, Continuous (Ψ ij)) (h0 : ∀ ij x, Ψ ij x = 0) : smoothField hΩ hb Ψ hΨ = 0 := by
  refine (WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_)
  filter_upwards [coeFn_smoothField hΩ hb Ψ hΨ ij, Lp.coeFn_zero ℝ 2 (volume.restrict Ω)]
    with x h1 h2
  rw [h1, h0]
  exact h2.symm

/-- `B_t ∈ L²(TSD)`: symmetric, trace-free and weakly divergence-free. -/
theorem symFld_mem_TSD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ) :
    smoothField hΩ hb (symFld t) (fun ij => (contDiff_symFld t ij).continuous) ∈ TSD Ω := by
  set K := smoothField hΩ hb (symFld t) (fun ij => (contDiff_symFld t ij).continuous)
  have hKc := coeFn_smoothField hΩ hb (symFld t) (fun ij => (contDiff_symFld t ij).continuous)
  refine ⟨fun i j => ?_, ?_, fun φ hφ => ?_⟩
  · refine Lp.ext ?_
    filter_upwards [hKc (i, j), hKc (j, i)] with x h1 h2
    rw [h1, h2, symFld_symm]
  · simp only [Fin.sum_univ_three]
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add (K (0, 0) + K (1, 1)) (K (2, 2)),
      Lp.coeFn_add (K (0, 0)) (K (1, 1)), hKc (0, 0), hKc (1, 1), hKc (2, 2),
      Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5, h6, symFld_diag, symFld_diag, symFld_diag]
    simp
  · have h1 : ∀ ij : Ix, ∫ x, K ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω =
        -∫ x, φ ij.1 x * pd ij.2 (symFld t ij) x ∂volume.restrict Ω := fun ij => by
      rw [integral_congr_ae (g := fun x => pd ij.2 (φ ij.1) x * symFld t ij x)
        ((hKc ij).mono fun x hx => by simp only; rw [hx, mul_comm]),
        integral_pd_mul (hφ ij.1) ((contDiff_symFld t ij).of_le (by simp)) ij.2]
    simp only [h1, Fintype.sum_prod_type, Finset.sum_neg_distrib, neg_eq_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← integral_finsetSum _ fun j _ => integrable_mul_of_compact (hφ i).continuous
      (hφ i).hasCompactSupport (continuous_pd ((contDiff_symFld t _).of_le (by simp)) _)]
    simp [← Finset.mul_sum, div_symFld]

/-- `P_{L²(TSD)} E = B`: `E - B` is skew, hence orthogonal to symmetric fields. -/
theorem starProjection_gradFld (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ) :
    (TSD Ω).starProjection
        (smoothField hΩ hb (gradFld t) (fun ij => (contDiff_gradFld t ij).continuous)) =
      smoothField hΩ hb (symFld t) (fun ij => (contDiff_symFld t ij).continuous) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (symFld_mem_TSD hΩ hb t) fun w hw => ?_
  set S := smoothField hΩ hb (skewFld t) (fun ij => (contDiff_skewFld t ij).continuous)
  have hS := coeFn_smoothField hΩ hb (skewFld t) (fun ij => (contDiff_skewFld t ij).continuous)
  have hES : smoothField hΩ hb (gradFld t) (fun ij => (contDiff_gradFld t ij).continuous) -
      smoothField hΩ hb (symFld t) (fun ij => (contDiff_symFld t ij).continuous) = S := by
    refine (WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_)
    filter_upwards [Lp.coeFn_sub
        (smoothField hΩ hb (gradFld t) (fun ij => (contDiff_gradFld t ij).continuous) ij)
        (smoothField hΩ hb (symFld t) (fun ij => (contDiff_symFld t ij).continuous) ij),
      coeFn_smoothField hΩ hb (gradFld t) (fun ij => (contDiff_gradFld t ij).continuous) ij,
      coeFn_smoothField hΩ hb (symFld t) (fun ij => (contDiff_symFld t ij).continuous) ij, hS ij]
      with x h1 h2 h3 h4
    simp only [PiLp.sub_apply] at h1 ⊢
    rw [h1, Pi.sub_apply, h2, h3, h4, gradFld_eq]
    ring
  have hskew : ∀ i j, S (j, i) = -S (i, j) := fun i j => Lp.ext (by
    filter_upwards [hS (j, i), hS (i, j), Lp.coeFn_neg (S (i, j))] with x h1 h2 h3
    rw [h1, h3, Pi.neg_apply, h2, skewFld_skew])
  rw [hES, PiLp.inner_apply]
  have e1 : ∑ ij : Ix, ⟪S ij, w ij⟫ = ∑ ij : Ix, ⟪S ij.swap, w ij.swap⟫ :=
    (Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun _ => rfl)
  have e2 : ∑ ij : Ix, ⟪S ij.swap, w ij.swap⟫ = -∑ ij : Ix, ⟪S ij, w ij⟫ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ij _ => ?_
    obtain ⟨i, j⟩ := ij
    simp only [Prod.swap_prod_mk]
    rw [hskew, hw.1 j i, inner_neg_left]
  linarith

/-- `‖E_t‖ > 0` on a nonempty open `Ω`. -/
theorem norm_sq_gradFld (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) (t : ℝ) :
    0 < ‖smoothField hΩ hb (gradFld t) (fun ij => (contDiff_gradFld t ij).continuous)‖ ^ 2 := by
  rw [norm_sq_smoothField]
  simp only [sum_sq_gradFld]
  have : NeZero (volume.restrict Ω) := ⟨fun h => by
    have := hΩ.measure_pos volume hne
    rw [← Measure.restrict_apply_self, h] at this
    simp at this⟩
  have : ∀ x : R3, 4 * Real.exp (-(t * x 0)) ^ 2 = Real.exp (Real.log 4 + 2 * -(t * x 0)) := by
    intro x
    rw [Real.exp_add, Real.exp_log (by norm_num), ← Real.exp_nat_mul]
    norm_num
  simp only [this]
  refine integral_exp_pos (integrable_of_continuous hb ?_)
  fun_prop

/-- `‖curl B_t‖² = (t²/2) ‖E_t‖²`. -/
theorem norm_sq_curlSymFld (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ) :
    ‖smoothField hΩ hb (curlM (symFld t))
        (continuous_curlM fun ij => (contDiff_symFld t ij).of_le (by simp))‖ ^ 2 =
      t ^ 2 / 2 *
        ‖smoothField hΩ hb (gradFld t) (fun ij => (contDiff_gradFld t ij).continuous)‖ ^ 2 := by
  rw [norm_sq_smoothField, norm_sq_smoothField, ← integral_const_mul]
  simp only [sum_sq_curlM_symFld]

variable {W0 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0] in
/-- **The second projection hypothesis of Prop 4.17 is false on every nonempty bounded open
`Ω ⊆ ℝ³`**: for any Hilbert complex `H : W0 → L²(Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)` whose `d1` is (a
restriction of) the closure of curl on `C_c^∞` (the thesis' `curl` on `H̊(curl, M)`),
`P_{L²(TSD)}` does not map `D(d1*)` (`= H(curl, M)` for `thesisComplex`) into itself.

Proof: otherwise `E ↦ d1* (P E)` is a linear map on the Banach space `graph(d1*)` with closed
graph, hence bounded (closed graph theorem, `LinearMap.continuous_of_isClosed_graph`); the fields
`E_t ∈ ker d1*`, with `P E_t = B_t` and `‖d1* B_t‖ = (t/√2) ‖E_t‖`, `‖E_t‖ > 0`, violate the bound
for large `t`.

Correction: refutes the second conjecture of [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem not_projection_hyp_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (H : HilbertComplex2 W0 (L2M Ω) (L2M Ω))
    (hd1 : ∀ u : H.d1.domain, ((u : L2M Ω), H.d1 u) ∈ closure (curlGraph Ω)) :
    ¬ ∀ B ∈ H.d1†.domain, (TSD Ω).starProjection B ∈ H.d1†.domain := by
  intro hyp
  set A := H.d1†
  have hAc : A.IsClosed := LinearPMap.adjoint_isClosed H.dense1
  have : CompleteSpace A.graph :=
    (show IsClosed (A.graph : Set (L2M Ω × L2M Ω)) from hAc).completeSpace_coe
  have hdom : ∀ p : A.graph, (TSD Ω).starProjection (p : L2M Ω × L2M Ω).1 ∈ A.domain :=
    fun p => hyp _ (LinearPMap.mem_domain_of_mem_graph (y := (p : L2M Ω × L2M Ω).2) p.2)
  let g0 : A.graph →ₗ[ℝ] A.domain := LinearMap.codRestrict A.domain
    (((TSD Ω).starProjection : L2M Ω →L[ℝ] L2M Ω).toLinearMap ∘ₗ
      (LinearMap.fst ℝ (L2M Ω) (L2M Ω)) ∘ₗ A.graph.subtype) hdom
  let g : A.graph →ₗ[ℝ] L2M Ω := A.toFun ∘ₗ g0
  have hgc : IsClosed (g.graph : Set (A.graph × L2M Ω)) := by
    have e : (g.graph : Set (A.graph × L2M Ω)) =
        (fun q : A.graph × L2M Ω => ((TSD Ω).starProjection (q.1 : L2M Ω × L2M Ω).1, q.2)) ⁻¹'
          (A.graph : Set (L2M Ω × L2M Ω)) := by
      ext ⟨p, F⟩
      simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, mem_preimage]
      constructor
      · rintro rfl
        exact A.mem_graph (g0 p)
      · intro h
        exact (apply_eq_of_mem_graph h (hdom p)).symm
    rw [e]
    exact hAc.preimage (((TSD Ω).starProjection.continuous.comp
      (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd)
  let gc : A.graph →L[ℝ] L2M Ω := ⟨g, g.continuous_of_isClosed_graph hgc⟩
  set t : ℝ := 2 * ‖gc‖ + 1
  set E := smoothField hΩ hb (gradFld t) (fun ij => (contDiff_gradFld t ij).continuous)
  obtain ⟨hE, hE'⟩ := smoothField_mem_adjoint hΩ hb H hd1 (Ψ := gradFld t)
    fun ij => (contDiff_gradFld t ij).of_le (by simp)
  obtain ⟨hB, hB'⟩ := smoothField_mem_adjoint hΩ hb H hd1 (Ψ := symFld t)
    fun ij => (contDiff_symFld t ij).of_le (by simp)
  rw [smoothField_eq_zero hΩ hb _ _ (curlM_gradFld t)] at hE'
  have hpmem : ((E, 0) : L2M Ω × L2M Ω) ∈ A.graph := by
    have := A.mem_graph ⟨E, hE⟩
    rwa [hE'] at this
  let p : A.graph := ⟨(E, 0), hpmem⟩
  have hgp : gc p = smoothField hΩ hb (curlM (symFld t))
      (continuous_curlM fun ij => (contDiff_symFld t ij).of_le (by simp)) := by
    have : g0 p = ⟨_, hB⟩ := Subtype.ext (starProjection_gradFld hΩ hb t)
    change A (g0 p) = _
    rw [this, hB']
  have hnp : ‖p‖ = ‖E‖ := by
    change ‖((E, 0) : L2M Ω × L2M Ω)‖ = ‖E‖
    simp [Prod.norm_def]
  have hbound := gc.le_opNorm p
  rw [hgp, hnp] at hbound
  have h1 := norm_sq_curlSymFld hΩ hb t
  have h2 := norm_sq_gradFld hΩ hb hne t
  have hsq : t ^ 2 / 2 * ‖E‖ ^ 2 ≤ (‖gc‖ * ‖E‖) ^ 2 := by
    rw [← h1]
    exact pow_le_pow_left₀ (norm_nonneg _) hbound 2
  have hc := norm_nonneg gc
  have : t ^ 2 / 2 ≤ ‖gc‖ ^ 2 := by
    rw [mul_pow] at hsq
    exact le_of_mul_le_mul_right hsq h2
  nlinarith

/-- **`P_{L²(TSD)} H(curl, M) ⊄ H(curl, M)`** on every nonempty bounded open `Ω ⊆ ℝ³`, with
`H(curl, M)` the weak-curl space `HcurlM` (no boundary condition).

Correction: refutes the second conjecture of [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem HcurlM_not_projection (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ¬ ∀ B ∈ HcurlM Ω, (TSD Ω).starProjection B ∈ HcurlM Ω := by
  intro h
  refine not_projection_hyp_adjoint hΩ hb hne (thesisComplex hΩ hb) (mem_closure_curlClosure hΩ hb)
    fun B hB => ?_
  exact (mem_adjoint_curlClosure_iff hΩ hb).2 (h B ((mem_adjoint_curlClosure_iff hΩ hb).1 hB))

open Feec.HilbertComplex2 Feec.Constraints in
variable {W0 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0] in
/-- **The projection hypothesis `hPD` of `Feec.Constraints.prop_4_17` fails through its
`B`-component**: for `K = {0} × S1 × L²(TSD)` with **any** closed `S1`, `P_K D(L) ⊄ D(L)`, for
every Hilbert complex `H` whose `d1` is (a restriction of) the closure of curl on `C_c^∞`. This is
independent of the failure through the `E`-component (`not_projection_hyp`).

See [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem not_projection_hyp_S2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (H : HilbertComplex2 W0 (L2M Ω) (L2M Ω))
    (hd1 : ∀ u : H.d1.domain, ((u : L2M Ω), H.d1 u) ∈ closure (curlGraph Ω))
    (S1 : Submodule ℝ (L2M Ω)) [S1.HasOrthogonalProjection] :
    ¬ ∀ x ∈ H.domL, projKc W0 S1 (TSD Ω) x ∈ H.domL := by
  intro hPD
  refine not_projection_hyp_adjoint hΩ hb hne H hd1 fun B hB => ?_
  have hx : ini W0 0 B ∈ H.domL := by
    rw [Feec.Constraints.mem_domL H, tot_ini]
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, hB⟩
  have h := (Feec.Constraints.mem_domL H).1 (hPD _ hx)
  rw [tot_projKc, tot_ini] at h
  exact h.2.2

open Feec.HilbertComplex2 Feec.Constraints in
/-- **The second projection hypothesis fails for the thesis' complex**
`H̊¹ → H̊(curl) → L²`: `P_{L²(TSD)} D(d1*) ⊄ D(d1*)`, and `P_K D(L) ⊄ D(L)` for
`K = {0} × S1 × L²(TSD)`, any `S1`.

Correction: refutes the second conjecture of [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem thesisComplex_not_projection_hyp2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (S1 : Submodule ℝ (L2M Ω)) [S1.HasOrthogonalProjection] :
    (¬ ∀ B ∈ (thesisComplex hΩ hb).d1†.domain,
      (TSD Ω).starProjection B ∈ (thesisComplex hΩ hb).d1†.domain) ∧
    ¬ ∀ x ∈ (thesisComplex hΩ hb).domL,
      projKc (L2V Ω) S1 (TSD Ω) x ∈ (thesisComplex hΩ hb).domL :=
  ⟨not_projection_hyp_adjoint hΩ hb hne _ (mem_closure_curlClosure hΩ hb),
    not_projection_hyp_S2 hΩ hb hne _ (mem_closure_curlClosure hΩ hb) S1⟩

/-! ## Quantitative form: `P_{L²(TSD)}` is unbounded in the `H(curl)` graph norm -/

/-- **`P_{L²(TSD)}` is unbounded for the `H(curl)` graph norm**, explicitly (no closed graph
theorem): for every `C` there is `t` such that `E_t` is smooth, curl-free (so
`‖E_t‖_{H(curl)} = ‖E_t‖`) and in `H(curl, M)`, `P_{L²(TSD)} E_t = B_t` is smooth and in
`H(curl, M)`, yet `‖curl B_t‖ > C ‖E_t‖`.

See [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem projection_unbounded (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (C : ℝ) : ∃ t : ℝ, curlM (gradFld t) = 0 ∧
      smoothField hΩ hb (gradFld t) (fun ij => (contDiff_gradFld t ij).continuous) ∈ HcurlM Ω ∧
      smoothField hΩ hb (symFld t) (fun ij => (contDiff_symFld t ij).continuous) ∈ HcurlM Ω ∧
      (TSD Ω).starProjection
          (smoothField hΩ hb (gradFld t) (fun ij => (contDiff_gradFld t ij).continuous)) =
        smoothField hΩ hb (symFld t) (fun ij => (contDiff_symFld t ij).continuous) ∧
      C * ‖smoothField hΩ hb (gradFld t) (fun ij => (contDiff_gradFld t ij).continuous)‖ <
        ‖smoothField hΩ hb (curlM (symFld t))
          (continuous_curlM fun ij => (contDiff_symFld t ij).of_le (by simp))‖ := by
  set t : ℝ := 2 * |C| + 2
  refine ⟨t, funext fun ij => funext fun x => curlM_gradFld t ij x,
    (thesisComplex_adjoint_d1_iff hΩ hb).1 (smoothField_mem_adjoint hΩ hb (thesisComplex hΩ hb)
      (mem_closure_curlClosure hΩ hb) fun ij => (contDiff_gradFld t ij).of_le (by simp)).1,
    (thesisComplex_adjoint_d1_iff hΩ hb).1 (smoothField_mem_adjoint hΩ hb (thesisComplex hΩ hb)
      (mem_closure_curlClosure hΩ hb) fun ij => (contDiff_symFld t ij).of_le (by simp)).1,
    starProjection_gradFld hΩ hb t, ?_⟩
  set E := smoothField hΩ hb (gradFld t) (fun ij => (contDiff_gradFld t ij).continuous)
  set cB := smoothField hΩ hb (curlM (symFld t))
    (continuous_curlM fun ij => (contDiff_symFld t ij).of_le (by simp))
  have h1 : ‖cB‖ ^ 2 = t ^ 2 / 2 * ‖E‖ ^ 2 := norm_sq_curlSymFld hΩ hb t
  have h2 : 0 < ‖E‖ ^ 2 := norm_sq_gradFld hΩ hb hne t
  have hC : C ^ 2 < t ^ 2 / 2 := by
    have := abs_nonneg C
    have := sq_abs C
    nlinarith
  have key : (|C| * ‖E‖) ^ 2 < ‖cB‖ ^ 2 := by
    rw [h1, mul_pow, sq_abs]
    exact mul_lt_mul_of_pos_right hC h2
  calc C * ‖E‖ ≤ |C| * ‖E‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
    _ < ‖cB‖ := lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) key

/-! ## Bochner form of the second refutation -/

variable (Ω) in
/-- `L²(TSD)` transported to the Bochner space `L²(Ω; ℝ³ˣ³)` through `bochnerM`. -/
abbrev TSDb : Submodule ℝ (Lp (EuclideanSpace ℝ Ix) 2 (volume.restrict Ω)) :=
  (TSD Ω).map ((bochnerM Ω).symm.toLinearEquiv : L2M Ω →ₗ[ℝ] _)

/-- `P_{TSDb} = bochnerM⁻¹ ∘ P_{L²(TSD)} ∘ bochnerM`. -/
theorem bochnerM_starProjection_TSDb (F : Lp (EuclideanSpace ℝ Ix) 2 (volume.restrict Ω)) :
    bochnerM Ω ((TSDb Ω).starProjection F) = (TSD Ω).starProjection (bochnerM Ω F) := by
  rw [Submodule.starProjection_map_apply, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.apply_symm_apply]

/-- **Second projection hypothesis, Bochner form**: on `L²(Ω; ℝ³ˣ³)` (Frobenius norm),
`P_{L²(TSD)} H(curl, M) ⊄ H(curl, M)`, with `L²(TSD)` and `H(curl, M)` transported through the
isometry `bochnerM`.

Correction: refutes the second conjecture of [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem HcurlM_not_projection_bochner (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    ¬ ∀ F : Lp (EuclideanSpace ℝ Ix) 2 (volume.restrict Ω), bochnerM Ω F ∈ HcurlM Ω →
      bochnerM Ω ((TSDb Ω).starProjection F) ∈ HcurlM Ω := by
  intro h
  refine HcurlM_not_projection hΩ hb hne fun B hB => ?_
  have := h ((bochnerM Ω).symm B) (by simpa using hB)
  rwa [bochnerM_starProjection_TSDb, LinearIsometryEquiv.apply_symm_apply] at this

/-! ## General form: `P_{L²(TSD)} ∇w = dev sym ∇w` -/

/-- A `C¹` matrix field that is pointwise symmetric, trace-free and row-wise divergence-free lies
in `L²(TSD)` (generalizes `symFld_mem_TSD`). -/
theorem smoothField_mem_TSD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Φ : Ix → R3 → ℝ}
    (hΦ : ∀ ij, ContDiff ℝ 1 (Φ ij)) (hsym : ∀ i j x, Φ (i, j) x = Φ (j, i) x)
    (htr : ∀ x, ∑ i, Φ (i, i) x = 0) (hdiv : ∀ i x, ∑ j, pd j (Φ (i, j)) x = 0) :
    smoothField hΩ hb Φ (fun ij => (hΦ ij).continuous) ∈ TSD Ω := by
  set K := smoothField hΩ hb Φ (fun ij => (hΦ ij).continuous)
  have hKc := coeFn_smoothField hΩ hb Φ (fun ij => (hΦ ij).continuous)
  refine ⟨fun i j => ?_, ?_, fun φ hφ => ?_⟩
  · refine Lp.ext ?_
    filter_upwards [hKc (i, j), hKc (j, i)] with x h1 h2
    rw [h1, h2, hsym]
  · simp only [Fin.sum_univ_three]
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add (K (0, 0) + K (1, 1)) (K (2, 2)),
      Lp.coeFn_add (K (0, 0)) (K (1, 1)), hKc (0, 0), hKc (1, 1), hKc (2, 2),
      Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5, h6]
    simpa [Fin.sum_univ_three] using htr x
  · have h1 : ∀ ij : Ix, ∫ x, K ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω =
        -∫ x, φ ij.1 x * pd ij.2 (Φ ij) x ∂volume.restrict Ω := fun ij => by
      rw [integral_congr_ae (g := fun x => pd ij.2 (φ ij.1) x * Φ ij x)
        ((hKc ij).mono fun x hx => by simp only; rw [hx, mul_comm]),
        integral_pd_mul (hφ ij.1) (hΦ ij) ij.2]
    simp only [h1, Fintype.sum_prod_type, Finset.sum_neg_distrib, neg_eq_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← integral_finsetSum _ fun j _ => integrable_mul_of_compact (hφ i).continuous
      (hφ i).hasCompactSupport (continuous_pd (hΦ _) _)]
    simp [← Finset.mul_sum, hdiv]

/-- A continuous matrix field whose symmetric part is a scalar multiple of the identity
(`R + Rᵀ = s I`, i.e. `R` = skew + scalar · I) is orthogonal to `L²(TSD)`. -/
theorem inner_smoothField_eq_zero_of_mem_TSD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {R : Ix → R3 → ℝ} (hR : ∀ ij, Continuous (R ij)) {s : R3 → ℝ} (hs : Continuous s)
    (hRs : ∀ i j x, R (i, j) x + R (j, i) x = if i = j then s x else 0)
    {B : L2M Ω} (hB : B ∈ TSD Ω) : ⟪smoothField hΩ hb R hR, B⟫ = 0 := by
  set S := smoothField hΩ hb R hR
  have hS := coeFn_smoothField hΩ hb R hR
  set sL : L2 Ω := (memLp_of_continuous hΩ hb hs).toLp _
  have hsL := MemLp.coeFn_toLp (memLp_of_continuous hΩ hb hs)
  have hsum : ∀ i j, S (i, j) + S (j, i) = if i = j then sL else 0 := fun i j => by
    split_ifs with h
    · refine Lp.ext ?_
      filter_upwards [Lp.coeFn_add (S (i, j)) (S (j, i)), hS (i, j), hS (j, i), hsL]
        with x h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, h3, h4, hRs]
      simp [h]
    · refine Lp.ext ?_
      filter_upwards [Lp.coeFn_add (S (i, j)) (S (j, i)), hS (i, j), hS (j, i),
        Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, h3, h4, hRs]
      simp [h]
  rw [PiLp.inner_apply]
  have e1 : ∑ ij : Ix, ⟪S ij, B ij⟫ = ∑ ij : Ix, ⟪S ij.swap, B ij.swap⟫ :=
    Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun _ => rfl
  have e2 : ∑ ij : Ix, ⟪S ij, B ij⟫ + ∑ ij : Ix, ⟪S ij.swap, B ij.swap⟫ = 0 := by
    rw [← Finset.sum_add_distrib]
    have h3 : ∀ ij : Ix, ⟪S ij, B ij⟫ + ⟪S ij.swap, B ij.swap⟫ =
        if ij.1 = ij.2 then ⟪sL, B (ij.1, ij.1)⟫ else 0 := by
      rintro ⟨i, j⟩
      simp only [Prod.swap_prod_mk]
      rw [hB.1 j i, ← inner_add_left, hsum]
      split_ifs with h
      · subst h; rfl
      · exact inner_zero_left _
    rw [Finset.sum_congr rfl fun ij _ => h3 ij, Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [← inner_sum, hB.2.1, inner_zero_right]
  linarith

/-- **General formula for `P_{L²(TSD)}` on smooth fields**: if `D` is a `C¹` symmetric, trace-free,
row-wise divergence-free field and `G + Gᵀ - 2D = s I` (so `G - D` = skew + scalar · I), then
`P_{L²(TSD)} G = D`. -/
theorem starProjection_smoothField_eq (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {G D : Ix → R3 → ℝ} (hG : ∀ ij, Continuous (G ij)) (hD : ∀ ij, ContDiff ℝ 1 (D ij))
    (hsym : ∀ i j x, D (i, j) x = D (j, i) x) (htr : ∀ x, ∑ i, D (i, i) x = 0)
    (hdiv : ∀ i x, ∑ j, pd j (D (i, j)) x = 0) {s : R3 → ℝ} (hs : Continuous s)
    (hGD : ∀ i j x, G (i, j) x + G (j, i) x - 2 * D (i, j) x = if i = j then s x else 0) :
    (TSD Ω).starProjection (smoothField hΩ hb G hG) =
      smoothField hΩ hb D (fun ij => (hD ij).continuous) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (smoothField_mem_TSD hΩ hb hD hsym htr hdiv) fun B hB => ?_
  have hR : ∀ ij, Continuous (fun x => G ij x - D ij x) := fun ij =>
    (hG ij).sub (hD ij).continuous
  have e : smoothField hΩ hb G hG - smoothField hΩ hb D (fun ij => (hD ij).continuous) =
      smoothField hΩ hb (fun ij x => G ij x - D ij x) hR := by
    refine (WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_)
    filter_upwards [Lp.coeFn_sub (smoothField hΩ hb G hG ij)
        (smoothField hΩ hb D (fun ij => (hD ij).continuous) ij),
      coeFn_smoothField hΩ hb G hG ij, coeFn_smoothField hΩ hb D (fun ij => (hD ij).continuous) ij,
      coeFn_smoothField hΩ hb _ hR ij] with x h1 h2 h3 h4
    simp only [PiLp.sub_apply] at h1 ⊢
    rw [h1, Pi.sub_apply, h2, h3, h4]
  rw [e]
  refine inner_smoothField_eq_zero_of_mem_TSD hΩ hb hR hs (fun i j x => ?_) hB
  have := hGD i j x
  rw [hsym j i x]
  linarith

/-- `C²` functions have `C¹` partial derivatives. -/
theorem contDiff_pd {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (k : Fin 3) : ContDiff ℝ 1 (pd k f) := by
  unfold pd
  exact (hf.fderiv_right (by norm_num)).clm_apply contDiff_const

/-- The gradient `(∇w)_{ij} = ∂_j w_i` of a vector field `w`. -/
def gradW (w : Fin 3 → R3 → ℝ) : Ix → R3 → ℝ := fun ij => pd ij.2 (w ij.1)

/-- `dev sym ∇w = ½ (∇w + ∇wᵀ) - ⅓ (div w) I`. -/
def devSymGrad (w : Fin 3 → R3 → ℝ) : Ix → R3 → ℝ := fun ij x =>
  (pd ij.2 (w ij.1) x + pd ij.1 (w ij.2) x) / 2 -
    (if ij.1 = ij.2 then (1 : ℝ) else 0) * (∑ k, pd k (w k) x) / 3

theorem contDiff_devSymGrad {w : Fin 3 → R3 → ℝ} (hw : ∀ i, ContDiff ℝ 2 (w i)) (ij : Ix) :
    ContDiff ℝ 1 (devSymGrad w ij) :=
  (((contDiff_pd (hw _) _).add (contDiff_pd (hw _) _)).div_const 2).sub
    ((contDiff_const.mul (ContDiff.sum fun k _ => contDiff_pd (hw k) k)).div_const 3)

/-- **`P_{L²(TSD)} ∇w = dev sym ∇w`** for a `C²` vector field `w` on `ℝ³` with
`div dev sym ∇w = 0` in `Ω` (i.e. `Δw + ⅓ ∇ div w = 0`): `∇w - dev sym ∇w = skew ∇w + ⅓ (div w) I`
is orthogonal to `L²(TSD)`. Generalizes `starProjection_gradFld` (`w = w_t`, `div w_t = 0`).

See [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem starProjection_grad (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {w : Fin 3 → R3 → ℝ}
    (hw : ∀ i, ContDiff ℝ 2 (w i)) (hdiv : ∀ i x, ∑ j, pd j (devSymGrad w (i, j)) x = 0) :
    (TSD Ω).starProjection
        (smoothField hΩ hb (gradW w) fun ij => continuous_pd ((hw ij.1).of_le (by norm_num)) ij.2) =
      smoothField hΩ hb (devSymGrad w) fun ij => (contDiff_devSymGrad hw ij).continuous := by
  refine starProjection_smoothField_eq hΩ hb _ (contDiff_devSymGrad hw) (fun i j x => ?_)
    (fun x => ?_) hdiv (s := fun x => 2 / 3 * ∑ k, pd k (w k) x)
    (continuous_const.mul (continuous_finsetSum _ fun k _ =>
      continuous_pd ((hw k).of_le (by norm_num)) k)) (fun i j x => ?_)
  · rcases eq_or_ne i j with rfl | h
    · rfl
    · simp [devSymGrad, h, h.symm, add_comm]
  · simp only [devSymGrad, ↓reduceIte, one_mul, Fin.sum_univ_three]
    ring
  · rcases eq_or_ne i j with rfl | h
    · simp only [gradW, devSymGrad, ↓reduceIte]
      ring
    · simp only [gradW, devSymGrad, h, ↓reduceIte]
      ring

end Feec.BoundedDomain
