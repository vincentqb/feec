module

public import Solution.Bridge
public import Feec.Counterexamples.CubeStationary

/-!
# The bridge for the electric boundary conditions

The real fields of `Challenge.lean` on the cube `C = ∏ (bᵢ, bᵢ + s)` with the electric boundary
conditions are those of the minimal grad–curl complex of `Feec`,
`Feec.Models.Cube.Ident.complexCube b s` (`H̊¹ → H̊(curl) → L²`, the bounded-domain complex
`Feec.Models.BoundedDomain.gradCurl` on the cube):

* `IsDiv` and `IsCurl` against `IsCompactTest` are the graphs of the adjoints `d₀† = -div` and
  `d₁† = curl` (`graph_adjoint_grad_iff`, `graph_adjoint_curl_iff`), the weak operators of
  `Feec.Domain.ConstCoeffOp.mem_adjoint_minimal_domain_iff`;
* `IsGrad₀` and `IsCurl₀` are the graphs of `d₀` and `d₁` (`graph_grad_iff`, `graph_curl_iff`), by
  the weak characterization of a closed operator through its adjoint
  (`LinearPMap.mem_graph_iff_of_isClosed`);
* the real states are carried to `PiLp 2 (Ident.WC b s)` by the unitary `toPiRI`;
* `IsWave₀` is the graph of the wave operator (`isWave₀_iff`), `Constraint₀` is
  `{0} × L²(TSD) × L²(TSD)` (`constraint₀_iff`, `isTSD₀_iff`), and the strong solutions are those
  of `Feec.Evolution` (`isStrongSolution₀_iff`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory Set LinearPMap
open scoped InnerProductSpace

@[expose] public noncomputable section

namespace FEEC.ConstraintPropagation

open Feec Feec.Domain Feec.Models.BoundedDomain
open Feec.Models.Cube.Geometry (openCube isOpen_openCube)
open Feec.HilbertComplex (totalSub)
open Feec.ShortHilbertComplex (W3 family3)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

variable {b : Fin 3 → ℝ} {s : ℝ}

/-- The minimal grad–curl complex on the cube (electric boundary conditions). -/
abbrev elec (b : Fin 3 → ℝ) (s : ℝ) := Feec.Models.Cube.Ident.complexCube b s

/-! ### Pairings and test functions -/

theorem inner_eq_sum {ι : Type*} [Fintype ι] (u v : PiLp 2 fun _ : ι => L2 ℝ b s) :
    ⟪u, v⟫_ℝ = ∑ i, ∫ x in cube b s, (u i : (Fin 3 → ℝ) → ℝ) x * (v i : (Fin 3 → ℝ) → ℝ) x := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

theorem isCompactTest_iff (ψ : (Fin 3 → ℝ) → ℝ) :
    IsCompactTest b s ψ ↔ Domain.IsTest (cube b s) ψ :=
  ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2, h.3⟩⟩

/-- The field equal to `ψ` in the slot `p` and to `0` elsewhere. -/
def single {ι : Type*} [DecidableEq ι] (p : ι) (ψ : (Fin 3 → ℝ) → ℝ) : ι → (Fin 3 → ℝ) → ℝ :=
  fun q => if q = p then ψ else 0

theorem isTestField_single {ι : Type*} [DecidableEq ι] (p : ι) {ψ : (Fin 3 → ℝ) → ℝ}
    (hψ : Domain.IsTest (cube b s) ψ) : IsTestField (cube b s) (single p ψ) := fun q => by
  unfold single; split_ifs
  exacts [hψ, Domain.IsTest.zero]

theorem single_self {ι : Type*} [DecidableEq ι] (p : ι) (ψ : (Fin 3 → ℝ) → ℝ) :
    single p ψ p = ψ := by simp [single]

theorem single_of_ne {ι : Type*} [DecidableEq ι] {p q : ι} (h : q ≠ p) (ψ : (Fin 3 → ℝ) → ℝ) :
    single p ψ q = 0 := by simp [single, h]

theorem setIntegral_mul_zero (u : L2 ℝ b s) :
    ∫ x in cube b s, (u : (Fin 3 → ℝ) → ℝ) x * (0 : (Fin 3 → ℝ) → ℝ) x = 0 := by simp

theorem setIntegral_mul_fderiv_zero (u : L2 ℝ b s) (v : Fin 3 → ℝ) :
    ∫ x in cube b s, (u : (Fin 3 → ℝ) → ℝ) x * fderiv ℝ (0 : (Fin 3 → ℝ) → ℝ) x v = 0 := by simp

/-! ### The distributional divergence and curl -/

/-- **`IsDiv` against `C_c^∞` is the weak divergence**: `⟪-D, φ⟫ = ⟪E, grad φ⟫` for all test
fields `φ`. -/
theorem isDiv_compact_iff (E : Mat ℝ b s) (D : Vec ℝ b s) :
    IsDiv b s (fun _ => IsCompactTest b s) E D ↔
      ∀ φ : Fin 3 → (Fin 3 → ℝ) → ℝ, ∀ hφ : IsTestField (cube b s) φ,
        ⟪-D, testField hφ⟫_ℝ =
          ⟪E, testField ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hφ)⟫_ℝ := by
  have key : ∀ φ : Fin 3 → (Fin 3 → ℝ) → ℝ, ∀ hφ : IsTestField (cube b s) φ,
      (⟪-D, testField hφ⟫_ℝ = ∑ i, -∫ x in cube b s, (D i : (Fin 3 → ℝ) → ℝ) x * φ i x) ∧
      ⟪E, testField ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hφ)⟫_ℝ =
        ∑ i, ∑ c, ∫ x in cube b s, (E (i, c) : (Fin 3 → ℝ) → ℝ) x *
          fderiv ℝ (φ i) x (Pi.single c 1) := by
    intro φ hφ
    refine ⟨(inner_testField_eq (-D) hφ).trans (Finset.sum_congr rfl fun i _ => ?_),
      (inner_grad_testField E hφ).trans ?_⟩
    · exact setIntegral_neg_mul (D i) (φ i)
    · rw [Fintype.sum_prod_type]
      rfl
  constructor
  · intro h φ hφ
    refine (key φ hφ).1.trans (Eq.trans ?_ (key φ hφ).2.symm)
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (h i (φ i) ((isCompactTest_iff _).2 (hφ i))).symm
  · intro h a ψ hψ
    have hφ := isTestField_single a ((isCompactTest_iff _).1 hψ)
    have e := ((key _ hφ).1.symm.trans (h _ hφ)).trans (key _ hφ).2
    rw [Finset.sum_eq_single a, Finset.sum_eq_single a] at e
    · simp only [single_self] at e
      exact e.symm
    · intro i _ hi
      simp only [single_of_ne hi, setIntegral_mul_fderiv_zero, Finset.sum_const_zero]
    · simp
    · intro i _ hi
      rw [single_of_ne hi, setIntegral_mul_zero, neg_zero]
    · simp

theorem fin3_add_one_add_two (c : Fin 3) : c + 1 + 2 = c := by fin_cases c <;> rfl
theorem fin3_add_one_add_one (c : Fin 3) : c + 1 + 1 = c + 2 := by fin_cases c <;> rfl
theorem fin3_add_two_add_one (c : Fin 3) : c + 2 + 1 = c := by fin_cases c <;> rfl
theorem fin3_add_two_add_two (c : Fin 3) : c + 2 + 2 = c + 1 := by fin_cases c <;> rfl

/-- `⟪B, curl Φ⟫ = Σ_{ac} (∫ B_{a,c+1} ∂_{c+2} Φ_{ac} - ∫ B_{a,c+2} ∂_{c+1} Φ_{ac})`. -/
theorem inner_curl_expand (B : Mat ℝ b s) {Φ : Ix → (Fin 3 → ℝ) → ℝ}
    (hΦ : IsTestField (cube b s) Φ) :
    ⟪B, testField ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply hΦ)⟫_ℝ =
      ∑ p : Fin 3 × Fin 3,
        ((∫ x in cube b s, (B (p.1, p.2 + 1) : (Fin 3 → ℝ) → ℝ) x *
            fderiv ℝ (Φ p) x (Pi.single (p.2 + 2) 1)) -
          ∫ x in cube b s, (B (p.1, p.2 + 2) : (Fin 3 → ℝ) → ℝ) x *
            fderiv ℝ (Φ p) x (Pi.single (p.2 + 1) 1)) := by
  refine (inner_testField_curl_eq B hΦ).trans ?_
  have hint : ∀ (q : Ix) (r : Ix) (k : Fin 3), Integrable
      (fun x => (B q : (Fin 3 → ℝ) → ℝ) x * partialDeriv k (Φ r) x)
      (volume.restrict (cube b s)) :=
    fun q r k => integrable_mul (B q) ((hΦ r).fderiv_apply (Pi.single k 1)).memLp
  have h1 : ∀ q : Ix, ∫ x in cube b s, (B q : (Fin 3 → ℝ) → ℝ) x * curlM Φ q x =
      (∫ x in cube b s, (B q : (Fin 3 → ℝ) → ℝ) x *
        partialDeriv (q.2 + 1) (Φ (q.1, q.2 + 2)) x) -
        ∫ x in cube b s, (B q : (Fin 3 → ℝ) → ℝ) x * partialDeriv (q.2 + 2) (Φ (q.1, q.2 + 1)) x :=
    fun q => by
      simp only [curlM, mul_sub]
      exact integral_sub (hint _ _ _) (hint _ _ _)
  rw [Finset.sum_congr rfl fun q _ => h1 q, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  · refine Fintype.sum_equiv ((Equiv.refl (Fin 3)).prodCongr (Equiv.addRight 2)) _ _ fun p => ?_
    simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id,
      Equiv.coe_addRight, fin3_add_two_add_one, fin3_add_two_add_two]
    rfl
  · refine Fintype.sum_equiv ((Equiv.refl (Fin 3)).prodCongr (Equiv.addRight 1)) _ _ fun p => ?_
    simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id,
      Equiv.coe_addRight, fin3_add_one_add_two, fin3_add_one_add_one]
    rfl

/-- **`IsCurl` against `C_c^∞` is the weak curl**: `⟪C, Φ⟫ = ⟪B, curl Φ⟫` for all test fields. -/
theorem isCurl_compact_iff (B C : Mat ℝ b s) :
    IsCurl b s (fun _ _ => IsCompactTest b s) B C ↔
      ∀ Φ : Ix → (Fin 3 → ℝ) → ℝ, ∀ hΦ : IsTestField (cube b s) Φ,
        ⟪C, testField hΦ⟫_ℝ =
          ⟪B, testField ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply hΦ)⟫_ℝ := by
  constructor
  · intro h Φ hΦ
    refine (inner_testField_eq C hΦ).trans (Eq.trans ?_ (inner_curl_expand B hΦ).symm)
    refine Finset.sum_congr rfl fun p _ => ?_
    have e := h p.1 p.2 (Φ p) ((isCompactTest_iff _).2 (hΦ p))
    change _ = -∫ x in cube b s, (C p : (Fin 3 → ℝ) → ℝ) x * Φ p x at e
    change ∫ x in cube b s, (C p : (Fin 3 → ℝ) → ℝ) x * Φ p x = _
    linarith
  · intro h a c ψ hψ
    have hΦ := isTestField_single (a, c) ((isCompactTest_iff _).1 hψ)
    have e := ((inner_testField_eq C hΦ).symm.trans (h _ hΦ)).trans (inner_curl_expand B hΦ)
    rw [Finset.sum_eq_single (a, c), Finset.sum_eq_single (a, c)] at e
    · simp only [single_self] at e
      change _ = -∫ x in cube b s, (C (a, c) : (Fin 3 → ℝ) → ℝ) x * ψ x
      change ∫ x in cube b s, (C (a, c) : (Fin 3 → ℝ) → ℝ) x * ψ x = _ at e
      linarith
    · intro q _ hq
      simp only [single_of_ne hq, setIntegral_mul_fderiv_zero, sub_self]
    · simp
    · intro q _ hq
      rw [single_of_ne hq]
      exact setIntegral_mul_zero _
    · simp

/-! ### The graphs of the electric complex -/

theorem mem_graph_adjoint_minimal_iff {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (A : ConstCoeffOp R3 ℝ ι κ) {Ω : Set R3} (hΩ : IsOpen Ω) {v : L2F ℝ Ω κ}
    {w : L2F ℝ Ω ι} :
    (v, w) ∈ (A.minimal Ω)†.graph ↔
      ∀ φ : ι → R3 → ℝ, ∀ hφ : IsTestField Ω φ,
        ⟪w, testField hφ⟫_ℝ = ⟪v, testField (A.isTestField_apply hφ)⟫_ℝ := by
  rw [mem_graph_iff']
  constructor
  · rintro ⟨h, rfl⟩ φ hφ
    exact A.adjoint_minimal_inner_testField hΩ ⟨v, h⟩ hφ
  · intro H
    have hd := (A.mem_adjoint_minimal_domain_iff hΩ).2 ⟨w, H⟩
    exact ⟨hd, A.adjoint_minimal_apply_eq hΩ ⟨v, hd⟩ H⟩

theorem elec_d01 : (elec b s).d 0 1 = (gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).minimal (openCube b s) :=
  rfl

theorem elec_d12 : (elec b s).d 1 2 = (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal (openCube b s) :=
  rfl

/-- The graph of `d₀† = -div` (no boundary condition). -/
theorem graph_adjoint_grad_iff (E : Mat ℝ b s) (w : Vec ℝ b s) :
    ((E, w) : W3 (L2F ℝ (openCube b s) (Fin 3)) (L2F ℝ (openCube b s) Ix)
        (L2F ℝ (openCube b s) Ix) 1 × W3 (L2F ℝ (openCube b s) (Fin 3)) (L2F ℝ (openCube b s) Ix)
        (L2F ℝ (openCube b s) Ix) 0) ∈ ((elec b s).d 0 1)†.graph ↔
      IsDiv b s (fun _ => IsCompactTest b s) E (-w) :=
  by
    rw [elec_d01]
    refine (mem_graph_adjoint_minimal_iff (gradOp 3 3) (isOpen_openCube b s) (v := E)
      (w := w)).trans ?_
    rw [isDiv_compact_iff, neg_neg]
    exact Iff.rfl

/-- The graph of `d₁† = curl` (no boundary condition). -/
theorem graph_adjoint_curl_iff (B C : Mat ℝ b s) :
    ((B, C) : W3 (L2F ℝ (openCube b s) (Fin 3)) (L2F ℝ (openCube b s) Ix)
        (L2F ℝ (openCube b s) Ix) 2 × W3 (L2F ℝ (openCube b s) (Fin 3)) (L2F ℝ (openCube b s) Ix)
        (L2F ℝ (openCube b s) Ix) 1) ∈ ((elec b s).d 1 2)†.graph ↔
      IsCurl b s (fun _ _ => IsCompactTest b s) B C :=
  by
    rw [elec_d12]
    refine (mem_graph_adjoint_minimal_iff (curlOp 3) (isOpen_openCube b s) (v := B)
      (w := C)).trans ?_
    rw [isCurl_compact_iff]
    exact Iff.rfl

/-- The graph of `d₀ = grad` with `σ = 0` on `∂C`. -/
theorem graph_grad_iff (σ : Vec ℝ b s) (G : Mat ℝ b s) :
    ((σ, G) : W3 (L2F ℝ (openCube b s) (Fin 3)) (L2F ℝ (openCube b s) Ix)
        (L2F ℝ (openCube b s) Ix) 0 × W3 (L2F ℝ (openCube b s) (Fin 3)) (L2F ℝ (openCube b s) Ix)
        (L2F ℝ (openCube b s) Ix) 1) ∈ ((elec b s).d 0 1).graph ↔
      IsGrad₀ b s σ G := by
  refine (mem_graph_iff_of_isClosed ((elec b s).dense 0 1) ((elec b s).closed 0 1)
    (x := (σ : W3 (L2F ℝ (openCube b s) (Fin 3)) (L2F ℝ (openCube b s) Ix)
        (L2F ℝ (openCube b s) Ix) 0)) (y := (G : W3 (L2F ℝ (openCube b s) (Fin 3)) (L2F ℝ (openCube b s) Ix)
        (L2F ℝ (openCube b s) Ix) 1))).trans ?_
  constructor
  · intro h E D hD
    obtain ⟨hdom, e⟩ := mem_graph_iff'.1 ((graph_adjoint_grad_iff E (-D)).2 (by rwa [neg_neg]))
    have h' := h ⟨E, hdom⟩
    rw [e] at h'
    change ⟪(-D : Vec ℝ b s), σ⟫_ℝ = ⟪E, G⟫_ℝ at h'
    rw [inner_neg_left, real_inner_comm σ D, real_inner_comm G E, inner_eq_sum,
      inner_eq_sum] at h'
    linarith
  · intro h w
    have hw := (graph_adjoint_grad_iff (w.1 : Mat ℝ b s) (((elec b s).d 0 1)† w)).1
      (((elec b s).d 0 1)†.mem_graph w)
    have e := h _ _ hw
    set T : Vec ℝ b s := ((elec b s).d 0 1)† w with hT
    set W : Mat ℝ b s := w.1 with hW
    have h1 : ⟪T, σ⟫_ℝ = ∑ a, ∫ x in cube b s, (σ a : (Fin 3 → ℝ) → ℝ) x *
        (T a : (Fin 3 → ℝ) → ℝ) x := by rw [real_inner_comm, inner_eq_sum]
    have h2 : ⟪W, G⟫_ℝ = ∑ p, ∫ x in cube b s, (G p : (Fin 3 → ℝ) → ℝ) x *
        (W p : (Fin 3 → ℝ) → ℝ) x := by rw [real_inner_comm, inner_eq_sum]
    have e' : ∀ a, ∫ x in cube b s, (σ a : (Fin 3 → ℝ) → ℝ) x *
        ((-T a : L2 ℝ b s) : (Fin 3 → ℝ) → ℝ) x =
        -∫ x in cube b s, (σ a : (Fin 3 → ℝ) → ℝ) x * (T a : (Fin 3 → ℝ) → ℝ) x := fun a => by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_neg (T a)] with x hx
      rw [hx, Pi.neg_apply, mul_neg]
    simp only [PiLp.neg_apply] at e
    simp only [e', Finset.sum_neg_distrib] at e
    have : ⟪T, σ⟫_ℝ = ⟪W, G⟫_ℝ := by rw [h1, h2]; linarith
    exact this

/-- The graph of `d₁ = curl` with `n × Eₐ = 0` on `∂C`. -/
theorem graph_curl_iff (E C : Mat ℝ b s) :
    ((E, C) : W3 (L2F ℝ (openCube b s) (Fin 3)) (L2F ℝ (openCube b s) Ix)
        (L2F ℝ (openCube b s) Ix) 1 × W3 (L2F ℝ (openCube b s) (Fin 3)) (L2F ℝ (openCube b s) Ix)
        (L2F ℝ (openCube b s) Ix) 2) ∈ ((elec b s).d 1 2).graph ↔
      IsCurl₀ b s E C := by
  refine (mem_graph_iff_of_isClosed ((elec b s).dense 1 2) ((elec b s).closed 1 2)
    (x := (E : W3 (L2F ℝ (openCube b s) (Fin 3)) (L2F ℝ (openCube b s) Ix)
        (L2F ℝ (openCube b s) Ix) 1)) (y := (C : W3 (L2F ℝ (openCube b s) (Fin 3)) (L2F ℝ (openCube b s) Ix)
        (L2F ℝ (openCube b s) Ix) 2))).trans ?_
  constructor
  · intro h B C' hB
    obtain ⟨hdom, e⟩ := mem_graph_iff'.1 ((graph_adjoint_curl_iff B C').2 hB)
    have h' := h ⟨B, hdom⟩
    rw [e] at h'
    change ⟪(C' : Mat ℝ b s), E⟫_ℝ = ⟪B, C⟫_ℝ at h'
    rw [real_inner_comm E C', real_inner_comm C B, inner_eq_sum, inner_eq_sum] at h'
    exact h'
  · intro h w
    have hw := (graph_adjoint_curl_iff (w.1 : Mat ℝ b s) (((elec b s).d 1 2)† w)).1
      (((elec b s).d 1 2)†.mem_graph w)
    have e := h _ _ hw
    set T : Mat ℝ b s := ((elec b s).d 1 2)† w with hT
    set W : Mat ℝ b s := w.1 with hW
    have : ⟪T, E⟫_ℝ = ⟪W, C⟫_ℝ := by
      rw [real_inner_comm E, real_inner_comm C, inner_eq_sum, inner_eq_sum]
      exact e
    exact this

/-! ### The states, the wave operator and the constraint -/

/-- The real states `(σ, E, B)` as elements of `PiLp 2 (Ident.WC b s)`. -/
def toPiRₗ : State ℝ b s ≃ₗ[ℝ] PiLp 2 (Feec.Models.Cube.Ident.WC b s) where
  toFun U := WithLp.toLp 2 fun i => match i with
    | 0 => U.fst
    | 1 => U.snd.fst
    | 2 => U.snd.snd
  invFun x := WithLp.toLp 2 (x 0, WithLp.toLp 2 (x 1, x 2))
  map_add' U V := by ext i; fin_cases i <;> rfl
  map_smul' c U := by ext i; fin_cases i <;> rfl
  left_inv U := rfl
  right_inv x := by ext i; fin_cases i <;> rfl

/-- `toPiRₗ` is unitary. -/
def toPiRI : State ℝ b s ≃ₗᵢ[ℝ] PiLp 2 (Feec.Models.Cube.Ident.WC b s) :=
  toPiRₗ.isometryOfInner fun U V => by
    rw [PiLp.inner_apply, Fin.sum_univ_three, WithLp.prod_inner_apply, WithLp.prod_inner_apply,
      add_assoc]
    rfl

/-- The real states as elements of `PiLp 2 (Ident.WC b s)`, a continuous linear isomorphism. -/
def toPiR : State ℝ b s ≃L[ℝ] PiLp 2 (Feec.Models.Cube.Ident.WC b s) :=
  toPiRI.toContinuousLinearEquiv

/-- **`IsWave₀` is the graph of the wave operator of the electric complex.** -/
theorem isWave₀_iff (U V : State ℝ b s) :
    IsWave₀ b s U V ↔ (toPiR U, toPiR V) ∈ (elec b s).wave.graph := by
  rw [mem_graph_iff']
  constructor
  · rintro ⟨hD, ⟨G, CB, hG, hCB, hV1⟩, hCE⟩
    obtain ⟨h0, e0⟩ := mem_graph_iff'.1 ((graph_grad_iff _ _).2 hG)
    obtain ⟨h1, e1⟩ := mem_graph_iff'.1 ((graph_curl_iff _ _).2 hCE)
    obtain ⟨h1', e1'⟩ := mem_graph_iff'.1 ((graph_adjoint_grad_iff U.snd.fst (-V.fst)).2
      (by rwa [neg_neg]))
    obtain ⟨h2, e2⟩ := mem_graph_iff'.1 ((graph_adjoint_curl_iff _ _).2 hCB)
    have hx : toPiR U ∈ (elec b s).wave.domain :=
      HilbertComplex.mem_wave_domain_fin3 _ h0 h1 h1' h2
    refine ⟨hx, ?_⟩
    have k0 : ((elec b s).wave ⟨_, hx⟩) 0 = V.fst := by
      rw [HilbertComplex.wave_apply_fin3_zero]
      change -((elec b s).d 0 1)† ⟨U.snd.fst, h1'⟩ = V.fst
      rw [e1']
      exact neg_neg _
    have k1 : ((elec b s).wave ⟨_, hx⟩) 1 = V.snd.fst := by
      rw [HilbertComplex.wave_apply_fin3_one]
      change (elec b s).d 0 1 ⟨U.fst, h0⟩ - ((elec b s).d 1 2)† ⟨U.snd.snd, h2⟩ = _
      rw [e0, e2, hV1]
      rfl
    have k2 : ((elec b s).wave ⟨_, hx⟩) 2 = V.snd.snd := by
      rw [HilbertComplex.wave_apply_fin3_two]
      exact e1
    exact PiLp.ext fun i => by fin_cases i; exacts [k0, k1, k2]
  · rintro ⟨hx, e⟩
    obtain ⟨hd, hd'⟩ := (HilbertComplex.mem_wave_domain _).1 hx
    have k0 := congrArg (fun y : PiLp 2 (Feec.Models.Cube.Ident.WC b s) => y 0) e
    have k1 := congrArg (fun y : PiLp 2 (Feec.Models.Cube.Ident.WC b s) => y 1) e
    have k2 := congrArg (fun y : PiLp 2 (Feec.Models.Cube.Ident.WC b s) => y 2) e
    simp only [HilbertComplex.wave_apply_fin3_zero, HilbertComplex.wave_apply_fin3_one,
      HilbertComplex.wave_apply_fin3_two] at k0 k1 k2
    refine ⟨?_, ⟨(elec b s).d 0 1 ⟨U.fst, hd 0 1⟩, ((elec b s).d 1 2)† ⟨U.snd.snd, hd' 1 2⟩,
      (graph_grad_iff _ _).1 (mem_graph_iff'.2 ⟨_, rfl⟩),
      (graph_adjoint_curl_iff _ _).1 (mem_graph_iff'.2 ⟨_, rfl⟩), k1.symm⟩, ?_⟩
    · have e0 : V.fst = -((elec b s).d 0 1)† ⟨U.snd.fst, hd' 0 1⟩ := k0.symm
      rw [e0]
      exact (graph_adjoint_grad_iff _ _).1 (mem_graph_iff'.2 ⟨_, rfl⟩)
    · have e2 : V.snd.snd = (elec b s).d 1 2 ⟨U.snd.fst, hd 1 2⟩ := k2.symm
      rw [e2]
      exact (graph_curl_iff _ _).1 (mem_graph_iff'.2 ⟨hd 1 2, rfl⟩)

/-- **`IsTSD₀` is `L²(TSD)`**, the TSD fields of `Feec` (no boundary condition). -/
theorem isTSD₀_iff (E : Mat ℝ b s) :
    IsTSD₀ b s E ↔ (E : L2F ℝ (openCube b s) Ix) ∈ tsd (openCube b s) := by
  refine Iff.trans ?_ (mem_tsd (Ω := cube b s) (B := E)).symm
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  change IsDiv b s (fun _ => IsCompactTest b s) E 0 ↔ _
  rw [isDiv_compact_iff]
  refine forall_congr' fun φ => forall_congr' fun hφ => ?_
  rw [neg_zero, inner_zero_left, eq_comm]

/-- **`Constraint₀` is `{0} × L²(TSD) × L²(TSD)`.** -/
theorem constraint₀_iff (U : State ℝ b s) :
    Constraint₀ b s U ↔ toPiR U ∈ totalSub (family3
      (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3))) (tsd (openCube b s)) (tsd (openCube b s))) := by
  refine Iff.trans ?_ ShortHilbertComplex.mem_totalSub_family3.symm
  exact and_congr (Submodule.mem_bot ℝ).symm (and_congr (isTSD₀_iff _) (isTSD₀_iff _))

/-! ### Solutions -/

/-- **Strong solutions with electric boundary conditions are those of `Feec`.** -/
theorem isStrongSolution₀_iff {I : Set ℝ} {F U : ℝ → State ℝ b s} :
    IsStrongSolution (IsWave₀ b s) I F U ↔ Evolution.IsStrongSolution (elec b s).wave I
      (fun t => toPiR (F t)) (fun t => toPiR (U t)) := by
  constructor
  · rintro ⟨hc, hd⟩
    refine ⟨toPiR.continuous.comp_continuousOn hc, fun t ht => ?_⟩
    obtain ⟨V, hV, hD⟩ := hd t ht
    refine ⟨toPiR V, (isWave₀_iff _ _).1 hV, ?_⟩
    have := (toPiR (b := b) (s := s)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t hD
    simpa [Function.comp_def, _root_.map_add] using this
  · rintro ⟨hc, hd⟩
    refine ⟨?_, fun t ht => ?_⟩
    · have := (toPiR (b := b) (s := s)).symm.continuous.comp_continuousOn hc
      simpa [Function.comp_def] using this
    · obtain ⟨v, hv, hD⟩ := hd t ht
      refine ⟨toPiR.symm v, (isWave₀_iff _ _).2 (by rwa [ContinuousLinearEquiv.apply_symm_apply]),
        ?_⟩
      have := (toPiR (b := b) (s := s)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt
        t hD
      simpa [Function.comp_def, _root_.map_add] using this

end FEEC.ConstraintPropagation
