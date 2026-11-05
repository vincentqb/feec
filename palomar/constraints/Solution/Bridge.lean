module

public import Solution.General
public import Feec.Models.Cube.MirrorTrace

/-!
# The bridge from the challenge to `Feec`

The fields of `Challenge.lean` on the cube `C = ∏ (bᵢ, bᵢ + s)` are those of `Feec`
(`Feec.Domain.L2F ℂ (openCube b s) _`, by definition); the states `(σ, E, B)` are carried to
`PiLp 2 (Feec.Models.Cube.Mirror.SpaceCube b s)` by the unitary `toPiI` (`toPi` as a continuous
linear isomorphism): both are `ℓ²` sums of `σ`, `E`, `B`. Along it:

* the test functions `IsTest` are the trace test functions `Mirror.IsTraceTestCube` of the parity
  of each formula (`isTest_iff`), so the Green's formulas `IsGrad`, `IsCurl`, `IsDiv` are those of
  `Mirror.GradTraceCube`, `Mirror.CurlTraceCube`, `Mirror.DivTraceCube`;
* these are the graphs of the differentials of the mirror complex on the cube
  `Mirror.complexCube b s hs` and of their adjoints (`graph_d₀_iff`, `graph_d₁_iff`,
  `graph_adjoint_d₀_iff`, `graph_adjoint_d₁_iff`; from `Mirror.complexQ_d₀_iff`, …, transported
  along `x ↦ (x - b)/(2s)`), so `IsWave` is the graph of its wave operator (`isWave_iff`);
* the constraint `Constraint` is `totalSub (Mirror.tsdCube b s hs)` (`constraint_iff`): the
  constraint of `Feec` is the pull-back of the TSD fibres `{Mᵀ = M, tr M = 0, M ξ = 0}` of the torus
  along the mirror extensions (`extF_mem_constraint_iff`; the divergence by
  `Mirror.MirrorTrace.isGreenClass_isTraceTest`);
* the solutions and the forcing class are those of `Feec.Evolution` (`isStrongSolution_iff`,
  `isClassicalSolution_iff`, `isAdmissible_iff`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory Set LinearPMap
open scoped InnerProductSpace ComplexConjugate

@[expose] public noncomputable section

namespace FEEC.ConstraintPropagation

open Feec Feec.Models.Cube Feec.Models.Cube.Mirror Feec.Models.Cube.MirrorTrace
open Feec.Models.Cube.MirrorTorus (sgn sgn_mul_self)
open Feec.HilbertComplex (totalSub)
open Feec.Models.BoundedDomain (R3)

variable {𝕜 : Type*} [RCLike 𝕜] {b : Fin 3 → ℝ} {s : ℝ}

/-! ### Signs and test functions -/

theorem sgn_eq_neg_one (k a : Fin 3) : sgn k a = -1 ↔ k = a := by
  unfold sgn; split_ifs with h
  · simp [h]
  · exact ⟨fun e => by norm_num at e, fun e => absurd e.symm h⟩

theorem sgn_cases (k a : Fin 3) : sgn k a = if k = a then -1 else 1 := by
  unfold sgn; split_ifs with h h' h' <;> simp_all [eq_comm]

theorem cE_eq_neg_one (a c j : Fin 3) : cE (a, c) j = -1 ↔ ¬(j = a ↔ j = c) := by
  simp only [cE, sgn_cases]
  by_cases h1 : j = a <;> by_cases h2 : j = c <;> simp [h1, h2] <;> norm_num

theorem cB_eq_neg_one (a c j : Fin 3) : cB (a, c) j = -1 ↔ (j = a ↔ j = c) := by
  simp only [cB, sgn_cases]
  by_cases h1 : j = a <;> by_cases h2 : j = c <;> simp [h1, h2] <;> norm_num

theorem cV_eq_neg_one (a j : Fin 3) : cV a j = -1 ↔ j = a := sgn_eq_neg_one j a

theorem cPV_eq_neg_one (a j : Fin 3) : cPV a j = -1 ↔ j ≠ a := by
  simp only [cPV, sgn_cases]
  by_cases h1 : j = a
  · simp [h1]; norm_num
  · simp [h1]

/-- The test functions of the challenge are the trace test functions of `Feec`. -/
theorem isTest_iff {S : Set (Fin 3)} {c : Fin 3 → ℂ} (hS : ∀ j, j ∈ S ↔ c j = -1)
    (ψ : (Fin 3 → ℝ) → ℂ) : IsTest b s S ψ ↔ IsTraceTestCube b s c ψ :=
  ⟨fun h => ⟨h.1, fun j hj => h.2 j ((hS j).2 hj)⟩,
    fun h => ⟨h.1, fun j hj => h.2 j ((hS j).1 hj)⟩⟩

/-! ### The Green's formulas -/

theorem isGrad_iff (σ : Vec ℂ b s) (G : Mat ℂ b s) : IsGrad b s σ G ↔ GradTraceCube b s σ G :=
  forall_congr' fun a => forall_congr' fun c => forall_congr' fun ψ =>
    imp_congr_left (isTest_iff (fun j => (cE_eq_neg_one a c j).symm) ψ)

theorem isCurlE_iff (E C : Mat ℂ b s) :
    IsCurl b s (fun a c => IsTest b s {j | j = a ↔ j = c}) E C ↔ CurlTraceCube b s cB E C :=
  forall_congr' fun a => forall_congr' fun c => forall_congr' fun ψ =>
    imp_congr_left (isTest_iff (fun j => (cB_eq_neg_one a c j).symm) ψ)

theorem isCurlB_iff (B C : Mat ℂ b s) :
    IsCurl b s (fun a c => IsTest b s {j | ¬(j = a ↔ j = c)}) B C ↔ CurlTraceCube b s cE B C :=
  forall_congr' fun a => forall_congr' fun c => forall_congr' fun ψ =>
    imp_congr_left (isTest_iff (fun j => (cE_eq_neg_one a c j).symm) ψ)

theorem setIntegral_neg_mul (u : L2 𝕜 b s) (ψ : (Fin 3 → ℝ) → 𝕜) :
    ∫ x in cube b s, ((-u : L2 𝕜 b s) : (Fin 3 → ℝ) → 𝕜) x * ψ x =
      -∫ x in cube b s, (u : (Fin 3 → ℝ) → 𝕜) x * ψ x := by
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_neg u] with x hx
  rw [hx, Pi.neg_apply, neg_mul]

theorem setIntegral_zero_mul (ψ : (Fin 3 → ℝ) → 𝕜) :
    ∫ x in cube b s, ((0 : L2 𝕜 b s) : (Fin 3 → ℝ) → 𝕜) x * ψ x = 0 := by
  rw [← integral_zero (Fin 3 → ℝ) 𝕜]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_zero 𝕜 2 (volume.restrict (cube b s))] with x hx
  rw [hx, Pi.zero_apply, zero_mul]

theorem isDivE_iff (E : Mat ℂ b s) (D : Vec ℂ b s) :
    IsDiv b s (fun a => IsTest b s {a}) E D ↔ DivTraceCube b s E (-D) :=
  forall_congr' fun a => forall_congr' fun ψ => by
    beta_reduce
    rw [isTest_iff (c := cV a) (fun j => (cV_eq_neg_one a j).symm) ψ]
    refine imp_congr_right fun _ => ?_
    change _ ↔ (∑ c, ∫ x in cube b s, (E (a, c) : (Fin 3 → ℝ) → ℂ) x *
      fderiv ℝ ψ x (Pi.single c 1)) = ∫ x in cube b s, ((-D a : L2 ℂ b s) : (Fin 3 → ℝ) → ℂ) x * ψ x
    rw [setIntegral_neg_mul]

/-! ### The graphs of the mirror complex on the cube -/

theorem mem_graph_iff' {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup F]
    [Module R F] {T : E →ₗ.[R] F} {x : E} {y : F} :
    (x, y) ∈ T.graph ↔ ∃ h : x ∈ T.domain, T ⟨x, h⟩ = y :=
  ⟨fun h => ⟨LinearPMap.mem_domain_of_mem_graph h,
    ((LinearPMap.image_iff (LinearPMap.mem_domain_of_mem_graph h)).2 h).symm⟩,
   fun ⟨h, e⟩ => e ▸ T.mem_graph ⟨x, h⟩⟩

theorem mem_ker_iff' {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup F]
    [Module R F] {T : E →ₗ.[R] F} {x : E} : x ∈ T.ker ↔ ∃ h : x ∈ T.domain, T ⟨x, h⟩ = 0 := by
  rw [LinearPMap.mem_ker_iff]
  constructor
  · rintro ⟨y, rfl, hy⟩; exact ⟨y.2, hy⟩
  · rintro ⟨h, e⟩; exact ⟨⟨x, h⟩, rfl, e⟩

variable (hs : 0 < s)
include hs

theorem two_s_ne_zero' : ((2 * s : ℝ) : ℂ) ≠ 0 :=
  RCLike.ofReal_ne_zero.2 (mul_pos two_pos hs).ne'

omit hs in
theorem kappa_inv (i j : Fin 3) : (kappa s i j)⁻¹ = ((2 * s : ℝ) : ℂ) := by
  simp only [kappa, Complex.ofReal_inv, inv_inv]

omit hs in
theorem conj_kappa (i j : Fin 3) : conj (kappa s i j) = kappa s i j := Complex.conj_ofReal _

theorem adjoint_complexCube_d (i j : Fin 3) : ((complexCube b s hs).d i j)† =
    HilbertComplex.transportD complexQ.dual (eCube b s hs) (fun a b' => conj (kappa s b' a)) j i :=
  HilbertComplex.adjoint_transportD (jac_inv_pos hs) (inner_eCube hs) (kappa_ne_zero hs i j)

theorem conj_kappa_ne_zero (i j : Fin 3) : (fun a b' => conj (kappa s b' a)) j i ≠ 0 := by
  simp only [conj_kappa]; exact kappa_ne_zero hs i j

/-- The graph of `d₀` on the cube: `grad` with `σ · n = 0`. -/
theorem graph_d₀_iff (σ : Vec ℂ b s) (G : Mat ℂ b s) :
    ((σ, G) : SpaceCube b s 0 × SpaceCube b s 1) ∈ ((complexCube b s hs).d 0 1).graph ↔
      IsGrad b s σ G := by
  refine (HilbertComplex.mem_transportD_graph_iff (kappa_ne_zero hs 0 1)).trans ?_
  refine mem_graph_iff'.trans ((complexQ_d₀_iff _ _).trans ?_)
  refine Iff.trans ?_ (isGrad_iff σ G).symm
  have h := gradTraceCube_pull_iff (b := b) hs ((eCube b s hs 0).symm σ) ((eCube b s hs 1).symm G)
  have e0 : pullCube b s hs (Fin 3) ((eCube b s hs 0).symm σ) = σ :=
    (eCube b s hs 0).apply_symm_apply σ
  have e1 : pullCube b s hs (Fin 3 × Fin 3) ((eCube b s hs 1).symm G) = G :=
    (eCube b s hs 1).apply_symm_apply G
  rw [e0, e1, ← kappa_inv (i := 0) (j := 1)] at h
  exact h.symm

/-- The graph of `d₁` on the cube: `curl` with `E_{nτ} = 0`. -/
theorem graph_d₁_iff (E C : Mat ℂ b s) :
    ((E, C) : SpaceCube b s 1 × SpaceCube b s 2) ∈ ((complexCube b s hs).d 1 2).graph ↔
      IsCurl b s (fun a c => IsTest b s {j | j = a ↔ j = c}) E C := by
  refine (HilbertComplex.mem_transportD_graph_iff (kappa_ne_zero hs 1 2)).trans ?_
  refine mem_graph_iff'.trans ((complexQ_d₁_iff _ _).trans ?_)
  refine Iff.trans ?_ (isCurlE_iff E C).symm
  have h := curlTraceCube_pull_iff (b := b) hs cB ((eCube b s hs 1).symm E)
    ((eCube b s hs 2).symm C)
  have e1 : pullCube b s hs (Fin 3 × Fin 3) ((eCube b s hs 1).symm E) = E :=
    (eCube b s hs 1).apply_symm_apply E
  have e2 : pullCube b s hs (Fin 3 × Fin 3) ((eCube b s hs 2).symm C) = C :=
    (eCube b s hs 2).apply_symm_apply C
  rw [e1, e2, ← kappa_inv (i := 1) (j := 2)] at h
  exact h.symm

/-- The graph of `d₀†` on the cube: `-div` with `E_{τn} = 0`. -/
theorem graph_adjoint_d₀_iff (E : Mat ℂ b s) (D : Vec ℂ b s) :
    ((E, D) : SpaceCube b s 1 × SpaceCube b s 0) ∈ ((complexCube b s hs).d 0 1)†.graph ↔
      DivTraceCube b s E D := by
  rw [adjoint_complexCube_d hs 0 1]
  refine (HilbertComplex.mem_transportD_graph_iff (κ := fun a b' => conj (kappa s b' a))
    (i := 1) (j := 0) (conj_kappa_ne_zero hs 0 1)).trans ?_
  refine mem_graph_iff'.trans ((complexQ_adjoint_d₀_iff _ _).trans ?_)
  have h := divTraceCube_pull_iff (b := b) hs ((eCube b s hs 1).symm E) ((eCube b s hs 0).symm D)
  have e1 : pullCube b s hs (Fin 3 × Fin 3) ((eCube b s hs 1).symm E) = E :=
    (eCube b s hs 1).apply_symm_apply E
  have e0 : pullCube b s hs (Fin 3) ((eCube b s hs 0).symm D) = D :=
    (eCube b s hs 0).apply_symm_apply D
  rw [e1, e0, ← kappa_inv (i := 0) (j := 1), ← conj_kappa 0 1] at h
  exact h.symm

/-- The graph of `d₁†` on the cube: `curl` with `B_{ττ} = 0`. -/
theorem graph_adjoint_d₁_iff (B C : Mat ℂ b s) :
    ((B, C) : SpaceCube b s 2 × SpaceCube b s 1) ∈ ((complexCube b s hs).d 1 2)†.graph ↔
      IsCurl b s (fun a c => IsTest b s {j | ¬(j = a ↔ j = c)}) B C := by
  rw [adjoint_complexCube_d hs 1 2]
  refine (HilbertComplex.mem_transportD_graph_iff (κ := fun a b' => conj (kappa s b' a))
    (i := 2) (j := 1) (conj_kappa_ne_zero hs 1 2)).trans ?_
  refine mem_graph_iff'.trans ((complexQ_adjoint_d₁_iff _ _).trans ?_)
  refine Iff.trans ?_ (isCurlB_iff B C).symm
  have h := curlTraceCube_pull_iff (b := b) hs cE ((eCube b s hs 2).symm B)
    ((eCube b s hs 1).symm C)
  have e2 : pullCube b s hs (Fin 3 × Fin 3) ((eCube b s hs 2).symm B) = B :=
    (eCube b s hs 2).apply_symm_apply B
  have e1 : pullCube b s hs (Fin 3 × Fin 3) ((eCube b s hs 1).symm C) = C :=
    (eCube b s hs 1).apply_symm_apply C
  rw [e2, e1, ← kappa_inv (i := 1) (j := 2), ← conj_kappa 1 2] at h
  exact h.symm

omit hs

/-! ### The states -/

/-- The states `(σ, E, B)` as elements of `PiLp 2 (SpaceCube b s)`. -/
def toPiₗ : State ℂ b s ≃ₗ[ℂ] PiLp 2 (SpaceCube b s) where
  toFun U := WithLp.toLp 2 fun i => match i with
    | 0 => U.fst
    | 1 => U.snd.fst
    | 2 => U.snd.snd
  invFun x := WithLp.toLp 2 (x 0, WithLp.toLp 2 (x 1, x 2))
  map_add' U V := by ext i; fin_cases i <;> rfl
  map_smul' c U := by ext i; fin_cases i <;> rfl
  left_inv U := rfl
  right_inv x := by ext i; fin_cases i <;> rfl

/-- `toPiₗ` is unitary: both inner products are the sums of the inner products of `σ`, `E`, `B`. -/
def toPiI : State ℂ b s ≃ₗᵢ[ℂ] PiLp 2 (SpaceCube b s) :=
  toPiₗ.isometryOfInner fun U V => by
    rw [PiLp.inner_apply, Fin.sum_univ_three, WithLp.prod_inner_apply, WithLp.prod_inner_apply,
      add_assoc]
    rfl

/-- The states as elements of `PiLp 2 (SpaceCube b s)`, as a continuous linear isomorphism. -/
def toPi : State ℂ b s ≃L[ℂ] PiLp 2 (SpaceCube b s) := toPiI.toContinuousLinearEquiv

theorem toPi_zero (U : State ℂ b s) : toPi U 0 = U.fst := rfl
theorem toPi_one (U : State ℂ b s) : toPi U 1 = U.snd.fst := rfl
theorem toPi_two (U : State ℂ b s) : toPi U 2 = U.snd.snd := rfl

include hs

/-- **`IsWave` is the graph of the wave operator of the mirror complex on the cube.** -/
theorem isWave_iff (U V : State ℂ b s) :
    IsWave b s U V ↔ (toPi U, toPi V) ∈ (complexCube b s hs).wave.graph := by
  rw [mem_graph_iff']
  constructor
  · rintro ⟨hD, ⟨G, CB, hG, hCB, hV1⟩, hCE⟩
    obtain ⟨h0, e0⟩ := mem_graph_iff'.1 ((graph_d₀_iff hs _ _).2 hG)
    obtain ⟨h1, e1⟩ := mem_graph_iff'.1 ((graph_d₁_iff hs _ _).2 hCE)
    obtain ⟨h1', e1'⟩ := mem_graph_iff'.1 ((graph_adjoint_d₀_iff hs _ _).2 ((isDivE_iff _ _).1 hD))
    obtain ⟨h2, e2⟩ := mem_graph_iff'.1 ((graph_adjoint_d₁_iff hs _ _).2 hCB)
    have hx : toPi U ∈ (complexCube b s hs).wave.domain :=
      HilbertComplex.mem_wave_domain_fin3 _ h0 h1 h1' h2
    refine ⟨hx, ?_⟩
    have k0 : ((complexCube b s hs).wave ⟨_, hx⟩) 0 = V.fst := by
      rw [HilbertComplex.wave_apply_fin3_zero]
      change -((complexCube b s hs).d 0 1)† ⟨U.snd.fst, h1'⟩ = V.fst
      rw [e1']
      exact neg_neg _
    have k1 : ((complexCube b s hs).wave ⟨_, hx⟩) 1 = V.snd.fst := by
      rw [HilbertComplex.wave_apply_fin3_one]
      change (complexCube b s hs).d 0 1 ⟨U.fst, h0⟩ -
        ((complexCube b s hs).d 1 2)† ⟨U.snd.snd, h2⟩ = _
      rw [e0, e2, hV1]
      rfl
    have k2 : ((complexCube b s hs).wave ⟨_, hx⟩) 2 = V.snd.snd := by
      rw [HilbertComplex.wave_apply_fin3_two]
      exact e1
    exact PiLp.ext fun i => by fin_cases i; exacts [k0, k1, k2]
  · rintro ⟨hx, e⟩
    obtain ⟨hd, hd'⟩ := (HilbertComplex.mem_wave_domain _).1 hx
    have k0 := congrArg (fun y : PiLp 2 (SpaceCube b s) => y 0) e
    have k1 := congrArg (fun y : PiLp 2 (SpaceCube b s) => y 1) e
    have k2 := congrArg (fun y : PiLp 2 (SpaceCube b s) => y 2) e
    simp only [HilbertComplex.wave_apply_fin3_zero, HilbertComplex.wave_apply_fin3_one,
      HilbertComplex.wave_apply_fin3_two] at k0 k1 k2
    have hD : DivTraceCube b s U.snd.fst
        (-(-((complexCube b s hs).d 0 1)† ⟨U.snd.fst, hd' 0 1⟩)) := by
      rw [neg_neg]
      exact (graph_adjoint_d₀_iff hs _ _).1 (mem_graph_iff'.2 ⟨_, rfl⟩)
    refine ⟨?_, ⟨(complexCube b s hs).d 0 1 ⟨U.fst, hd 0 1⟩,
      ((complexCube b s hs).d 1 2)† ⟨U.snd.snd, hd' 1 2⟩,
      (graph_d₀_iff hs _ _).1 (mem_graph_iff'.2 ⟨_, rfl⟩),
      (graph_adjoint_d₁_iff hs _ _).1 (mem_graph_iff'.2 ⟨_, rfl⟩), k1.symm⟩, ?_⟩
    · have e0 : V.fst = -((complexCube b s hs).d 0 1)† ⟨U.snd.fst, hd' 0 1⟩ := k0.symm
      rw [e0]
      exact (isDivE_iff _ _).2 hD
    · have e2 : V.snd.snd = (complexCube b s hs).d 1 2 ⟨U.snd.fst, hd 1 2⟩ := k2.symm
      rw [e2]
      exact (graph_d₁_iff hs _ _).1 (mem_graph_iff'.2 ⟨hd 1 2, rfl⟩)

/-! ### The constraint -/

omit hs

section TSD

open Matrix Feec.Models.Cube.MirrorExt Feec.Fourier
open Feec.Fourier.GradCurl (tsd mem_tsd toMatrix toMatrix_apply cfreq div div_apply adjoint_grad
  gradCurl_m01 gradCurl grad)

variable {cv : Fin 3 → Fin 3 → ℂ} {cm : Fin 3 × Fin 3 → Fin 3 → ℂ}
  (hcv : ∀ a k, cv a k * cv a k = 1) (hcm : ∀ p k, cm p k * cm p k = 1)

include hcv in
/-- **`grad†` of mirror extensions with general parities, as Green's formulas** (the argument of
`Mirror.complexQ_adjoint_d₀_iff`, for matrix parities `cm` obtained from vector parities `cv` by
`grad`). -/
theorem adjoint_grad_extF_iff
    (hgrad : ∀ a c, cm (a, c) = Function.update (cv a) c (-cv a c)) (M : MQ) (D : VQ) :
    (∃ h : extF hcm M ∈ ((Models.Torus.GradCurl.complex.d 0 1)†).domain,
        (Models.Torus.GradCurl.complex.d 0 1)† ⟨_, h⟩ = extF hcv D) ↔
      ∀ a : Fin 3, ∀ ψ : R3 → ℂ, IsTraceTest (cv a) ψ →
        ∑ c, ∫ y in Geometry.Q (Fin 3), (M (a, c) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1) =
          ∫ y in Geometry.Q (Fin 3), (D a : R3 → ℂ) y * ψ y := by
  refine (Models.Torus.GradCurl.mem_domain_adjoint_grad_iff_weak (extPi hcm M)
    (extPi hcv D)).trans ?_
  have hpar : ∀ a, ∀ c (p : Fin 3 × Fin 3), (if p = (a, c) then (-1 : ℂ) else 0) ≠ 0 →
      Function.update (cm p) c (-cm p c) = cv a := by
    intro a c p hα
    split_ifs at hα with h1
    · subst h1
      rw [hgrad]
      funext j
      by_cases h : j = c
      · subst h; simp
      · simp [Function.update_of_ne h]
    · exact absurd rfl hα
  refine ⟨fun h a ψ hψ => ?_, fun h a => ?_⟩
  · have e := (isGreenClass_isTraceTest _ hcm (hcv a) (fun c p hα => by
      simp only [gradCurl_m01, adjoint_grad, neg_I_mul_div_single] at hα
      exact hpar a c p hα) (fun p => M p) (D a)).1 (h a) ψ hψ
    simp only [gradCurl_m01, adjoint_grad, neg_I_mul_div_single] at e
    rw [sum_div_coeff a (fun c p =>
      ∫ y in Geometry.Q (Fin 3), (M p : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1))] at e
    exact neg_inj.1 e
  · refine (isGreenClass_isTraceTest _ hcm (hcv a) (fun c p hα => by
      simp only [gradCurl_m01, adjoint_grad, neg_I_mul_div_single] at hα
      exact hpar a c p hα) (fun p => M p) (D a)).2 fun ψ hψ => ?_
    simp only [gradCurl_m01, adjoint_grad, neg_I_mul_div_single]
    rw [sum_div_coeff a (fun c p =>
      ∫ y in Geometry.Q (Fin 3), (M p : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1)), h a ψ hψ]

theorem div_eq_zero_iff (ξ : Fourier.GradCurl.Freq) (M : Fourier.GradCurl.Mat) :
    div ξ M = 0 ↔ toMatrix M *ᵥ cfreq ξ = 0 := by
  constructor
  · intro h
    funext a
    have := congrArg (fun v : Fourier.GradCurl.Vec => v a) h
    simp only [div_apply, PiLp.zero_apply, mul_eq_zero, neg_eq_zero, Complex.I_ne_zero,
      false_or] at this
    simpa [Matrix.mulVec, dotProduct, cfreq] using this
  · intro h
    ext a
    have := congrFun h a
    simp only [Matrix.mulVec, dotProduct, toMatrix_apply, cfreq, Pi.zero_apply] at this
    simp [div_apply, this]

theorem setIntegralQ_zero_mul (ψ : R3 → ℂ) :
    ∫ y in Geometry.Q (Fin 3), ((0 : Domain.L2 ℂ (Geometry.Q (Fin 3))) : R3 → ℂ) y * ψ y = 0 := by
  rw [← integral_zero R3 ℂ]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (Geometry.Q (Fin 3)))] with x hx
  rw [hx, Pi.zero_apply, zero_mul]

include hcv in
/-- **The torus constraint pulled back along the mirror extensions**: the extension of `E` has TSD
Fourier coefficients iff `E` is symmetric, trace-free and divergence-free with the wall condition
of the parities `cv`. -/
theorem extF_mem_constraint_iff (hsym : ∀ a c, cm (a, c) = cm (c, a))
    (hdiag : ∀ a, cm (a, a) = cm (0, 0))
    (hgrad : ∀ a c, cm (a, c) = Function.update (cv a) c (-cv a c)) (E : MQ) :
    extF hcm E ∈ Models.Torus.GradCurl.constraint 1 ↔
      (∀ i j, E (i, j) = E (j, i)) ∧ ∑ i, E (i, i) = 0 ∧
        ∀ a : Fin 3, ∀ ψ : R3 → ℂ, IsTraceTest (cv a) ψ →
          ∑ c, ∫ y in Geometry.Q (Fin 3), (E (a, c) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1) =
            0 := by
  have hfib : extF hcm E ∈ Models.Torus.GradCurl.constraint 1 ↔
      ∀ n, (extF hcm E : (Fin 3 → ℤ) → Fourier.GradCurl.Mat) n ∈ tsd (Fourier.Torus.freq n) :=
    Operator.mem_fibreSub.trans Measure.ae_count_iff
  have hc0 : ∀ j, cm (0, 0) j * cm (0, 0) j = 1 := hcm (0, 0)
  -- the trace of the coefficients
  have htr : ∀ n, (toMatrix ((extF hcm E : (Fin 3 → ℤ) → Fourier.GradCurl.Mat) n)).trace =
      coeffCLM n (extL2 hc0 (∑ i, E (i, i))) := by
    intro n
    simp only [Matrix.trace, Matrix.diag, toMatrix_apply, extF_coeff]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeffCLM_apply, extL2_congr (hdiag i) (hcm (i, i)) hc0]
  -- the divergence of the coefficients
  have hker : (∀ n, toMatrix ((extF hcm E : (Fin 3 → ℤ) → Fourier.GradCurl.Mat) n) *ᵥ
        cfreq (Fourier.Torus.freq n) = 0) ↔
      ∃ h : extF hcm E ∈ ((Models.Torus.GradCurl.complex.d 0 1)†).domain,
        (Models.Torus.GradCurl.complex.d 0 1)† ⟨_, h⟩ = extF hcv 0 := by
    have e : (Models.Torus.GradCurl.complex.d 0 1)† = Operator.mulOp Measure.count
        fun n => ContinuousLinearMap.adjoint (gradCurl.m 0 1 (Fourier.Torus.freq n)) :=
      (Fourier.Torus.symbolComplex gradCurl).adjoint_d 0 1
    have h1 : (∀ n, toMatrix ((extF hcm E : (Fin 3 → ℤ) → Fourier.GradCurl.Mat) n) *ᵥ
          cfreq (Fourier.Torus.freq n) = 0) ↔ extF hcm E ∈ (Operator.mulOp Measure.count
            fun n => ContinuousLinearMap.adjoint (gradCurl.m 0 1 (Fourier.Torus.freq n))).ker := by
      refine Iff.trans ?_ Operator.mem_ker_mulOp.symm
      refine Iff.trans ?_ Measure.ae_count_iff.symm
      refine forall_congr' fun n => ?_
      change _ ↔ ContinuousLinearMap.adjoint (grad (Fourier.Torus.freq n))
        ((extF hcm E : (Fin 3 → ℤ) → Fourier.GradCurl.Mat) n) = 0
      rw [adjoint_grad, div_eq_zero_iff]
    have h0 : extF hcv (0 : VQ) = 0 := _root_.map_zero _
    refine h1.trans (Iff.trans ?_ ((mem_ker_iff' (T := (Models.Torus.GradCurl.complex.d 0 1)†)
      (x := extF hcm E)).trans ?_))
    · rw [e]
      exact Iff.rfl
    · rw [h0]
      exact Iff.rfl
  rw [hfib]
  simp only [mem_tsd, forall_and]
  refine and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · intro h i j
      have h' : extL2 (hcm (i, j)) (E (i, j)) = extL2 (hcm (j, i)) (E (j, i)) := by
        refine TorusWeak.eq_of_mFourierCoeff_eq fun n => ?_
        rw [← extF_coeff, ← extF_coeff]
        have := congrFun (congrFun (h n) j) i
        simpa [Matrix.transpose_apply, toMatrix_apply] using this
      rw [extL2_congr (hsym i j) _ (hcm (j, i))] at h'
      rw [← resQ_extL2 (hcm (j, i)) (E (i, j)), h', resQ_extL2]
    · intro h n
      ext i j
      simp only [Matrix.transpose_apply, toMatrix_apply, extF_coeff]
      rw [h j i, extL2_congr (hsym j i) (hcm (j, i)) (hcm (i, j))]
  · simp only [htr]
    constructor
    · intro h
      have h0 : extL2 hc0 (∑ i, E (i, i)) = 0 := by
        refine TorusWeak.eq_of_mFourierCoeff_eq fun n => ?_
        rw [← coeffCLM_apply, ← coeffCLM_apply, h n, _root_.map_zero]
      rw [← resQ_extL2 hc0 (∑ i, E (i, i)), h0, _root_.map_zero]
    · intro h n
      rw [h, _root_.map_zero, _root_.map_zero]
  · refine hker.trans ((adjoint_grad_extF_iff hcv hcm hgrad E 0).trans ?_)
    refine forall_congr' fun a => forall_congr' fun ψ => imp_congr_right fun _ => ?_
    rw [PiLp.zero_apply, setIntegralQ_zero_mul]

end TSD

/-! ### The constraint on the cube -/

/-- TSD fields on the cube with the wall condition of the parities `cv`, on the fields of
`Feec`. -/
def TSDCube (cv : Fin 3 → Fin 3 → ℂ) (M : Domain.L2F ℂ (Geometry.openCube b s) (Fin 3 × Fin 3)) :
    Prop :=
  (∀ i j, M (i, j) = M (j, i)) ∧ ∑ i, M (i, i) = 0 ∧
    ∀ a : Fin 3, ∀ φ : R3 → ℂ, IsTraceTestCube b s (cv a) φ →
      ∑ c, ∫ x in Geometry.openCube b s, (M (a, c) : R3 → ℂ) x * fderiv ℝ φ x (Pi.single c 1) = 0

/-- TSD fields on `Q` with the wall condition of the parities `cv`. -/
def TSDQ (cv : Fin 3 → Fin 3 → ℂ) (M : MQ) : Prop :=
  (∀ i j, M (i, j) = M (j, i)) ∧ ∑ i, M (i, i) = 0 ∧
    ∀ a : Fin 3, ∀ ψ : R3 → ℂ, IsTraceTest (cv a) ψ →
      ∑ c, ∫ y in Geometry.Q (Fin 3), (M (a, c) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1) = 0

theorem isTSD_iff {cv : Fin 3 → Fin 3 → ℂ} {S : Fin 3 → Set (Fin 3)}
    (hS : ∀ a j, j ∈ S a ↔ cv a j = -1) (E : Mat ℂ b s) :
    IsTSD b s (fun a => IsTest b s (S a)) E ↔ TSDCube cv E := by
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  refine forall_congr' fun a => forall_congr' fun φ => ?_
  beta_reduce
  rw [isTest_iff (hS a) φ, PiLp.zero_apply, setIntegral_zero_mul, neg_zero]
  exact Iff.rfl

section Pull

include hs

theorem pullCube_comp_eq {E' : MQ} {p q : Fin 3 × Fin 3}
    (h : pullCube b s hs _ E' p = pullCube b s hs _ E' q) : E' p = E' q := by
  rw [← (pullCube b s hs (Fin 3 × Fin 3)).symm_apply_apply E']
  simp only [Domain.pullF_symm_apply, Domain.pullF_apply] at h ⊢
  rw [h]

theorem tsdCube_pullCube_iff (cv : Fin 3 → Fin 3 → ℂ) (E' : MQ) :
    TSDCube cv (pullCube b s hs _ E') ↔ TSDQ cv E' := by
  have h2 := two_s_ne_zero' hs
  have hJ := jacCube_ne_zero hs
  refine and_congr ⟨fun h i j => pullCube_comp_eq hs (h i j), fun h i j => by
    simp only [Domain.pullF_apply]; rw [h i j]⟩ (and_congr ⟨fun h => ?_, fun h => ?_⟩ ?_)
  · rw [← (pullCube b s hs (Fin 3 × Fin 3)).symm_apply_apply E']
    simp only [Domain.pullF_symm_apply, Domain.pullF_apply] at h ⊢
    rw [← _root_.map_sum, ← _root_.map_sum] at *
    rw [h, _root_.map_zero]
  · simp only [Domain.pullF_apply]
    rw [← _root_.map_sum, h, _root_.map_zero]
  · constructor
    · intro h a ψ hψ
      have e := h a (ψ ∘ cubeMap b s) (isTraceTestCube_comp_cubeMap hs hψ)
      simp_rw [setIntegral_pullCube_mul_fderiv hs E' _ hψ.contDiff] at e
      rw [← Finset.mul_sum, ← Finset.mul_sum] at e
      rcases mul_eq_zero.1 e with e | e
      · exact absurd e (by simpa using h2)
      · exact (mul_eq_zero.1 e).resolve_left hJ
    · intro h a φ hφ
      have hψ := hφ.comp_aff hs
      rw [← comp_aff_cubeMap (b := b) hs φ]
      simp_rw [setIntegral_pullCube_mul_fderiv hs E' _ hψ.contDiff]
      rw [← Finset.mul_sum, ← Finset.mul_sum, h a _ hψ, mul_zero, mul_zero]

end Pull

section Constraint

include hs

theorem mem_tsdCube_zero_iff (σ : Vec ℂ b s) : (σ : SpaceCube b s 0) ∈ tsdCube b s hs 0 ↔ σ = 0 :=
  mem_tsdQ_zero.trans (eCube b s hs 0).symm.map_eq_zero_iff

theorem mem_tsdCube_one_iff (E : Mat ℂ b s) :
    (E : SpaceCube b s 1) ∈ tsdCube b s hs 1 ↔ IsTSD b s (fun a => IsTest b s {a}) E := by
  obtain ⟨E', rfl⟩ := (eCube b s hs 1).surjective E
  refine Iff.trans ?_ (isTSD_iff (cv := cV) (fun a j => Set.mem_singleton_iff.trans
    (cV_eq_neg_one a j).symm) _).symm
  refine Iff.trans ?_ (tsdCube_pullCube_iff hs cV E').symm
  change J 1 ((eCube b s hs 1).symm (eCube b s hs 1 E')) ∈ Models.Torus.GradCurl.constraint 1 ↔ _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact extF_mem_constraint_iff cV_sq cE_sq (fun a c => funext fun k => by simp only [cE]; ring)
    (fun a => funext fun k => by simp only [cE, sgn_mul_self]) cE_eq_update E'

theorem mem_tsdCube_two_iff (B : Mat ℂ b s) :
    (B : SpaceCube b s 2) ∈ tsdCube b s hs 2 ↔ IsTSD b s (fun a => IsTest b s {j | j ≠ a}) B := by
  obtain ⟨B', rfl⟩ := (eCube b s hs 2).surjective B
  refine Iff.trans ?_ (isTSD_iff (cv := cPV) (fun a j => (cPV_eq_neg_one a j).symm) _).symm
  refine Iff.trans ?_ (tsdCube_pullCube_iff hs cPV B').symm
  change MirrorExt.extF cB_sq ((eCube b s hs 2).symm (eCube b s hs 2 B')) ∈
    Models.Torus.GradCurl.constraint 1 ↔ _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact extF_mem_constraint_iff cPV_sq cB_sq (fun a c => funext fun k => by simp only [cB]; ring)
    (fun a => funext fun k => by simp only [cB, sgn_mul_self]) cB_eq_update B'

/-- **The constraint of the challenge is the constraint `tsdCube` of `Feec`.** -/
theorem constraint_iff (U : State ℂ b s) :
    Constraint b s U ↔ toPi U ∈ totalSub (tsdCube b s hs) :=
  ⟨fun h i => by
    fin_cases i
    exacts [(mem_tsdCube_zero_iff hs U.fst).2 h.1, (mem_tsdCube_one_iff hs U.snd.fst).2 h.2.1,
      (mem_tsdCube_two_iff hs U.snd.snd).2 h.2.2],
   fun h => ⟨(mem_tsdCube_zero_iff hs U.fst).1 (h 0), (mem_tsdCube_one_iff hs U.snd.fst).1 (h 1),
     (mem_tsdCube_two_iff hs U.snd.snd).1 (h 2)⟩⟩

end Constraint

/-! ### Solutions and forcing -/

section Solutions

theorem hasDerivWithinAt_map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] (L : E →L[ℂ] F) {u : ℝ → E} {u' : E} {I : Set ℝ}
    {t : ℝ} (h : HasDerivWithinAt u u' I t) : HasDerivWithinAt (fun τ => L (u τ)) (L u') I t :=
  (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t h

theorem intervalIntegral_map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    (L : E ≃L[ℂ] F) (g : ℝ → E) (a t : ℝ) : ∫ τ in a..t, L (g τ) = L (∫ τ in a..t, g τ) := by
  simp only [intervalIntegral, L.integral_comp_comm, _root_.map_sub]

include hs

/-- **Strong solutions of the challenge are those of `Feec`.** -/
theorem isStrongSolution_iff {I : Set ℝ} {F U : ℝ → State ℂ b s} :
    IsStrongSolution (IsWave b s) I F U ↔ Evolution.IsStrongSolution (complexCube b s hs).wave I
      (fun t => toPi (F t)) (fun t => toPi (U t)) := by
  constructor
  · rintro ⟨hc, hd⟩
    refine ⟨toPi.continuous.comp_continuousOn hc, fun t ht => ?_⟩
    obtain ⟨V, hV, hD⟩ := hd t ht
    refine ⟨toPi V, (isWave_iff hs _ _).1 hV, ?_⟩
    have := hasDerivWithinAt_map (toPi (b := b) (s := s)).toContinuousLinearMap hD
    rwa [_root_.map_add] at this
  · rintro ⟨hc, hd⟩
    refine ⟨?_, fun t ht => ?_⟩
    · have := (toPi (b := b) (s := s)).symm.continuous.comp_continuousOn hc
      simpa [Function.comp_def] using this
    · obtain ⟨v, hv, hD⟩ := hd t ht
      refine ⟨toPi.symm v, (isWave_iff hs _ _).2 (by rwa [ContinuousLinearEquiv.apply_symm_apply]),
        ?_⟩
      have := hasDerivWithinAt_map (toPi (b := b) (s := s)).symm.toContinuousLinearMap hD
      simpa [_root_.map_add] using this

/-- **Classical solutions of the challenge are those of `Feec`.** -/
theorem isClassicalSolution_iff {I : Set ℝ} {F U : ℝ → State ℂ b s} :
    IsClassicalSolution (IsWave b s) I F U ↔ Evolution.IsClassicalSolution (complexCube b s hs).wave I
      (fun t => toPi (F t)) (fun t => toPi (U t)) := by
  constructor
  · rintro ⟨h, V, hV, hW⟩
    exact ⟨(isStrongSolution_iff hs).1 h, fun t => toPi (V t),
      toPi.continuous.comp_continuousOn hV, fun t ht => (isWave_iff hs _ _).1 (hW t ht)⟩
  · intro h
    obtain ⟨V, hV, hW⟩ := h.deriv_cont
    refine ⟨(isStrongSolution_iff hs).2 h.toIsStrongSolution, fun t => toPi.symm (V t),
      (toPi (b := b) (s := s)).symm.continuous.comp_continuousOn hV,
      fun t ht => (isWave_iff hs _ _).2 ?_⟩
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hW t ht

/-- **The admissible forcing of the challenge is that of `Feec`.** -/
theorem isAdmissible_iff {a c : ℝ} {F : ℝ → State ℂ b s} :
    IsAdmissible (IsWave b s) a c F ↔
      Evolution.ForcingClass.admissible (complexCube b s hs).wave a c (fun t => toPi (F t)) := by
  unfold IsAdmissible Evolution.ForcingClass.admissible Evolution.ForcingClass.w11
    Evolution.ForcingClass.l1Domain
  refine and_congr ⟨fun h => toPi.continuous.comp_continuousOn h, fun h => ?_⟩ (or_congr ?_ ?_)
  · have := (toPi (b := b) (s := s)).symm.continuous.comp_continuousOn h
    simpa [Function.comp_def] using this
  · constructor
    · rintro ⟨x₀, g, hg, hF⟩
      refine ⟨toPi x₀, fun t => toPi (g t), toPi.integrable_comp_iff.2 hg, ?_⟩
      filter_upwards [hF] with t ht
      rw [ht, _root_.map_add, intervalIntegral_map]
    · rintro ⟨x₀, g, hg, hF⟩
      refine ⟨toPi.symm x₀, fun t => toPi.symm (g t), toPi.symm.integrable_comp_iff.2 hg, ?_⟩
      filter_upwards [hF] with t ht
      have := congrArg toPi.symm ht
      simp only [ContinuousLinearEquiv.symm_apply_apply] at this
      rw [this, _root_.map_add, intervalIntegral_map]
  · constructor
    · rintro ⟨H, hH, hF⟩
      refine ⟨fun t => toPi (H t), toPi.integrable_comp_iff.2 hH, ?_⟩
      filter_upwards [hF] with t ht
      exact LinearPMap.mem_graph_iff_exists.1 ((isWave_iff hs _ _).1 ht)
    · rintro ⟨H, hH, hF⟩
      refine ⟨fun t => toPi.symm (H t), toPi.symm.integrable_comp_iff.2 hH, ?_⟩
      filter_upwards [hF] with t ht
      refine (isWave_iff hs _ _).2 ?_
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact LinearPMap.mem_graph_iff_exists.2 ht

end Solutions

end FEEC.ConstraintPropagation
