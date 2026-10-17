module

public import Feec.HilbertComplex.DomainComplex
public import Feec.Variational.BabuskaNecas
public import Feec.Variational.GalerkinEvolution

/-!
# Semi-discrete Hodge wave equation: elliptic projection and convergence

For an operator `T : E →ₗ.[𝕜] E` (the total differential `𝐝` of a finite Hilbert complex), the
weak Hodge wave equation `⟪ψ, ξ'⟫ = ⟪ψ, T ξ⟫ - ⟪T ψ, ξ⟫` is posed on the graph space
`V = Γ(T)`, as `⟪ψ, ξ'⟫ + a(ξ, ψ) = 0` with the **wave form** `a(ξ, ψ) = ⟪T ψ, ξ⟫ - ⟪ψ, T ξ⟫`,
whose real part vanishes on the diagonal. A semi-discretization takes a finite-dimensional
`K ⊆ V` (e.g. the total space of a finite element subcomplex) and seeks `ξₕ(t) ∈ K` with the
same equation for test functions in `K`.

## Main definitions

* `Feec.HodgeWave.waveForm T`, `Feec.HodgeWave.shiftedForm T = ⟪·,·⟫ + a` (bounded sesquilinear
  forms on `Γ(T)`).
* `Feec.HodgeWave.ellipticProjection T K`: the elliptic projection onto a finite-dimensional
  `K ⊆ Γ(T)` for the shifted form (the thesis' (4.11)), a bounded projection.

## Main results

* `shiftedForm_ellipticProjection`, `ellipticProjection_mem`, `ellipticProjection_of_mem`.
* `norm_sub_le_of_semidiscrete`: **the semi-discrete error estimate**
  `‖ξ(t) - ξₕ(t)‖ ≤ ‖Pξ(t₀) - ξₕ(t₀)‖ + ‖e(t)‖ + (t - t₀) ‖e(t₀)‖ + (1 + (t - t₀)) ∫ ‖e'‖`
  with `e = Pξ - ξ`, for every operator `T` and every finite-dimensional `K`, over `ℝ` and `ℂ`.
  For the short complex of the thesis this is Thm 4.14; here the complex may have any length.
* `weak_eq_iff`: the graph-space equation is the weak form of `Feec.HodgeWave.IsWeakSolution`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.6 ((4.10), (4.11), Thm 4.14)
* [T. Dupont, *L²-estimates for Galerkin methods for second order hyperbolic equations*][Dupont1973]
  (energy-method error estimates)
* [G. A. Baker, *Error estimates for finite element methods for second order hyperbolic equations*][Baker1976]
  (energy-method error estimates)
* [T. Geveci, *On the application of mixed finite element methods to the wave equations*][Geveci1988]
  (mixed methods for the wave equation)
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]
  (FEEC for evolution problems)
-/

open scoped InnerProductSpace
open Set LinearPMap Feec.Variational

@[expose] public noncomputable section

namespace Feec.HodgeWave

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  (T : E →ₗ.[𝕜] E)

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The **wave form** `a(ξ, ψ) = ⟪T ψ, ξ⟫ - ⟪ψ, T ξ⟫` on the graph space. -/
def waveForm : T.GraphSpace →L[𝕜] T.GraphSpace →L⋆[𝕜] 𝕜 :=
  (innerSLFlip 𝕜).bilinearComp T.graphFst T.graphSnd -
    (innerSLFlip 𝕜).bilinearComp T.graphSnd T.graphFst

/-- The **shifted form** `A(ξ, ψ) = ⟪ψ, ξ⟫ + a(ξ, ψ)` (pivot inner product in `E`). -/
def shiftedForm : T.GraphSpace →L[𝕜] T.GraphSpace →L⋆[𝕜] 𝕜 :=
  (innerSLFlip 𝕜).bilinearComp T.graphFst T.graphFst + waveForm T

variable {T}

theorem waveForm_apply (x ψ : T.GraphSpace) :
    waveForm T x ψ = ⟪T.graphSnd ψ, T.graphFst x⟫ - ⟪T.graphFst ψ, T.graphSnd x⟫ := by
  simp [waveForm]

theorem shiftedForm_apply (x ψ : T.GraphSpace) :
    shiftedForm T x ψ = ⟪T.graphFst ψ, T.graphFst x⟫ + waveForm T x ψ := by
  simp [shiftedForm]

/-- `re a(ψ, ψ) = 0`. -/
theorem re_waveForm_self (ψ : T.GraphSpace) : RCLike.re (waveForm T ψ ψ) = 0 := by
  rw [waveForm_apply, _root_.map_sub, inner_re_symm, sub_self]

/-- `re A(ψ, ψ) = ‖ψ‖²_E`. -/
theorem re_shiftedForm_self (ψ : T.GraphSpace) :
    RCLike.re (shiftedForm T ψ ψ) = ‖T.graphFst ψ‖ ^ 2 := by
  rw [shiftedForm_apply, _root_.map_add, re_waveForm_self, add_zero, inner_self_eq_norm_sq]

/-! ### The elliptic projection -/

section Projection

variable (K : Submodule 𝕜 T.GraphSpace) [FiniteDimensional 𝕜 K]

omit [FiniteDimensional 𝕜 K] in
/-- The shifted form restricted to `K` is injective. -/
theorem injective_restrict_shiftedForm : Function.Injective (restrict (shiftedForm T) K K) := by
  intro x y hxy
  have h0 : restrict (shiftedForm T) K K (x - y) = 0 := by rw [_root_.map_sub, hxy, sub_self]
  have hre : RCLike.re (shiftedForm T ((x - y : K) : T.GraphSpace)
      ((x - y : K) : T.GraphSpace)) = 0 := by
    have := congrArg (fun f => f (x - y)) h0
    simp only [Variational.restrict_apply, _root_.zero_apply] at this
    rw [this, _root_.map_zero]
  rw [re_shiftedForm_self] at hre
  have h1 : T.graphFst ((x - y : K) : T.GraphSpace) = 0 := by
    rw [← norm_eq_zero]; exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 hre
  have h2 : ((x - y : K) : T.GraphSpace) = 0 :=
    T.graphFst_injective (h1.trans (T.graphFst.map_zero).symm)
  exact sub_eq_zero.1 (Subtype.ext h2)

/-- The shifted form restricted to `K` is onto the antidual of `K`. -/
theorem surjective_restrict_shiftedForm : Function.Surjective (restrict (shiftedForm T) K K) := by
  set B := restrict (shiftedForm T) K K
  have hinj : Function.Injective B := injective_restrict_shiftedForm K
  have hR : Function.Injective (rieszOp B : K →ₗ[𝕜] K) := fun x y hxy => hinj (by
    rw [← innerSLFlip_rieszOp B x, ← innerSLFlip_rieszOp B y]
    exact congrArg _ hxy)
  have hRs : Function.Surjective (rieszOp B : K →ₗ[𝕜] K) := LinearMap.injective_iff_surjective.1 hR
  intro f
  obtain ⟨g, rfl⟩ := innerSLFlip_surjective f
  obtain ⟨x, hx⟩ := hRs g
  refine ⟨x, ?_⟩
  rw [← innerSLFlip_rieszOp B x]
  exact congrArg _ hx

/-- `A|_K : K ≃ K*` (antidual). -/
def shiftedFormEquiv : K ≃L[𝕜] (K →L⋆[𝕜] 𝕜) :=
  ContinuousLinearEquiv.ofBijective (restrict (shiftedForm T) K K)
    (LinearMap.ker_eq_bot.2 (injective_restrict_shiftedForm K))
    (LinearMap.range_eq_top.2 (surjective_restrict_shiftedForm K))

/-- `ζ ↦ A(ζ, ·)|_K`. -/
def shiftedFormRestrict : T.GraphSpace →L[𝕜] (K →L⋆[𝕜] 𝕜) :=
  LinearMap.mkContinuous
    { toFun := fun ζ => (shiftedForm T ζ).comp K.subtypeL
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
    ‖shiftedForm T‖ fun ζ => by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ψ => ?_
      exact (shiftedForm T).le_opNorm₂ ζ ψ

/-- The **elliptic projection** onto a finite-dimensional `K ⊆ Γ(T)`:
`P ζ ∈ K` with `A(P ζ, ψ) = A(ζ, ψ)` for `ψ ∈ K`. [QuennevilleBelair2015], (4.11) -/
def ellipticProjection : T.GraphSpace →L[𝕜] T.GraphSpace :=
  K.subtypeL.comp (((shiftedFormEquiv K).symm : (K →L⋆[𝕜] 𝕜) →L[𝕜] K).comp
    (shiftedFormRestrict K))

theorem ellipticProjection_mem (ζ : T.GraphSpace) : ellipticProjection K ζ ∈ K :=
  ((shiftedFormEquiv K).symm (shiftedFormRestrict K ζ)).2

/-- `A(P ζ, ψ) = A(ζ, ψ)` for `ψ ∈ K`. [QuennevilleBelair2015], (4.11) -/
theorem shiftedForm_ellipticProjection (ζ : T.GraphSpace) {ψ : T.GraphSpace} (hψ : ψ ∈ K) :
    shiftedForm T (ellipticProjection K ζ) ψ = shiftedForm T ζ ψ := by
  have h := (shiftedFormEquiv K).apply_symm_apply (shiftedFormRestrict K ζ)
  have := congrArg (fun f => f ⟨ψ, hψ⟩) h
  exact this

/-- `P` is a projection: `P ζ = ζ` on `K`. -/
theorem ellipticProjection_of_mem {ζ : T.GraphSpace} (hζ : ζ ∈ K) :
    ellipticProjection K ζ = ζ := by
  have h : restrict (shiftedForm T) K K ⟨_, ellipticProjection_mem K ζ⟩ =
      restrict (shiftedForm T) K K ⟨ζ, hζ⟩ :=
    ContinuousLinearMap.ext fun ψ => shiftedForm_ellipticProjection K ζ ψ.2
  exact congrArg Subtype.val (injective_restrict_shiftedForm K h)

/-- **Galerkin orthogonality of the elliptic projection**: `A(P ζ - ζ, ψ) = 0` on `K`. -/
theorem shiftedForm_ellipticProjection_sub (ζ : T.GraphSpace) {ψ : T.GraphSpace} (hψ : ψ ∈ K) :
    shiftedForm T (ellipticProjection K ζ - ζ) ψ = 0 := by
  rw [_root_.map_sub, _root_.sub_apply, shiftedForm_ellipticProjection K ζ hψ, sub_self]

end Projection

/-! ### The semi-discrete error estimate -/

/-- The graph-space equation `⟪ψ, ξ'⟫ + a(ξ, ψ) = 0` is the weak form
`⟪ξ', ψ⟫ = ⟪T ξ, ψ⟫ - ⟪ξ, T ψ⟫` of `Feec.HodgeWave.IsWeakSolution` (with `F = 0`). -/
theorem weak_eq_iff (ξ ψ : T.GraphSpace) (ξ' : E) :
    ⟪T.graphFst ψ, ξ'⟫ + waveForm T ξ ψ = 0 ↔
      ⟪ξ', T.graphFst ψ⟫ = ⟪T.graphSnd ξ, T.graphFst ψ⟫ - ⟪T.graphFst ξ, T.graphSnd ψ⟫ := by
  rw [waveForm_apply]
  constructor
  · intro h
    have := congrArg (starRingEnd 𝕜) h
    simp only [_root_.map_add, _root_.map_sub, inner_conj_symm, _root_.map_zero] at this
    linear_combination this
  · intro h
    have := congrArg (starRingEnd 𝕜) h
    simp only [_root_.map_sub, inner_conj_symm] at this
    linear_combination this

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **Convergence of the semi-discrete Hodge wave equation** (error estimate). Let
`K ⊆ Γ(T)` be finite-dimensional with elliptic projection `P`, `ξ ∈ C¹([t₀,t₁]; Γ(T))` a
solution of `⟪ψ, ξ'⟫ + a(ξ, ψ) = 0` for `ψ ∈ K` (in particular any weak solution of the Hodge
wave equation in `C¹(Γ(T))`), and `ξₕ ∈ K` the semi-discrete solution. Then, with
`e = P ξ - ξ` measured in `E`,
`‖ξ(t) - ξₕ(t)‖ ≤ ‖P ξ(t₀) - ξₕ(t₀)‖ + ‖e(t)‖ + (t - t₀) ‖e(t₀)‖ + (1 + (t - t₀)) ∫ ‖e'‖`.
[QuennevilleBelair2015], Thm 4.14 -/
theorem norm_sub_le_of_semidiscrete (K : Submodule 𝕜 T.GraphSpace) [FiniteDimensional 𝕜 K]
    {ξ ξ' ξh ξh' : ℝ → T.GraphSpace} {t₀ t₁ : ℝ}
    (hξc : ContinuousOn ξ (Icc t₀ t₁)) (hξ'c : ContinuousOn ξ' (Icc t₀ t₁))
    (hξd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt ξ (ξ' t) (Ici t) t)
    (hξ : ∀ t ∈ Ico t₀ t₁, ∀ ψ ∈ K,
      ⟪T.graphFst ψ, T.graphFst (ξ' t)⟫ + waveForm T (ξ t) ψ = 0)
    (hξhc : ContinuousOn ξh (Icc t₀ t₁)) (hξhK : ∀ t ∈ Icc t₀ t₁, ξh t ∈ K)
    (hξhd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt ξh (ξh' t) (Ici t) t)
    (hξh : ∀ t ∈ Ico t₀ t₁, ∀ ψ ∈ K,
      ⟪T.graphFst ψ, T.graphFst (ξh' t)⟫ + waveForm T (ξh t) ψ = 0) :
    ∀ t ∈ Icc t₀ t₁, ‖T.graphFst (ξ t - ξh t)‖ ≤
      ‖T.graphFst (ellipticProjection K (ξ t₀) - ξh t₀)‖ +
      ‖T.graphFst (ellipticProjection K (ξ t) - ξ t)‖ +
      (t - t₀) * ‖T.graphFst (ellipticProjection K (ξ t₀) - ξ t₀)‖ +
      (1 + (t - t₀)) * ∫ s in t₀..t, ‖T.graphFst (ellipticProjection K (ξ' s) - ξ' s)‖ :=
  GalerkinEvolution.error_bound_refined T.graphFst (fun x ψ => waveForm T x ψ)
    (fun x y ψ => by rw [_root_.map_sub, _root_.sub_apply]) K
    (fun ψ _ => (re_waveForm_self ψ).ge) (ellipticProjection K) (ellipticProjection_mem K)
    (fun ζ ψ hψ => by
      have h := shiftedForm_ellipticProjection_sub K ζ hψ
      rwa [shiftedForm_apply] at h)
    hξc hξ'c hξd hξ hξhc hξhK hξhd hξh

end Feec.HodgeWave
