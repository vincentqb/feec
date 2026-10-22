module

public import Feec.HilbertComplex.Approximation.SemidiscreteWave
public import Feec.HilbertComplex.Approximation.Subcomplex
public import Feec.HilbertComplex.HodgeWave

/-!
# Convergence of the semi-discrete Hodge wave equation

Let `T : E →ₗ.[𝕜] E` be closed and densely defined with `T T = 0` (the total differential `𝐝`
of a finite Hilbert complex, any length) and `L = T - T†` its Hodge wave operator. The weak
Hodge wave equation is posed on the graph space `V = Γ(T)`; a semi-discretization takes a
finite-dimensional `K ⊆ Γ(T)` (e.g. the total space of a finite element subcomplex) and seeks
`ξₕ(t) ∈ K` with `⟪ψ, ξₕ'⟫ + a(ξₕ, ψ) = 0` for `ψ ∈ K` (`IsSemidiscreteSolution`).

## Main results

* `exists_isSemidiscreteSolution`, `IsSemidiscreteSolution.norm_sub_le`,
  `IsSemidiscreteSolution.eqOn`: the semi-discrete problem (4.10) is well posed and `E`-stable.
* `norm_ellipticProjection_le`: for a subcomplex (`d K ⊆ K`) the elliptic projection (4.11)
  is bounded by `√12 ‖A‖`, uniformly in `K` (the inf-sup constant `1/√12` of Prop 4.13, via
  the test map `ξ ↦ ξ - d ξ`).
* `exists_isGraphSolution`: for `ξ₀ ∈ D(L²)` the exact solution lies in `C¹([a,b]; Γ(T))`
  (the hypothesis of Thm 4.14), as the orbit `e^{tL} ξ₀` read in `Γ(T)`.
* `tendstoUniformlyOn_of_isGraphSolution`, `tendstoUniformlyOn_semidiscrete`: convergence in
  `L∞(a,b; E)` for `D(L²)` data under the density hypothesis.
* `tendstoUniformlyOn_of_tendsto` (data in `E`, limit `e^{tL} ξ₀`),
  `tendstoUniformlyOn_ellipticProjection` (data in `D(L)` with `ξₕ(a) = Pₕ ξ₀`) and
  `tendstoUniformlyOn_of_isWeakSolution` (the thesis' weak solution): convergence without a
  rate, by stability plus density; `norm_sub_le_of_comparison`: the comparison-datum bound.
* `HilbertComplex.Subcomplex.graphSub`: the total space of a subcomplex in `Γ(𝐝)`, finite
  dimensional and `d`-invariant.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.6 ((4.10), (4.11), Prop 4.13, Thm 4.14 and the convergence remark after it), §4.4 (Thm 4.6,
  (4.7)–(4.8))
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.2 (Thm 2.4, density of `D(A²)`), §1.10
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
  (FEEC convergence of the discrete Hodge Laplacian)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  Thms 3.8–3.9 (stability and quasi-optimality)
* [T. Dupont, *L²-estimates for Galerkin methods for second order hyperbolic equations*][Dupont1973]
* [G. A. Baker, *Error estimates for finite element methods for second order hyperbolic equations*][Baker1976]
* [T. Geveci, *On the application of mixed finite element methods to the wave equations*][Geveci1988]
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Set Filter LinearPMap Feec.Variational

@[expose] public noncomputable section

namespace Feec.HodgeWave

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {T : E →ₗ.[𝕜] E}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- `‖v‖² = ‖v₁‖² + ‖v₂‖²` in the graph space. -/
theorem norm_sq_graphSpace (v : T.GraphSpace) :
    ‖v‖ ^ 2 = ‖T.graphFst v‖ ^ 2 + ‖T.graphSnd v‖ ^ 2 := by
  obtain ⟨x, rfl, -, -⟩ := T.exists_toGraphSpace_eq v
  exact WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 ((x : E), T x))

theorem norm_graphFst_le (v : T.GraphSpace) : ‖T.graphFst v‖ ≤ ‖v‖ := by
  have := norm_sq_graphSpace v
  nlinarith [norm_nonneg (T.graphFst v), norm_nonneg v, sq_nonneg ‖T.graphSnd v‖]

/-! ### The semi-discrete operator -/

section Operator

variable (T) in
/-- The **mass form** `m(ξ, ψ) = ⟪ψ, ξ⟫_E` on the graph space. -/
def massForm : T.GraphSpace →L[𝕜] T.GraphSpace →L⋆[𝕜] 𝕜 :=
  (innerSLFlip 𝕜).bilinearComp T.graphFst T.graphFst

theorem massForm_apply (x ψ : T.GraphSpace) : massForm T x ψ = ⟪T.graphFst ψ, T.graphFst x⟫ := by
  simp [massForm]

variable (K : Submodule 𝕜 T.GraphSpace) [FiniteDimensional 𝕜 K]

omit [FiniteDimensional 𝕜 K] in
theorem injective_restrict_massForm :
    Function.Injective (Variational.restrict (massForm T) K K) := by
  intro x y hxy
  have h0 : Variational.restrict (massForm T) K K (x - y) = 0 := by
    rw [_root_.map_sub, hxy, sub_self]
  have h1 := congrArg (fun f => f (x - y)) h0
  simp only [Variational.restrict_apply, _root_.zero_apply, massForm_apply,
    inner_self_eq_zero] at h1
  exact sub_eq_zero.1 (Subtype.ext (T.graphFst_injective (h1.trans (_root_.map_zero _).symm)))

theorem surjective_restrict_massForm :
    Function.Surjective (Variational.restrict (massForm T) K K) := by
  set B := Variational.restrict (massForm T) K K
  have hinj : Function.Injective B := injective_restrict_massForm K
  set R : K →L[𝕜] K := rieszOp (𝕜 := 𝕜) (X := K) (Y := K) B
  have hR : Function.Injective (R : K →ₗ[𝕜] K) := fun x y hxy => hinj (by
    rw [← innerSLFlip_rieszOp (X := K) (Y := K) B x, ← innerSLFlip_rieszOp (X := K) (Y := K) B y]
    exact congrArg _ hxy)
  have hRs : Function.Surjective (R : K →ₗ[𝕜] K) := LinearMap.injective_iff_surjective.1 hR
  intro f
  obtain ⟨g, rfl⟩ := innerSLFlip_surjective f
  obtain ⟨x, hx⟩ := hRs g
  refine ⟨x, ?_⟩
  rw [← innerSLFlip_rieszOp (X := K) (Y := K) B x]
  exact congrArg _ hx

/-- `m|_K : K ≃ K*` (antidual). -/
def massFormEquiv : K ≃L[𝕜] (K →L⋆[𝕜] 𝕜) :=
  ContinuousLinearEquiv.ofBijective (E := K) (Variational.restrict (massForm T) K K)
    (LinearMap.ker_eq_bot.2 (injective_restrict_massForm K))
    (LinearMap.range_eq_top.2 (surjective_restrict_massForm K))

/-- The **semi-discrete operator** `Mₕ : K → K`, `⟪ψ, Mₕ ξ⟫ = -a(ξ, ψ)` for `ψ ∈ K`, so that the
semi-discrete Hodge wave equation (4.10) is the ODE `ξₕ' = Mₕ ξₕ`. -/
def semidiscreteOp : K →L[𝕜] K :=
  ((massFormEquiv K).symm : (K →L⋆[𝕜] 𝕜) →L[𝕜] K).comp (-Variational.restrict (waveForm T) K K)

theorem semidiscreteOp_spec (x ψ : K) :
    ⟪T.graphFst ψ, T.graphFst (semidiscreteOp K x)⟫ + waveForm T x ψ = 0 := by
  have h := (massFormEquiv K).apply_symm_apply (-Variational.restrict (waveForm T) K K x)
  have := congrArg (fun f => f ψ) h
  simp only [_root_.neg_apply, Variational.restrict_apply] at this
  change massForm T (semidiscreteOp K x : T.GraphSpace) ψ = -waveForm T x ψ at this
  rw [massForm_apply] at this
  rw [this, neg_add_cancel]

end Operator

/-! ### Semi-discrete solutions -/

section Semidiscrete

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- `ξₕ` is a **solution of the semi-discrete Hodge wave equation** (4.10) in `K` on the time
set `I`: `ξₕ(t) ∈ K`, `ξₕ' = ξₕ'` within `I`, and `⟪ψ, ξₕ'⟫ + a(ξₕ, ψ) = 0` for `ψ ∈ K`.
See [QuennevilleBelair2015], (4.10) (§4.6); the FEEC semi-discretization of evolution problems is
[GilletteHolstZhu2017] (the thesis cites its 2012 preprint). -/
structure IsSemidiscreteSolution (K : Submodule 𝕜 T.GraphSpace) (I : Set ℝ)
    (ξh ξh' : ℝ → T.GraphSpace) : Prop where
  mem : ∀ t ∈ I, ξh t ∈ K
  deriv : ∀ t ∈ I, HasDerivWithinAt ξh (ξh' t) I t
  eq : ∀ t ∈ I, ∀ ψ ∈ K, ⟪T.graphFst ψ, T.graphFst (ξh' t)⟫ + waveForm T (ξh t) ψ = 0

variable {K : Submodule 𝕜 T.GraphSpace}

theorem IsSemidiscreteSolution.continuousOn {I : Set ℝ} {ξh ξh' : ℝ → T.GraphSpace}
    (h : IsSemidiscreteSolution K I ξh ξh') : ContinuousOn ξh I :=
  fun t ht => (h.deriv t ht).continuousWithinAt

theorem IsSemidiscreteSolution.mono {I J : Set ℝ} {ξh ξh' : ℝ → T.GraphSpace}
    (h : IsSemidiscreteSolution K I ξh ξh') (hJ : J ⊆ I) : IsSemidiscreteSolution K J ξh ξh' :=
  ⟨fun t ht => h.mem t (hJ ht), fun t ht => (h.deriv t (hJ ht)).mono hJ,
    fun t ht => h.eq t (hJ ht)⟩

/-- **`E`-stability of the semi-discrete Hodge wave equation** (energy method,
`re a(ψ, ψ) = 0`): `‖ξ₁(t) - ξ₂(t)‖_E ≤ ‖ξ₁(a) - ξ₂(a)‖_E` on `[a, b]`, uniformly in `K`.
See [QuennevilleBelair2015], §4.6. -/
theorem IsSemidiscreteSolution.norm_sub_le {a b : ℝ} {ξ₁ ξ₁' ξ₂ ξ₂' : ℝ → T.GraphSpace}
    (h₁ : IsSemidiscreteSolution K (Icc a b) ξ₁ ξ₁')
    (h₂ : IsSemidiscreteSolution K (Icc a b) ξ₂ ξ₂') :
    ∀ t ∈ Icc a b, ‖T.graphFst (ξ₁ t - ξ₂ t)‖ ≤ ‖T.graphFst (ξ₁ a - ξ₂ a)‖ := by
  have hd : ∀ t ∈ Ico a b, HasDerivWithinAt (fun s => T.graphFst (ξ₁ s - ξ₂ s))
      (T.graphFst (ξ₁' t - ξ₂' t)) (Ici t) t := fun t ht =>
    ((T.graphFst.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      (((h₁.deriv t (Ico_subset_Icc_self ht)).sub
        (h₂.deriv t (Ico_subset_Icc_self ht))))).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  refine Evolution.Energy.norm_le_of_re_inner_deriv_nonpos (𝕜 := 𝕜)
    (T.graphFst.continuous.comp_continuousOn (h₁.continuousOn.sub h₂.continuousOn)) hd
    fun t ht => ?_
  have ht' := Ico_subset_Icc_self ht
  set ψ := ξ₁ t - ξ₂ t
  have hψ : ψ ∈ K := K.sub_mem (h₁.mem t ht') (h₂.mem t ht')
  have E1 := h₁.eq t ht' ψ hψ
  have E2 := h₂.eq t ht' ψ hψ
  have hw : waveForm T (ξ₁ t) ψ - waveForm T (ξ₂ t) ψ = waveForm T ψ ψ := by
    simp only [ψ, _root_.map_sub, _root_.sub_apply]; abel
  have key : ⟪T.graphFst ψ, T.graphFst (ξ₁' t - ξ₂' t)⟫ = -waveForm T ψ ψ := by
    rw [show T.graphFst (ξ₁' t - ξ₂' t) = T.graphFst (ξ₁' t) - T.graphFst (ξ₂' t) from
      _root_.map_sub _ _ _, inner_sub_right, ← hw]
    linear_combination E1 - E2
  rw [← inner_conj_symm, RCLike.conj_re, key, _root_.map_neg, re_waveForm_self, neg_zero]

/-- **Uniqueness** of semi-discrete solutions. -/
theorem IsSemidiscreteSolution.eqOn {a b : ℝ} {ξ₁ ξ₁' ξ₂ ξ₂' : ℝ → T.GraphSpace}
    (h₁ : IsSemidiscreteSolution K (Icc a b) ξ₁ ξ₁')
    (h₂ : IsSemidiscreteSolution K (Icc a b) ξ₂ ξ₂') (h0 : ξ₁ a = ξ₂ a) :
    EqOn ξ₁ ξ₂ (Icc a b) := fun t ht => by
  have := h₁.norm_sub_le h₂ t ht
  rw [h0, sub_self, _root_.map_zero, norm_zero, norm_le_zero_iff,
    ← _root_.map_zero T.graphFst] at this
  exact sub_eq_zero.1 (T.graphFst_injective this)

variable (K) [FiniteDimensional 𝕜 K]

/-- **Existence for the semi-discrete Hodge wave equation** (4.10): for every `ξ₀ ∈ K` the
solution `ξₕ(t) = e^{(t-a) Mₕ} ξ₀` exists for all times, with continuous derivative.
See [QuennevilleBelair2015], (4.10) (§4.6). -/
theorem exists_isSemidiscreteSolution {ξ₀ : T.GraphSpace} (h₀ : ξ₀ ∈ K) (a : ℝ) :
    ∃ ξh ξh' : ℝ → T.GraphSpace, ξh a = ξ₀ ∧ Continuous ξh' ∧
      (∀ t, HasDerivAt ξh (ξh' t) t) ∧ IsSemidiscreteSolution K univ ξh ξh' := by
  set M := semidiscreteOp K
  set G := C0Group.ofBounded M
  set x₀ : K := ⟨ξ₀, h₀⟩
  have hdom : ∀ x : K, x ∈ G.generator.domain := C0Group.mem_domain_generator_ofBounded M
  have hgen : ∀ x : K, G.generator ⟨x, hdom x⟩ = M x := fun x =>
    C0Group.generator_ofBounded_apply M ⟨x, hdom x⟩
  set f : ℝ → K := fun t => G.S (t - a) x₀
  have hf : ∀ t, HasDerivAt f (M (f t)) t := fun t => by
    have h := (G.hasDerivAt_apply ⟨x₀, hdom x₀⟩ (t - a)).comp_sub_const t a
    rw [hgen] at h
    convert h using 1
    change M (G.S (t - a) x₀) = G.S (t - a) (M x₀)
    have := G.generator_apply_S ⟨x₀, hdom x₀⟩ (t - a)
    rw [hgen, hgen] at this
    exact this
  refine ⟨fun t => (f t : T.GraphSpace), fun t => (M (f t) : T.GraphSpace), ?_, ?_, fun t => ?_,
    ⟨fun t _ => (f t).2, fun t _ => ?_, fun t _ ψ hψ => ?_⟩⟩
  · simp [f, x₀]
  · exact continuous_subtype_val.comp (M.continuous.comp (G.strongCont x₀ |>.comp
      (continuous_id.sub continuous_const)))
  · exact (K.subtypeL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hf t)
  · exact ((K.subtypeL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hf t)).hasDerivWithinAt
  · exact semidiscreteOp_spec K (f t) ⟨ψ, hψ⟩

end Semidiscrete

/-! ### Uniform stability of the elliptic projection on subcomplexes (Prop 4.13) -/

section Stability

variable (hmaps : ∀ x : T.domain, (T x : E) ∈ T.domain)
  (hcomp : ∀ x : T.domain, T ⟨T x, hmaps x⟩ = 0)

include hcomp in
theorem graphSnd_mem_graphL2 (v : T.GraphSpace) :
    WithLp.toLp 2 (T.graphSnd v, (0 : E)) ∈ T.graphL2 := by
  obtain ⟨x, rfl, -, -⟩ := T.exists_toGraphSpace_eq v
  rw [mem_graphL2, WithLp.ofLp_toLp, LinearPMap.mem_graph_iff]
  exact ⟨⟨T x, hmaps x⟩, rfl, hcomp x⟩

/-- The differential on the graph space, `d (x, T x) = (T x, 0)` (`T T = 0`). -/
def graphD : T.GraphSpace →L[𝕜] T.GraphSpace :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨WithLp.toLp 2 (T.graphSnd v, (0 : E)), graphSnd_mem_graphL2 hmaps hcomp v⟩
      map_add' := fun v w => Subtype.ext (WithLp.ofLp_injective 2 (by simp))
      map_smul' := fun c v => Subtype.ext (WithLp.ofLp_injective 2 (by simp)) }
    1 fun v => by
      rw [one_mul]
      have h : ‖(⟨WithLp.toLp 2 (T.graphSnd v, (0 : E)), graphSnd_mem_graphL2 hmaps hcomp v⟩ :
          T.GraphSpace)‖ = ‖T.graphSnd v‖ := by
        change ‖WithLp.toLp 2 (T.graphSnd v, (0 : E))‖ = _
        rw [WithLp.prod_norm_eq_of_L2]; simp
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [h]
      have := norm_sq_graphSpace v
      nlinarith [norm_nonneg (T.graphSnd v), norm_nonneg v, sq_nonneg ‖T.graphFst v‖]

@[simp] theorem graphFst_graphD (v : T.GraphSpace) :
    T.graphFst (graphD hmaps hcomp v) = T.graphSnd v := rfl

@[simp] theorem graphSnd_graphD (v : T.GraphSpace) : T.graphSnd (graphD hmaps hcomp v) = 0 := rfl

/-- **Inf-sup by the test map `ξ ↦ ξ - d ξ`** (thesis Prop 4.13, for every operator with
`T T = 0`, i.e. every finite Hilbert complex of any length): on every `d`-invariant `K ⊆ Γ(T)`
the shifted form `A = ⟪·,·⟫ + a` satisfies the inf-sup condition with constant `1/√12`.
See [QuennevilleBelair2015], Prop. 4.13. Without the lower-order term the corresponding discrete
stability is the FEEC result [AFW2006], [AFW2010], Thm 3.8, recalled by the thesis after Prop 4.13;
here the test map gives the shifted form directly on every `d`-invariant `K`. -/
theorem infSup_shiftedForm (K : Submodule 𝕜 T.GraphSpace)
    (hK : ∀ ξ ∈ K, graphD hmaps hcomp ξ ∈ K) :
    InfSup (Variational.restrict (shiftedForm T) K K) ((1 / 2) / √3) := by
  refine InfSup.restrict_of_testMap K K (fun ξ => ξ - graphD hmaps hcomp ξ)
    (fun ξ hξ => K.sub_mem hξ (hK ξ hξ)) (by norm_num) (by positivity) (fun ξ _ => ?_)
    (fun ξ _ => ?_)
  · have h1 := norm_sq_graphSpace ξ
    have h2 := norm_sq_graphSpace (ξ - graphD hmaps hcomp ξ)
    simp only [_root_.map_sub, graphFst_graphD, graphSnd_graphD, sub_zero] at h2
    have h3 := norm_sub_le (T.graphFst ξ) (T.graphSnd ξ)
    have h4 : ‖ξ - graphD hmaps hcomp ξ‖ ^ 2 ≤ (√3 * ‖ξ‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), h2]
      nlinarith [norm_nonneg (T.graphFst ξ), norm_nonneg (T.graphSnd ξ),
        norm_nonneg (T.graphFst ξ - T.graphSnd ξ), sq_nonneg (‖T.graphFst ξ‖ - ‖T.graphSnd ξ‖)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h4
  · rw [shiftedForm_apply, waveForm_apply]
    simp only [_root_.map_sub, graphFst_graphD, graphSnd_graphD, sub_zero, inner_sub_left]
    have h1 := norm_sq_graphSpace ξ
    have hre : RCLike.re (⟪T.graphFst ξ, T.graphFst ξ⟫ - ⟪T.graphSnd ξ, T.graphFst ξ⟫ +
        (⟪T.graphSnd ξ, T.graphFst ξ⟫ - (⟪T.graphFst ξ, T.graphSnd ξ⟫ -
          ⟪T.graphSnd ξ, T.graphSnd ξ⟫))) =
        ‖T.graphFst ξ‖ ^ 2 + ‖T.graphSnd ξ‖ ^ 2 - RCLike.re ⟪T.graphFst ξ, T.graphSnd ξ⟫ := by
      simp only [_root_.map_add, _root_.map_sub, inner_self_eq_norm_sq]; ring
    rw [hre]
    have hcs := (RCLike.re_le_norm (⟪T.graphFst ξ, T.graphSnd ξ⟫)).trans
      (norm_inner_le_norm (𝕜 := 𝕜) (T.graphFst ξ) (T.graphSnd ξ))
    nlinarith [sq_nonneg (‖T.graphFst ξ‖ - ‖T.graphSnd ξ‖)]

/-- **Uniform bound on the elliptic projection** of a subcomplex: `‖P_K ζ‖ ≤ √12 ‖A‖ ‖ζ‖` for
every finite-dimensional `d`-invariant `K` (thesis: `‖Πₕ‖ ≤ 2√12`). See
[QuennevilleBelair2015], Prop. 4.13 and (4.11). -/
theorem norm_ellipticProjection_le (K : Submodule 𝕜 T.GraphSpace) [FiniteDimensional 𝕜 K]
    (hK : ∀ ξ ∈ K, graphD hmaps hcomp ξ ∈ K) (ζ : T.GraphSpace) :
    ‖ellipticProjection K ζ‖ ≤ ‖shiftedForm T‖ / ((1 / 2) / √3) * ‖ζ‖ :=
  (infSup_shiftedForm hmaps hcomp K hK).norm_le_of_restrict_eq (ellipticProjection_mem K ζ)
    fun _ hψ => shiftedForm_ellipticProjection K ζ hψ

/-- **Quasi-optimality of the elliptic projection** on a subcomplex:
`‖ζ - P_K ζ‖ ≤ (1 + √12 ‖A‖) ‖ζ - w‖` for every `w ∈ K`. [QuennevilleBelair2015], §4.6 reduces
Thm 4.14 to this estimate; it plays the role of the quasi-optimality [AFW2010], Thm 3.9 (cf.
[AFW2006]) for `dd* + d*d + I`. The thesis notes that the known FEEC convergence [AFW2006],
[AFW2010] needs the compactness property and defers the lower-order term to a result of Arnold and
Li; neither is needed here: the bound follows from `infSup_shiftedForm` on every subcomplex. -/
theorem norm_sub_ellipticProjection_le (K : Submodule 𝕜 T.GraphSpace) [FiniteDimensional 𝕜 K]
    (hK : ∀ ξ ∈ K, graphD hmaps hcomp ξ ∈ K) (ζ : T.GraphSpace) {w : T.GraphSpace}
    (hw : w ∈ K) :
    ‖ζ - ellipticProjection K ζ‖ ≤ (1 + ‖shiftedForm T‖ / ((1 / 2) / √3)) * ‖ζ - w‖ :=
  (infSup_shiftedForm hmaps hcomp K hK).norm_sub_le_of_orthogonal (ellipticProjection_mem K ζ)
    (fun ψ hψ => by
      have h := shiftedForm_ellipticProjection_sub K ζ hψ
      rw [_root_.map_sub, _root_.sub_apply] at h ⊢
      rw [← neg_sub, h, neg_zero]) hw

end Stability

/-! ### Exact solutions in `C¹(Γ(T))` and convergence for them -/

section Convergence

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- `ξ` is a **weak solution of the Hodge wave equation in `C¹(I; Γ(T))`**: `ξ`, `ξ'` continuous
into the graph space, `ξ' = ξ'` within `I`, and `⟪ψ, ξ'⟫ + a(ξ, ψ) = 0` for all `ψ ∈ Γ(T)` (the
class assumed by thesis Thm 4.14). See [QuennevilleBelair2015], (4.8), Thm 4.14. -/
structure IsGraphSolution (I : Set ℝ) (ξ ξ' : ℝ → T.GraphSpace) : Prop where
  continuousOn_deriv : ContinuousOn ξ' I
  deriv : ∀ t ∈ I, HasDerivWithinAt ξ (ξ' t) I t
  eq : ∀ t ∈ I, ∀ ψ : T.GraphSpace, ⟪T.graphFst ψ, T.graphFst (ξ' t)⟫ + waveForm T (ξ t) ψ = 0

theorem IsGraphSolution.continuousOn {I : Set ℝ} {ξ ξ' : ℝ → T.GraphSpace}
    (h : IsGraphSolution I ξ ξ') : ContinuousOn ξ I :=
  fun t ht => (h.deriv t ht).continuousWithinAt

/-- A graph solution is a semi-discrete solution for `K = Γ(T)`. -/
theorem IsGraphSolution.isSemidiscreteSolution_top {I : Set ℝ} {ξ ξ' : ℝ → T.GraphSpace}
    (h : IsGraphSolution I ξ ξ') : IsSemidiscreteSolution ⊤ I ξ ξ' :=
  ⟨fun _ _ => Submodule.mem_top, h.deriv, fun t ht ψ _ => h.eq t ht ψ⟩

/-- **Uniqueness of weak solutions in `C¹(Γ(T))`** (energy method; thesis l. 2120). -/
theorem IsGraphSolution.eqOn {a b : ℝ} {ξ₁ ξ₁' ξ₂ ξ₂' : ℝ → T.GraphSpace}
    (h₁ : IsGraphSolution (Icc a b) ξ₁ ξ₁') (h₂ : IsGraphSolution (Icc a b) ξ₂ ξ₂')
    (h0 : ξ₁ a = ξ₂ a) : EqOn ξ₁ ξ₂ (Icc a b) :=
  h₁.isSemidiscreteSolution_top.eqOn h₂.isSemidiscreteSolution_top h0

/-- **The error estimate of Thm 4.14** for a graph solution: `norm_sub_le_of_semidiscrete`
with the right derivatives of the solutions. See [QuennevilleBelair2015], Thm 4.14. -/
theorem IsGraphSolution.norm_sub_le {K : Submodule 𝕜 T.GraphSpace} [FiniteDimensional 𝕜 K]
    {a b : ℝ} {ξ ξ' ξh ξh' : ℝ → T.GraphSpace} (hξ : IsGraphSolution (Icc a b) ξ ξ')
    (hξh : IsSemidiscreteSolution K (Icc a b) ξh ξh') :
    ∀ t ∈ Icc a b, ‖T.graphFst (ξ t - ξh t)‖ ≤
      ‖T.graphFst (ellipticProjection K (ξ a) - ξh a)‖ +
      ‖T.graphFst (ellipticProjection K (ξ t) - ξ t)‖ +
      (t - a) * ‖T.graphFst (ellipticProjection K (ξ a) - ξ a)‖ +
      (1 + (t - a)) * ∫ s in a..t, ‖T.graphFst (ellipticProjection K (ξ' s) - ξ' s)‖ :=
  norm_sub_le_of_semidiscrete K hξ.continuousOn hξ.continuousOn_deriv
    (fun t ht => (hξ.deriv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht ψ _ => hξ.eq t (Ico_subset_Icc_self ht) ψ) hξh.continuousOn hξh.mem
    (fun t ht => (hξh.deriv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => hξh.eq t (Ico_subset_Icc_self ht))

variable {ι : Type*}

/-- A family of finite-dimensional discrete spaces `Kₕ ⊆ Γ(T)` is **approximating** along `l`:
the elliptic projections are uniformly bounded (automatic for subcomplexes,
`norm_ellipticProjection_le`) and every `ζ ∈ Γ(T)` is eventually approximated by `Kₕ` (the
density hypothesis of thesis §4.6). See [QuennevilleBelair2015], §4.6. -/
structure IsApproximating (l : Filter ι) (K : ι → Submodule 𝕜 T.GraphSpace)
    [∀ h, FiniteDimensional 𝕜 (K h)] : Prop where
  bound : ∃ C, ∀ h ζ, ‖ellipticProjection (K h) ζ‖ ≤ C * ‖ζ‖
  dense : ∀ ζ : T.GraphSpace, ∀ δ > 0, ∀ᶠ h in l, ∃ w ∈ K h, ‖ζ - w‖ < δ

variable {l : Filter ι} {K : ι → Submodule 𝕜 T.GraphSpace} [∀ h, FiniteDimensional 𝕜 (K h)]

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- **The elliptic projections converge to the identity, uniformly on compact sets.** -/
theorem IsApproximating.tendstoUniformlyOn_ellipticProjection (hK : IsApproximating l K)
    {S : Set T.GraphSpace} (hS : IsCompact S) :
    TendstoUniformlyOn (fun h ζ => ellipticProjection (K h) ζ) id l S := by
  obtain ⟨C, hC⟩ := hK.bound
  set C' := max C 0
  have hqo : ∀ h ζ, ∀ w ∈ K h, ‖ζ - ellipticProjection (K h) ζ‖ ≤ (1 + C') * ‖ζ - w‖ :=
    fun h ζ w hw => by
      have e : ζ - ellipticProjection (K h) ζ =
          (ζ - w) - ellipticProjection (K h) (ζ - w) := by
        rw [_root_.map_sub, ellipticProjection_of_mem (K h) hw]; abel
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      have := (hC h (ζ - w)).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _))
      linarith
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ : 0 < ε / (2 * (1 + C')) := by positivity
  obtain ⟨t, htS, htf, hcov⟩ := hS.finite_cover_balls hδ
  have hev : ∀ᶠ h in l, ∀ z ∈ t, ∃ w ∈ K h, ‖z - w‖ < ε / (2 * (1 + C')) :=
    (htf.eventually_all).2 fun z _ => hK.dense z _ hδ
  filter_upwards [hev] with h hh ζ hζ
  obtain ⟨z, hz, hζz⟩ := mem_iUnion₂.1 (hcov hζ)
  obtain ⟨w, hw, hzw⟩ := hh z hz
  rw [Metric.mem_ball, dist_eq_norm] at hζz
  rw [dist_eq_norm, id]
  calc ‖ζ - ellipticProjection (K h) ζ‖ ≤ (1 + C') * ‖ζ - w‖ := hqo h ζ w hw
    _ ≤ (1 + C') * (‖ζ - z‖ + ‖z - w‖) := by
        gcongr; exact (norm_sub_le_norm_sub_add_norm_sub ζ z w)
    _ < (1 + C') * (ε / (2 * (1 + C')) + ε / (2 * (1 + C'))) := by gcongr
    _ = ε := by
        have : (1 + C') ≠ 0 := by positivity
        field_simp; ring

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem IsApproximating.tendsto_ellipticProjection (hK : IsApproximating l K) (ζ : T.GraphSpace) :
    Tendsto (fun h => ellipticProjection (K h) ζ) l (𝓝 ζ) := by
  have := (hK.tendstoUniformlyOn_ellipticProjection isCompact_singleton).tendsto_at
    (mem_singleton ζ)
  simpa using this

/-- **Convergence of the semi-discrete method for solutions in `C¹(Γ(T))`**: under the density
hypothesis, `ξₕ → ξ` in `E`, uniformly on `[a, b]`, as soon as the initial errors
`‖Pₕ ξ(a) - ξₕ(a)‖_E` tend to `0`. See [QuennevilleBelair2015], Thm 4.14 and the convergence
remark after it. -/
theorem tendstoUniformlyOn_of_isGraphSolution (hK : IsApproximating l K) {a b : ℝ}
    {ξ ξ' : ℝ → T.GraphSpace} (hξ : IsGraphSolution (Icc a b) ξ ξ')
    {ξh ξh' : ι → ℝ → T.GraphSpace}
    (hξh : ∀ h, IsSemidiscreteSolution (K h) (Icc a b) (ξh h) (ξh' h))
    (h0 : Tendsto (fun h => ‖T.graphFst (ellipticProjection (K h) (ξ a) - ξh h a)‖) l (𝓝 0)) :
    TendstoUniformlyOn (fun h t => T.graphFst (ξh h t)) (fun t => T.graphFst (ξ t)) l
      (Icc a b) := by
  rcases lt_or_ge b a with hba | hab
  · rw [Icc_eq_empty_of_lt hba]; exact tendstoUniformlyOn_empty
  have hS1 : IsCompact (ξ '' Icc a b) := isCompact_Icc.image_of_continuousOn hξ.continuousOn
  have hS2 : IsCompact (ξ' '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn hξ.continuousOn_deriv
  have u1 := Metric.tendstoUniformlyOn_iff.1 (hK.tendstoUniformlyOn_ellipticProjection hS1)
  have u2 := Metric.tendstoUniformlyOn_iff.1 (hK.tendstoUniformlyOn_ellipticProjection hS2)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set M : ℝ := 2 + 2 * (b - a) + (b - a) ^ 2 + 1
  have hM : 0 < M := by positivity
  have hη : 0 < ε / (2 * M) := by positivity
  filter_upwards [u1 _ hη, u2 _ hη, (tendsto_order.1 h0).2 _ (half_pos hε)] with h h1 h2 h3
  intro t ht
  have e1 : ∀ s ∈ Icc a b, ‖T.graphFst (ellipticProjection (K h) (ξ s) - ξ s)‖ ≤ ε / (2 * M) :=
    fun s hs => by
      refine (norm_graphFst_le _).trans ?_
      have := h1 _ (mem_image_of_mem ξ hs)
      rw [dist_eq_norm, id, norm_sub_rev] at this
      exact this.le
  have e2 : ∀ s ∈ Icc a b, ‖T.graphFst (ellipticProjection (K h) (ξ' s) - ξ' s)‖ ≤ ε / (2 * M) :=
    fun s hs => by
      refine (norm_graphFst_le _).trans ?_
      have := h2 _ (mem_image_of_mem ξ' hs)
      rw [dist_eq_norm, id, norm_sub_rev] at this
      exact this.le
  have hint : ∫ s in a..t, ‖T.graphFst (ellipticProjection (K h) (ξ' s) - ξ' s)‖ ≤
      (t - a) * (ε / (2 * M)) := by
    have hcont : ContinuousOn (fun s => ‖T.graphFst (ellipticProjection (K h) (ξ' s) - ξ' s)‖)
        (Icc a t) := (T.graphFst.continuous.comp_continuousOn
          (((ellipticProjection (K h)).continuous.comp_continuousOn hξ.continuousOn_deriv).sub
            hξ.continuousOn_deriv)).norm.mono (Icc_subset_Icc le_rfl ht.2)
    have := intervalIntegral.integral_mono_on ht.1 (hcont.intervalIntegrable_of_Icc ht.1)
      (intervalIntegrable_const (μ := MeasureTheory.volume)) fun s hs =>
        e2 s ⟨hs.1, hs.2.trans ht.2⟩
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using this
  have hb := hξ.norm_sub_le (hξh h) t ht
  rw [dist_eq_norm, ← _root_.map_sub]
  have hta : 0 ≤ t - a := sub_nonneg.2 ht.1
  have htb : t - a ≤ b - a := by linarith [ht.2]
  have h3' : ‖T.graphFst (ellipticProjection (K h) (ξ a) - ξh h a)‖ < ε / 2 := by
    simpa using h3
  have ea := e1 a ⟨le_rfl, hab⟩
  have et := e1 t ht
  calc ‖T.graphFst (ξ t - ξh h t)‖ ≤ _ := hb
    _ < ε / 2 + ε / (2 * M) + (b - a) * (ε / (2 * M)) +
        (1 + (b - a)) * ((b - a) * (ε / (2 * M))) := by
      have hη0 := hη.le
      have i1 : (t - a) * ‖T.graphFst (ellipticProjection (K h) (ξ a) - ξ a)‖ ≤
          (b - a) * (ε / (2 * M)) := mul_le_mul htb ea (norm_nonneg _) (by linarith)
      have i2 : (1 + (t - a)) * ∫ s in a..t, ‖T.graphFst (ellipticProjection (K h) (ξ' s) - ξ' s)‖
          ≤ (1 + (b - a)) * ((b - a) * (ε / (2 * M))) := by
        refine mul_le_mul (by linarith) (hint.trans ?_) ?_ (by linarith)
        · exact mul_le_mul_of_nonneg_right htb hη0
        · exact intervalIntegral.integral_nonneg ht.1 fun _ _ => norm_nonneg _
      linarith
    _ ≤ ε := by
      have : ε / (2 * M) * (1 + (b - a) + (1 + (b - a)) * (b - a)) ≤ ε / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hε, sub_nonneg.2 hab]
      nlinarith

end Convergence

/-! ### The Hodge wave group: exact solutions for `D(L²)` data -/

section WaveGroup

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  (hT : Dense (T.domain : Set E)) (hc : T.IsClosed)
  (hmaps : ∀ x : T.domain, (T x : E) ∈ T.domain) (hcomp : ∀ x : T.domain, T ⟨T x, hmaps x⟩ = 0)

/-- The **Hodge wave group** `e^{tL}`, `L = T - T†` (Stone): the solution operator of the Hodge
wave equation. See [QuennevilleBelair2015], (4.4), Thm 4.6. -/
def waveGroup : C0Group 𝕜 E := (isSkewAdjoint_sub_adjoint hT hc hmaps hcomp).group

theorem generator_waveGroup : (waveGroup hT hc hmaps hcomp).generator = T - T† :=
  (isSkewAdjoint_sub_adjoint hT hc hmaps hcomp).generator_group

theorem isIsometric_waveGroup : (waveGroup hT hc hmaps hcomp).IsIsometric :=
  (isSkewAdjoint_sub_adjoint hT hc hmaps hcomp).isIsometric_group

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
private theorem apply_of_eq {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    {A B : E →ₗ.[𝕜] F} (h : A = B) (x : A.domain) : A x = B ⟨x, h ▸ x.2⟩ := by
  subst h; rfl

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
include hT hcomp in
/-- `‖T x‖ ≤ ‖L x‖` on `D(L) = D(T) ∩ D(T†)` (`R(T) ⊥ R(T†)`). -/
theorem norm_apply_le_norm_sub_adjoint_apply (x : (T - T†).domain) :
    ‖T ⟨x, x.2.1⟩‖ ≤ ‖(T - T†) x‖ := by
  have h0 : ⟪T ⟨x, x.2.1⟩, T† ⟨x, x.2.2⟩⟫ = 0 :=
    inner_apply_adjoint_apply hT hmaps hcomp ⟨x, x.2.1⟩ ⟨x, x.2.2⟩
  have hsq : ‖(T - T†) x‖ ^ 2 = ‖T ⟨x, x.2.1⟩‖ ^ 2 + ‖T† ⟨x, x.2.2⟩‖ ^ 2 := by
    rw [LinearPMap.sub_apply, @norm_sub_sq 𝕜, h0, _root_.map_zero, mul_zero, sub_zero]
  nlinarith [norm_nonneg (T ⟨x, x.2.1⟩), norm_nonneg ((T - T†) x), sq_nonneg ‖T† ⟨x, x.2.2⟩‖]

/-- The graph-space lift `D(L) → Γ(T)`, `x ↦ (x, T x)`. -/
def liftGraph : (waveGroup hT hc hmaps hcomp).generator.domain →ₗ[𝕜] T.GraphSpace where
  toFun x := T.toGraphSpace ⟨x, (show (x : E) ∈ (T - T†).domain by
    rw [← generator_waveGroup hT hc hmaps hcomp]; exact x.2).1⟩
  map_add' x y := Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext rfl (by
    simp only [toGraphSpace, Submodule.coe_add, WithLp.ofLp_add, Prod.snd_add]
    rw [← LinearPMap.map_add]; rfl)))
  map_smul' c x := Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext rfl (by
    simp only [toGraphSpace, Submodule.coe_smul, WithLp.ofLp_smul, Prod.smul_snd,
      RingHom.id_apply]
    rw [← LinearPMap.map_smul]; rfl)))

@[simp] theorem graphFst_liftGraph (x : (waveGroup hT hc hmaps hcomp).generator.domain) :
    T.graphFst (liftGraph hT hc hmaps hcomp x) = x := rfl

theorem norm_liftGraph_le (x : (waveGroup hT hc hmaps hcomp).generator.domain) :
    ‖liftGraph hT hc hmaps hcomp x‖ ≤
      1 * (‖(x : E)‖ + ‖(waveGroup hT hc hmaps hcomp).generator x‖) := by
  have hx : (x : E) ∈ (T - T†).domain := by
    rw [← generator_waveGroup hT hc hmaps hcomp]; exact x.2
  have hLx : (waveGroup hT hc hmaps hcomp).generator x = (T - T†) ⟨x, hx⟩ :=
    apply_of_eq (generator_waveGroup hT hc hmaps hcomp) x
  have h1 := norm_sq_graphSpace (liftGraph hT hc hmaps hcomp x)
  have h2 := norm_apply_le_norm_sub_adjoint_apply hT hmaps hcomp ⟨x, hx⟩
  rw [one_mul, hLx]
  change ‖liftGraph hT hc hmaps hcomp x‖ ^ 2 = ‖(x : E)‖ ^ 2 + ‖T ⟨x, hx.1⟩‖ ^ 2 at h1
  have hl := norm_nonneg (liftGraph hT hc hmaps hcomp x)
  nlinarith [norm_nonneg (x : E), norm_nonneg (T ⟨x, hx.1⟩), norm_nonneg ((T - T†) ⟨x, hx⟩)]

/-- **The exact solution required by Thm 4.14 exists for `D(L²)` data**: for `ξ₀ ∈ D(L)` with
`L ξ₀ ∈ D(L)`, the orbit `t ↦ e^{(t-a)L} ξ₀`, read in `Γ(T)`, is a weak solution in
`C¹(Γ(T))`; it is the unique one with this initial value (`IsGraphSolution.eqOn`).

Correction: Thm 4.14 assumes `ξ ∈ C¹([0,T]; V)` without saying for which data this holds;
`D(L²)` suffices, while `D(L)` does not (`Feec.Counterexamples.ClassicalRegularity`).
See [QuennevilleBelair2015], Thm 4.14; cf. [Pazy1983], §1.2, Thm 2.4. -/
theorem exists_isGraphSolution {ξ₀ : E} (h₀ : ξ₀ ∈ (T - T†).domain)
    (hL₀ : (T - T†) ⟨ξ₀, h₀⟩ ∈ (T - T†).domain) (a b : ℝ) :
    ∃ ξ ξ' : ℝ → T.GraphSpace, IsGraphSolution (Icc a b) ξ ξ' ∧
      ∀ t, T.graphFst (ξ t) = (waveGroup hT hc hmaps hcomp).S (t - a) ξ₀ := by
  set G := waveGroup hT hc hmaps hcomp
  have hgen := generator_waveGroup hT hc hmaps hcomp
  set x : G.generator.domain := ⟨ξ₀, by rw [hgen]; exact h₀⟩
  have hxL : G.generator x = (T - T†) ⟨ξ₀, h₀⟩ := apply_of_eq hgen x
  set y : G.generator.domain := ⟨(T - T†) ⟨ξ₀, h₀⟩, by rw [hgen]; exact hL₀⟩
  have hxy : G.generator x = y := hxL
  set Φ := (liftGraph hT hc hmaps hcomp).restrictScalars ℝ
  have hΦ : ∀ z, ‖Φ z‖ ≤ 1 * (‖(z : E)‖ + ‖G.generator z‖) := norm_liftGraph_le hT hc hmaps hcomp
  refine ⟨fun s => Φ ⟨G.S (s - a) x, G.mapsTo_domain x _⟩,
    fun s => Φ ⟨G.S (s - a) y, G.mapsTo_domain y _⟩, ⟨?_, fun t _ => ?_, fun t _ ψ => ?_⟩,
    fun t => rfl⟩
  · exact ((G.continuous_graph Φ 1 hΦ y).comp (continuous_id.sub continuous_const)).continuousOn
  · exact ((G.hasDerivAt_graph Φ 1 hΦ x y hxy (t - a)).comp_sub_const t a).hasDerivWithinAt
  · -- the weak form: `⟪ψ, L ξ⟫ + ⟪T ψ, ξ⟫ - ⟪ψ, T ξ⟫ = 0`
    set z : G.generator.domain := ⟨G.S (t - a) x, G.mapsTo_domain x _⟩
    have hz : (z : E) ∈ (T - T†).domain := by rw [← hgen]; exact z.2
    have hGz : G.S (t - a) (y : E) = (T - T†) ⟨z, hz⟩ := by
      rw [← hxy, ← G.generator_apply_S]; exact apply_of_eq hgen z
    change ⟪T.graphFst ψ, G.S (t - a) (y : E)⟫ + waveForm T (liftGraph hT hc hmaps hcomp z) ψ = 0
    rw [hGz, waveForm_apply, graphFst_liftGraph, LinearPMap.sub_apply, inner_sub_right]
    obtain ⟨w, rfl, -, -⟩ := T.exists_toGraphSpace_eq ψ
    simp only [graphFst_toGraphSpace, graphSnd_toGraphSpace]
    have hadj := adjoint_isFormalAdjoint hT ⟨z, hz.2⟩ w
    have e1 : ⟪(w : E), T† ⟨z, hz.2⟩⟫ = ⟪T w, (z : E)⟫ := by
      rw [← inner_conj_symm, hadj, inner_conj_symm]
    change ⟪(w : E), T ⟨z, hz.1⟩⟫ - ⟪(w : E), T† ⟨z, hz.2⟩⟫ +
      (⟪T w, (z : E)⟫ - ⟪(w : E), T ⟨z, hz.1⟩⟫) = 0
    rw [e1]; ring

end WaveGroup

/-! ### Convergence for `D(L²)`, `D(L)` and `E` data -/

section ConvergenceData

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  (hT : Dense (T.domain : Set E)) (hc : T.IsClosed)
  (hmaps : ∀ x : T.domain, (T x : E) ∈ T.domain) (hcomp : ∀ x : T.domain, T ⟨T x, hmaps x⟩ = 0)
  {ι : Type*} {l : Filter ι} {K : ι → Submodule 𝕜 T.GraphSpace} [∀ h, FiniteDimensional 𝕜 (K h)]

/-- **Convergence of the semi-discrete method for `D(L²)` data**: for `ξ₀ ∈ D(L)` with
`L ξ₀ ∈ D(L)`, the exact weak solution `ξ ∈ C¹([a,b]; Γ(T))` exists and is unique, the
semi-discrete solutions with `ξₕ(a) = Pₕ ξ(a)` exist, and `ξₕ → ξ` in `E`, uniformly on
`[a, b]`. See [QuennevilleBelair2015], Thm 4.14 and the convergence remark after it. -/
theorem tendstoUniformlyOn_semidiscrete (hK : IsApproximating l K) {ξ₀ : E}
    (h₀ : ξ₀ ∈ (T - T†).domain) (hL₀ : (T - T†) ⟨ξ₀, h₀⟩ ∈ (T - T†).domain) (a b : ℝ) :
    ∃ ξ ξ' : ℝ → T.GraphSpace, IsGraphSolution (Icc a b) ξ ξ' ∧
      (∀ t, T.graphFst (ξ t) = (waveGroup hT hc hmaps hcomp).S (t - a) ξ₀) ∧
      (∀ ζ ζ' : ℝ → T.GraphSpace, IsGraphSolution (Icc a b) ζ ζ' → ζ a = ξ a →
        EqOn ζ ξ (Icc a b)) ∧
      ∃ ξh ξh' : ι → ℝ → T.GraphSpace,
        (∀ h, IsSemidiscreteSolution (K h) (Icc a b) (ξh h) (ξh' h)) ∧
        (∀ h, ξh h a = ellipticProjection (K h) (ξ a)) ∧
        TendstoUniformlyOn (fun h t => T.graphFst (ξh h t)) (fun t => T.graphFst (ξ t)) l
          (Icc a b) := by
  obtain ⟨ξ, ξ', hξ, hξS⟩ := exists_isGraphSolution hT hc hmaps hcomp h₀ hL₀ a b
  choose ξh ξh' hξh0 _hc _hd hξh using fun h =>
    exists_isSemidiscreteSolution (K h) (ellipticProjection_mem (K h) (ξ a)) a
  have hξh' : ∀ h, IsSemidiscreteSolution (K h) (Icc a b) (ξh h) (ξh' h) := fun h =>
    (hξh h).mono (subset_univ _)
  refine ⟨ξ, ξ', hξ, hξS, fun ζ ζ' hζ h0 => hζ.eqOn hξ h0, ξh, ξh', hξh', hξh0,
    tendstoUniformlyOn_of_isGraphSolution hK hξ hξh' ?_⟩
  simp only [hξh0, sub_self, _root_.map_zero, norm_zero, tendsto_const_nhds]

/-- **The comparison-datum bound**: for every `ζ₀ ∈ D(L²)`, with `ζ` its exact solution, every
semi-discrete solution `ξₕ` and every `ξ₀ ∈ E`,
`‖e^{(t-a)L} ξ₀ - ξₕ(t)‖ ≤ ‖ξ₀ - ζ₀‖ + ‖Pζ(a) - ξₕ(a)‖ + ‖e(t)‖ + (t-a) ‖e(a)‖ +
(1 + (t-a)) ∫ ‖e'‖`, `e = Pζ - ζ` (all in `E`). A K-functional-type bound; no rate.
See [QuennevilleBelair2015], Thm 4.14. -/
theorem norm_sub_le_of_comparison {ζ₀ : E} (h₀ : ζ₀ ∈ (T - T†).domain)
    (hL₀ : (T - T†) ⟨ζ₀, h₀⟩ ∈ (T - T†).domain) (a b : ℝ) :
    ∃ ζ ζ' : ℝ → T.GraphSpace, IsGraphSolution (Icc a b) ζ ζ' ∧
      (∀ t, T.graphFst (ζ t) = (waveGroup hT hc hmaps hcomp).S (t - a) ζ₀) ∧
      ∀ (K : Submodule 𝕜 T.GraphSpace) [FiniteDimensional 𝕜 K] (ξh ξh' : ℝ → T.GraphSpace),
        IsSemidiscreteSolution K (Icc a b) ξh ξh' → ∀ (ξ₀ : E), ∀ t ∈ Icc a b,
          ‖(waveGroup hT hc hmaps hcomp).S (t - a) ξ₀ - T.graphFst (ξh t)‖ ≤ ‖ξ₀ - ζ₀‖ +
            ‖T.graphFst (ellipticProjection K (ζ a) - ξh a)‖ +
            ‖T.graphFst (ellipticProjection K (ζ t) - ζ t)‖ +
            (t - a) * ‖T.graphFst (ellipticProjection K (ζ a) - ζ a)‖ +
            (1 + (t - a)) * ∫ s in a..t, ‖T.graphFst (ellipticProjection K (ζ' s) - ζ' s)‖ := by
  obtain ⟨ζ, ζ', hζ, hζS⟩ := exists_isGraphSolution hT hc hmaps hcomp h₀ hL₀ a b
  refine ⟨ζ, ζ', hζ, hζS, fun K _ ξh ξh' hξh ξ₀ t ht => ?_⟩
  have hb := hζ.norm_sub_le hξh t ht
  have hiso := isIsometric_waveGroup hT hc hmaps hcomp (t - a) (ξ₀ - ζ₀)
  rw [_root_.map_sub] at hiso
  calc ‖(waveGroup hT hc hmaps hcomp).S (t - a) ξ₀ - T.graphFst (ξh t)‖
      = ‖((waveGroup hT hc hmaps hcomp).S (t - a) ξ₀ - (waveGroup hT hc hmaps hcomp).S (t - a) ζ₀)
          + T.graphFst (ζ t - ξh t)‖ := by rw [_root_.map_sub, hζS]; congr 1; abel
    _ ≤ ‖(waveGroup hT hc hmaps hcomp).S (t - a) ξ₀ - (waveGroup hT hc hmaps hcomp).S (t - a) ζ₀‖
          + ‖T.graphFst (ζ t - ξh t)‖ := norm_add_le _ _
    _ ≤ _ := by rw [hiso]; linarith

/-- **Convergence of the semi-discrete method for data in `E`** (thesis' convergence remark,
extended): under the density hypothesis, if `ξₕ(a) → ξ₀` in `E` then `ξₕ(t) → e^{(t-a)L} ξ₀`
(the mild solution), uniformly on `[a, b]`. Stability of the semi-discrete flow plus density of
`D(L²)`; no rate. See [QuennevilleBelair2015], Thm 4.14 and the convergence remark after it. -/
theorem tendstoUniformlyOn_of_tendsto (hK : IsApproximating l K) {a b : ℝ} (ξ₀ : E)
    {ξh ξh' : ι → ℝ → T.GraphSpace}
    (hξh : ∀ h, IsSemidiscreteSolution (K h) (Icc a b) (ξh h) (ξh' h))
    (h0 : Tendsto (fun h => T.graphFst (ξh h a)) l (𝓝 ξ₀)) :
    TendstoUniformlyOn (fun h t => T.graphFst (ξh h t))
      (fun t => (waveGroup hT hc hmaps hcomp).S (t - a) ξ₀) l (Icc a b) := by
  set G := waveGroup hT hc hmaps hcomp
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε5 : 0 < ε / 5 := by positivity
  obtain ⟨x, hx, hxξ⟩ :=
    (isSkewAdjoint_sub_adjoint hT hc hmaps hcomp).exists_mem_domain_sq_near ξ₀ hε5
  obtain ⟨ζ, ζ', hζ, hζS⟩ := exists_isGraphSolution hT hc hmaps hcomp x.2 hx a b
  have hza : T.graphFst (ζ a) = x := by rw [hζS, sub_self, C0Group.S_zero_apply]
  choose ζh ζh' hζh0 _hc _hd hζh using fun h =>
    exists_isSemidiscreteSolution (K h) (ellipticProjection_mem (K h) (ζ a)) a
  have hζh' : ∀ h, IsSemidiscreteSolution (K h) (Icc a b) (ζh h) (ζh' h) := fun h =>
    (hζh h).mono (subset_univ _)
  have hconv := tendstoUniformlyOn_of_isGraphSolution hK hζ hζh' (by
    simp only [hζh0, sub_self, _root_.map_zero, norm_zero, tendsto_const_nhds])
  have hP : Tendsto (fun h => T.graphFst (ellipticProjection (K h) (ζ a))) l
      (𝓝 (T.graphFst (ζ a))) :=
    (T.graphFst.continuous.tendsto _).comp (hK.tendsto_ellipticProjection _)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hconv _ hε5, Metric.tendsto_nhds.1 hP _ hε5,
    Metric.tendsto_nhds.1 h0 _ hε5] with h h1 h2 h3 t ht
  rw [dist_eq_norm] at h2 h3 ⊢
  have h1t := h1 t ht
  rw [dist_eq_norm, hζS] at h1t
  have hstab := (hζh' h).norm_sub_le (hξh h) t ht
  rw [hζh0, _root_.map_sub, _root_.map_sub] at hstab
  have hiso := isIsometric_waveGroup hT hc hmaps hcomp (t - a) (ξ₀ - x)
  rw [_root_.map_sub] at hiso
  rw [hza] at h2
  have e : G.S (t - a) ξ₀ - T.graphFst (ξh h t) = (G.S (t - a) ξ₀ - G.S (t - a) x) +
      (G.S (t - a) x - T.graphFst (ζh h t)) + (T.graphFst (ζh h t) - T.graphFst (ξh h t)) := by
    abel
  have e2 : T.graphFst (ellipticProjection (K h) (ζ a)) - T.graphFst (ξh h a) =
      (T.graphFst (ellipticProjection (K h) (ζ a)) - x) + (x - ξ₀) +
        (ξ₀ - T.graphFst (ξh h a)) := by
    abel
  have hxξ' : ‖x - ξ₀‖ < ε / 5 := by rw [norm_sub_rev]; exact hxξ
  have h3' : ‖ξ₀ - T.graphFst (ξh h a)‖ < ε / 5 := by rw [norm_sub_rev]; exact h3
  have hn1 : ‖T.graphFst (ellipticProjection (K h) (ζ a)) - x + (x - ξ₀) +
      (ξ₀ - T.graphFst (ξh h a))‖ ≤ ‖T.graphFst (ellipticProjection (K h) (ζ a)) - x‖ +
        ‖(x : E) - ξ₀‖ + ‖ξ₀ - T.graphFst (ξh h a)‖ := norm_add₃_le
  have hn2 : ‖G.S (t - a) ξ₀ - G.S (t - a) x + (G.S (t - a) x - T.graphFst (ζh h t)) +
      (T.graphFst (ζh h t) - T.graphFst (ξh h t))‖ ≤ ‖G.S (t - a) ξ₀ - G.S (t - a) x‖ +
        ‖G.S (t - a) x - T.graphFst (ζh h t)‖ + ‖T.graphFst (ζh h t) - T.graphFst (ξh h t)‖ :=
    norm_add₃_le
  rw [← e2] at hn1
  rw [← e] at hn2
  rw [hiso] at hn2
  linarith

/-- **The thesis' convergence remark for `D(L)` data**: for `ξ₀ ∈ D(L)` and `ξₕ(a) = Pₕ ξ₀`,
`ξₕ(t) → e^{(t-a)L} ξ₀` in `E`, uniformly on `[a, b]` (Thm 4.14 itself does not apply: the
solution need not be `C¹` into `Γ(T)`). See [QuennevilleBelair2015], Thm 4.14 and the
convergence remark after it. -/
theorem tendstoUniformlyOn_ellipticProjection (hK : IsApproximating l K) {a b : ℝ}
    (x : (T - T†).domain) {ξh ξh' : ι → ℝ → T.GraphSpace}
    (hξh : ∀ h, IsSemidiscreteSolution (K h) (Icc a b) (ξh h) (ξh' h))
    (hinit : ∀ h, ξh h a = ellipticProjection (K h) (T.toGraphSpace ⟨x, x.2.1⟩)) :
    TendstoUniformlyOn (fun h t => T.graphFst (ξh h t))
      (fun t => (waveGroup hT hc hmaps hcomp).S (t - a) x) l (Icc a b) := by
  refine tendstoUniformlyOn_of_tendsto hT hc hmaps hcomp hK (x : E) hξh ?_
  simp only [hinit]
  exact (T.graphFst.continuous.tendsto _).comp (hK.tendsto_ellipticProjection _)

/-- The orbit `t ↦ e^{(t-a)L} ξ₀` of `ξ₀ ∈ D(L)` is a classical solution of `U' = L U`. -/
theorem isClassicalSolution_waveGroup (a b : ℝ) (x : (T - T†).domain) :
    Evolution.IsClassicalSolution (T - T†) (Icc a b) 0
      (fun t => (waveGroup hT hc hmaps hcomp).S (t - a) x) := by
  have hgen := generator_waveGroup hT hc hmaps hcomp
  have horb := (waveGroup hT hc hmaps hcomp).toC0Semigroup.isClassicalSolution_orbit
    (U₀ := (x : E)) (by
      change (x : E) ∈ (waveGroup hT hc hmaps hcomp).generator.domain
      rw [hgen]; exact x.2) a b
  change Evolution.IsClassicalSolution (waveGroup hT hc hmaps hcomp).generator _ _ _ at horb
  rwa [hgen] at horb

/-- `D(L)` data: the semi-discrete solutions with `ξₕ(a) = Pₕ ξ₀` exist and converge to the
classical solution. See [QuennevilleBelair2015], Thm 4.14 and the remark after it. -/
theorem exists_tendstoUniformlyOn_ellipticProjection (hK : IsApproximating l K) (a b : ℝ)
    (x : (T - T†).domain) :
    Evolution.IsClassicalSolution (T - T†) (Icc a b) 0
      (fun t => (waveGroup hT hc hmaps hcomp).S (t - a) x) ∧
    ∃ ξh ξh' : ι → ℝ → T.GraphSpace,
      (∀ h, IsSemidiscreteSolution (K h) (Icc a b) (ξh h) (ξh' h)) ∧
      (∀ h, ξh h a = ellipticProjection (K h) (T.toGraphSpace ⟨x, x.2.1⟩)) ∧
      TendstoUniformlyOn (fun h t => T.graphFst (ξh h t))
        (fun t => (waveGroup hT hc hmaps hcomp).S (t - a) x) l (Icc a b) := by
  have horb := isClassicalSolution_waveGroup hT hc hmaps hcomp a b x
  choose ξh ξh' hξh0 _hc _hd hξh using fun h => exists_isSemidiscreteSolution (K h)
    (ellipticProjection_mem (K h) (T.toGraphSpace ⟨x, x.2.1⟩)) a
  have hξh' : ∀ h, IsSemidiscreteSolution (K h) (Icc a b) (ξh h) (ξh' h) := fun h =>
    (hξh h).mono (subset_univ _)
  exact ⟨horb, ξh, ξh', hξh', hξh0,
    tendstoUniformlyOn_ellipticProjection hT hc hmaps hcomp hK x hξh' hξh0⟩

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
include hT in
/-- Initial data for `E`-data convergence: the `E`-orthogonal projections of `ξ₀` onto the
discrete spaces converge to `ξ₀` (`D(T)` is dense and the `Kₕ` approximate `Γ(T)`). -/
theorem exists_tendsto_init (hK : IsApproximating l K) (ξ₀ : E) :
    ∃ v : ι → T.GraphSpace, (∀ h, v h ∈ K h) ∧ Tendsto (fun h => T.graphFst (v h)) l (𝓝 ξ₀) := by
  set K' : ι → Submodule 𝕜 E := fun h => (K h).map (T.graphFst : T.GraphSpace →ₗ[𝕜] E)
  have hK' : ∀ h, FiniteDimensional 𝕜 (K' h) := fun h => inferInstance
  have hp : ∀ h, ∃ v ∈ K h, T.graphFst v = (K' h).starProjection ξ₀ := fun h =>
    Submodule.mem_map.1 ((K' h).starProjection_apply_mem ξ₀)
  choose v hvK hv using hp
  refine ⟨v, hvK, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨w, hw, hwξ⟩ := hT.exists_dist_lt ξ₀ (half_pos hε)
  filter_upwards [hK.dense (T.toGraphSpace ⟨w, hw⟩) _ (half_pos hε)] with h ⟨u, hu, hwu⟩
  rw [dist_eq_norm, hv, norm_sub_rev]
  have hmin : ‖ξ₀ - (K' h).starProjection ξ₀‖ ≤ ‖ξ₀ - T.graphFst u‖ := by
    rw [← dist_eq_norm, Submodule.dist_starProjection_eq_infDist, ← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem ⟨u, hu, rfl⟩
  have hu' : ‖w - T.graphFst u‖ < ε / 2 := by
    have := (norm_graphFst_le (T.toGraphSpace ⟨w, hw⟩ - u)).trans_lt hwu
    rwa [_root_.map_sub, graphFst_toGraphSpace] at this
  rw [dist_eq_norm] at hwξ
  calc ‖ξ₀ - (K' h).starProjection ξ₀‖ ≤ ‖ξ₀ - T.graphFst u‖ := hmin
    _ ≤ ‖ξ₀ - w‖ + ‖w - T.graphFst u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hwξ hu'
    _ = ε := add_halves ε

/-- **`E`-data convergence with existence of the discrete solutions**: for every `ξ₀ ∈ E` there
are semi-discrete solutions with `ξₕ(a) → ξ₀`, and they converge to `e^{(t-a)L} ξ₀` uniformly
on `[a, b]`. See [QuennevilleBelair2015], the convergence remark after Thm 4.14. -/
theorem exists_tendstoUniformlyOn_of_tendsto (hK : IsApproximating l K) (a b : ℝ) (ξ₀ : E) :
    ∃ ξh ξh' : ι → ℝ → T.GraphSpace,
      (∀ h, IsSemidiscreteSolution (K h) (Icc a b) (ξh h) (ξh' h)) ∧
      Tendsto (fun h => T.graphFst (ξh h a)) l (𝓝 ξ₀) ∧
      TendstoUniformlyOn (fun h t => T.graphFst (ξh h t))
        (fun t => (waveGroup hT hc hmaps hcomp).S (t - a) ξ₀) l (Icc a b) := by
  obtain ⟨v, hvK, hv⟩ := exists_tendsto_init hT hK ξ₀
  choose ξh ξh' hξh0 _hc _hd hξh using fun h => exists_isSemidiscreteSolution (K h) (hvK h) a
  have hξh' : ∀ h, IsSemidiscreteSolution (K h) (Icc a b) (ξh h) (ξh' h) := fun h =>
    (hξh h).mono (subset_univ _)
  have h0 : Tendsto (fun h => T.graphFst (ξh h a)) l (𝓝 ξ₀) := by simpa only [hξh0] using hv
  exact ⟨ξh, ξh', hξh', h0, tendstoUniformlyOn_of_tendsto hT hc hmaps hcomp hK ξ₀ hξh' h0⟩

/-- **Weak solutions are the group orbit**: every weak solution of the Hodge wave equation
(4.7)/(4.8) on `[a, b]` with initial value `ξ₀ ∈ D(L)` is `e^{(t-a)L} ξ₀`.
See [QuennevilleBelair2015], Thm 4.6, Thm 4.7. -/
theorem eqOn_waveGroup_of_isWeakSolution (x : (T - T†).domain) {a b : ℝ} {U : ℝ → E}
    (hU : IsWeakSolution T (Icc a b) 0 U) (hU0 : U a = x) :
    EqOn U (fun t => (waveGroup hT hc hmaps hcomp).S (t - a) x) (Icc a b) := by
  have horb := isClassicalSolution_waveGroup hT hc hmaps hcomp a b x
  obtain ⟨V, hV0, -, hVs, hVw⟩ := existsUnique hT hc hmaps hcomp x.2
    (Evolution.ForcingClass.admissible_zero (T - T†) a b)
  intro t ht
  rw [hVw U hU0 hU ht, hVs _ (by simp) horb.toIsStrongSolution ht]

include hT hc hcomp in
/-- **The thesis' convergence remark, literally**: for the weak solution `ξ` of (4.7)/(4.8) with
`ξ(a) = ξ₀ ∈ D(L)` and `ξₕ(a) = Pₕ ξ₀`, `ξₕ → ξ` in `E`, uniformly on `[a, b]`.
See [QuennevilleBelair2015], the convergence remark after Thm 4.14. -/
theorem tendstoUniformlyOn_of_isWeakSolution (hK : IsApproximating l K) {a b : ℝ}
    (x : (T - T†).domain) {U : ℝ → E} (hU : IsWeakSolution T (Icc a b) 0 U) (hU0 : U a = x)
    {ξh ξh' : ι → ℝ → T.GraphSpace}
    (hξh : ∀ h, IsSemidiscreteSolution (K h) (Icc a b) (ξh h) (ξh' h))
    (hinit : ∀ h, ξh h a = ellipticProjection (K h) (T.toGraphSpace ⟨x, x.2.1⟩)) :
    TendstoUniformlyOn (fun h t => T.graphFst (ξh h t)) U l (Icc a b) :=
  (tendstoUniformlyOn_ellipticProjection hT hc hmaps hcomp hK x hξh hinit).congr_right
    fun _ ht => (eqOn_waveGroup_of_isWeakSolution hT hc hmaps hcomp x hU hU0 ht).symm

include hT hc hcomp in
/-- `D(L)` data, with existence: the weak solution in `C⁰([a,b]; Γ(T)) ∩ C¹([a,b]; E)` exists and
is unique, and the semi-discrete solutions with `ξₕ(a) = Pₕ ξ₀` converge to it.
See [QuennevilleBelair2015], Thm 4.6, Thm 4.7 and the convergence remark after Thm 4.14. -/
theorem exists_isClassicalWeakSolution_tendstoUniformlyOn (hK : IsApproximating l K) (a b : ℝ)
    (x : (T - T†).domain) :
    ∃ U : ℝ → E, U a = x ∧ IsClassicalWeakSolution T (Icc a b) 0 U ∧
      (∀ V : ℝ → E, V a = x → IsWeakSolution T (Icc a b) 0 V → EqOn V U (Icc a b)) ∧
      ∃ ξh ξh' : ι → ℝ → T.GraphSpace,
        (∀ h, IsSemidiscreteSolution (K h) (Icc a b) (ξh h) (ξh' h)) ∧
        (∀ h, ξh h a = ellipticProjection (K h) (T.toGraphSpace ⟨x, x.2.1⟩)) ∧
        TendstoUniformlyOn (fun h t => T.graphFst (ξh h t)) U l (Icc a b) := by
  obtain ⟨U, hU0, hU, -, hUw⟩ := existsUnique hT hc hmaps hcomp x.2
    (Evolution.ForcingClass.admissible_zero (T - T†) a b)
  have hcw := isClassicalWeakSolution_of_isClassicalSolution hT hmaps hcomp
    (continuousOn_const (c := (0 : E))) hU
  obtain ⟨-, ξh, ξh', hξh, hinit, -⟩ := exists_tendstoUniformlyOn_ellipticProjection hT hc hmaps
    hcomp hK a b x
  exact ⟨U, hU0, hcw, hUw, ξh, ξh', hξh, hinit,
    tendstoUniformlyOn_of_isWeakSolution hT hc hmaps hcomp hK x hcw.toIsWeakSolution hU0 hξh
      hinit⟩

end ConvergenceData

end Feec.HodgeWave

/-! ### Subcomplexes of a finite Hilbert complex -/

namespace Feec.HilbertComplex.Subcomplex

open _root_.Feec.HodgeWave

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W} (S : H.Subcomplex)

/-- The **total space of a subcomplex** in the graph space `Γ(𝐝)` of the total differential:
`(x, 𝐝 x)` with `x i ∈ Vₕⁱ` for every `i`. See [QuennevilleBelair2015], §4.6. -/
def graphSub : Submodule 𝕜 H.totalD.GraphSpace :=
  (totalSub S.V).comap (H.totalD.graphFst : H.totalD.GraphSpace →ₗ[𝕜] PiLp 2 W)

instance [∀ i, FiniteDimensional 𝕜 (S.V i)] : FiniteDimensional 𝕜 S.graphSub := by
  let f : S.graphSub →ₗ[𝕜] ∀ i, S.V i :=
    { toFun := fun v i => ⟨H.totalD.graphFst v i, v.2 i⟩
      map_add' := fun v w => funext fun i => Subtype.ext (by simp)
      map_smul' := fun a v => funext fun i => Subtype.ext (by simp) }
  refine Module.Finite.of_injective f fun v w hvw => Subtype.ext (H.totalD.graphFst_injective
    (PiLp.ext fun i => ?_))
  exact congrArg Subtype.val (congrFun hvw i)

/-- A subcomplex is invariant under the differential of the graph space. -/
theorem graphD_mem_graphSub {v : H.totalD.GraphSpace} (hv : v ∈ S.graphSub) :
    graphD H.totalD_mapsTo H.totalD_comp_totalD v ∈ S.graphSub := fun j => by
  change H.totalD.graphFst (graphD H.totalD_mapsTo H.totalD_comp_totalD v) j ∈ S.V j
  rw [graphFst_graphD]
  obtain ⟨x, rfl, hx1, -⟩ := H.totalD.exists_toGraphSpace_eq v
  rw [graphSnd_toGraphSpace, totalD_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hxi : (x : PiLp 2 W) i ∈ S.V i := hv i
  exact S.mapsTo i j _ hxi

/-- **The elliptic projections of subcomplexes are uniformly bounded** (thesis Prop 4.13 and
(4.11), for every finite Hilbert complex). -/
theorem norm_ellipticProjection_le [∀ i, FiniteDimensional 𝕜 (S.V i)] (ζ : H.totalD.GraphSpace) :
    ‖ellipticProjection S.graphSub ζ‖ ≤ ‖shiftedForm H.totalD‖ / ((1 / 2) / √3) * ‖ζ‖ :=
  HodgeWave.norm_ellipticProjection_le H.totalD_mapsTo H.totalD_comp_totalD S.graphSub
    (fun _ hξ => S.graphD_mem_graphSub hξ) ζ

/-- **A dense family of finite-dimensional subcomplexes is approximating**: the density
hypothesis of thesis §4.6 alone suffices (the uniform bound comes from Prop 4.13). -/
theorem isApproximating {κ : Type*} {l : Filter κ} {S : κ → H.Subcomplex}
    [∀ h i, FiniteDimensional 𝕜 ((S h).V i)]
    (hd : ∀ ζ : H.totalD.GraphSpace, ∀ δ > 0, ∀ᶠ h in l, ∃ w ∈ (S h).graphSub, ‖ζ - w‖ < δ) :
    IsApproximating l fun h => (S h).graphSub :=
  ⟨⟨_, fun h ζ => (S h).norm_ellipticProjection_le ζ⟩, hd⟩

end Feec.HilbertComplex.Subcomplex

/-! ### Finite Hilbert complexes -/

namespace Feec.HilbertComplex.HodgeWave

open _root_.Feec.HodgeWave

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] (H : HilbertComplex 𝕜 c W)

/-- The Hodge wave group of `T = 𝐝` is the wave group of the complex. -/
theorem waveGroup_totalD : Feec.HodgeWave.waveGroup H.dense_totalDomain H.isClosed_totalD
    H.totalD_mapsTo H.totalD_comp_totalD = H.waveGroup :=
  H.isSkewAdjoint_wave.eq_group ((Feec.HodgeWave.generator_waveGroup _ _ _ _).trans H.wave_eq.symm)

/-- **Convergence of the semi-discrete method for `D(L)` data on a finite Hilbert complex** (any
length): for `x ∈ D(L)` and an approximating family `Kₕ ⊆ Γ(𝐝)`, the semi-discrete solutions
with `ξₕ(a) = Pₕ x` exist and converge to `e^{(t-a)L} x` in `L∞(a,b; W)`.
See [QuennevilleBelair2015], Thm 4.14 and the convergence remark after it. -/
theorem exists_tendstoUniformlyOn_ellipticProjection {κ : Type*} {l : Filter κ}
    {K : κ → Submodule 𝕜 H.totalD.GraphSpace} [∀ h, FiniteDimensional 𝕜 (K h)]
    (hK : IsApproximating l K) (a b : ℝ) (x : H.wave.domain) :
    ∃ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
      (∀ h, IsSemidiscreteSolution (K h) (Icc a b) (ξh h) (ξh' h)) ∧
      (∀ h, ξh h a = ellipticProjection (K h)
        (H.totalD.toGraphSpace ⟨x, (H.mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun h t => H.totalD.graphFst (ξh h t))
        (fun t => H.waveGroup.S (t - a) x) l (Icc a b) := by
  have hx : (x : PiLp 2 W) ∈ (H.totalD - H.totalD†).domain := by rw [← wave_eq]; exact x.2
  obtain ⟨-, ξh, ξh', hξh, hinit, hconv⟩ :=
    Feec.HodgeWave.exists_tendstoUniformlyOn_ellipticProjection H.dense_totalDomain
      H.isClosed_totalD H.totalD_mapsTo H.totalD_comp_totalD hK a b ⟨x, hx⟩
  rw [waveGroup_totalD] at hconv
  exact ⟨ξh, ξh', hξh, hinit, hconv⟩

end Feec.HilbertComplex.HodgeWave
