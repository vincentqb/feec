module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Feec.Legacy.ShortComplex
public import Feec.Legacy.Galerkin
public import Feec.Variational.GalerkinEvolution

/-!
# Ch 4.6: discretization, Lemma 4.12, Prop 4.13, elliptic projection, Thm 4.14, convergence

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

Thesis §4.6 (l.2258–2453), on the algebraic segment `AlgSegment` (each type carries the `W` inner
product, `d` is linear on the domain type).

* `le_add_half_sub_of_sq_deriv_le`, `le_add_half_integral_of_sq_deriv_le`: Lemma 4.12, corrected (`Q` only continuous, `Q²`
  right-differentiable); `le_add_half_integral_sharp`: the sharpness remark.
* `VSp`: the space `V = V⁰ × V¹ × W²` with its graph inner product; `toW : V → W`; the forms
  `a`, `A = (·,·)_W + a` as bounded bilinear forms (`AL`, `‖A‖ ≤ 2`).
* `formA_test_lower`, `infSup_of_testMap_mem`, `Sub.infSup`: Prop 4.13 (inf-sup constant `1/√12`) on `V` and
  on every subcomplex `Vₕ`.
* `ellProj`: the elliptic projection (4.11), with existence/uniqueness, `‖Πₕ‖ ≤ 2√12` and
  quasi-optimality with constant `1 + 2√12`.
* `discrete_solution_exists`, `discrete_solution_unique`: well-posedness of (4.10).
* `semidiscrete_error_bound_pointwise`, `semidiscrete_error_bound`: Thm 4.14 (corrected regularity `ξ ∈ C¹([0,T]; V)`).
* `convergence`, `convergence_exists`: convergence in `L∞(0,T; W)` from density alone.

## References

* [QuennevilleBelair2015], §4.4 (abstract Hodge wave equation (4.7)–(4.8)), §4.5 (Thm 4.9,
  Thm 4.10: inf-sup and quasi-optimality), §4.6 (discretization (4.10), Lemma 4.12, Prop 4.13,
  elliptic projection (4.11), Thm 4.14)
* [Arnold2018] (FEEC framework: Hilbert complexes, subcomplexes, stability of discretizations)
* [AFW2010], §3 (approximation of Hilbert complexes by subcomplexes, graph norms on `Vᵏ`)
* [Babuska1971], [BoffiBrezziFortin2013] (inf-sup stability and quasi-optimality of Galerkin
  methods)
* [Dupont1973], [Baker1976] (energy-method error estimates for second-order hyperbolic
  equations)
* [Geveci1988] (mixed finite element methods for the wave equation), [GilletteHolstZhu2017]
  (FEEC for evolution problems)
-/

open scoped RealInnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Legacy

/-! ## Lemma 4.12 (corrected) -/

/-- **Thesis Lemma 4.12** (l.2287), primitive form: if `Q ≥ 0` is continuous on `[0,T]`, `Q²` has
right derivative `q'` on `[0,T)`, `G` is continuous on `[0,T]` with right derivative `F ≥ 0`, and
`q' ≤ F Q`, then `Q t ≤ Q 0 + (G t − G 0)/2` on `[0,T]`.

Correction: the thesis assumes `Q ∈ C¹([0,T])`, but applies the lemma (l.2423) to `Q = ‖εₕ‖`,
which is not differentiable where `εₕ` vanishes; only `Q²` is differentiable there. The hypothesis
is therefore on `Q²`; the proof compares `√(Q² + ε²)` with `√(Q(0)² + ε²) + (G − G 0)/2` and lets
`ε → 0`.
See [QuennevilleBelair2015, Lemma 4.12] (§4.6). -/
theorem le_add_half_sub_of_sq_deriv_le {Q q' F G : ℝ → ℝ} {T : ℝ}
    (hQc : ContinuousOn Q (Icc 0 T)) (hQ0 : ∀ t ∈ Icc 0 T, 0 ≤ Q t)
    (hq : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun s => Q s ^ 2) (q' t) (Ici t) t)
    (hGc : ContinuousOn G (Icc 0 T))
    (hG : ∀ t ∈ Ico 0 T, HasDerivWithinAt G (F t) (Ici t) t)
    (hF : ∀ t ∈ Ico 0 T, 0 ≤ F t)
    (hle : ∀ t ∈ Ico 0 T, q' t ≤ F t * Q t) :
    ∀ t ∈ Icc 0 T, Q t ≤ Q 0 + (G t - G 0) / 2 :=
  le_add_half_sub_of_sq_deriv_le_mul hQc hQ0 hq hGc hG hF hle

/-- **Thesis Lemma 4.12** (l.2287), integral form as stated in the thesis:
`Q t ≤ Q 0 + ½ ∫₀ᵗ F` for `F ≥ 0` continuous on `[0,T]` and `d/dt Q² ≤ F Q` (corrected
hypotheses as in `le_add_half_sub_of_sq_deriv_le`).
See [QuennevilleBelair2015, Lemma 4.12]. -/
theorem le_add_half_integral_of_sq_deriv_le {Q q' F : ℝ → ℝ} {T : ℝ}
    (hQc : ContinuousOn Q (Icc 0 T)) (hQ0 : ∀ t ∈ Icc 0 T, 0 ≤ Q t)
    (hq : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun s => Q s ^ 2) (q' t) (Ici t) t)
    (hFc : ContinuousOn F (Icc 0 T)) (hF : ∀ t ∈ Ico 0 T, 0 ≤ F t)
    (hle : ∀ t ∈ Ico 0 T, q' t ≤ F t * Q t) :
    ∀ t ∈ Icc 0 T, Q t ≤ Q 0 + (1 / 2) * ∫ s in (0:ℝ)..t, F s :=
  le_add_half_integral_of_sq_deriv_le_mul hQc hQ0 hq hFc hF hle

/-- **Thesis Lemma 4.12**, sharpness remark (l.2297): `Q(t) = t`, `F = 2` satisfy the hypotheses
of `le_add_half_integral_of_sq_deriv_le` (`d/dt Q² = 2t = F Q`), and the resulting bound `Q t ≤ Q 0 + ½∫₀ᵗ F`
is an equality.
See [QuennevilleBelair2015, Lemma 4.12] and the remark following it. -/
theorem le_add_half_integral_sharp {T : ℝ} :
    (∀ t ∈ Icc 0 T, t ≤ 0 + (1 / 2) * ∫ _ in (0:ℝ)..t, (2 : ℝ)) ∧
      ∀ t : ℝ, t = 0 + (1 / 2) * ∫ _ in (0:ℝ)..t, (2 : ℝ) := by
  have hbound := le_add_half_integral_of_sq_deriv_le (Q := fun t => t) (q' := fun t => 2 * t)
    (F := fun _ => (2 : ℝ)) (T := T) continuousOn_id (fun t ht => ht.1)
    (fun t _ => by simpa using (hasDerivAt_pow 2 t).hasDerivWithinAt) continuousOn_const
    (fun _ _ => zero_le_two) (fun _ _ => le_rfl)
  exact ⟨hbound, fun t => by simp; ring⟩

/-! ## Abstract energy estimates (core of Thm 4.14)

Stated in an arbitrary real inner product space `E` (no completeness), with continuity on
`[0,T]` and right derivatives on `[0,T)`. -/

section Energy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `‖f t‖ ≤ ‖f 0‖ + ∫₀ᵗ ‖f'‖` on `[0,T]`: the step "`|f(t)| ≤ |f(0)| + |∫₀ᵗ ḟ|`" of the
proof of Thm 4.14, obtained from Lemma 4.12 (so no completeness of `E` is needed).
See [QuennevilleBelair2015, proof of Thm 4.14]. -/
theorem norm_le_norm_zero_add_integral {f f' : ℝ → E} {T : ℝ}
    (hfc : ContinuousOn f (Icc 0 T))
    (hf : ∀ t ∈ Ico 0 T, HasDerivWithinAt f (f' t) (Ici t) t)
    (hf'c : ContinuousOn f' (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, ‖f t‖ ≤ ‖f 0‖ + ∫ s in (0:ℝ)..t, ‖f' s‖ :=
  Evolution.Energy.norm_le_add_integral_norm_deriv hfc hf hf'c

/-- Energy estimate for the projected error (proof of Thm 4.14): if
`(ε̇, ε) = (ė, ε) − (e, ε)` on `[0,T)`, then `‖ε t‖ ≤ ‖ε 0‖ + ∫₀ᵗ (‖ė‖ + ‖e‖)`.
See [QuennevilleBelair2015, proof of Thm 4.14]; the energy argument for the projected error
follows [Baker1976], [Dupont1973]. -/
theorem projected_error_bound {ε ε' e e' : ℝ → E} {T : ℝ}
    (hεc : ContinuousOn ε (Icc 0 T)) (hε : ∀ t ∈ Ico 0 T, HasDerivWithinAt ε (ε' t) (Ici t) t)
    (hec : ContinuousOn e (Icc 0 T)) (he'c : ContinuousOn e' (Icc 0 T))
    (herr : ∀ t ∈ Ico 0 T, ⟪ε' t, ε t⟫ = ⟪e' t, ε t⟫ - ⟪e t, ε t⟫) :
    ∀ t ∈ Icc 0 T, ‖ε t‖ ≤ ‖ε 0‖ + ∫ s in (0:ℝ)..t, (‖e' s‖ + ‖e s‖) := by
  refine Evolution.Energy.norm_le_add_integral_of_re_inner_deriv_le (𝕜 := ℝ) hεc hε
    (he'c.norm.add hec.norm) (fun _ _ => by positivity) fun s hs => ?_
  rw [RCLike.re_to_real, herr s hs]
  have h1 := real_inner_le_norm (e' s) (ε s)
  have h2 := neg_le_of_abs_le (abs_real_inner_le_norm (e s) (ε s))
  nlinarith [norm_nonneg (ε s)]

/-- Core of **Thm 4.14** (pointwise, sharp form): with `ξ − ξₕ = ε − e`,
`‖ε t − e t‖ ≤ ‖ε 0‖ + ‖e t‖ + t ‖e 0‖ + (1 + t) ∫₀ᵗ ‖ė‖`.
See [QuennevilleBelair2015, Thm 4.14 and its proof]. -/
theorem error_bound_core {ε ε' e e' : ℝ → E} {T : ℝ}
    (hεc : ContinuousOn ε (Icc 0 T)) (hε : ∀ t ∈ Ico 0 T, HasDerivWithinAt ε (ε' t) (Ici t) t)
    (hec : ContinuousOn e (Icc 0 T)) (he : ∀ t ∈ Ico 0 T, HasDerivWithinAt e (e' t) (Ici t) t)
    (he'c : ContinuousOn e' (Icc 0 T))
    (herr : ∀ t ∈ Ico 0 T, ⟪ε' t, ε t⟫ = ⟪e' t, ε t⟫ - ⟪e t, ε t⟫) :
    ∀ t ∈ Icc 0 T, ‖ε t - e t‖ ≤ ‖ε 0‖ + ‖e t‖ + t * ‖e 0‖
        + (1 + t) * ∫ s in (0:ℝ)..t, ‖e' s‖ := by
  intro t ht
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hu : uIcc 0 t ⊆ Icc 0 T := by rw [uIcc_of_le ht.1]; exact hsub
  have h1 := projected_error_bound hεc hε hec he'c herr t ht
  have hI1 : IntervalIntegrable (fun s => ‖e' s‖) MeasureTheory.volume 0 t :=
    (he'c.norm.mono hu).intervalIntegrable
  have hI2 : IntervalIntegrable (fun s => ‖e s‖) MeasureTheory.volume 0 t :=
    (hec.norm.mono hu).intervalIntegrable
  have hsplit : ∫ s in (0:ℝ)..t, (‖e' s‖ + ‖e s‖)
      = (∫ s in (0:ℝ)..t, ‖e' s‖) + ∫ s in (0:ℝ)..t, ‖e s‖ :=
    intervalIntegral.integral_add hI1 hI2
  have hmono : ∀ s ∈ Icc 0 t, ‖e s‖ ≤ ‖e 0‖ + ∫ r in (0:ℝ)..t, ‖e' r‖ := by
    intro s hs
    have := norm_le_norm_zero_add_integral hec he he'c s (hsub hs)
    have hle : ∫ r in (0:ℝ)..s, ‖e' r‖ ≤ ∫ r in (0:ℝ)..t, ‖e' r‖ :=
      intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
        (Filter.Eventually.of_forall fun _ => norm_nonneg _) hI1
    linarith
  have hE : ∫ s in (0:ℝ)..t, ‖e s‖ ≤ t * (‖e 0‖ + ∫ r in (0:ℝ)..t, ‖e' r‖) := by
    have := intervalIntegral.integral_mono_on ht.1 hI2 intervalIntegrable_const hmono
    simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] using this
  calc ‖ε t - e t‖ ≤ ‖ε t‖ + ‖e t‖ := norm_sub_le _ _
    _ ≤ _ := by rw [hsplit] at h1; nlinarith

end Energy

/-! ## The space `V = V⁰ × V¹ × W²` -/

namespace AlgSegment

open HilbertComplex2 (Tot tot)

variable {X0 X1 X2 : Type*}
  [NormedAddCommGroup X0] [InnerProductSpace ℝ X0]
  [NormedAddCommGroup X1] [InnerProductSpace ℝ X1]
  [NormedAddCommGroup X2] [InnerProductSpace ℝ X2]
  (C : AlgSegment X0 X1 X2)

/-- The space `V = V⁰ × V¹ × W²` of §4.6: a type synonym of `X0 × X1 × X2` carrying the graph
inner product `(σ,τ) + (dσ,dτ) + (u,v) + (du,dv) + (ρ,μ)`, so that `‖ξ‖² = C.normVSq σ u ρ`.
See [QuennevilleBelair2015, §4.4–4.6]; the domain spaces `Vᵏ` with graph norm as in
[AFW2010, §3], [Arnold2018]. -/
def VSp (_C : AlgSegment X0 X1 X2) : Type _ := X0 × X1 × X2

instance : AddCommGroup C.VSp := inferInstanceAs (AddCommGroup (X0 × X1 × X2))
instance : Module ℝ C.VSp := inferInstanceAs (Module ℝ (X0 × X1 × X2))

/-- Coordinates `ξ = (σ, u, ρ)` of an element of `V`. -/
def vEquiv : C.VSp ≃ₗ[ℝ] X0 × X1 × X2 := LinearEquiv.refl ℝ _

/-- The element `(σ, u, ρ)` of `V`. -/
def mkV (σ : X0) (u : X1) (ρ : X2) : C.VSp := C.vEquiv.symm (σ, u, ρ)

@[simp] theorem vEquiv_mkV (σ : X0) (u : X1) (ρ : X2) : C.vEquiv (C.mkV σ u ρ) = (σ, u, ρ) :=
  rfl

@[simp] theorem mkV_vEquiv (ξ : C.VSp) :
    C.mkV (C.vEquiv ξ).1 (C.vEquiv ξ).2.1 (C.vEquiv ξ).2.2 = ξ := rfl

theorem mkV_add (σ τ : X0) (u v : X1) (ρ μ : X2) :
    C.mkV σ u ρ + C.mkV τ v μ = C.mkV (σ + τ) (u + v) (ρ + μ) := rfl

theorem mkV_smul (r : ℝ) (σ : X0) (u : X1) (ρ : X2) :
    r • C.mkV σ u ρ = C.mkV (r • σ) (r • u) (r • ρ) := rfl

theorem mkV_sub (σ τ : X0) (u v : X1) (ρ μ : X2) :
    C.mkV σ u ρ - C.mkV τ v μ = C.mkV (σ - τ) (u - v) (ρ - μ) := rfl

theorem mkV_zero : C.mkV 0 0 0 = 0 := rfl

/-- Induction principle: every element of `V` is some `mkV σ u ρ`. -/
@[elab_as_elim]
theorem VSp.induction {C : AlgSegment X0 X1 X2} {P : C.VSp → Prop} (h : ∀ σ u ρ, P (C.mkV σ u ρ))
    (ξ : C.VSp) : P ξ :=
  h (C.vEquiv ξ).1 (C.vEquiv ξ).2.1 (C.vEquiv ξ).2.2

/-- The graph inner product on `V`.
See [QuennevilleBelair2015, §4.6]; cf. [AFW2010, §3] (the `V`-inner product). -/
def vInner (ξ ψ : C.VSp) : ℝ :=
  ⟪(C.vEquiv ξ).1, (C.vEquiv ψ).1⟫ + ⟪C.d0 (C.vEquiv ξ).1, C.d0 (C.vEquiv ψ).1⟫
    + ⟪(C.vEquiv ξ).2.1, (C.vEquiv ψ).2.1⟫
    + ⟪C.d1 (C.vEquiv ξ).2.1, C.d1 (C.vEquiv ψ).2.1⟫ + ⟪(C.vEquiv ξ).2.2, (C.vEquiv ψ).2.2⟫

@[simp] theorem vInner_mkV (σ τ : X0) (u v : X1) (ρ μ : X2) :
    C.vInner (C.mkV σ u ρ) (C.mkV τ v μ)
      = ⟪σ, τ⟫ + ⟪C.d0 σ, C.d0 τ⟫ + ⟪u, v⟫ + ⟪C.d1 u, C.d1 v⟫ + ⟪ρ, μ⟫ := rfl

/-- The graph inner product is an inner product. -/
@[instance_reducible]
def vCore : InnerProductSpace.Core ℝ C.VSp where
  inner := C.vInner
  conj_inner_symm ξ ψ := by
    induction ξ using VSp.induction
    induction ψ using VSp.induction
    simp only [vInner_mkV, conj_trivial]
    simp only [real_inner_comm]
  re_inner_nonneg ξ := by
    induction ξ using VSp.induction
    simp only [vInner_mkV, RCLike.re_to_real, real_inner_self_eq_norm_sq]
    positivity
  add_left ξ ψ χ := by
    induction ξ using VSp.induction
    induction ψ using VSp.induction
    induction χ using VSp.induction
    simp only [mkV_add, vInner_mkV, map_add, inner_add_left]; ring
  smul_left ξ ψ r := by
    induction ξ using VSp.induction
    induction ψ using VSp.induction
    simp only [mkV_smul, vInner_mkV, map_smul, real_inner_smul_left, conj_trivial]; ring
  definite ξ h := by
    induction ξ using VSp.induction with
    | h σ u ρ =>
    simp only [vInner_mkV, real_inner_self_eq_norm_sq] at h
    have h1 : ‖σ‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖σ‖, sq_nonneg ‖C.d0 σ‖, sq_nonneg ‖u‖, sq_nonneg ‖C.d1 u‖,
        sq_nonneg ‖ρ‖]
    have h2 : ‖u‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖σ‖, sq_nonneg ‖C.d0 σ‖, sq_nonneg ‖u‖, sq_nonneg ‖C.d1 u‖,
        sq_nonneg ‖ρ‖]
    have h3 : ‖ρ‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖σ‖, sq_nonneg ‖C.d0 σ‖, sq_nonneg ‖u‖, sq_nonneg ‖C.d1 u‖,
        sq_nonneg ‖ρ‖]
    simp only [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h1 h2 h3
    subst h1 h2 h3
    rfl

instance : NormedAddCommGroup C.VSp :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := C.vCore)

instance : InnerProductSpace ℝ C.VSp := InnerProductSpace.ofCore C.vCore.toCore

theorem inner_mkV (σ τ : X0) (u v : X1) (ρ μ : X2) :
    ⟪C.mkV σ u ρ, C.mkV τ v μ⟫
      = ⟪σ, τ⟫ + ⟪C.d0 σ, C.d0 τ⟫ + ⟪u, v⟫ + ⟪C.d1 u, C.d1 v⟫ + ⟪ρ, μ⟫ := rfl

/-- `‖(σ,u,ρ)‖_V² = ‖σ‖² + ‖dσ‖² + ‖u‖² + ‖du‖² + ‖ρ‖²`. -/
theorem norm_mkV_sq (σ : X0) (u : X1) (ρ : X2) : ‖C.mkV σ u ρ‖ ^ 2 = C.normVSq σ u ρ := by
  rw [← real_inner_self_eq_norm_sq, inner_mkV]
  simp only [real_inner_self_eq_norm_sq, normVSq]

theorem normVSq_nonneg (σ : X0) (u : X1) (ρ : X2) : 0 ≤ C.normVSq σ u ρ := by
  unfold normVSq; positivity

theorem norm_mkV (σ : X0) (u : X1) (ρ : X2) : ‖C.mkV σ u ρ‖ = √(C.normVSq σ u ρ) := by
  rw [← norm_mkV_sq, Real.sqrt_sq (norm_nonneg _)]

/-! ### The `W`-norm on `V` -/

/-- The inclusion `V → W = W⁰ × W¹ × W²` (`Tot`, with the `ℓ²` product inner product). -/
def toW : C.VSp →L[ℝ] Tot X0 X1 X2 :=
  LinearMap.mkContinuous (((tot X0 X1 X2).symm.toLinearMap).comp C.vEquiv.toLinearMap) 1
    fun ξ => by
      induction ξ using VSp.induction with
      | h σ u ρ =>
      rw [one_mul, norm_mkV]
      refine Real.le_sqrt_of_sq_le ?_
      change ‖WithLp.toLp 2 (σ, WithLp.toLp 2 (u, ρ))‖ ^ 2 ≤ _
      simp only [WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd]
      unfold normVSq
      nlinarith [sq_nonneg ‖C.d0 σ‖, sq_nonneg ‖C.d1 u‖]

theorem toW_mkV (σ : X0) (u : X1) (ρ : X2) :
    C.toW (C.mkV σ u ρ) = WithLp.toLp 2 (σ, WithLp.toLp 2 (u, ρ)) := rfl

theorem inner_toW_mkV (σ τ : X0) (u v : X1) (ρ μ : X2) :
    ⟪C.toW (C.mkV σ u ρ), C.toW (C.mkV τ v μ)⟫ = ⟪σ, τ⟫ + ⟪u, v⟫ + ⟪ρ, μ⟫ := by
  rw [toW_mkV, toW_mkV, WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  ring

theorem norm_toW_le (ξ : C.VSp) : ‖C.toW ξ‖ ≤ ‖ξ‖ := by
  simpa using (LinearMap.mkContinuous_norm_le _ zero_le_one _ : ‖C.toW‖ ≤ 1) |>
    fun h => (C.toW.le_opNorm ξ).trans (mul_le_of_le_one_left (norm_nonneg _) h)

theorem toW_injective : Function.Injective C.toW := by
  intro ξ ψ h
  induction ξ using VSp.induction
  induction ψ using VSp.induction
  simp only [toW_mkV, WithLp.toLp.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-! ### The forms `a` and `A` on `V` -/

/-- The skew form `a` of (4.7) as a bilinear form on `V`.
See [QuennevilleBelair2015, (4.7)]. -/
def aL : C.VSp →ₗ[ℝ] C.VSp →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun ξ ψ => C.a (C.vEquiv ξ).1 (C.vEquiv ξ).2.1 (C.vEquiv ξ).2.2
      (C.vEquiv ψ).1 (C.vEquiv ψ).2.1 (C.vEquiv ψ).2.2)
    (fun ξ₁ ξ₂ ψ => by
      simp only [map_add, Prod.fst_add, Prod.snd_add, a, inner_add_left]; ring)
    (fun r ξ ψ => by
      simp only [map_smul, Prod.smul_fst, Prod.smul_snd, a, real_inner_smul_left, smul_eq_mul]
      ring)
    (fun ξ ψ₁ ψ₂ => by
      simp only [map_add, Prod.fst_add, Prod.snd_add, a, inner_add_right]; ring)
    (fun r ξ ψ => by
      simp only [map_smul, Prod.smul_fst, Prod.smul_snd, a, real_inner_smul_right, smul_eq_mul]
      ring)

@[simp] theorem aL_mkV (σ τ : X0) (u v : X1) (ρ μ : X2) :
    C.aL (C.mkV σ u ρ) (C.mkV τ v μ) = C.a σ u ρ τ v μ := rfl

/-- `a(ψ, ψ) = 0` on all of `V` (used in the thesis, l.2415, for `ψ ∈ Vₕ`). -/
theorem aL_self (ξ : C.VSp) : C.aL ξ ξ = 0 := by
  induction ξ using VSp.induction
  exact C.a_self _ _ _

/-- The shifted form `A = (·,·)_W + a` (§4.6) as a bilinear form on `V`.
See [QuennevilleBelair2015, §4.6] (the form `A` of Prop 4.13). -/
def formAV : C.VSp →ₗ[ℝ] C.VSp →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun ξ ψ => ⟪C.toW ξ, C.toW ψ⟫ + C.aL ξ ψ)
    (fun ξ₁ ξ₂ ψ => by simp only [map_add, inner_add_left, LinearMap.add_apply]; ring)
    (fun r ξ ψ => by
      simp only [map_smul, real_inner_smul_left, LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun ξ ψ₁ ψ₂ => by simp only [map_add, inner_add_right]; ring)
    (fun r ξ ψ => by simp only [map_smul, real_inner_smul_right, smul_eq_mul]; ring)

theorem formAV_apply (ξ ψ : C.VSp) : C.formAV ξ ψ = ⟪C.toW ξ, C.toW ψ⟫ + C.aL ξ ψ := rfl

@[simp] theorem formAV_mkV (σ τ : X0) (u v : X1) (ρ μ : X2) :
    C.formAV (C.mkV σ u ρ) (C.mkV τ v μ) = C.formA σ u ρ τ v μ := by
  rw [formAV_apply, inner_toW_mkV, aL_mkV, formA]

/-- Cauchy–Schwarz in `ℝ⁴`. -/
private theorem cs4 (x1 x2 x3 x4 y1 y2 y3 y4 : ℝ) :
    x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4
      ≤ √(x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) * √(y1 ^ 2 + y2 ^ 2 + y3 ^ 2 + y4 ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  nlinarith [sq_nonneg (x1 * y2 - x2 * y1), sq_nonneg (x1 * y3 - x3 * y1),
    sq_nonneg (x1 * y4 - x4 * y1), sq_nonneg (x2 * y3 - x3 * y2),
    sq_nonneg (x2 * y4 - x4 * y2), sq_nonneg (x3 * y4 - x4 * y3)]

/-- Boundedness of `A` on `V × V` with constant `2` (thesis l.2336: "uniformly bounded in h").
Thesis gap: the bound is asserted without proof or constant. Proof: `|(ξ,ψ)_W| ≤ ‖ξ‖_V ‖ψ‖_V`
and `|a(ξ,ψ)| ≤ ‖ξ‖_V ‖ψ‖_V`, each by Cauchy–Schwarz. The constant `2` is not optimized; it is
the constant entering `norm_AL_le` and hence the quasi-optimality constant `1 + 2√12` of `ellProj_quasiopt`.
See [QuennevilleBelair2015, §4.6, proof of Thm 4.14]. -/
theorem abs_formA_le (σ τ : X0) (u v : X1) (ρ μ : X2) :
    |C.formA σ u ρ τ v μ| ≤ 2 * √(C.normVSq σ u ρ) * √(C.normVSq τ v μ) := by
  have i1 := abs_real_inner_le_norm σ τ
  have i2 := abs_real_inner_le_norm u v
  have i3 := abs_real_inner_le_norm ρ μ
  have i4 := abs_real_inner_le_norm u (C.d0 τ)
  have i5 := abs_real_inner_le_norm (C.d0 σ) v
  have i6 := abs_real_inner_le_norm ρ (C.d1 v)
  have i7 := abs_real_inner_le_norm (C.d1 u) μ
  have hW := cs4 ‖σ‖ ‖u‖ ‖ρ‖ 0 ‖τ‖ ‖v‖ ‖μ‖ 0
  have ha := cs4 ‖u‖ ‖C.d0 σ‖ ‖ρ‖ ‖C.d1 u‖ ‖C.d0 τ‖ ‖v‖ ‖C.d1 v‖ ‖μ‖
  have m1 : √(‖σ‖ ^ 2 + ‖u‖ ^ 2 + ‖ρ‖ ^ 2 + 0 ^ 2) ≤ √(C.normVSq σ u ρ) :=
    Real.sqrt_le_sqrt (by unfold normVSq; nlinarith [sq_nonneg ‖C.d0 σ‖, sq_nonneg ‖C.d1 u‖])
  have m2 : √(‖τ‖ ^ 2 + ‖v‖ ^ 2 + ‖μ‖ ^ 2 + 0 ^ 2) ≤ √(C.normVSq τ v μ) :=
    Real.sqrt_le_sqrt (by unfold normVSq; nlinarith [sq_nonneg ‖C.d0 τ‖, sq_nonneg ‖C.d1 v‖])
  have m3 : √(‖u‖ ^ 2 + ‖C.d0 σ‖ ^ 2 + ‖ρ‖ ^ 2 + ‖C.d1 u‖ ^ 2) ≤ √(C.normVSq σ u ρ) :=
    Real.sqrt_le_sqrt (by unfold normVSq; nlinarith [sq_nonneg ‖σ‖])
  have m4 : √(‖C.d0 τ‖ ^ 2 + ‖v‖ ^ 2 + ‖C.d1 v‖ ^ 2 + ‖μ‖ ^ 2) ≤ √(C.normVSq τ v μ) :=
    Real.sqrt_le_sqrt (by unfold normVSq; nlinarith [sq_nonneg ‖τ‖])
  have p1 := mul_le_mul m1 m2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have p2 := mul_le_mul m3 m4 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  unfold formA a
  rw [abs_le]
  constructor <;>
  · nlinarith [abs_le.1 i1, abs_le.1 i2, abs_le.1 i3, abs_le.1 i4, abs_le.1 i5, abs_le.1 i6,
      abs_le.1 i7]

theorem abs_formAV_le (ξ ψ : C.VSp) : |C.formAV ξ ψ| ≤ 2 * ‖ξ‖ * ‖ψ‖ := by
  induction ξ using VSp.induction
  induction ψ using VSp.induction
  rw [formAV_mkV, norm_mkV, norm_mkV]
  exact C.abs_formA_le _ _ _ _ _ _

/-- `A` as a continuous bilinear form on `(V, ‖·‖_V)`, with `‖A‖ ≤ 2`.
See [QuennevilleBelair2015, §4.6]. -/
def AL : C.VSp →L[ℝ] C.VSp →L[ℝ] ℝ :=
  C.formAV.mkContinuous₂ 2 fun ξ ψ => by
    rw [Real.norm_eq_abs]; exact C.abs_formAV_le ξ ψ

theorem AL_apply (ξ ψ : C.VSp) : C.AL ξ ψ = ⟪C.toW ξ, C.toW ψ⟫ + C.aL ξ ψ := rfl

theorem norm_AL_le : ‖C.AL‖ ≤ 2 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_two _

/-- `A(ψ, ψ) = ‖ψ‖_W²`. -/
theorem AL_self (ξ : C.VSp) : C.AL ξ ξ = ‖C.toW ξ‖ ^ 2 := by
  rw [AL_apply, aL_self, add_zero, real_inner_self_eq_norm_sq]

/-- `A(ψ, ψ) = 0` forces `ψ = 0`: the dense-range condition for `A` on `V` (and on any
subspace).
See [QuennevilleBelair2015, §4.5] (dense-range condition of Thm 4.9); cf. [Babuska1971]. -/
theorem AL_self_eq_zero {ξ : C.VSp} (h : C.AL ξ ξ = 0) : ξ = 0 := by
  rw [AL_self, sq_eq_zero_iff, norm_eq_zero] at h
  exact C.toW_injective (h.trans (map_zero _).symm)

/-! ## Prop 4.13: the inf-sup condition for `A` -/

/-- The test function `ψ = (σ, u + dσ, ρ − du)` of the proof of Prop 4.13.
See [QuennevilleBelair2015, proof of Prop 4.13]. -/
def testMap : C.VSp →ₗ[ℝ] C.VSp where
  toFun ξ := C.mkV (C.vEquiv ξ).1 ((C.vEquiv ξ).2.1 + C.d0 (C.vEquiv ξ).1)
    ((C.vEquiv ξ).2.2 - C.d1 (C.vEquiv ξ).2.1)
  map_add' ξ ψ := by
    induction ξ using VSp.induction
    induction ψ using VSp.induction
    simp only [mkV_add, vEquiv_mkV, map_add, mkV_add]
    congr 1 <;> abel
  map_smul' r ξ := by
    induction ξ using VSp.induction
    simp only [mkV_smul, vEquiv_mkV, map_smul, RingHom.id_apply, smul_add, smul_sub]

@[simp] theorem testMap_mkV (σ : X0) (u : X1) (ρ : X2) :
    C.testMap (C.mkV σ u ρ) = C.mkV σ (u + C.d0 σ) (ρ - C.d1 u) := rfl

/-- Prop 4.13, first step: `A(ξ; ψ) ≥ ½ ‖ξ‖_V²` for `ψ = (σ, u + dσ, ρ − du)`. -/
theorem normVSq_half_le_formA_test (σ : X0) (u : X1) (ρ : X2) :
    C.normVSq σ u ρ / 2 ≤ C.formA σ u ρ σ (u + C.d0 σ) (ρ - C.d1 u) := by
  unfold formA a normVSq
  simp only [map_add, C.d1_d0, add_zero, inner_add_right, inner_sub_right,
    real_inner_self_eq_norm_sq]
  have c1 := real_inner_comm u (C.d0 σ)
  have c2 := real_inner_comm ρ (C.d1 u)
  have h1 := abs_real_inner_le_norm u (C.d0 σ)
  have h2 := abs_real_inner_le_norm ρ (C.d1 u)
  nlinarith [abs_le.1 h1, abs_le.1 h2, sq_nonneg (‖u‖ - ‖C.d0 σ‖), sq_nonneg (‖ρ‖ - ‖C.d1 u‖),
    sq_nonneg ‖σ‖]

/-- Prop 4.13, second step: `‖ψ‖_V ≤ √3 ‖ξ‖_V` (squared form). -/
theorem normVSq_test_le (σ : X0) (u : X1) (ρ : X2) :
    C.normVSq σ (u + C.d0 σ) (ρ - C.d1 u) ≤ 3 * C.normVSq σ u ρ := by
  unfold normVSq
  simp only [map_add, C.d1_d0, add_zero]
  have h1 : ‖u + C.d0 σ‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖C.d0 σ‖ ^ 2 := by
    have := norm_add_le u (C.d0 σ)
    nlinarith [norm_nonneg (u + C.d0 σ), norm_nonneg u, norm_nonneg (C.d0 σ),
      sq_nonneg (‖u‖ - ‖C.d0 σ‖)]
  have h2 : ‖ρ - C.d1 u‖ ^ 2 ≤ 2 * ‖ρ‖ ^ 2 + 2 * ‖C.d1 u‖ ^ 2 := by
    have := norm_sub_le ρ (C.d1 u)
    nlinarith [norm_nonneg (ρ - C.d1 u), norm_nonneg ρ, norm_nonneg (C.d1 u),
      sq_nonneg (‖ρ‖ - ‖C.d1 u‖)]
  nlinarith [sq_nonneg ‖σ‖, sq_nonneg ‖C.d0 σ‖, sq_nonneg ‖u‖, sq_nonneg ‖C.d1 u‖,
    sq_nonneg ‖ρ‖]

/-- **Thesis Prop 4.13**: for `ψ = (σ, u + dσ, ρ − du)`,
`A(ξ; ψ) ≥ (1/√12) ‖ξ‖_V ‖ψ‖_V`.

Correction: the thesis writes `V = V⁰ × V¹ × V²`; the space is `V = V⁰ × V¹ × W²` (§4.4; the
`ρ`-component carries only the `W²` norm, as in `normVSq`). The proof is the thesis's: `A(ξ;ψ) ≥ ½‖ξ‖²`
and `‖ψ‖ ≤ √3 ‖ξ‖`, the latter left unproved in the thesis. Only `d ∘ d = 0` is used, so the same
statement covers every subcomplex (see `infSup_of_testMap_mem`).
See [QuennevilleBelair2015, Prop 4.13]; cf. [Babuska1971], [BoffiBrezziFortin2013] (inf-sup
conditions), and the discrete Hodge Laplacian inf-sup argument of [AFW2010, §3], [Arnold2018]. -/
theorem formA_test_lower (σ : X0) (u : X1) (ρ : X2) :
    √(C.normVSq σ u ρ) * √(C.normVSq σ (u + C.d0 σ) (ρ - C.d1 u)) / √12
      ≤ C.formA σ u ρ σ (u + C.d0 σ) (ρ - C.d1 u) := by
  have hN := C.normVSq_nonneg σ u ρ
  have hlow := C.normVSq_half_le_formA_test σ u ρ
  have hup := C.normVSq_test_le σ u ρ
  have h12 : √12 = 2 * √3 := by
    rw [show (12:ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have hψ : √(C.normVSq σ (u + C.d0 σ) (ρ - C.d1 u)) ≤ √3 * √(C.normVSq σ u ρ) := by
    rw [← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt hup
  have h3 : 0 < √3 := by positivity
  rw [h12, div_le_iff₀ (by positivity)]
  calc √(C.normVSq σ u ρ) * √(C.normVSq σ (u + C.d0 σ) (ρ - C.d1 u))
      ≤ √(C.normVSq σ u ρ) * (√3 * √(C.normVSq σ u ρ)) := by gcongr
    _ = √3 * C.normVSq σ u ρ := by rw [mul_left_comm, Real.mul_self_sqrt hN]
    _ ≤ √3 * (2 * C.formA σ u ρ σ (u + C.d0 σ) (ρ - C.d1 u)) := by gcongr; linarith
    _ = _ := by ring

/-- Prop 4.13 on `V`: `‖ξ‖_V² / 2 ≤ A(ξ, testMap ξ)`. -/
theorem norm_sq_div_two_le_AL_testMap (ξ : C.VSp) : ‖ξ‖ ^ 2 / 2 ≤ C.AL ξ (C.testMap ξ) := by
  induction ξ using VSp.induction
  rw [norm_mkV_sq, testMap_mkV]
  change _ ≤ C.formAV _ _
  rw [formAV_mkV]
  exact C.normVSq_half_le_formA_test _ _ _

/-- Prop 4.13 on `V`: `(1/√12) ‖ξ‖_V ‖testMap ξ‖_V ≤ A(ξ, testMap ξ)`. -/
theorem formAV_test_lower (ξ : C.VSp) : ‖ξ‖ * ‖C.testMap ξ‖ / √12 ≤ C.AL ξ (C.testMap ξ) := by
  induction ξ using VSp.induction
  rw [testMap_mkV, norm_mkV, norm_mkV]
  change _ ≤ C.formAV _ _
  rw [formAV_mkV]
  exact C.formA_test_lower _ _ _

/-- **Prop 4.13, inf-sup form**, on any subspace `K ⊆ V` stable under the test map (in particular
`V` itself and every subcomplex `Vₕ`, see `Sub.testMap_mem`): for every `w ∈ K` there is `v ∈ K`,
`‖v‖_V ≤ 1`, with `(1/√12) ‖w‖_V ≤ A(w, v)`. This is the hypothesis of `Galerkin.quasi_opt`.
See [QuennevilleBelair2015, Prop 4.13, Thm 4.9]; cf. [Babuska1971], [BoffiBrezziFortin2013]. -/
theorem infSup_of_testMap_mem (K : Submodule ℝ C.VSp) (hK : ∀ ξ ∈ K, C.testMap ξ ∈ K) :
    ∀ w ∈ K, ∃ v ∈ K, ‖v‖ ≤ 1 ∧ 1 / √12 * ‖w‖ ≤ C.AL w v := by
  intro w hw
  by_cases h0 : ‖C.testMap w‖ = 0
  · refine ⟨0, K.zero_mem, by simp, ?_⟩
    have hlow := C.norm_sq_div_two_le_AL_testMap w
    rw [norm_eq_zero.1 h0, map_zero] at hlow
    have : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
    simp [this]
  · have hpos : 0 < ‖C.testMap w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    refine ⟨‖C.testMap w‖⁻¹ • C.testMap w, K.smul_mem _ (hK w hw), ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h0]
    · rw [map_smul, smul_eq_mul]
      have := C.formAV_test_lower w
      rw [le_inv_mul_iff₀ hpos]
      calc ‖C.testMap w‖ * (1 / √12 * ‖w‖) = ‖w‖ * ‖C.testMap w‖ / √12 := by ring
        _ ≤ _ := this

/-! ## The discrete space `Vₕ = Vₕ⁰ × Vₕ¹ × Vₕ²` -/

/-- The discrete space `Vₕ = Vₕ⁰ × Vₕ¹ × Vₕ²` of a subcomplex, as a subspace of `V`.
See [QuennevilleBelair2015, §4.6]; subcomplexes as in [AFW2010, §3], [Arnold2018]. -/
def Sub.toV (S : C.Sub) : Submodule ℝ C.VSp :=
  (S.V0h.prod (S.V1h.prod S.V2h)).comap C.vEquiv.toLinearMap

variable {C} in
theorem Sub.mem_toV {S : C.Sub} {ξ : C.VSp} :
    ξ ∈ S.toV ↔ (C.vEquiv ξ).1 ∈ S.V0h ∧ (C.vEquiv ξ).2.1 ∈ S.V1h ∧ (C.vEquiv ξ).2.2 ∈ S.V2h :=
  Iff.rfl

variable {C} in
theorem Sub.mkV_mem_toV {S : C.Sub} {σ : X0} {u : X1} {ρ : X2} :
    C.mkV σ u ρ ∈ S.toV ↔ σ ∈ S.V0h ∧ u ∈ S.V1h ∧ ρ ∈ S.V2h :=
  Iff.rfl

/-- The subcomplex property makes `Vₕ` stable under the test map of Prop 4.13 (thesis: "this
result also holds at the discrete level by the same proof", l.2366).
See [QuennevilleBelair2015, proof of Prop 4.13] (subcomplex property); cf. [AFW2010, §3],
[Arnold2018]. -/
theorem Sub.testMap_mem (S : C.Sub) {ξ : C.VSp} (hξ : ξ ∈ S.toV) : C.testMap ξ ∈ S.toV := by
  induction ξ using VSp.induction with
  | h σ u ρ =>
  obtain ⟨h0, h1, h2⟩ := Sub.mkV_mem_toV.1 hξ
  exact Sub.mkV_mem_toV.2 ⟨h0, S.V1h.add_mem h1 (S.d0_mem σ h0), S.V2h.sub_mem h2 (S.d1_mem u h1)⟩

/-- `Vₕ` is finite-dimensional when its three components are. -/
instance Sub.finiteDimensional_toV (S : C.Sub) [FiniteDimensional ℝ S.V0h]
    [FiniteDimensional ℝ S.V1h] [FiniteDimensional ℝ S.V2h] : FiniteDimensional ℝ S.toV := by
  let f : S.V0h × S.V1h × S.V2h →ₗ[ℝ] C.VSp :=
    C.vEquiv.symm.toLinearMap.comp
      (S.V0h.subtype.prodMap (S.V1h.subtype.prodMap S.V2h.subtype))
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range f) fun ξ hξ => ?_
  obtain ⟨h0, h1, h2⟩ := Sub.mem_toV.1 hξ
  exact ⟨(⟨_, h0⟩, ⟨_, h1⟩, ⟨_, h2⟩), rfl⟩

/-- Discrete Prop 4.13: the inf-sup condition on `Vₕ` with the `h`-independent constant `1/√12`.
See [QuennevilleBelair2015, Prop 4.13]; uniform discrete inf-sup stability in the sense of
[Babuska1971], [BoffiBrezziFortin2013]; cf. [AFW2010, §3], [Arnold2018]. -/
theorem Sub.infSup (S : C.Sub) :
    ∀ w ∈ S.toV, ∃ v ∈ S.toV, ‖v‖ ≤ 1 ∧ 1 / √12 * ‖w‖ ≤ C.AL w v :=
  C.infSup_of_testMap_mem S.toV fun _ h => Sub.testMap_mem C S h

/-! ## The elliptic projection (4.11) -/

section EllProj

variable (S : C.Sub) [FiniteDimensional ℝ S.toV]

theorem one_div_sqrt12_pos : (0:ℝ) < 1 / √12 := by positivity

/-- **(4.11)**, well-posedness of the elliptic projection: for `ζ ∈ V` there is a unique
`Πₕζ ∈ Vₕ` with `A(Πₕζ, ψ) = A(ζ, ψ)` for all `ψ ∈ Vₕ`. The thesis argues "square system +
injectivity (test with `ψ = Πₕζ`)", which is correct on a finite-dimensional `Vₕ`; here it
follows from the discrete inf-sup condition (Prop 4.13) and `Galerkin.discrete_existsUnique`.
See [QuennevilleBelair2015, (4.11), Thm 4.9]; cf. [Babuska1971], [BoffiBrezziFortin2013]. -/
theorem ellProj_existsUnique (ζ : C.VSp) :
    ∃! p, p ∈ S.toV ∧ ∀ ψ ∈ S.toV, C.AL p ψ = C.AL ζ ψ :=
  Galerkin.discrete_existsUnique C.AL S.toV one_div_sqrt12_pos (Sub.infSup C S) (C.AL ζ)

/-- The elliptic projection as a function (the unique solution of (4.11)). -/
def ellProjFun (ζ : C.VSp) : C.VSp := (C.ellProj_existsUnique S ζ).exists.choose

theorem ellProjFun_spec (ζ : C.VSp) :
    C.ellProjFun S ζ ∈ S.toV ∧ ∀ ψ ∈ S.toV, C.AL (C.ellProjFun S ζ) ψ = C.AL ζ ψ :=
  (C.ellProj_existsUnique S ζ).exists.choose_spec

theorem ellProjFun_eq {ζ p : C.VSp} (hp : p ∈ S.toV) (h : ∀ ψ ∈ S.toV, C.AL p ψ = C.AL ζ ψ) :
    C.ellProjFun S ζ = p :=
  (C.ellProj_existsUnique S ζ).unique (C.ellProjFun_spec S ζ) ⟨hp, h⟩

/-- Stability of the elliptic projection: `‖Πₕζ‖_V ≤ 2√12 ‖ζ‖_V`, uniformly in `h`.
See [QuennevilleBelair2015, §4.6, Thm 4.9]. -/
theorem norm_ellProjFun_le (ζ : C.VSp) : ‖C.ellProjFun S ζ‖ ≤ 2 * √12 * ‖ζ‖ := by
  obtain ⟨hm, hs⟩ := C.ellProjFun_spec S ζ
  obtain ⟨v, hv, hv1, h⟩ := Sub.infSup C S _ hm
  rw [hs v hv] at h
  have hA : C.AL ζ v ≤ 2 * ‖ζ‖ := by
    calc C.AL ζ v ≤ ‖C.AL ζ v‖ := Real.le_norm_self _
      _ ≤ ‖C.AL ζ‖ * ‖v‖ := (C.AL ζ).le_opNorm v
      _ ≤ (‖C.AL‖ * ‖ζ‖) * 1 := by
          gcongr
          · exact C.AL.le_opNorm ζ
      _ ≤ 2 * ‖ζ‖ := by rw [mul_one]; gcongr; exact C.norm_AL_le
  have h12 : 0 < √12 := by positivity
  have := h.trans hA
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ h12] at this
  linarith

/-- **The elliptic projection** `Πₕ : V → V` (values in `Vₕ`) of (4.11), as a bounded linear
map with `‖Πₕ‖ ≤ 2√12`.
See [QuennevilleBelair2015, (4.11)]; elliptic projections in error analyses of second-order
hyperbolic problems as in [Baker1976]; for mixed wave formulations cf. [Geveci1988],
[GilletteHolstZhu2017]. -/
def ellProj : C.VSp →L[ℝ] C.VSp :=
  LinearMap.mkContinuous
    { toFun := C.ellProjFun S
      map_add' := fun ζ₁ ζ₂ => C.ellProjFun_eq S
        (S.toV.add_mem (C.ellProjFun_spec S ζ₁).1 (C.ellProjFun_spec S ζ₂).1)
        fun ψ hψ => by
          rw [map_add, map_add, add_apply, add_apply,
            (C.ellProjFun_spec S ζ₁).2 ψ hψ, (C.ellProjFun_spec S ζ₂).2 ψ hψ]
      map_smul' := fun r ζ => C.ellProjFun_eq S (S.toV.smul_mem r (C.ellProjFun_spec S ζ).1)
        fun ψ hψ => by
          rw [map_smul, map_smul, smul_apply, smul_apply,
            (C.ellProjFun_spec S ζ).2 ψ hψ, RingHom.id_apply] }
    (2 * √12) (C.norm_ellProjFun_le S)

theorem ellProj_apply (ζ : C.VSp) : C.ellProj S ζ = C.ellProjFun S ζ := rfl

theorem ellProj_mem (ζ : C.VSp) : C.ellProj S ζ ∈ S.toV := (C.ellProjFun_spec S ζ).1

/-- The defining relation (4.11): `(Πₕζ, ψ) + a(Πₕζ, ψ) = (ζ, ψ) + a(ζ, ψ)` for `ψ ∈ Vₕ`. -/
theorem ellProj_spec (ζ : C.VSp) {ψ : C.VSp} (hψ : ψ ∈ S.toV) :
    C.AL (C.ellProj S ζ) ψ = C.AL ζ ψ := (C.ellProjFun_spec S ζ).2 ψ hψ

theorem ellProj_eq {ζ p : C.VSp} (hp : p ∈ S.toV) (h : ∀ ψ ∈ S.toV, C.AL p ψ = C.AL ζ ψ) :
    C.ellProj S ζ = p := C.ellProjFun_eq S hp h

theorem norm_ellProj_le : ‖C.ellProj S‖ ≤ 2 * √12 :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- **Quasi-optimality of the elliptic projection** (thesis l.2368–2372, via Thm 4.10):
`‖ζ − Πₕζ‖_V ≤ (1 + 2√12) ‖ζ − ψ‖_V` for every `ψ ∈ Vₕ`.

Thesis gap: the thesis only asserts "there exists a constant C"; the constant
`C = 1 + ‖A‖·√12 ≤ 1 + 2√12` follows from `‖A‖ ≤ 2` (`norm_AL_le`) and Prop 4.13.
See [QuennevilleBelair2015, Thm 4.10, §4.6]; cf. [Babuska1971], [BoffiBrezziFortin2013]. -/
theorem ellProj_quasiopt (ζ : C.VSp) {ψ : C.VSp} (hψ : ψ ∈ S.toV) :
    ‖ζ - C.ellProj S ζ‖ ≤ (1 + 2 * √12) * ‖ζ - ψ‖ := by
  have h := Galerkin.quasi_opt C.AL S.toV one_div_sqrt12_pos (Sub.infSup C S) (u := ζ)
    (C.ellProj_mem S ζ) (fun v hv => by
      rw [map_sub, sub_apply, C.ellProj_spec S ζ hv, sub_self]) ψ hψ
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have h12 : 0 < √12 := by positivity
  rw [one_div, div_inv_eq_mul]
  gcongr
  exact C.norm_AL_le

/-- Squared-norm form of `ellProj_quasiopt` (as in the blueprint):
`normVSq (ζ − Πₕζ) ≤ (1 + 2√12)² normVSq (ζ − ψ)`. -/
theorem ellProj_quasiopt_sq (ζ : C.VSp) {ψ : C.VSp} (hψ : ψ ∈ S.toV) :
    ‖ζ - C.ellProj S ζ‖ ^ 2 ≤ (1 + 2 * √12) ^ 2 * ‖ζ - ψ‖ ^ 2 := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (C.ellProj_quasiopt S ζ hψ) 2

end EllProj

/-! ## Weak and discrete solutions -/

/-- A **weak solution** of the mixed Hodge wave equation (4.8) on `[0,T]` with the regularity
`ξ ∈ C¹([0,T]; V)` needed by Thm 4.14: `ξ` and `ξ'` are continuous on `[0,T]` in the `V`-norm,
`ξ'` is the right derivative of `ξ` in `V` on `[0,T)`, and `(ξ̇, ψ)_W + a(ξ, ψ) = 0` for all
`ψ ∈ V`.

Correction: the thesis's weak solutions are only `C⁰([0,T]; V) ∩ C¹([0,T]; W)` (l.2113), but
the proof of Thm 4.14 differentiates `ξₕ^Π = Πₕξ`, and `Πₕ` is bounded on `V`, not on `W`
(it involves `d`); so `ξ ∈ C¹([0,T]; V)` is assumed. Such a `ξ` is in particular a weak solution
in the thesis's sense (`IsWeakSol.hasDerivWithinAt_toW`).
See [QuennevilleBelair2015, (4.8), §4.4, Thm 4.14]. -/
def IsWeakSol (T : ℝ) (ξ ξ' : ℝ → C.VSp) : Prop :=
  ContinuousOn ξ (Icc 0 T) ∧ ContinuousOn ξ' (Icc 0 T) ∧
    (∀ t ∈ Ico 0 T, HasDerivWithinAt ξ (ξ' t) (Ici t) t) ∧
    ∀ t ∈ Ico 0 T, ∀ ψ : C.VSp, ⟪C.toW (ξ' t), C.toW ψ⟫ + C.aL (ξ t) ψ = 0

variable {C} in
/-- The `W`-valued trajectory of a weak solution is right-differentiable in `W` with derivative
`toW ξ'` (so `ξ ∈ C⁰(V) ∩ C¹(W)` as in the thesis). -/
theorem IsWeakSol.hasDerivWithinAt_toW {T : ℝ} {ξ ξ' : ℝ → C.VSp} (h : C.IsWeakSol T ξ ξ') :
    ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun s => C.toW (ξ s)) (C.toW (ξ' t)) (Ici t) t :=
  fun t ht => C.toW.hasFDerivAt.comp_hasDerivWithinAt t (h.2.2.1 t ht)

/-- A **discrete solution** of (4.10) on `[0,T]`: `ξₕ(t) ∈ Vₕ`, `ξₕ` continuous on `[0,T]` with
right derivative `ξₕ'` on `[0,T)`, and `(ξ̇ₕ, ψ)_W + a(ξₕ, ψ) = 0` for all `ψ ∈ Vₕ`. (The thesis
asks `ξₕ ∈ C¹([0,T]; Vₕ)`; one-sided derivatives suffice and make uniqueness stronger; the
solutions constructed in `discrete_solution_exists` are `C¹` on `ℝ`.)
See [QuennevilleBelair2015, (4.10)]. -/
def IsDiscreteSol (S : C.Sub) (T : ℝ) (ξh ξh' : ℝ → C.VSp) : Prop :=
  ContinuousOn ξh (Icc 0 T) ∧ (∀ t ∈ Icc 0 T, ξh t ∈ S.toV) ∧
    (∀ t ∈ Ico 0 T, HasDerivWithinAt ξh (ξh' t) (Ici t) t) ∧
    ∀ t ∈ Ico 0 T, ∀ ψ ∈ S.toV, ⟪C.toW (ξh' t), C.toW ψ⟫ + C.aL (ξh t) ψ = 0

section Discrete

variable (S : C.Sub) [FiniteDimensional ℝ S.toV]

/-- The `W` Gram map `Vₕ → Vₕ*`, `ξ ↦ (ξ, ·)_W`. -/
def gramW : S.toV →ₗ[ℝ] Module.Dual ℝ S.toV :=
  (innerₗ (Tot X0 X1 X2)).compl₁₂ (C.toW.toLinearMap.comp S.toV.subtype)
    (C.toW.toLinearMap.comp S.toV.subtype)

omit [FiniteDimensional ℝ S.toV] in
theorem gramW_apply (ξ ψ : S.toV) : C.gramW S ξ ψ = ⟪C.toW ξ, C.toW ψ⟫ := rfl

theorem gramW_bijective : Function.Bijective (C.gramW S) := by
  have hinj : Function.Injective (C.gramW S) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ξ hξ
    have h := LinearMap.congr_fun hξ ξ
    rw [gramW_apply, LinearMap.zero_apply, real_inner_self_eq_norm_sq, sq_eq_zero_iff,
      norm_eq_zero] at h
    exact Subtype.ext (C.toW_injective (h.trans (map_zero _).symm))
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    Subspace.dual_finrank_eq.symm).1 hinj⟩

/-- The form `a` restricted to `Vₕ`, as a map `Vₕ → Vₕ*`. -/
def aFlat : S.toV →ₗ[ℝ] Module.Dual ℝ S.toV :=
  C.aL.compl₁₂ S.toV.subtype S.toV.subtype

/-- The discrete operator `Mₕ : Vₕ → Vₕ`, `(Mₕ ξ, ψ)_W = −a(ξ, ψ)` for `ψ ∈ Vₕ`, so that (4.10)
reads `ξ̇ₕ = Mₕ ξₕ`.
See [QuennevilleBelair2015, (4.10)]. -/
def semidiscreteOp : S.toV →L[ℝ] S.toV :=
  LinearMap.toContinuousLinearMap
    (-((LinearEquiv.ofBijective (C.gramW S) (C.gramW_bijective S)).symm.toLinearMap.comp
      (C.aFlat S)))

theorem semidiscreteOp_spec (ξ ψ : S.toV) : ⟪C.toW (C.semidiscreteOp S ξ), C.toW ψ⟫ = -C.aL ξ ψ := by
  rw [← gramW_apply]
  change C.gramW S (-(LinearEquiv.ofBijective (C.gramW S) (C.gramW_bijective S)).symm
    (C.aFlat S ξ)) ψ = _
  have h := (LinearEquiv.ofBijective (C.gramW S) (C.gramW_bijective S)).apply_symm_apply
    (C.aFlat S ξ)
  rw [LinearEquiv.ofBijective_apply] at h
  rw [map_neg, h, LinearMap.neg_apply]
  rfl

/-- **Existence of the discrete solution** (thesis l.2316: "a square system of linear ordinary
differential equations"): for every `ξ₀ ∈ Vₕ` there is a `C¹` trajectory `ξₕ : ℝ → Vₕ` with
`ξₕ(0) = ξ₀` solving (4.10) for all `t`, namely `ξₕ(t) = exp(t Mₕ) ξ₀`.
See [QuennevilleBelair2015, §4.6]. -/
theorem discrete_solution_exists {ξ₀ : C.VSp} (h₀ : ξ₀ ∈ S.toV) :
    ∃ ξh ξh' : ℝ → C.VSp, ξh 0 = ξ₀ ∧ (∀ t, ξh t ∈ S.toV) ∧ (∀ t, HasDerivAt ξh (ξh' t) t) ∧
      Continuous ξh' ∧ ∀ t, ∀ ψ ∈ S.toV, ⟪C.toW (ξh' t), C.toW ψ⟫ + C.aL (ξh t) ψ = 0 := by
  set M := C.semidiscreteOp S
  set x : ℝ → S.toV := fun t => NormedSpace.exp (t • M) ⟨ξ₀, h₀⟩ with hx
  have hxd : ∀ t, HasDerivAt x (M (x t)) t := by
    intro t
    have := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) M t).clm_apply (hasDerivAt_const t ⟨ξ₀, h₀⟩)
    simpa [hx] using this
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hxd t).continuousAt
  refine ⟨fun t => (x t : C.VSp), fun t => (M (x t) : C.VSp), by simp [hx], fun t => (x t).2,
    fun t => S.toV.subtypeL.hasFDerivAt.comp_hasDerivAt t (hxd t),
    S.toV.subtypeL.continuous.comp (M.continuous.comp hxc), fun t ψ hψ => ?_⟩
  have := C.semidiscreteOp_spec S (x t) ⟨ψ, hψ⟩
  simp only at this ⊢
  change ⟪C.toW (M (x t) : C.VSp), C.toW ψ⟫ + _ = 0
  rw [this]; ring

omit [FiniteDimensional ℝ S.toV] in
/-- `discrete_solution_exists` produces discrete solutions in the sense of `IsDiscreteSol`. -/
theorem isDiscreteSol_of_global {T : ℝ} {ξh ξh' : ℝ → C.VSp} (hm : ∀ t, ξh t ∈ S.toV)
    (hd : ∀ t, HasDerivAt ξh (ξh' t) t)
    (heq : ∀ t, ∀ ψ ∈ S.toV, ⟪C.toW (ξh' t), C.toW ψ⟫ + C.aL (ξh t) ψ = 0) :
    C.IsDiscreteSol S T ξh ξh' :=
  ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => hm t,
    fun t _ => (hd t).hasDerivWithinAt, fun t _ => heq t⟩

omit [FiniteDimensional ℝ S.toV] in
variable {C S} in
/-- **Stability of the semi-discrete scheme (4.10)** in `W`, uniform in the subcomplex: for two
discrete solutions on the same `Vₕ`, `‖ξ₁(t) − ξ₂(t)‖_W ≤ ‖ξ₁(0) − ξ₂(0)‖_W` on `[0,T]`
(energy argument: `a(ψ, ψ) = 0`, then the energy estimate with zero forcing).
See [QuennevilleBelair2015, §4.6]. -/
theorem IsDiscreteSol.norm_toW_sub_le {T : ℝ} {ξ₁ ξ₁' ξ₂ ξ₂' : ℝ → C.VSp}
    (h₁ : C.IsDiscreteSol S T ξ₁ ξ₁') (h₂ : C.IsDiscreteSol S T ξ₂ ξ₂') :
    ∀ t ∈ Icc 0 T, ‖C.toW (ξ₁ t - ξ₂ t)‖ ≤ ‖C.toW (ξ₁ 0 - ξ₂ 0)‖ := by
  obtain ⟨c₁, m₁, d₁, e₁⟩ := h₁
  obtain ⟨c₂, m₂, d₂, e₂⟩ := h₂
  set e : ℝ → Tot X0 X1 X2 := fun t => C.toW (ξ₁ t - ξ₂ t) with he
  have hec : ContinuousOn e (Icc 0 T) := C.toW.continuous.comp_continuousOn (c₁.sub c₂)
  have hed : ∀ t ∈ Ico 0 T, HasDerivWithinAt e (C.toW (ξ₁' t - ξ₂' t)) (Ici t) t :=
    fun t ht => C.toW.hasFDerivAt.comp_hasDerivWithinAt t ((d₁ t ht).sub (d₂ t ht))
  have key := Evolution.Energy.norm_le_add_integral_of_re_inner_deriv_le (𝕜 := ℝ) (g := 0)
    hec hed continuousOn_const (fun _ _ => le_rfl) (fun t ht => by
      have hm : ξ₁ t - ξ₂ t ∈ S.toV :=
        S.toV.sub_mem (m₁ t (Ico_subset_Icc_self ht)) (m₂ t (Ico_subset_Icc_self ht))
      have E1 := e₁ t ht _ hm
      have E2 := e₂ t ht _ hm
      have hs := C.aL_self (ξ₁ t - ξ₂ t)
      rw [RCLike.re_to_real, Pi.zero_apply, zero_mul]
      simp only [he, map_sub, inner_sub_left, inner_sub_right, LinearMap.sub_apply] at E1 E2 hs ⊢
      linarith)
  intro t ht
  simpa only [he, Pi.zero_apply, intervalIntegral.integral_zero, add_zero] using key t ht

omit [FiniteDimensional ℝ S.toV] in
/-- **Uniqueness of the discrete solution**: two discrete solutions with the same initial value
agree on `[0,T]`. Energy proof (thesis l.2120 at the discrete level): `d/dt ‖ξ₁ − ξ₂‖_W² =
−2a(ξ₁ − ξ₂, ξ₁ − ξ₂) = 0` (`IsDiscreteSol.norm_toW_sub_le`); the `W`-norm is definite on `V`.
See [QuennevilleBelair2015, §4.6]. -/
theorem discrete_solution_unique {T : ℝ} {ξ₁ ξ₁' ξ₂ ξ₂' : ℝ → C.VSp}
    (h₁ : C.IsDiscreteSol S T ξ₁ ξ₁') (h₂ : C.IsDiscreteSol S T ξ₂ ξ₂') (h0 : ξ₁ 0 = ξ₂ 0) :
    ∀ t ∈ Icc 0 T, ξ₁ t = ξ₂ t := by
  intro t ht
  have h := h₁.norm_toW_sub_le h₂ t ht
  rw [h0, sub_self, map_zero, norm_zero] at h
  have : C.toW (ξ₁ t - ξ₂ t) = C.toW 0 := by
    rw [map_zero]; exact norm_le_zero_iff.1 h
  exact sub_eq_zero.1 (C.toW_injective this)

end Discrete

/-! ## Thm 4.14 -/

section ErrorBound

variable (S : C.Sub) [FiniteDimensional ℝ S.toV]

/-- `ζ ↦ toW (Πₕζ − ζ)`, the `W`-valued elliptic-projection error, as a bounded linear map. -/
def projErr : C.VSp →L[ℝ] Tot X0 X1 X2 :=
  C.toW.comp (C.ellProj S - ContinuousLinearMap.id ℝ C.VSp)

theorem projErr_apply (ζ : C.VSp) : C.projErr S ζ = C.toW (C.ellProj S ζ - ζ) := rfl

theorem norm_projErr_le (ζ : C.VSp) : ‖C.projErr S ζ‖ ≤ ‖ζ - C.ellProj S ζ‖ := by
  rw [projErr_apply, norm_sub_rev]; exact C.norm_toW_le _

/-- **Thm 4.14**, pointwise and sharp form. Let `ξ` be a weak solution (`IsWeakSol`, with the
corrected regularity `C¹([0,T]; V)`), `ξₕ` a discrete solution, `e = Πₕξ − ξ` the
elliptic-projection error and `εₕ = Πₕξ − ξₕ` the projected error. Then for `t ∈ [0,T]`
`‖ξ(t) − ξₕ(t)‖_W ≤ ‖εₕ(0)‖_W + ‖e(t)‖_W + t ‖e(0)‖_W + (1 + t) ∫₀ᵗ ‖ė‖_W`.

The proof is the thesis's: the error equation `(ε̇ₕ, ψ) + a(εₕ, ψ) = (ė, ψ) − (e, ψ)` on `Vₕ`
(from (4.8), (4.10), (4.11)), tested with `ψ = εₕ` and `a(εₕ, εₕ) = 0`, then Lemma 4.12 and
`|f(t)| ≤ |f(0)| + ∫₀ᵗ |ḟ|`.
See [QuennevilleBelair2015, Thm 4.14]; classical analogues for second-order hyperbolic
equations in [Dupont1973], [Baker1976], for mixed methods [Geveci1988], and in the FEEC setting
[GilletteHolstZhu2017]. -/
theorem semidiscrete_error_bound_pointwise {T : ℝ} {ξ ξ' ξh ξh' : ℝ → C.VSp} (hξ : C.IsWeakSol T ξ ξ')
    (hξh : C.IsDiscreteSol S T ξh ξh') :
    ∀ t ∈ Icc 0 T, ‖C.toW (ξ t - ξh t)‖ ≤ ‖C.toW (C.ellProj S (ξ 0) - ξh 0)‖
      + ‖C.projErr S (ξ t)‖ + t * ‖C.projErr S (ξ 0)‖
      + (1 + t) * ∫ s in (0:ℝ)..t, ‖C.projErr S (ξ' s)‖ := by
  obtain ⟨c, c', d, w⟩ := hξ
  obtain ⟨ch, mh, dh, eh⟩ := hξh
  have h := Variational.GalerkinEvolution.error_bound_refined (𝕜 := ℝ) C.toW
    (fun x ψ => C.aL x ψ) (fun x y ψ => by simp only [map_sub, LinearMap.sub_apply]) S.toV
    (fun ψ _ => by rw [C.aL_self, RCLike.re_to_real]) (C.ellProj S) (C.ellProj_mem S)
    (fun ζ ψ hψ => by
      have E := C.ellProj_spec S ζ hψ
      simp only [AL_apply] at E
      simp only [map_sub, inner_sub_right, LinearMap.sub_apply]
      have h1 := real_inner_comm (C.toW (C.ellProj S ζ)) (C.toW ψ)
      have h2 := real_inner_comm (C.toW ζ) (C.toW ψ)
      linarith)
    c c' d (fun t ht ψ _ => by rw [real_inner_comm]; exact w t ht ψ) ch mh dh
    (fun t ht ψ hψ => by rw [real_inner_comm]; exact eh t ht ψ hψ)
  intro t ht
  simpa only [sub_zero, projErr_apply] using h t ht

/-- **Thm 4.14** in the thesis's form: for `t ∈ [0,T]`,
`‖ξ(t) − ξₕ(t)‖_W ≤ ‖εₕ(0)‖_W + ‖e(t)‖_W + (1 + T)(‖e(0)‖_W + ∫₀ᵀ ‖ė‖_W)`; taking the
supremum over `t` gives the thesis's `L∞(W)` bound (with `‖e(t)‖ ≤ ‖e‖_{L∞(W)}`).

Correction: (i) `ξ ∈ C¹([0,T]; V)` is required (see `IsWeakSol`), since the proof
differentiates `Πₕξ`; (ii) the factor `(1 + T)` is loose — the proof gives
`t ‖e(0)‖ + (1 + t) ∫₀ᵗ ‖ė‖` (`semidiscrete_error_bound_pointwise`). Thesis gap: the step from
`‖εₕ(t)‖ ≤ ‖εₕ(0)‖ + ∫₀ᵗ(‖ė‖ + ‖e‖)` to the `(1 + T)` bound uses `‖e(s)‖ ≤ ‖e(0)‖ + ∫₀ˢ ‖ė‖`
for the `L¹` norm of `e`, which is spelled out in `error_bound_core`.
See [QuennevilleBelair2015, Thm 4.14]; cf. [Baker1976], [Dupont1973], [Geveci1988],
[GilletteHolstZhu2017]. -/
theorem semidiscrete_error_bound {T : ℝ} {ξ ξ' ξh ξh' : ℝ → C.VSp} (hξ : C.IsWeakSol T ξ ξ')
    (hξh : C.IsDiscreteSol S T ξh ξh') :
    ∀ t ∈ Icc 0 T, ‖C.toW (ξ t - ξh t)‖ ≤ ‖C.toW (C.ellProj S (ξ 0) - ξh 0)‖
      + ‖C.projErr S (ξ t)‖
      + (1 + T) * (‖C.projErr S (ξ 0)‖ + ∫ s in (0:ℝ)..T, ‖C.projErr S (ξ' s)‖) := by
  intro t ht
  have h := C.semidiscrete_error_bound_pointwise S hξ hξh t ht
  have hI : ∫ s in (0:ℝ)..t, ‖C.projErr S (ξ' s)‖ ≤ ∫ s in (0:ℝ)..T, ‖C.projErr S (ξ' s)‖ :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (((C.projErr S).continuous.comp_continuousOn hξ.2.1).norm.intervalIntegrable_of_Icc
        (ht.1.trans ht.2))
  have hI0 : 0 ≤ ∫ s in (0:ℝ)..t, ‖C.projErr S (ξ' s)‖ :=
    intervalIntegral.integral_nonneg ht.1 fun _ _ => norm_nonneg _
  have h1 : t * ‖C.projErr S (ξ 0)‖ ≤ (1 + T) * ‖C.projErr S (ξ 0)‖ :=
    mul_le_mul_of_nonneg_right (by linarith [ht.2]) (norm_nonneg _)
  have h2 : (1 + t) * ∫ s in (0:ℝ)..t, ‖C.projErr S (ξ' s)‖
      ≤ (1 + T) * ∫ s in (0:ℝ)..T, ‖C.projErr S (ξ' s)‖ :=
    mul_le_mul (by linarith [ht.2]) hI hI0 (by linarith [ht.1, ht.2])
  linarith

end ErrorBound

/-! ## Convergence -/

section Convergence

variable {ι : Type*} {l : Filter ι} (S : ι → C.Sub)

/-- The thesis's density hypothesis (§4.6, l.2261): for each `i` and `v ∈ Vⁱ`,
`inf_{w ∈ Vₕⁱ} ‖v − w‖_{Vⁱ} → 0` as `h → 0` (along the filter `l`), written out with the graph
norms of `V⁰`, `V¹` and the `W²` norm.
See [QuennevilleBelair2015, §4.6]; cf. the approximation hypothesis of [AFW2010, §3],
[Arnold2018]. -/
def DensityHyp (l : Filter ι) (S : ι → C.Sub) : Prop :=
  (∀ σ : X0, ∀ δ > 0, ∀ᶠ h in l, ∃ τ ∈ (S h).V0h, ‖σ - τ‖ ^ 2 + ‖C.d0 (σ - τ)‖ ^ 2 < δ) ∧
  (∀ u : X1, ∀ δ > 0, ∀ᶠ h in l, ∃ v ∈ (S h).V1h, ‖u - v‖ ^ 2 + ‖C.d1 (u - v)‖ ^ 2 < δ) ∧
  (∀ ρ : X2, ∀ δ > 0, ∀ᶠ h in l, ∃ μ ∈ (S h).V2h, ‖ρ - μ‖ ^ 2 < δ)

variable {C S}

/-- Componentwise density gives density of `Vₕ` in `V`. -/
theorem DensityHyp.approx (hd : C.DensityHyp l S) (ζ : C.VSp) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ h in l, ∃ w ∈ (S h).toV, ‖ζ - w‖ < δ := by
  induction ζ using VSp.induction with
  | h σ u ρ =>
  have hδ' : 0 < δ ^ 2 / 3 := by positivity
  filter_upwards [hd.1 σ _ hδ', hd.2.1 u _ hδ', hd.2.2 ρ _ hδ'] with h ⟨τ, hτ, h0⟩ ⟨v, hv, h1⟩
    ⟨μ, hμ, h2⟩
  refine ⟨C.mkV τ v μ, Sub.mkV_mem_toV.2 ⟨hτ, hv, hμ⟩, ?_⟩
  rw [mkV_sub, norm_mkV]
  rw [Real.sqrt_lt' hδ]
  unfold normVSq
  linarith

/-- Density, uniformly on compact subsets of `V`. -/
theorem DensityHyp.approx_compact (hd : C.DensityHyp l S) {K : Set C.VSp} (hK : IsCompact K) {δ : ℝ}
    (hδ : 0 < δ) : ∀ᶠ h in l, ∀ ζ ∈ K, ∃ w ∈ (S h).toV, ‖ζ - w‖ < δ := by
  obtain ⟨t, -, ht, hcov⟩ := hK.finite_cover_balls (half_pos hδ)
  have hev := (Filter.eventually_all_finite ht).2 fun z _ => hd.approx z (half_pos hδ)
  filter_upwards [hev] with h hh ζ hζ
  obtain ⟨z, hz, hζz⟩ := Set.mem_iUnion₂.1 (hcov hζ)
  obtain ⟨w, hw, hzw⟩ := hh z hz
  refine ⟨w, hw, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hζz
  calc ‖ζ - w‖ = ‖(ζ - z) + (z - w)‖ := by congr 1; abel
    _ ≤ ‖ζ - z‖ + ‖z - w‖ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := add_lt_add hζz hzw
    _ = δ := add_halves δ

/-- **Convergence of the elliptic projection**, uniformly on compact sets of `V`: under density
alone (with Prop 4.13 and quasi-optimality), `‖ζ − Πₕζ‖_V → 0` uniformly for `ζ ∈ K`.

Correction (thesis l.2449: "if we have a Hilbert complex with the compactness property, the
elliptic projection converges"): compactness is not needed.
See [QuennevilleBelair2015, §4.6, Thm 4.10]. -/
theorem DensityHyp.ellProj_tendsto [∀ h, FiniteDimensional ℝ (S h).toV] (hd : C.DensityHyp l S)
    {K : Set C.VSp} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ h in l, ∀ ζ ∈ K, ‖ζ - C.ellProj (S h) ζ‖ ≤ δ := by
  have hC : 0 < 1 + 2 * √12 := by positivity
  filter_upwards [hd.approx_compact hK (div_pos hδ hC)] with h hh ζ hζ
  obtain ⟨w, hw, hζw⟩ := hh ζ hζ
  calc ‖ζ - C.ellProj (S h) ζ‖ ≤ (1 + 2 * √12) * ‖ζ - w‖ := C.ellProj_quasiopt (S h) ζ hw
    _ ≤ (1 + 2 * √12) * (δ / (1 + 2 * √12)) := by gcongr
    _ = δ := by field_simp

/-- **Convergence of the method** (thesis, after Thm 4.14): let `ξ` be a weak solution with
`ξ ∈ C¹([0,T]; V)`, `Vₕ` finite-dimensional subcomplexes satisfying the density hypothesis, and
`ξₕ` discrete solutions with `‖εₕ(0)‖_W = ‖Πₕξ(0) − ξₕ(0)‖_W → 0`. Then `ξₕ → ξ` in `W`,
uniformly on `[0,T]` (i.e. in `L∞(0,T; W)`).

Correction: the thesis states this under the compactness property and for `ξₕ(0) = Πₕξ(0)`;
neither is needed beyond `εₕ(0) → 0` (see `convergence_of_initProj`): density, Prop 4.13 and
Thm 4.14 suffice. The assumption `ξ ∈ C¹([0,T]; V)` is removed in `Feec.Legacy.ErrorEstimateDomain`:
convergence holds for every `ξ₀ ∈ D(L)` with `ξₕ(0) = Πₕ ξ₀`
(`HilbertComplex2.convergence_domL_weakSolution`) and for every `ξ₀ ∈ W` with `ξₕ(0) → ξ₀`
(`HilbertComplex2.convergence_W`), without a rate.
See [QuennevilleBelair2015, §4.6, discussion after Thm 4.14]. -/
theorem convergence [∀ h, FiniteDimensional ℝ (S h).toV] (hd : C.DensityHyp l S) {T : ℝ}
    {ξ ξ' : ℝ → C.VSp} (hξ : C.IsWeakSol T ξ ξ') {ξh ξh' : ι → ℝ → C.VSp}
    (hξh : ∀ h, C.IsDiscreteSol (S h) T (ξh h) (ξh' h))
    (h0 : Tendsto (fun h => ‖C.toW (C.ellProj (S h) (ξ 0) - ξh h 0)‖) l (𝓝 0)) :
    TendstoUniformlyOn (fun h t => C.toW (ξh h t)) (fun t => C.toW (ξ t)) l (Icc 0 T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  rcases lt_or_ge T 0 with hT | hT
  · exact Filter.Eventually.of_forall fun h t ht => absurd (ht.1.trans ht.2) (not_le.2 hT)
  set c : ℝ := 2 + (1 + T) ^ 2 with hc
  have hcpos : 0 < c := by positivity
  set δ : ℝ := η / (2 * c) with hδ
  have hδpos : 0 < δ := by positivity
  have hK1 : IsCompact (ξ '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hξ.1
  have hK2 : IsCompact (ξ' '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hξ.2.1
  have h0' : ∀ᶠ h in l, ‖C.toW (C.ellProj (S h) (ξ 0) - ξh h 0)‖ < δ := by
    have := (h0.eventually (gt_mem_nhds hδpos))
    exact this
  filter_upwards [h0', hd.ellProj_tendsto hK1 hδpos, hd.ellProj_tendsto hK2 hδpos]
    with h hε0 hP1 hP2 t ht
  have hT0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hb := C.semidiscrete_error_bound (S h) hξ (hξh h) t ht
  have e1 : ‖C.projErr (S h) (ξ t)‖ ≤ δ :=
    (C.norm_projErr_le _ _).trans (hP1 _ (Set.mem_image_of_mem _ ht))
  have e0 : ‖C.projErr (S h) (ξ 0)‖ ≤ δ :=
    (C.norm_projErr_le _ _).trans (hP1 _ (Set.mem_image_of_mem _ hT0))
  have eI : ∫ s in (0:ℝ)..T, ‖C.projErr (S h) (ξ' s)‖ ≤ T * δ := by
    have := intervalIntegral.integral_mono_on hT
      (((C.projErr (S h)).continuous.comp_continuousOn hξ.2.1).norm.intervalIntegrable_of_Icc
        (μ := MeasureTheory.volume) hT)
      intervalIntegrable_const (fun s hs =>
        (C.norm_projErr_le _ _).trans (hP2 _ (Set.mem_image_of_mem _ hs)))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, Function.comp_apply]
      using this
  have h1T : 0 ≤ 1 + T := by linarith
  have key : (1 + T) * (‖C.projErr (S h) (ξ 0)‖ + ∫ s in (0:ℝ)..T, ‖C.projErr (S h) (ξ' s)‖)
      ≤ (1 + T) * (δ + T * δ) := by gcongr
  rw [dist_eq_norm, ← map_sub]
  have hfin : δ + δ + (1 + T) * (δ + T * δ) = η / 2 := by
    rw [hδ, hc]; field_simp; ring
  linarith

/-- Convergence with the thesis's initial data `ξₕ(0) = Πₕξ(0)`. -/
theorem convergence_of_initProj [∀ h, FiniteDimensional ℝ (S h).toV] (hd : C.DensityHyp l S)
    {T : ℝ} {ξ ξ' : ℝ → C.VSp} (hξ : C.IsWeakSol T ξ ξ') {ξh ξh' : ι → ℝ → C.VSp}
    (hξh : ∀ h, C.IsDiscreteSol (S h) T (ξh h) (ξh' h))
    (hinit : ∀ h, ξh h 0 = C.ellProj (S h) (ξ 0)) :
    TendstoUniformlyOn (fun h t => C.toW (ξh h t)) (fun t => C.toW (ξ t)) l (Icc 0 T) :=
  convergence hd hξ hξh (by simp [hinit, tendsto_const_nhds])

/-- Convergence, existence form: the discrete solutions with `ξₕ(0) = Πₕξ(0)` exist (and are
unique on `[0,T]` by `discrete_solution_unique`), and they converge to `ξ` uniformly on `[0,T]`
in `W`. -/
theorem convergence_exists [∀ h, FiniteDimensional ℝ (S h).toV] (hd : C.DensityHyp l S)
    {T : ℝ} {ξ ξ' : ℝ → C.VSp} (hξ : C.IsWeakSol T ξ ξ') :
    ∃ ξh ξh' : ι → ℝ → C.VSp, (∀ h, C.IsDiscreteSol (S h) T (ξh h) (ξh' h)) ∧
      (∀ h, ξh h 0 = C.ellProj (S h) (ξ 0)) ∧
      TendstoUniformlyOn (fun h t => C.toW (ξh h t)) (fun t => C.toW (ξ t)) l (Icc 0 T) := by
  choose ξh ξh' hinit hm hdv _ heq using fun h =>
    C.discrete_solution_exists (S h) (C.ellProj_mem (S h) (ξ 0))
  have hsol : ∀ h, C.IsDiscreteSol (S h) T (ξh h) (ξh' h) := fun h =>
    C.isDiscreteSol_of_global (S h) (hm h) (hdv h) (heq h)
  exact ⟨ξh, ξh', hsol, hinit, convergence_of_initProj hd hξ hsol hinit⟩

end Convergence

/-! ## Non-vacuity of the hypotheses -/

/-- The full subcomplex `Vₕ = V`. -/
def Sub.top : C.Sub where
  V0h := ⊤
  V1h := ⊤
  V2h := ⊤
  d0_mem _ _ := trivial
  d1_mem _ _ := trivial

theorem Sub.top_toV : (Sub.top C).toV = ⊤ := by
  ext ξ; exact ⟨fun _ => trivial, fun _ => ⟨trivial, trivial, trivial⟩⟩

/-- The constant family `Vₕ = V` satisfies the density hypothesis (exact approximation). -/
theorem dense_top {ι : Type*} (l : Filter ι) : C.DensityHyp l fun _ => Sub.top C :=
  ⟨fun σ δ hδ => Filter.Eventually.of_forall fun _ => ⟨σ, trivial, by simpa using hδ⟩,
    fun u δ hδ => Filter.Eventually.of_forall fun _ => ⟨u, trivial, by simpa using hδ⟩,
    fun ρ δ hδ => Filter.Eventually.of_forall fun _ => ⟨ρ, trivial, by simpa using hδ⟩⟩

/-- Non-vacuity of `IsWeakSol`: when `X⁰, X¹, X²` are finite-dimensional, every initial datum
`ξ₀ ∈ V` has a weak solution with the regularity `C¹([0,T]; V)` of Thm 4.14 (the discrete
solution for `Vₕ = V`). -/
theorem exists_isWeakSol [FiniteDimensional ℝ X0] [FiniteDimensional ℝ X1]
    [FiniteDimensional ℝ X2] (T : ℝ) (ξ₀ : C.VSp) :
    ∃ ξ ξ' : ℝ → C.VSp, ξ 0 = ξ₀ ∧ C.IsWeakSol T ξ ξ' := by
  have hfin : FiniteDimensional ℝ (Sub.top C).toV := inferInstance
  obtain ⟨ξ, ξ', h0, -, hd, hc, heq⟩ :=
    C.discrete_solution_exists (Sub.top C) (ξ₀ := ξ₀) (by rw [Sub.top_toV]; trivial)
  exact ⟨ξ, ξ', h0, fun t _ => (hd t).continuousAt.continuousWithinAt, hc.continuousOn,
    fun t _ => (hd t).hasDerivWithinAt,
    fun t _ ψ => heq t ψ (by rw [Sub.top_toV]; trivial)⟩

end AlgSegment

end Feec.Legacy
