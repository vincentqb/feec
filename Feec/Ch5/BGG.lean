module

public import Feec.Ch4.Galerkin
public import Feec.Foundation.BGG
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# The abstract BGG framework (thesis §5.1): Props 5.1 and 5.2

Two exact closed Hilbert complexes `V⁰ → V¹ → W²` and `Ṽ⁰ → Ṽ¹ → W̃²`, linked by
`S₀ : Ṽ⁰ → V¹`, `S₁ : Ṽ¹ → W²` with `d¹S₀ = -S₁d̃⁰`, give the complex with weak symmetries (5.1)
`Γ̄ ⊃ Γ --(0 d)--> W̃¹ ⊃ Ṽ¹ --(S, d)--> W² × W̃²`, `Γ = {(σ, φ) | dσ = Sφ}`.

* Algebra (`BGGData`): `range_D0` (`R(0 d) = R(d̃⁰) ∩ N(S₁)`), `exact_mid` (exactness at `Ṽ¹`,
  **missing in the thesis**), `D0_injective`, `range_D1`, `D1_surjective`.
* Analytic model `BGGHilb`: domains carry their graph inner products; the analytic hypotheses
  (closed ranges, exactness, regularity `d¹V¹ ⊆ d¹S₀Ṽ⁰`) are the explicit `BGGHilb.Hyps`.
* **Prop 5.1** (`BGGHilb.prop_5_1`): `(0 d)` (as a `LinearPMap` `W⁰ → W̃¹` with dense domain in
  the concrete `Γ̄ ⊂ W⁰`) and `(S, d)` are closed, densely defined, with closed ranges, and
  compose to zero; the complex is exact at `Γ̄` and `W̃¹`. Supporting results: `isClosed_Γ`,
  `isClosed_range_prod` (closed range of `(S, d)`, open mapping), `poincare_Γ`, `poincare_T`,
  `hodge_Vt1` (Hodge decomposition of `Ṽ¹` without harmonic part).
* Multiplier space `W̌¹` (`Wcheck`): the closure of `R(B*)`, `B(τ,ψ) = dτ - Sψ`;
  `tripleNorm_spec` (`|||λ||| = ‖B*λ‖` is the thesis' sup), `tripleNorm_definite` (norm under the
  corrected density hypothesis), `jW_spec` (`W̌¹` is the completion of `(W¹, |||·|||)`).
* **Prop 5.2** (`prop_5_2_wellPosed`, `prop_5_2`): (5.3) is well posed on
  `V⁰ × Ṽ⁰ × Ṽ¹ × W̌¹`, via Brezzi (M7) with `infSup_b`, `infSup_a` (ε-test function restored)
  and the transposed condition `nondeg_a` (**missing in the thesis**).
* (5.2) ↔ (5.3): `reduced_of_saddle`, `reduced_existsUnique` ((5.2) is well posed),
  `existsUnique_multiplier`, `saddle_iff_reduced`, `saddle_of_saddle53` (consistency with the
  thesis' `λ ∈ W¹`).
* Non-vacuity: `exampleBGG_hyps`.

Corrections to the thesis (see `docs/BLUEPRINT.md` §4): typos `Z̃ = N(d⁰)` (should be `N(d̃¹)`)
and `W¹` (should be `W²`) in the proof of Prop 5.1; `φ` undefined on `Γ̄` (here `Γ̄ ⊂ W⁰` and
`Γ` is closed in `V⁰ × Ṽ⁰`); exactness of (5.1) at `Ṽ¹` proved; Prop 5.2: `λ ∈ W̌¹` not `W¹`,
transposed Brezzi condition added, the ε's restored, the density hypothesis is only needed to
embed `W¹` into `W̌¹`, and its exact form is density of `d⁰V⁰ + S₀Ṽ⁰`; the ℓ² product norm
replaces the sum norm (equivalent). Model choices: `S₀, S₁` are only assumed bounded in graph
norms (implied by the thesis' boundedness on `W̃⁰, W̃¹`); `W² × W̃²` carries the sup norm (only
topological statements are made on it).

## References

* [QuennevilleBelair2015], §5.1 (Props 5.1, 5.2, (5.1)–(5.3)); §4.2 (Hilbert complexes, Thms 4.1,
  4.2), §4.5 (Brezzi's theorem, Thm 4.11)
* [ArnoldHu2021] (the general BGG construction of complexes from complexes)
* [BruningLesch1992], [AFW2010], [Arnold2018] (closed Hilbert complexes, Hodge decomposition,
  Poincaré inequality, mixed Hodge Laplacian)
* [AFW2007] (weakly imposed symmetry)
* [DuranLiberman1992], [Falk2008] (multiplier formulation of Reissner–Mindlin plates; the norm
  `|||·|||` mirrors the limiting case `t = 0`)
* [Brezzi1974], [BoffiBrezziFortin2013] (saddle point problems)
-/

open scoped RealInnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Ch5.BGG

/-! ## Algebraic core of the complex (5.1) -/

section Algebra

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [AddCommGroup V0] [Module ℝ V0] [AddCommGroup V1] [Module ℝ V1]
  [AddCommGroup W2] [Module ℝ W2] [AddCommGroup Vt0] [Module ℝ Vt0]
  [AddCommGroup Vt1] [Module ℝ Vt1] [AddCommGroup Wt2] [Module ℝ Wt2]
  (D : BGGData V0 V1 W2 Vt0 Vt1 Wt2)

@[simp] lemma D0_apply (x : D.Γ) : D.D0 x = D.dt0 (x : V0 × Vt0).2 := rfl
@[simp] lemma D1_apply (u : Vt1) : D.D1 u = (D.S1 u, D.dt1 u) := rfl

/-- Thesis Prop 5.1 proof (last paragraph): `S₁ d̃ φ = 0` for `(σ, φ) ∈ Γ`. -/
lemma S1_dt0_of_mem {x : V0 × Vt0} (hx : x ∈ D.Γ) : D.S1 (D.dt0 x.2) = 0 := by
  have h := D.d1_d0 x.1
  rw [D.mem_Γ.1 hx, D.anticomm] at h
  simpa using h

/-- **Thesis Prop 5.1** (closed range of `(0 d)`, algebraic part): `R(0 d) = R(d̃⁰) ∩ N(S₁)`.
Thesis gap: the thesis proves closedness of `R(0 d)` by a sequential argument; this one-line
characterisation (using exactness of the top complex at `V¹`) is missing.

See [QuennevilleBelair2015, Prop 5.1]. -/
theorem range_D0 (hT : D.ExactTop) :
    LinearMap.range D.D0 = LinearMap.range D.dt0 ⊓ LinearMap.ker D.S1 := by
  ext y
  simp only [LinearMap.mem_range, Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨_, rfl⟩, S1_dt0_of_mem D x.2⟩
  · rintro ⟨⟨φ, rfl⟩, hS⟩
    have : D.S0 φ ∈ LinearMap.ker D.d1 := by simp [D.anticomm, hS]
    rw [hT] at this
    obtain ⟨σ, hσ⟩ := this
    exact ⟨⟨(σ, φ), D.mem_Γ.2 hσ⟩, rfl⟩

/-- **Exactness of (5.1) at `Ṽ¹`** (missing in the thesis): `N(S₁) ∩ N(d̃¹) = R(0 d)`.

Thesis gap: never stated or proved, yet needed for (5.2) to be well posed without harmonic
term, for the Hodge decomposition `u = d̃χ + w` in the proof of Prop 5.2, and for the transposed
Brezzi condition. It follows from exactness of the bottom complex at `Ṽ¹` and of the top
complex at `V¹`.

Cf. [QuennevilleBelair2015, §5.1, (5.1)]; for exactness of BGG-type complexes in general, cf.
[ArnoldHu2021]. -/
theorem exact_mid (hT : D.ExactTop) (hB : D.ExactBot) :
    LinearMap.ker D.D1 = LinearMap.range D.D0 := by
  rw [range_D0 D hT, ← hB]
  ext u
  simp [and_comm]

/-- Exactness of (5.1) at `Γ`: `(0 d)` is injective when `d⁰` and `d̃⁰` are. -/
theorem D0_injective (hd0 : Function.Injective D.d0) (hdt0 : Function.Injective D.dt0) :
    Function.Injective D.D0 := by
  rintro ⟨⟨σ, φ⟩, hx⟩ ⟨⟨τ, ψ⟩, hy⟩ e
  have hφ : φ = ψ := hdt0 e
  subst hφ
  have h1 := D.mem_Γ.1 hx
  have h2 := D.mem_Γ.1 hy
  have : σ = τ := hd0 (h1.trans h2.symm)
  subst this
  rfl

/-- Thesis Prop 5.1 proof (third paragraph), algebraic part: under the regularity hypothesis
`d¹V¹ ⊆ d¹S₀Ṽ⁰`, `R(S, d) = {(ρ, μ) | ∃ w, d̃¹w = μ, ρ - S₁w ∈ R(d¹)}`. -/
theorem range_D1 (hreg : LinearMap.range D.d1 ≤ LinearMap.range (D.d1 ∘ₗ D.S0)) :
    (LinearMap.range D.D1 : Set (W2 × Wt2)) =
      {p | ∃ w, D.dt1 w = p.2 ∧ p.1 - D.S1 w ∈ LinearMap.range D.d1} := by
  ext ⟨ρ, μ⟩
  simp only [SetLike.mem_coe, LinearMap.mem_range, Set.mem_ofPred_eq, D1_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨u, rfl, rfl⟩
    exact ⟨u, rfl, 0, by simp⟩
  · rintro ⟨w, hw, hρ⟩
    obtain ⟨φ, hφ⟩ := hreg hρ
    simp only [LinearMap.comp_apply, D.anticomm] at hφ
    refine ⟨w - D.dt0 φ, ?_, ?_⟩
    · rw [map_sub, sub_eq_add_neg, hφ]; abel
    · simp [D.dt1_dt0, hw]

/-- Exactness of (5.1) at `W² × W̃²`: if moreover `d¹` and `d̃¹` are onto, so is `(S, d)`.
(The thesis' diagrams have no trailing `0`; this records what "exact" would add.) -/
theorem D1_surjective (hreg : LinearMap.range D.d1 ≤ LinearMap.range (D.d1 ∘ₗ D.S0))
    (h1 : Function.Surjective D.d1) (h2 : Function.Surjective D.dt1) :
    Function.Surjective D.D1 := by
  intro p
  have : p ∈ (LinearMap.range D.D1 : Set (W2 × Wt2)) := by
    rw [range_D1 D hreg]
    obtain ⟨w, hw⟩ := h2 p.2
    obtain ⟨y, hy⟩ := h1 (p.1 - D.S1 w)
    exact ⟨w, hw, y, hy⟩
  exact this

end Algebra

/-- Thesis Prop 5.1, third paragraph (closed range of `(S, d)`), for bounded operators: under
exactness of the bottom complex at `Ṽ¹`, closed ranges of `d¹`, `d̃¹` and the regularity
`d¹V¹ ⊆ d¹S₀Ṽ⁰`, the range of `u ↦ (S₁u, d̃¹u)` is closed.
Thesis gap: the thesis' proof goes through a Hodge decomposition of `Ṽ¹`; here only the open
mapping theorem on `R(d̃¹)` is used (typos `Z̃ = N(d⁰)` and "`W¹`" for `W²` corrected).

See [QuennevilleBelair2015, Prop 5.1 (proof)]. -/
theorem isClosed_range_prod {V1 W2 Vt0 Vt1 Wt2 : Type*}
    [NormedAddCommGroup V1] [NormedSpace ℝ V1]
    [NormedAddCommGroup W2] [NormedSpace ℝ W2]
    [NormedAddCommGroup Vt0] [NormedSpace ℝ Vt0]
    [NormedAddCommGroup Vt1] [NormedSpace ℝ Vt1] [CompleteSpace Vt1]
    [NormedAddCommGroup Wt2] [NormedSpace ℝ Wt2] [CompleteSpace Wt2]
    (d1 : V1 →L[ℝ] W2) (dt0 : Vt0 →L[ℝ] Vt1) (dt1 : Vt1 →L[ℝ] Wt2)
    (S0 : Vt0 →L[ℝ] V1) (S1 : Vt1 →L[ℝ] W2)
    (anticomm : ∀ φ, d1 (S0 φ) = -S1 (dt0 φ)) (hdd : ∀ φ, dt1 (dt0 φ) = 0)
    (exact_bot : ∀ z, dt1 z = 0 → ∃ φ, dt0 φ = z)
    (hd1 : IsClosed (Set.range d1)) (hdt1 : IsClosed (Set.range dt1))
    (hreg : Set.range d1 ⊆ Set.range (d1 ∘ S0)) :
    IsClosed (Set.range (S1.prod dt1)) := by
  let R : Submodule ℝ Wt2 := LinearMap.range (dt1 : Vt1 →ₗ[ℝ] Wt2)
  have : CompleteSpace R := by
    have : IsClosed (R : Set Wt2) := hdt1
    exact this.completeSpace_coe
  let g : Vt1 →L[ℝ] R := (dt1 : Vt1 →L[ℝ] Wt2).codRestrict R (fun x => ⟨x, rfl⟩)
  have gsurj : Function.Surjective g := by
    rintro ⟨_, ⟨x, rfl⟩⟩; exact ⟨x, rfl⟩
  obtain ⟨C, -, hC⟩ := g.exists_preimage_norm_le gsurj
  have hker : ∀ z, dt1 z = 0 → S1 z ∈ Set.range d1 := by
    intro z hz
    obtain ⟨φ, rfl⟩ := exact_bot z hz
    exact ⟨-(S0 φ), by simp [anticomm]⟩
  refine isClosed_of_closure_subset fun p hp => ?_
  obtain ⟨q, hq, hqp⟩ := mem_closure_iff_seq_limit.1 hp
  choose u hu using hq
  have hμ : Tendsto (fun n => (q n).2) atTop (𝓝 p.2) := (continuous_snd.tendsto _).comp hqp
  have hρ : Tendsto (fun n => (q n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto _).comp hqp
  obtain ⟨w, hw⟩ : p.2 ∈ Set.range dt1 :=
    hdt1.mem_of_tendsto hμ (Eventually.of_forall fun n => ⟨u n, by simp [← hu n]⟩)
  have hmem : ∀ n, (q n).2 - p.2 ∈ R := fun n => ⟨u n - w, by simp [← hu n, hw]⟩
  choose w' hw' hw'n using fun n => hC ⟨(q n).2 - p.2, hmem n⟩
  have hw'0 : Tendsto w' atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => hw'n n) ?_
    have : Tendsto (fun n => ‖(q n).2 - p.2‖) atTop (𝓝 0) := by
      simpa using (hμ.sub_const p.2).norm
    simpa using this.const_mul C
  have hin : ∀ n, (q n).1 - S1 w - S1 (w' n) ∈ Set.range d1 := by
    intro n
    have h1 : dt1 (u n - w - w' n) = 0 := by
      have : dt1 (w' n) = (q n).2 - p.2 := congrArg Subtype.val (hw' n)
      rw [map_sub, map_sub, this, hw, ← hu n]; simp
    obtain ⟨y, hy⟩ := hker _ h1
    refine ⟨y, ?_⟩
    rw [hy, map_sub, map_sub, ← hu n]; simp
  have hlim : Tendsto (fun n => (q n).1 - S1 w - S1 (w' n)) atTop (𝓝 (p.1 - S1 w)) := by
    have := (hρ.sub_const (S1 w)).sub ((S1.continuous.tendsto 0).comp hw'0)
    simpa using this
  obtain ⟨lam, hlam⟩ := hreg (hd1.mem_of_tendsto hlim (Eventually.of_forall hin))
  refine ⟨w - dt0 lam, ?_⟩
  simp only [Function.comp_apply, anticomm] at hlam
  ext
  · show S1 (w - dt0 lam) = p.1
    rw [map_sub, sub_eq_add_neg, hlam]; abel
  · simp [hdd, hw]

/-! ## Product spaces for the saddle point problem (5.3) -/

section ProdSpaces

variable {V0 Vt0 Vt1 : Type*} [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0] [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]


/-- `P = V⁰ × Ṽ⁰` with the ℓ² product norm (correction: the thesis' sum norm
`‖τ‖_V + ‖ψ‖_V` gives an equivalent, non-Hilbertian norm). -/
abbrev Psp (V0 Vt0 : Type*) := WithLp 2 (V0 × Vt0)

/-- The trial/test space `X = V⁰ × Ṽ⁰ × Ṽ¹` of (5.3), with the ℓ² product of graph norms. -/
abbrev Xsp (V0 Vt0 Vt1 : Type*) := WithLp 2 (Psp V0 Vt0 × Vt1)

variable (V0 Vt0 Vt1) in
/-- coordinate projections of `X` -/
def pP : Xsp V0 Vt0 Vt1 →L[ℝ] Psp V0 Vt0 := WithLp.fstL 2 ℝ (Psp V0 Vt0) Vt1
variable (V0 Vt0 Vt1) in
def pu : Xsp V0 Vt0 Vt1 →L[ℝ] Vt1 := WithLp.sndL 2 ℝ (Psp V0 Vt0) Vt1
variable (V0 Vt0 Vt1) in
def pσ : Xsp V0 Vt0 Vt1 →L[ℝ] V0 := WithLp.fstL 2 ℝ V0 Vt0 ∘L pP V0 Vt0 Vt1
variable (V0 Vt0 Vt1) in
def pφ : Xsp V0 Vt0 Vt1 →L[ℝ] Vt0 := WithLp.sndL 2 ℝ V0 Vt0 ∘L pP V0 Vt0 Vt1

/-- `(σ, φ, u) ∈ X` -/
def mkX (σ : V0) (φ : Vt0) (u : Vt1) : Xsp V0 Vt0 Vt1 := WithLp.toLp 2 (WithLp.toLp 2 (σ, φ), u)

@[simp] lemma pσ_mkX (σ : V0) (φ : Vt0) (u : Vt1) : pσ V0 Vt0 Vt1 (mkX σ φ u) = σ := rfl
@[simp] lemma pφ_mkX (σ : V0) (φ : Vt0) (u : Vt1) : pφ V0 Vt0 Vt1 (mkX σ φ u) = φ := rfl
@[simp] lemma pu_mkX (σ : V0) (φ : Vt0) (u : Vt1) : pu V0 Vt0 Vt1 (mkX σ φ u) = u := rfl

lemma mkX_eta (x : Xsp V0 Vt0 Vt1) :
    mkX (pσ V0 Vt0 Vt1 x) (pφ V0 Vt0 Vt1 x) (pu V0 Vt0 Vt1 x) = x := rfl

lemma pP_apply (x : Xsp V0 Vt0 Vt1) :
    pP V0 Vt0 Vt1 x = WithLp.toLp 2 (pσ V0 Vt0 Vt1 x, pφ V0 Vt0 Vt1 x) := rfl

lemma norm_sq_X (x : Xsp V0 Vt0 Vt1) :
    ‖x‖ ^ 2 = ‖pσ V0 Vt0 Vt1 x‖ ^ 2 + ‖pφ V0 Vt0 Vt1 x‖ ^ 2 + ‖pu V0 Vt0 Vt1 x‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]; rfl

lemma inner_X (x y : Xsp V0 Vt0 Vt1) :
    ⟪x, y⟫ = ⟪pσ V0 Vt0 Vt1 x, pσ V0 Vt0 Vt1 y⟫ + ⟪pφ V0 Vt0 Vt1 x, pφ V0 Vt0 Vt1 y⟫ +
      ⟪pu V0 Vt0 Vt1 x, pu V0 Vt0 Vt1 y⟫ := rfl

/-- bounded bilinear form `(x, y) ↦ ⟪f x, g y⟫` -/
def ip {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : Xsp V0 Vt0 Vt1 →L[ℝ] E) : Xsp V0 Vt0 Vt1 →L[ℝ] Xsp V0 Vt0 Vt1 →L[ℝ] ℝ :=
  (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp f g

@[simp] lemma ip_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : Xsp V0 Vt0 Vt1 →L[ℝ] E) (x y : Xsp V0 Vt0 Vt1) : ip f g x y = ⟪f x, g y⟫ := rfl

end ProdSpaces

/-! ## The analytic setting of §5.1 (bundled-domain model) -/

section Analytic

/-- **Standing hypotheses of thesis §5.1**, in the bundled-domain model: each domain
`V⁰, V¹, Ṽ⁰, Ṽ¹` is a Hilbert space carrying its *graph* inner product, with a continuous
injective, dense inclusion `ι` into its `W`-space; the operators `d` are bounded on the domains
(so closedness of the unbounded operators is built in); `S₀ Ṽ⁰ ⊂ V¹`, anticommutation
`d¹S₀ = -S₁d̃⁰`. `W²`, `W̃²` are the end spaces.

The thesis assumes `S₀ : W̃⁰ → W¹`, `S₁ : W̃¹ → W²` bounded; only the (weaker, and implied)
boundedness `S₀ : Ṽ⁰ → V¹`, `S₁ : Ṽ¹ → W²` in graph norms is used. Closed ranges, exactness,
regularity and injectivity of `S₀` are *not* fields: they are the explicit hypotheses
`BGGHilb.Hyps` (and `Function.Injective D.S0`) of the theorems that use them.

See [QuennevilleBelair2015, §5.1]; Hilbert complexes and graph-norm domains as in
[BruningLesch1992], [AFW2010], [Arnold2018]. -/
structure BGGHilb (W0 W1 Wt0 Wt1 W2 Wt2 V0 V1 Vt0 Vt1 : Type*)
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0] [CompleteSpace Wt0]
    [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [CompleteSpace Wt1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2] [CompleteSpace Wt2]
    [NormedAddCommGroup V0] [InnerProductSpace ℝ V0] [CompleteSpace V0]
    [NormedAddCommGroup V1] [InnerProductSpace ℝ V1] [CompleteSpace V1]
    [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0] [CompleteSpace Vt0]
    [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1] [CompleteSpace Vt1] where
  ι0 : V0 →L[ℝ] W0
  ι1 : V1 →L[ℝ] W1
  ιt0 : Vt0 →L[ℝ] Wt0
  ιt1 : Vt1 →L[ℝ] Wt1
  ι0_injective : Function.Injective ι0
  ι1_injective : Function.Injective ι1
  ιt0_injective : Function.Injective ιt0
  ιt1_injective : Function.Injective ιt1
  /-- densely defined operators -/
  dense0 : DenseRange ι0
  dense1 : DenseRange ι1
  denset0 : DenseRange ιt0
  denset1 : DenseRange ιt1
  d0 : V0 →L[ℝ] V1
  d1 : V1 →L[ℝ] W2
  dt0 : Vt0 →L[ℝ] Vt1
  dt1 : Vt1 →L[ℝ] Wt2
  S0 : Vt0 →L[ℝ] V1
  S1 : Vt1 →L[ℝ] W2
  /-- graph inner products -/
  graph0 : ∀ u v : V0, ⟪u, v⟫ = ⟪ι0 u, ι0 v⟫ + ⟪ι1 (d0 u), ι1 (d0 v)⟫
  graph1 : ∀ u v : V1, ⟪u, v⟫ = ⟪ι1 u, ι1 v⟫ + ⟪d1 u, d1 v⟫
  grapht0 : ∀ u v : Vt0, ⟪u, v⟫ = ⟪ιt0 u, ιt0 v⟫ + ⟪ιt1 (dt0 u), ιt1 (dt0 v)⟫
  grapht1 : ∀ u v : Vt1, ⟪u, v⟫ = ⟪ιt1 u, ιt1 v⟫ + ⟪dt1 u, dt1 v⟫
  d1_d0 : ∀ σ, d1 (d0 σ) = 0
  dt1_dt0 : ∀ φ, dt1 (dt0 φ) = 0
  anticomm : ∀ φ, d1 (S0 φ) = -S1 (dt0 φ)

namespace BGGHilb

variable {W0 W1 Wt0 Wt1 W2 Wt2 V0 V1 Vt0 Vt1 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0] [CompleteSpace Wt0]
    [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [CompleteSpace Wt1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2] [CompleteSpace Wt2]
    [NormedAddCommGroup V0] [InnerProductSpace ℝ V0] [CompleteSpace V0]
    [NormedAddCommGroup V1] [InnerProductSpace ℝ V1] [CompleteSpace V1]
    [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0] [CompleteSpace Vt0]
    [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1] [CompleteSpace Vt1]
    (D : BGGHilb W0 W1 Wt0 Wt1 W2 Wt2 V0 V1 Vt0 Vt1)

/-- The algebraic BGG data underlying `D`. -/
def toBGGData : BGGData V0 V1 W2 Vt0 Vt1 Wt2 where
  d0 := D.d0
  d1 := D.d1
  dt0 := D.dt0
  dt1 := D.dt1
  S0 := D.S0
  S1 := D.S1
  d1_d0 := D.d1_d0
  dt1_dt0 := D.dt1_dt0
  anticomm := D.anticomm

/-- `Γ = {(σ, φ) ∈ V⁰ × Ṽ⁰ | d σ = S φ}` -/
abbrev Γ : Submodule ℝ (V0 × Vt0) := D.toBGGData.Γ

lemma mem_Γ {x : V0 × Vt0} : x ∈ D.Γ ↔ D.d0 x.1 = D.S0 x.2 := D.toBGGData.mem_Γ

/-- `(S₁, d̃¹) : Ṽ¹ → W² × W̃²` as a bounded operator. -/
def T : Vt1 →L[ℝ] W2 × Wt2 := D.S1.prod D.dt1

@[simp] lemma T_apply (u : Vt1) : D.T u = (D.S1 u, D.dt1 u) := rfl

/-- `N(S₁) ∩ N(d̃¹)` -/
abbrev Z1 : Submodule ℝ Vt1 := D.T.ker

lemma mem_Z1 {u : Vt1} : u ∈ D.Z1 ↔ D.S1 u = 0 ∧ D.dt1 u = 0 := by
  simp [Z1, LinearMap.mem_ker, Prod.ext_iff]

/-- The explicit analytic hypotheses (H1)–(H3), (H6) of §5.1 (corrected form, see
`docs/audit.json`): `d⁰, d̃⁰` injective with closed range (exactness at `V⁰`, `Ṽ⁰`), exactness at
`V¹`, `Ṽ¹`, closed ranges of `d¹, d̃¹`, and the regularity hypothesis, of which only the
direction `d¹V¹ ⊆ d¹S₀Ṽ⁰` has content. Ranges are closed in the `W`-spaces, as in the thesis.

See [QuennevilleBelair2015, §5.1, hypotheses of Prop 5.1]. -/
structure Hyps : Prop where
  d0_injective : Function.Injective D.d0
  dt0_injective : Function.Injective D.dt0
  d0_closed : IsClosed (Set.range (D.ι1 ∘L D.d0))
  dt0_closed : IsClosed (Set.range (D.ιt1 ∘L D.dt0))
  exact1 : D.toBGGData.ExactTop
  exactt1 : D.toBGGData.ExactBot
  d1_closed : IsClosed (Set.range D.d1)
  dt1_closed : IsClosed (Set.range D.dt1)
  reg : Set.range D.d1 ⊆ Set.range (D.d1 ∘ D.S0)

lemma norm_ι0_le (σ : V0) : ‖D.ι0 σ‖ ≤ ‖σ‖ := by
  have h := D.graph0 σ σ
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (D.ι0 σ), norm_nonneg σ, sq_nonneg ‖D.ι1 (D.d0 σ)‖]

lemma norm_ιt1_le (u : Vt1) : ‖D.ιt1 u‖ ≤ ‖u‖ := by
  have h := D.grapht1 u u
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (D.ιt1 u), norm_nonneg u, sq_nonneg ‖D.dt1 u‖]

lemma norm_sq_Vt1 (u : Vt1) : ‖u‖ ^ 2 = ‖D.ιt1 u‖ ^ 2 + ‖D.dt1 u‖ ^ 2 := by
  have h := D.grapht1 u u
  simpa only [real_inner_self_eq_norm_sq] using h

lemma norm_sq_V0 (σ : V0) : ‖σ‖ ^ 2 = ‖D.ι0 σ‖ ^ 2 + ‖D.ι1 (D.d0 σ)‖ ^ 2 := by
  have h := D.graph0 σ σ
  simpa only [real_inner_self_eq_norm_sq] using h

/-- Poincaré inequality from injectivity plus closed range (open mapping theorem). -/
lemma exists_poincare {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (f : E →L[ℝ] F)
    (hf : Function.Injective f) (hr : IsClosed (Set.range f)) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖x‖ ≤ C * ‖f x‖ := by
  obtain ⟨K, hK⟩ := f.antilipschitz_of_injective_of_isClosed_range hf hr
  exact ⟨K, K.2, fun x => hK.le_mul_norm (map_zero f) x⟩

/-- `Γ` is closed in `V⁰ × Ṽ⁰` (thesis Prop 5.1, corrected: the thesis' `(σ, φ) ∈ Γ̄` is
meaningless for limit points of the completion; closedness of `Γ` is the usable statement).

See [QuennevilleBelair2015, Prop 5.1 (proof)]. -/
theorem isClosed_Γ : IsClosed (D.Γ : Set (V0 × Vt0)) := by
  have : (D.Γ : Set (V0 × Vt0)) = {x | D.d0 x.1 = D.S0 x.2} := by
    ext x; exact D.mem_Γ
  rw [this]
  exact isClosed_eq (D.d0.continuous.comp continuous_fst) (D.S0.continuous.comp continuous_snd)

instance : CompleteSpace D.Γ := D.isClosed_Γ.completeSpace_coe

/-- **Poincaré inequality for (5.1) on `Γ`** (thesis, after Prop 5.1): for `(σ, φ) ∈ Γ`,
`‖σ‖_{V⁰} ≤ C ‖d̃φ‖` and `‖φ‖_{Ṽ⁰} ≤ C ‖d̃φ‖`.
Thesis gap: the thesis derives `‖σ‖ ≤ C_p‖dφ‖` from "the closed Hilbert complex", which only
controls the part orthogonal to the kernel; the direct proof chains the Poincaré inequalities of
`d⁰`, `d̃⁰` (injective, closed range) with `‖S₀‖`. The bound here is in the stronger `V`-norms.

See [QuennevilleBelair2015, §5.1, after Prop 5.1]; cf. the Poincaré inequality for closed
Hilbert complexes [QuennevilleBelair2015, Thm 4.2], [AFW2010], [Arnold2018]. -/
theorem poincare_Γ (h : D.Hyps) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ D.Γ, ‖x.1‖ ≤ C * ‖D.ιt1 (D.dt0 x.2)‖ ∧
      ‖x.2‖ ≤ C * ‖D.ιt1 (D.dt0 x.2)‖ := by
  obtain ⟨K, hK0, hK⟩ := exists_poincare (D.ι1 ∘L D.d0)
    (D.ι1_injective.comp h.d0_injective) h.d0_closed
  obtain ⟨Kt, hKt0, hKt⟩ := exists_poincare (D.ιt1 ∘L D.dt0)
    (D.ιt1_injective.comp h.dt0_injective) h.dt0_closed
  refine ⟨max Kt (K * ‖D.ι1 ∘L D.S0‖ * Kt), le_max_of_le_left hKt0, fun x hx => ?_⟩
  have hφ := hKt x.2
  simp only [ContinuousLinearMap.comp_apply] at hφ
  have hσ := hK x.1
  simp only [ContinuousLinearMap.comp_apply, D.mem_Γ.1 hx] at hσ
  have hS : ‖D.ι1 (D.S0 x.2)‖ ≤ ‖D.ι1 ∘L D.S0‖ * ‖x.2‖ := (D.ι1 ∘L D.S0).le_opNorm x.2
  have hn := norm_nonneg (D.ιt1 (D.dt0 x.2))
  constructor
  · calc ‖x.1‖ ≤ K * ‖D.ι1 (D.S0 x.2)‖ := hσ
      _ ≤ K * (‖D.ι1 ∘L D.S0‖ * ‖x.2‖) := by gcongr
      _ ≤ K * (‖D.ι1 ∘L D.S0‖ * (Kt * ‖D.ιt1 (D.dt0 x.2)‖)) := by gcongr
      _ = K * ‖D.ι1 ∘L D.S0‖ * Kt * ‖D.ιt1 (D.dt0 x.2)‖ := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · exact hφ.trans (by gcongr; exact le_max_left _ _)


lemma exactt1' (h : D.Hyps) (z : Vt1) (hz : D.dt1 z = 0) : ∃ φ, D.dt0 φ = z := by
  have : z ∈ LinearMap.ker D.toBGGData.dt1 := hz
  rw [h.exactt1] at this
  exact this

/-- **Thesis Prop 5.1** (closed range of `(S, d)`).

See [QuennevilleBelair2015, Prop 5.1]. -/
theorem isClosed_range_T (h : D.Hyps) : IsClosed (Set.range D.T) :=
  isClosed_range_prod D.d1 D.dt0 D.dt1 D.S0 D.S1 D.anticomm D.dt1_dt0 (D.exactt1' h)
    h.d1_closed h.dt1_closed h.reg

lemma isClosed_Z1 : IsClosed (D.Z1 : Set Vt1) := D.T.isClosed_ker

instance : CompleteSpace D.Z1 := D.isClosed_Z1.completeSpace_coe

/-- Exactness of (5.1) at `Ṽ¹` (missing in the thesis, cf. `exact_mid`), in the form used
below: `N(S₁) ∩ N(d̃¹) = d̃(π₂ Γ)`.

Cf. [QuennevilleBelair2015, §5.1]. -/
theorem mem_Z1_iff (h : D.Hyps) {u : Vt1} : u ∈ D.Z1 ↔ ∃ x ∈ D.Γ, D.dt0 x.2 = u := by
  have e := exact_mid D.toBGGData h.exact1 h.exactt1
  have h1 : u ∈ D.Z1 ↔ u ∈ LinearMap.ker D.toBGGData.D1 := by
    rw [mem_Z1, LinearMap.mem_ker, D1_apply, Prod.mk_eq_zero]; rfl
  rw [h1, e]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩

lemma dt0_mem_Z1 {x : V0 × Vt0} (hx : x ∈ D.Γ) : D.dt0 x.2 ∈ D.Z1 :=
  D.mem_Z1.2 ⟨S1_dt0_of_mem D.toBGGData hx, D.dt1_dt0 _⟩

/-- **Poincaré inequality for (5.1) at `Ṽ¹`** (thesis, after Prop 5.1):
`‖u‖_{Ṽ¹} ≤ C ‖(S₁u, d̃¹u)‖` for `u ⊥ N(S₁) ∩ N(d̃¹)` (orthogonality in the graph inner product,
which agrees with `W̃¹`-orthogonality against `N(d̃¹)`).

See [QuennevilleBelair2015, §5.1, after Prop 5.1]; cf. the Poincaré inequality for closed
Hilbert complexes [QuennevilleBelair2015, Thm 4.2], [AFW2010], [Arnold2018]. -/
theorem poincare_T (h : D.Hyps) : ∃ C, 0 ≤ C ∧ ∀ w ∈ D.Z1ᗮ, ‖w‖ ≤ C * ‖D.T w‖ := by
  let f : D.Z1ᗮ →L[ℝ] W2 × Wt2 := D.T ∘L D.Z1ᗮ.subtypeL
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun w hw => ?_
    have h1 : (w : Vt1) ∈ D.Z1 := hw
    have : (w : Vt1) ∈ D.Z1 ⊓ D.Z1ᗮ := ⟨h1, w.2⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
    exact Subtype.ext this
  have hr : Set.range f = Set.range D.T := by
    ext p
    constructor
    · rintro ⟨w, rfl⟩; exact ⟨w, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨⟨u - D.Z1.starProjection u, D.Z1.sub_starProjection_mem_orthogonal u⟩, ?_⟩
      have := D.mem_Z1.1 (D.Z1.starProjection_apply_mem u)
      simp [f, this.1, this.2]
  obtain ⟨C, hC0, hC⟩ := exists_poincare f hf (hr ▸ D.isClosed_range_T h)
  exact ⟨C, hC0, fun w hw => hC ⟨w, hw⟩⟩

/-- Hodge decomposition of `Ṽ¹` for the complex (5.1), *without harmonic part* (thesis, proof of
Prop 5.2): `u = d̃χ + w` with `(ρ, χ) ∈ Γ` and `w ⊥ N(S₁) ∩ N(d̃¹)`.
Thesis gap: the absence of a harmonic part is exactness of (5.1) at `Ṽ¹` (`exact_mid`).

See [QuennevilleBelair2015, proof of Prop 5.2]; cf. the Hodge decomposition of closed Hilbert
complexes [QuennevilleBelair2015, Thm 4.1], [BruningLesch1992], [AFW2010], [Arnold2018]. -/
theorem hodge_Vt1 (h : D.Hyps) (u : Vt1) : ∃ x ∈ D.Γ, ∃ w ∈ D.Z1ᗮ, u = D.dt0 x.2 + w := by
  obtain ⟨x, hx, hxu⟩ := (D.mem_Z1_iff h).1 (D.Z1.starProjection_apply_mem u)
  exact ⟨x, hx, _, D.Z1.sub_starProjection_mem_orthogonal u, by rw [hxu]; abel⟩

/-! ### The complex (5.1) as unbounded operators: Prop 5.1 -/

/-- `(σ, φ) ↦ (σ, d̃φ)` (in `W⁰ × W̃¹`), whose image of `Γ` is the graph of `(0 d)`. -/
def LΓ : V0 × Vt0 →L[ℝ] W0 × Wt1 :=
  (D.ι0 ∘L ContinuousLinearMap.fst ℝ V0 Vt0).prod
    ((D.ιt1 ∘L D.dt0) ∘L ContinuousLinearMap.snd ℝ V0 Vt0)

/-- `Γ̄`: the completion of `Γ` in `‖(σ, φ)‖ = ‖σ‖_{W⁰}`, realised as the closure of `π₁Γ` in
`W⁰` (correction: the thesis' abstract completion leaves `φ` undefined on limit points). -/
def Γbar : Submodule ℝ W0 :=
  (D.Γ.map ((D.ι0 : V0 →ₗ[ℝ] W0) ∘ₗ LinearMap.fst ℝ V0 Vt0)).topologicalClosure

/-- The first operator `(0 d) : Γ̄ ⊃ Γ → W̃¹` of (5.1), as an unbounded operator `W⁰ → W̃¹` with
graph `{(σ, d̃φ) | (σ, φ) ∈ Γ}` (its domain lies in, and is dense in, `Γ̄`: `D0op_domain`).
It is a well-defined operator when `S₀` is injective (`D0op_graph`); this is where injectivity
of `S₀` is used, as the thesis says.

See [QuennevilleBelair2015, (5.1)]. -/
def D0op : W0 →ₗ.[ℝ] Wt1 := (D.Γ.map (D.LΓ : V0 × Vt0 →ₗ[ℝ] W0 × Wt1)).toLinearPMap

/-- The second operator `(S, d) : W̃¹ ⊃ Ṽ¹ → W² × W̃²` of (5.1), with graph
`{(u, S₁u, d̃¹u) | u ∈ Ṽ¹}`.

See [QuennevilleBelair2015, (5.1)]. -/
def D1op : Wt1 →ₗ.[ℝ] W2 × Wt2 :=
  (LinearMap.range ((D.ιt1.prod D.T : Vt1 →L[ℝ] Wt1 × (W2 × Wt2)) :
    Vt1 →ₗ[ℝ] Wt1 × (W2 × Wt2))).toLinearPMap

lemma graph0_hg (hS0 : Function.Injective D.S0) :
    ∀ (x : W0 × Wt1) (_ : x ∈ D.Γ.map (D.LΓ : V0 × Vt0 →ₗ[ℝ] W0 × Wt1)), x.1 = 0 → x.2 = 0 := by
  rintro _ ⟨y, hy, rfl⟩ h0
  have h1 : y.1 = 0 := D.ι0_injective (by simpa [LΓ] using h0)
  have h2 : y.2 = 0 := hS0 (by rw [← D.mem_Γ.1 hy, h1, map_zero, map_zero])
  simp [LΓ, h2]

lemma graph1_hg : ∀ (x : Wt1 × (W2 × Wt2))
    (_ : x ∈ LinearMap.range ((D.ιt1.prod D.T : Vt1 →L[ℝ] Wt1 × (W2 × Wt2)) :
      Vt1 →ₗ[ℝ] Wt1 × (W2 × Wt2))), x.1 = 0 → x.2 = 0 := by
  rintro _ ⟨v, rfl⟩ h0
  have : v = 0 := D.ιt1_injective (by simpa using h0)
  simp [this]

/-- Thesis Prop 5.1: the graph of `(0 d)` is `{(σ, d̃φ) | (σ, φ) ∈ Γ}` (needs `S₀` injective). -/
theorem D0op_graph (hS0 : Function.Injective D.S0) :
    D.D0op.graph = D.Γ.map (D.LΓ : V0 × Vt0 →ₗ[ℝ] W0 × Wt1) :=
  Submodule.toLinearPMap_graph_eq _ (D.graph0_hg hS0)

/-- Thesis Prop 5.1: the graph of `(S, d)` is `{(u, S₁u, d̃¹u) | u ∈ Ṽ¹}`. -/
theorem D1op_graph : D.D1op.graph = LinearMap.range ((D.ιt1.prod D.T : Vt1 →L[ℝ]
    Wt1 × (W2 × Wt2)) : Vt1 →ₗ[ℝ] Wt1 × (W2 × Wt2)) :=
  Submodule.toLinearPMap_graph_eq _ D.graph1_hg

/-- The domain `π₁Γ` of `(0 d)` is dense in `Γ̄` (densely defined), by construction. -/
theorem D0op_domain : D.D0op.domain.topologicalClosure = D.Γbar := by
  simp only [D0op, Submodule.toLinearPMap_domain, Γbar, ← Submodule.map_comp]
  rfl

/-- Thesis Prop 5.1: `(S, d)` has domain `Ṽ¹`. -/
theorem D1op_domain : D.D1op.domain = LinearMap.range (D.ιt1 : Vt1 →ₗ[ℝ] Wt1) := by
  simp only [D1op, Submodule.toLinearPMap_domain, ← LinearMap.range_comp]
  rfl

/-- On `Γ`, the graph norm of `(0 d)` controls the `V⁰ × Ṽ⁰` norm (thesis Prop 5.1 proof:
"the graph norm is equivalent to the product norm"). -/
lemma exists_bound_Γ (h : D.Hyps) : ∃ C : NNReal, ∀ x : D.Γ,
    ‖x‖ ≤ C * ‖D.ιt1 (D.dt0 (x : V0 × Vt0).2)‖ := by
  obtain ⟨C, hC0, hC⟩ := D.poincare_Γ h
  refine ⟨⟨C, hC0⟩, fun x => ?_⟩
  obtain ⟨h1, h2⟩ := hC x x.2
  show ‖(x : V0 × Vt0)‖ ≤ _
  rw [Prod.norm_def]
  exact max_le h1 h2

/-- **Thesis Prop 5.1**, closedness of `(0 d)`.

See [QuennevilleBelair2015, Prop 5.1 (proof)]. -/
theorem D0op_isClosed (h : D.Hyps) (hS0 : Function.Injective D.S0) : D.D0op.IsClosed := by
  obtain ⟨C, hC⟩ := D.exists_bound_Γ h
  let g : D.Γ →L[ℝ] W0 × Wt1 := D.LΓ ∘L D.Γ.subtypeL
  have hg : AntilipschitzWith C g := g.antilipschitz_of_bound fun x =>
    (hC x).trans (by gcongr; exact norm_snd_le (g x))
  have hset : (D.D0op.graph : Set (W0 × Wt1)) = Set.range g := by
    rw [D.D0op_graph hS0]
    ext p
    simp only [SetLike.mem_coe, Submodule.mem_map, Set.mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, y.2, rfl⟩
  show IsClosed (D.D0op.graph : Set (W0 × Wt1))
  rw [hset]
  exact hg.isClosed_range g.uniformContinuous

/-- **Thesis Prop 5.1**, closed range of `(0 d)` (in `W̃¹`). -/
theorem D0op_isClosed_range (h : D.Hyps) (hS0 : Function.Injective D.S0) :
    IsClosed (LinearMap.range D.D0op.toFun : Set Wt1) := by
  obtain ⟨C, hC⟩ := D.exists_bound_Γ h
  let g : D.Γ →L[ℝ] Wt1 := (D.ιt1 ∘L D.dt0) ∘L ContinuousLinearMap.snd ℝ V0 Vt0 ∘L D.Γ.subtypeL
  have hg : AntilipschitzWith C g := g.antilipschitz_of_bound hC
  have hset : (LinearMap.range D.D0op.toFun : Set Wt1) = Set.range g := by
    rw [D0op, Submodule.toLinearPMap_range _ (D.graph0_hg hS0)]
    ext p
    simp only [SetLike.mem_coe, Submodule.mem_map, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨_, ⟨y, y.2, rfl⟩, rfl⟩
  rw [hset]
  exact hg.isClosed_range g.uniformContinuous

/-- **Thesis Prop 5.1**, closedness of `(S, d)` ("clearly closed": the graph norm controls the
`Ṽ¹`-norm).

See [QuennevilleBelair2015, Prop 5.1 (proof)]. -/
theorem D1op_isClosed : D.D1op.IsClosed := by
  let g : Vt1 →L[ℝ] Wt1 × (W2 × Wt2) := D.ιt1.prod D.T
  have hb : ∀ v, ‖v‖ ≤ (2 : NNReal) * ‖g v‖ := by
    intro v
    have h1 : ‖D.ιt1 v‖ ≤ ‖g v‖ := norm_fst_le (g v)
    have h2 : ‖D.dt1 v‖ ≤ ‖g v‖ :=
      (norm_snd_le (D.T v)).trans (norm_snd_le (g v))
    have := D.norm_sq_Vt1 v
    push_cast
    nlinarith [norm_nonneg v, norm_nonneg (g v), norm_nonneg (D.ιt1 v), norm_nonneg (D.dt1 v)]
  have hg : AntilipschitzWith 2 g := g.antilipschitz_of_bound hb
  show IsClosed (D.D1op.graph : Set (Wt1 × (W2 × Wt2)))
  rw [D.D1op_graph]
  exact hg.isClosed_range g.uniformContinuous

/-- **Thesis Prop 5.1**, closed range of `(S, d)` (in `W² × W̃²`).

See [QuennevilleBelair2015, Prop 5.1 (proof)]. -/
theorem D1op_isClosed_range (h : D.Hyps) :
    IsClosed (LinearMap.range D.D1op.toFun : Set (W2 × Wt2)) := by
  have hset : (LinearMap.range D.D1op.toFun : Set (W2 × Wt2)) = Set.range D.T := by
    rw [D1op, Submodule.toLinearPMap_range _ D.graph1_hg]
    ext p
    simp only [SetLike.mem_coe, Submodule.mem_map, Set.mem_range, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩; exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩; exact ⟨_, ⟨v, rfl⟩, rfl⟩
  rw [hset]
  exact D.isClosed_range_T h

lemma mem_ker_D1op {y : Wt1} : y ∈ D.D1op.ker ↔ ∃ v ∈ D.Z1, D.ιt1 v = y := by
  rw [LinearPMap.mem_ker_iff]
  constructor
  · rintro ⟨x, rfl, hx⟩
    have hm : ((x : Wt1), D.D1op x) ∈ D.D1op.graph := LinearPMap.mem_graph D.D1op x
    rw [D.D1op_graph, hx] at hm
    obtain ⟨v, hv⟩ := hm
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.prod_apply,
      Prod.mk.injEq] at hv
    exact ⟨v, hv.2, hv.1⟩
  · rintro ⟨v, hv, rfl⟩
    have hm : (D.ιt1 v, (0 : W2 × Wt2)) ∈ D.D1op.graph := by
      rw [D.D1op_graph]
      exact ⟨v, by simp [show D.T v = 0 from hv]⟩
    obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff D.D1op).1 hm
    exact ⟨x, hx1.symm, hx2⟩

lemma mem_range_D0op (hS0 : Function.Injective D.S0) {y : Wt1} :
    y ∈ LinearMap.range D.D0op.toFun ↔ ∃ x ∈ D.Γ, D.ιt1 (D.dt0 x.2) = y := by
  rw [D0op, Submodule.toLinearPMap_range _ (D.graph0_hg hS0)]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

/-- **Thesis Prop 5.1**, complex property `(S, d) ∘ (0 d) = 0`, i.e. `R(0 d) ⊆ N(S, d)`
(the thesis checks only the `S`-component; `d̃d̃ = 0` and `R(0 d) ⊆ Ṽ¹` are implicit). -/
theorem range_D0op_le_ker_D1op (hS0 : Function.Injective D.S0) :
    LinearMap.range D.D0op.toFun ≤ D.D1op.ker := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (D.mem_range_D0op hS0).1 hy
  exact D.mem_ker_D1op.2 ⟨_, D.dt0_mem_Z1 hx, rfl⟩

/-- **Exactness of (5.1)** (missing in the thesis), for the unbounded operators:
`N(S, d) = R(0 d)` at `W̃¹`, and `(0 d)` is injective.

Cf. [QuennevilleBelair2015, Prop 5.1]; cf. [ArnoldHu2021]. -/
theorem exact_D0op_D1op (h : D.Hyps) (hS0 : Function.Injective D.S0) :
    D.D1op.ker = LinearMap.range D.D0op.toFun ∧ D.D0op.ker = ⊥ := by
  constructor
  · ext y
    rw [D.mem_ker_D1op, D.mem_range_D0op hS0]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (D.mem_Z1_iff h).1 hv
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, D.dt0_mem_Z1 hx, rfl⟩
  · rw [Submodule.eq_bot_iff]
    intro y hy
    rw [LinearPMap.mem_ker_iff] at hy
    obtain ⟨z, rfl, hz⟩ := hy
    have hm : ((z : W0), D.D0op z) ∈ D.D0op.graph := LinearPMap.mem_graph D.D0op z
    rw [D.D0op_graph hS0, hz] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    simp only [LΓ, ContinuousLinearMap.coe_coe, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Prod.mk.injEq] at hxe
    have h2 : x.2 = 0 := h.dt0_injective (D.ιt1_injective (by rw [hxe.2, map_zero, map_zero]))
    have h1 : x.1 = 0 := h.d0_injective (by rw [D.mem_Γ.1 hx, h2, map_zero, map_zero])
    rw [← hxe.1, h1, map_zero]

/-- **Thesis Prop 5.1**: the complex with weak symmetries (5.1),
`Γ̄ ⊃ Γ --(0 d)--> W̃¹ ⊃ Ṽ¹ --(S, d)--> W² × W̃²`, is a closed Hilbert complex: both operators are
closed and densely defined (in `Γ̄`, resp. `W̃¹`), have closed ranges, and compose to zero.
Moreover (missing in the thesis) it is exact at `Γ̄` and at `W̃¹`.

Corrections / gaps filled: `Γ̄` is realised concretely as a closed subspace of `W⁰`, so the
thesis' "`(σ, φ) ∈ Γ̄`" makes sense (closedness of the graph of `(0 d)` in `W⁰ × W̃¹` is the same
as in `Γ̄ × W̃¹`, `Γ̄` being closed); the Poincaré inequalities used implicitly are proved
(`poincare_Γ`, `poincare_T`); typos `Z̃ = N(d⁰)`, `W¹`/`W²` corrected; exactness at `Ṽ¹`
(`exact_mid`) is proved. `W² × W̃²` carries the (equivalent) sup norm.

See [QuennevilleBelair2015, Prop 5.1]. Closed Hilbert complexes as in [BruningLesch1992], [AFW2010], [Arnold2018];
the general construction of complexes from complexes is [ArnoldHu2021]; the weak-symmetry
mechanism is that of [AFW2007]. -/
theorem prop_5_1 (h : D.Hyps) (hS0 : Function.Injective D.S0) :
    D.D0op.IsClosed ∧ D.D0op.domain.topologicalClosure = D.Γbar ∧
    IsClosed (LinearMap.range D.D0op.toFun : Set Wt1) ∧
    D.D1op.IsClosed ∧ Dense (D.D1op.domain : Set Wt1) ∧
    IsClosed (LinearMap.range D.D1op.toFun : Set (W2 × Wt2)) ∧
    LinearMap.range D.D0op.toFun ≤ D.D1op.ker ∧
    D.D1op.ker = LinearMap.range D.D0op.toFun ∧ D.D0op.ker = ⊥ := by
  refine ⟨D.D0op_isClosed h hS0, D.D0op_domain, D.D0op_isClosed_range h hS0, D.D1op_isClosed,
    ?_, D.D1op_isClosed_range h, D.range_D0op_le_ker_D1op hS0, D.exact_D0op_D1op h hS0⟩
  rw [D.D1op_domain]
  exact D.denset1

/-! ### The saddle point problem (5.3) and Prop 5.2 -/

/-- The bilinear form `a` of (5.3):
`a(σ,φ,u; τ,ψ,v) = (σ,τ) - (u, d̃ψ) + (d̃φ, v) + (S₁u, S₁v) + (d̃u, d̃v)` (all `W`-inner products).

See [QuennevilleBelair2015, (5.3)]; symmetry imposed weakly as in [AFW2007]. -/
def aForm : Xsp V0 Vt0 Vt1 →L[ℝ] Xsp V0 Vt0 Vt1 →L[ℝ] ℝ :=
  ip (D.ι0 ∘L pσ V0 Vt0 Vt1) (D.ι0 ∘L pσ V0 Vt0 Vt1)
    - ip (D.ιt1 ∘L pu V0 Vt0 Vt1) (D.ιt1 ∘L D.dt0 ∘L pφ V0 Vt0 Vt1)
    + ip (D.ιt1 ∘L D.dt0 ∘L pφ V0 Vt0 Vt1) (D.ιt1 ∘L pu V0 Vt0 Vt1)
    + ip (D.S1 ∘L pu V0 Vt0 Vt1) (D.S1 ∘L pu V0 Vt0 Vt1)
    + ip (D.dt1 ∘L pu V0 Vt0 Vt1) (D.dt1 ∘L pu V0 Vt0 Vt1)

lemma aForm_mkX (σ τ : V0) (φ ψ : Vt0) (u v : Vt1) :
    D.aForm (mkX σ φ u) (mkX τ ψ v) = ⟪D.ι0 σ, D.ι0 τ⟫ - ⟪D.ιt1 u, D.ιt1 (D.dt0 ψ)⟫ +
      ⟪D.ιt1 (D.dt0 φ), D.ιt1 v⟫ + ⟪D.S1 u, D.S1 v⟫ + ⟪D.dt1 u, D.dt1 v⟫ := rfl

lemma aForm_apply (x y : Xsp V0 Vt0 Vt1) : D.aForm x y =
    ⟪D.ι0 (pσ V0 Vt0 Vt1 x), D.ι0 (pσ V0 Vt0 Vt1 y)⟫ -
      ⟪D.ιt1 (pu V0 Vt0 Vt1 x), D.ιt1 (D.dt0 (pφ V0 Vt0 Vt1 y))⟫ +
      ⟪D.ιt1 (D.dt0 (pφ V0 Vt0 Vt1 x)), D.ιt1 (pu V0 Vt0 Vt1 y)⟫ +
      ⟪D.S1 (pu V0 Vt0 Vt1 x), D.S1 (pu V0 Vt0 Vt1 y)⟫ +
      ⟪D.dt1 (pu V0 Vt0 Vt1 x), D.dt1 (pu V0 Vt0 Vt1 y)⟫ := rfl

/-- `B(τ, ψ) = dτ - Sψ ∈ W¹`, so that `b(τ,ψ,v; λ) = -(λ, B(τ,ψ))`. -/
def Bop : Psp V0 Vt0 →L[ℝ] W1 :=
  D.ι1 ∘L (D.d0 ∘L WithLp.fstL 2 ℝ V0 Vt0 - D.S0 ∘L WithLp.sndL 2 ℝ V0 Vt0)

lemma Bop_apply (q : Psp V0 Vt0) : D.Bop q = D.ι1 (D.d0 q.fst - D.S0 q.snd) := rfl

lemma Bop_eq_zero_iff (q : Psp V0 Vt0) : D.Bop q = 0 ↔ (q.fst, q.snd) ∈ D.Γ := by
  rw [Bop_apply, D.mem_Γ, ← sub_eq_zero (a := D.d0 _)]
  constructor
  · intro h0; exact D.ι1_injective (by rw [h0, map_zero])
  · intro h0; rw [h0, map_zero]

local notation "adj" => ContinuousLinearMap.adjoint

/-- **The multiplier space `W̌¹`**: the completion of `W¹` in
`|||λ||| = sup_{(τ,ψ)} (λ, dτ - Sψ)/‖(τ,ψ)‖`, realised as the closure of `R(B*)` in `V⁰ × Ṽ⁰`
(`|||λ||| = ‖B*λ‖`, see `tripleNorm_spec`, `jW`).

See [QuennevilleBelair2015, §5.1, before Prop 5.2]; analogous to the multiplier norm in the
limiting case `t = 0` of the Reissner–Mindlin plate [Falk2008], cf. [DuranLiberman1992]. -/
def Wcheck : Submodule ℝ (Psp V0 Vt0) := (adj D.Bop).range.topologicalClosure

instance : CompleteSpace D.Wcheck :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- `|||λ|||` (thesis §5.1), with the ℓ² norm on `V⁰ × Ṽ⁰`. -/
def tripleNorm (l : W1) : ℝ := ‖adj D.Bop l‖

/-- Thesis §5.1 (definition of `|||·|||`): `|||λ||| = ‖B*λ‖` is the thesis' supremum: `(λ, dτ - Sψ) ≤ |||λ||| ‖(τ,ψ)‖`, with equality attained
on the unit ball.

See [QuennevilleBelair2015, §5.1, before Prop 5.2]. -/
theorem tripleNorm_spec (l : W1) :
    (∀ q, ⟪l, D.Bop q⟫ ≤ D.tripleNorm l * ‖q‖) ∧
      ∃ q, ‖q‖ ≤ 1 ∧ ⟪l, D.Bop q⟫ = D.tripleNorm l := by
  refine ⟨fun q => ?_, ?_⟩
  · rw [← ContinuousLinearMap.adjoint_inner_left, real_inner_comm, tripleNorm]
    exact (real_inner_le_norm _ _).trans (by rw [mul_comm])
  · rcases eq_or_ne (adj D.Bop l) 0 with h0 | h0
    · exact ⟨0, by simp, by simp [tripleNorm, h0]⟩
    · refine ⟨‖adj D.Bop l‖⁻¹ • adj D.Bop l, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
      · rw [← ContinuousLinearMap.adjoint_inner_left, inner_smul_right,
          real_inner_self_eq_norm_sq, tripleNorm]
        field_simp

/-- `|||λ||| ≤ ‖B‖ ‖λ‖` (thesis: `≤ max(1, ‖S‖) ‖λ‖` for the sum norm). -/
theorem tripleNorm_le (l : W1) : D.tripleNorm l ≤ ‖D.Bop‖ * ‖l‖ := by
  have : ‖adj D.Bop‖ = ‖D.Bop‖ := LinearIsometryEquiv.norm_map _ _
  rw [tripleNorm, ← this]
  exact (adj D.Bop).le_opNorm l

/-- **`|||·|||` is a norm** (thesis: "is actually a norm", no proof), under the corrected density
hypothesis `d⁰V⁰ + S₀Ṽ⁰` dense in `W¹`.

See [QuennevilleBelair2015, §5.1, before Prop 5.2]. -/
theorem tripleNorm_definite
    (hdense : Dense ((LinearMap.range (D.ι1 ∘L D.d0 : V0 →ₗ[ℝ] W1) ⊔
      LinearMap.range (D.ι1 ∘L D.S0 : Vt0 →ₗ[ℝ] W1) : Submodule ℝ W1) : Set W1))
    {l : W1} (hl : D.tripleNorm l = 0) : l = 0 := by
  have h0 : adj D.Bop l = 0 := norm_eq_zero.1 hl
  refine hdense.eq_zero_of_mem_orthogonal ?_
  rw [Submodule.mem_orthogonal]
  intro k hk
  have hB : ∀ q, ⟪D.Bop q, l⟫ = 0 := fun q => by
    rw [← ContinuousLinearMap.adjoint_inner_right, h0, inner_zero_right]
  obtain ⟨a, ⟨τ, rfl⟩, b, ⟨ψ, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hk
  have h1 := hB (WithLp.toLp 2 (τ, 0))
  have h2 := hB (WithLp.toLp 2 (0, ψ))
  simp only [Bop_apply, WithLp.toLp_fst, WithLp.toLp_snd, map_zero, sub_zero, zero_sub,
    map_neg, inner_neg_left, neg_eq_zero] at h1 h2
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, inner_add_left]
  rw [h1, h2, add_zero]

/-- The thesis' hypothesis "`S Ṽ⁰` dense in `W¹`" implies the corrected one. -/
theorem dense_sup_of_denseRange_S0 (hS : DenseRange (D.ι1 ∘L D.S0)) :
    Dense ((LinearMap.range (D.ι1 ∘L D.d0 : V0 →ₗ[ℝ] W1) ⊔
      LinearMap.range (D.ι1 ∘L D.S0 : Vt0 →ₗ[ℝ] W1) : Submodule ℝ W1) : Set W1) :=
  Dense.mono (fun y hy => by
    obtain ⟨ψ, rfl⟩ := hy
    exact Submodule.mem_sup_right ⟨ψ, rfl⟩) hS

/-- The embedding `W¹ → W̌¹`, `λ ↦ B*λ`. -/
def jW : W1 →L[ℝ] D.Wcheck :=
  (adj D.Bop).codRestrict D.Wcheck fun l =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ l)

/-- Thesis §5.1 / Prop 5.2: **`W̌¹` is the completion of `(W¹, |||·|||)`**: `jW` is isometric for `|||·|||`, has dense
range, and is injective under the density hypothesis.

See [QuennevilleBelair2015, §5.1, Prop 5.2]. -/
theorem jW_spec
    (hdense : Dense ((LinearMap.range (D.ι1 ∘L D.d0 : V0 →ₗ[ℝ] W1) ⊔
      LinearMap.range (D.ι1 ∘L D.S0 : Vt0 →ₗ[ℝ] W1) : Submodule ℝ W1) : Set W1)) :
    (∀ l, ‖D.jW l‖ = D.tripleNorm l) ∧ DenseRange D.jW ∧ Function.Injective D.jW := by
  refine ⟨fun l => rfl, ?_, ?_⟩
  · intro μ
    have hμ : (μ : Psp V0 Vt0) ∈ closure (Set.range (adj D.Bop)) := μ.2
    rw [mem_closure_iff_seq_limit] at hμ ⊢
    obtain ⟨q, hq, hlim⟩ := hμ
    choose l hl using hq
    refine ⟨fun n => D.jW (l n), fun n => ⟨l n, rfl⟩, ?_⟩
    rw [tendsto_subtype_rng]
    have : (fun n => ((D.jW (l n) : D.Wcheck) : Psp V0 Vt0)) = q := funext fun n => hl n
    rw [this]; exact hlim
  · refine (injective_iff_map_eq_zero _).2 fun l hl => D.tripleNorm_definite hdense ?_
    rw [tripleNorm, show adj D.Bop l = (D.jW l : Psp V0 Vt0) from rfl, hl]
    simp

/-- The constraint operator: `b(y, μ) = ⟪Bs y, μ⟫`. -/
def Bs : Xsp V0 Vt0 Vt1 →L[ℝ] D.Wcheck := -(D.Wcheck.orthogonalProjectionOnto ∘L pP V0 Vt0 Vt1)

/-- The bilinear form `b` of (5.3), extended to `μ ∈ W̌¹`: `b(τ,ψ,v; μ) = -⟪(τ,ψ), μ⟫`. -/
def bForm (y : Xsp V0 Vt0 Vt1) (μ : D.Wcheck) : ℝ := -⟪pP V0 Vt0 Vt1 y, (μ : Psp V0 Vt0)⟫

lemma inner_Bs (y : Xsp V0 Vt0 Vt1) (μ : D.Wcheck) : ⟪D.Bs y, μ⟫ = D.bForm y μ := by
  simp [Bs, bForm, inner_neg_left]

/-- On `W¹ ⊂ W̌¹`, `b` is the thesis' `b(τ,ψ,v; λ) = -(λ, dτ - Sψ)`. -/
lemma bForm_jW (y : Xsp V0 Vt0 Vt1) (l : W1) :
    D.bForm y (D.jW l) = -⟪l, D.ι1 (D.d0 (pσ V0 Vt0 Vt1 y) - D.S0 (pφ V0 Vt0 Vt1 y))⟫ := by
  rw [bForm, show ((D.jW l : D.Wcheck) : Psp V0 Vt0) = adj D.Bop l from rfl,
    ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
  rfl

lemma mem_orth_Wcheck_iff (q : Psp V0 Vt0) : q ∈ D.Wcheckᗮ ↔ (q.fst, q.snd) ∈ D.Γ := by
  rw [Wcheck, Submodule.orthogonal_closure, ← D.Bop_eq_zero_iff]
  have := ContinuousLinearMap.orthogonal_range (adj D.Bop)
  rw [ContinuousLinearMap.adjoint_adjoint] at this
  rw [this]
  rfl

/-- The kernel of `b` is `Z = Γ × Ṽ¹` (thesis, proof of Prop 5.2). -/
lemma mem_ker_Bs (y : Xsp V0 Vt0 Vt1) :
    y ∈ D.Bs.ker ↔ (pσ V0 Vt0 Vt1 y, pφ V0 Vt0 Vt1 y) ∈ D.Γ := by
  show D.Bs y = 0 ↔ _
  rw [Bs, neg_apply, neg_eq_zero,
    ContinuousLinearMap.comp_apply, Submodule.orthogonalProjectionOnto_eq_zero_iff,
    mem_orth_Wcheck_iff]
  rfl

lemma mkX_mem_ker {σ : V0} {φ : Vt0} (u : Vt1) (h : (σ, φ) ∈ D.Γ) : mkX σ φ u ∈ D.Bs.ker :=
  (D.mem_ker_Bs _).2 h

/-- Inf-sup of `b` with constant `1` (thesis: "holds by definition of the norm on `W̌¹`").

See [QuennevilleBelair2015, proof of Prop 5.2]; the inf-sup condition on `b` of Brezzi's theorem
[QuennevilleBelair2015, Thm 4.11], [Brezzi1974], [BoffiBrezziFortin2013]. -/
theorem infSup_b : ∀ μ : D.Wcheck, 1 * ‖μ‖ ≤ ‖adj D.Bs μ‖ := by
  intro μ
  rw [one_mul]
  set x : Xsp V0 Vt0 Vt1 := WithLp.toLp 2 (-(μ : Psp V0 Vt0), 0)
  have hx : ‖x‖ = ‖μ‖ := by
    have h2 : ‖x‖ ^ 2 = ‖μ‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp [x]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
  have hi : ⟪adj D.Bs μ, x⟫ = ‖μ‖ ^ 2 := by
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm, inner_Bs, bForm]
    simp [x, pP, inner_neg_left]
  have hle : ‖μ‖ ^ 2 ≤ ‖adj D.Bs μ‖ * ‖μ‖ := by
    rw [← hi, ← hx]; exact real_inner_le_norm _ _
  rcases (norm_nonneg μ).lt_or_eq with hpos | h0
  · nlinarith
  · rw [← h0]; exact norm_nonneg _


lemma norm_Z1 {e : Vt1} (he : e ∈ D.Z1) : ‖e‖ = ‖D.ιt1 e‖ := by
  have h1 := D.norm_sq_Vt1 e
  rw [(D.mem_Z1.1 he).2, norm_zero] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

lemma inner_ιt1_of_orth {e w : Vt1} (he : e ∈ D.Z1) (hw : w ∈ D.Z1ᗮ) :
    ⟪D.ιt1 w, D.ιt1 e⟫ = 0 := by
  have h0 : ⟪w, e⟫ = 0 := Submodule.inner_left_of_mem_orthogonal he hw
  rwa [D.grapht1, (D.mem_Z1.1 he).2, inner_zero_right, add_zero] at h0

/-- Real-arithmetic core of the inf-sup estimate (Young's inequality step). -/
private lemma core_low {s r E P A B ε c : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hεc : ε * c ^ 2 = 1)
    (hr : r ≤ s * (c * E)) :
    ε / 2 * (E ^ 2 + P ^ 2 + A ^ 2 + B ^ 2) ≤ s ^ 2 - ε * r + ε * E ^ 2 + ε * P ^ 2 + A ^ 2 + B ^ 2 := by
  have h1 : ε * r ≤ ε * (s * (c * E)) := mul_le_mul_of_nonneg_left hr hε0
  have h3 : ε ^ 2 * c ^ 2 * E ^ 2 = ε * E ^ 2 := by
    rw [show ε ^ 2 * c ^ 2 * E ^ 2 = (ε * c ^ 2) * (ε * E ^ 2) by ring, hεc, one_mul]
  nlinarith [sq_nonneg (s - ε * c * E), mul_nonneg (sub_nonneg.2 hε1) (sq_nonneg A),
    mul_nonneg (sub_nonneg.2 hε1) (sq_nonneg B), mul_nonneg hε0 (sq_nonneg P),
    mul_nonneg hε0 (sq_nonneg E)]

private lemma core_prod {a b n M : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) (hn : n ≤ a + b)
    (ha2 : a ^ 2 ≤ M) (hb2 : b ^ 2 ≤ M) : a * n ≤ 2 * M := by
  have := mul_le_mul_of_nonneg_left hn ha
  nlinarith [sq_nonneg (a - b)]

private lemma sq_add_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

private lemma sq3_eq_zero {a b c : ℝ} (h : a ^ 2 + b ^ 2 + c ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hb : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hc : c ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  exact ⟨pow_eq_zero_iff two_ne_zero |>.1 ha, pow_eq_zero_iff two_ne_zero |>.1 hb,
    pow_eq_zero_iff two_ne_zero |>.1 hc⟩

/-- **Inf-sup condition for `a` on `Z = Γ × Ṽ¹`** (thesis, proof of Prop 5.2), with the thesis'
test function restored: `(τ, ψ, v) = (σ - ερ, φ - εχ, u + ε d̃φ)` where `u = d̃χ + w`,
`(ρ, χ) ∈ Γ`, `w ⊥ N(S₁) ∩ N(d̃¹)`, and `ε = 1/c²`.
Thesis gaps: the ε's are lost in the text; the decomposition without harmonic part needs
exactness of (5.1) at `Ṽ¹` (`hodge_Vt1`); the final step `a ≥ C ‖x‖ ‖y‖` needs the bounds
`‖x‖², ‖y - x‖² ≤ 2c² Q`, written out below.

See [QuennevilleBelair2015, proof of Prop 5.2]; the inf-sup condition on the kernel of Brezzi's
theorem [QuennevilleBelair2015, Thm 4.11], [Brezzi1974], [BoffiBrezziFortin2013]. -/
theorem infSup_a (h : D.Hyps) :
    ∃ γ > 0, ∀ z ∈ D.Bs.ker, ∃ z' ∈ D.Bs.ker, ‖z'‖ ≤ 1 ∧ γ * ‖z‖ ≤ D.aForm z z' := by
  obtain ⟨C1, hC1, hP1⟩ := D.poincare_Γ h
  obtain ⟨C2, hC2, hP2⟩ := D.poincare_T h
  set c := max 1 (max C1 C2) with hc
  have hc1 : 1 ≤ c := le_max_left _ _
  have hcC1 : C1 ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hcC2 : C2 ≤ c := (le_max_right _ _).trans (le_max_right _ _)
  have hcpos : 0 < c := by linarith
  have hc2 : 1 ≤ c ^ 2 := one_le_pow₀ hc1
  set ε := 1 / c ^ 2 with hε
  have hεc : ε * c ^ 2 = 1 := by rw [hε]; field_simp
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by rw [hε, div_le_one (by positivity)]; exact hc2
  refine ⟨ε / (8 * c ^ 2), by positivity, fun z hz => ?_⟩
  set σ := pσ V0 Vt0 Vt1 z with hσdef
  set φ := pφ V0 Vt0 Vt1 z with hφdef
  set u := pu V0 Vt0 Vt1 z with hudef
  have hΓ : (σ, φ) ∈ D.Γ := (D.mem_ker_Bs z).1 hz
  obtain ⟨xr, hxr, w, hw, hu⟩ := D.hodge_Vt1 h u
  set ρ := xr.1
  set χ := xr.2
  set p := D.dt0 φ with hpdef
  set e := D.dt0 χ with hedef
  have hpZ : p ∈ D.Z1 := D.dt0_mem_Z1 hΓ
  have heZ : e ∈ D.Z1 := D.dt0_mem_Z1 hxr
  obtain ⟨hS1p, hdt1p⟩ := D.mem_Z1.1 hpZ
  obtain ⟨hS1e, hdt1e⟩ := D.mem_Z1.1 heZ
  have hwp := D.inner_ιt1_of_orth hpZ hw
  have hwe := D.inner_ιt1_of_orth heZ hw
  have hew : ⟪e, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal heZ hw
  -- the test function
  set y := mkX (σ - ε • ρ) (φ - ε • χ) (u + ε • p) with hydef
  have hy : y ∈ D.Bs.ker := D.mkX_mem_ker _ (D.Γ.sub_mem hΓ (D.Γ.smul_mem ε hxr))
  set s := ‖D.ι0 σ‖
  set E := ‖D.ιt1 e‖
  set P := ‖D.ιt1 p‖
  set A := ‖D.S1 w‖
  set B := ‖D.dt1 w‖
  have hval : D.aForm z y =
      s ^ 2 - ε * ⟪D.ι0 σ, D.ι0 ρ⟫ + ε * E ^ 2 + ε * P ^ 2 + A ^ 2 + B ^ 2 := by
    show D.aForm (mkX σ φ u) y = _
    rw [hydef, aForm_mkX, hu]
    simp only [map_add, map_sub, map_smul, ← hpdef, ← hedef, hS1p, hS1e, hdt1p, hdt1e,
      inner_add_left, inner_add_right, inner_sub_right, real_inner_smul_right,
      smul_zero, add_zero, zero_add, real_inner_self_eq_norm_sq,
      real_inner_comm (D.ιt1 w) (D.ιt1 p), hwp, hwe, real_inner_comm (D.ιt1 e) (D.ιt1 p)]
    ring
  -- Poincaré bounds
  obtain ⟨hρ, hχ⟩ := hP1 xr hxr
  obtain ⟨hσ, hφ⟩ := hP1 (σ, φ) hΓ
  have hρc : ‖ρ‖ ≤ c * E := hρ.trans (by gcongr)
  have hχc : ‖χ‖ ≤ c * E := hχ.trans (by gcongr)
  have hσc : ‖σ‖ ≤ c * P := hσ.trans (by gcongr)
  have hφc : ‖φ‖ ≤ c * P := hφ.trans (by gcongr)
  have hcs : ⟪D.ι0 σ, D.ι0 ρ⟫ ≤ s * (c * E) :=
    (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left ((D.norm_ι0_le ρ).trans hρc) (norm_nonneg _))
  set Q := E ^ 2 + P ^ 2 + A ^ 2 + B ^ 2 with hQ
  have hlow : ε / 2 * Q ≤ D.aForm z y := by
    rw [hval]; exact core_low hε0.le hε1 hεc hcs
  -- upper bounds
  have hpn : ‖p‖ = P := D.norm_Z1 hpZ
  have hen : ‖e‖ = E := D.norm_Z1 heZ
  have hun : ‖u‖ ^ 2 = E ^ 2 + ‖w‖ ^ 2 := by
    rw [hu, norm_add_sq_real, hew, hen]; ring
  have hwT : ‖D.T w‖ ≤ A + B := by
    rw [T_apply, Prod.norm_def]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have hwn : ‖w‖ ≤ c * (A + B) := (hP2 w hw).trans (by gcongr)
  have hw2 : ‖w‖ ^ 2 ≤ 2 * c ^ 2 * (A ^ 2 + B ^ 2) := by
    calc ‖w‖ ^ 2 ≤ (c * (A + B)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwn 2
      _ = c ^ 2 * (A + B) ^ 2 := by ring
      _ ≤ c ^ 2 * (2 * (A ^ 2 + B ^ 2)) := by gcongr; exact sq_add_le_two A B
      _ = _ := by ring
  have hz2 : ‖z‖ ^ 2 ≤ 2 * c ^ 2 * Q := by
    rw [norm_sq_X, ← hσdef, ← hφdef, ← hudef, hun]
    have a1 : ‖σ‖ ^ 2 ≤ c ^ 2 * P ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hσc 2; rwa [mul_pow] at this
    have a2 : ‖φ‖ ^ 2 ≤ c ^ 2 * P ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hφc 2; rwa [mul_pow] at this
    have a3 : E ^ 2 ≤ c ^ 2 * E ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hc2
    have p1 : 0 ≤ c ^ 2 * E ^ 2 := by positivity
    have p2 : 0 ≤ c ^ 2 * (A ^ 2 + B ^ 2) := by positivity
    rw [hQ]; linarith
  have hyz2 : ‖y - z‖ ^ 2 ≤ 2 * c ^ 2 * Q := by
    rw [norm_sq_X]
    have e1 : pσ V0 Vt0 Vt1 (y - z) = -(ε • ρ) := by
      rw [map_sub, hydef, pσ_mkX, ← hσdef]; abel
    have e2 : pφ V0 Vt0 Vt1 (y - z) = -(ε • χ) := by
      rw [map_sub, hydef, pφ_mkX, ← hφdef]; abel
    have e3 : pu V0 Vt0 Vt1 (y - z) = ε • p := by
      rw [map_sub, hydef, pu_mkX, ← hudef]; abel
    rw [e1, e2, e3, norm_neg, norm_neg, norm_smul, norm_smul, norm_smul,
      Real.norm_of_nonneg hε0.le, hpn]
    have a1 : ‖ρ‖ ^ 2 ≤ c ^ 2 * E ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hρc 2; rwa [mul_pow] at this
    have a2 : ‖χ‖ ^ 2 ≤ c ^ 2 * E ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hχc 2; rwa [mul_pow] at this
    have a3 : P ^ 2 ≤ c ^ 2 * P ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hc2
    have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1
    have hb : ‖ρ‖ ^ 2 + ‖χ‖ ^ 2 + P ^ 2 ≤ 2 * c ^ 2 * Q := by
      have p1 : 0 ≤ c ^ 2 * P ^ 2 := by positivity
      have p2 : 0 ≤ c ^ 2 * (A ^ 2 + B ^ 2) := by positivity
      rw [hQ]; linarith
    have hnn : 0 ≤ ‖ρ‖ ^ 2 + ‖χ‖ ^ 2 + P ^ 2 := by positivity
    calc (ε * ‖ρ‖) ^ 2 + (ε * ‖χ‖) ^ 2 + (ε * P) ^ 2
        = ε ^ 2 * (‖ρ‖ ^ 2 + ‖χ‖ ^ 2 + P ^ 2) := by ring
      _ ≤ 1 * (‖ρ‖ ^ 2 + ‖χ‖ ^ 2 + P ^ 2) := by gcongr
      _ ≤ _ := by rw [one_mul]; exact hb
  have hyle : ‖y‖ ≤ ‖z‖ + ‖y - z‖ := by
    calc ‖y‖ = ‖z + (y - z)‖ := by rw [add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  have hprod : ‖z‖ * ‖y‖ ≤ 2 * (2 * c ^ 2 * Q) :=
    core_prod (norm_nonneg _) (norm_nonneg _) hyle hz2 hyz2
  have hmain : ε / (8 * c ^ 2) * ‖z‖ * ‖y‖ ≤ D.aForm z y := by
    have e : ε / (8 * c ^ 2) * (2 * (2 * c ^ 2 * Q)) = ε / 2 * Q := by field_simp; ring
    calc ε / (8 * c ^ 2) * ‖z‖ * ‖y‖ = ε / (8 * c ^ 2) * (‖z‖ * ‖y‖) := by ring
      _ ≤ ε / (8 * c ^ 2) * (2 * (2 * c ^ 2 * Q)) := by gcongr
      _ = ε / 2 * Q := e
      _ ≤ _ := hlow
  rcases eq_or_ne y 0 with hy0 | hy0
  · refine ⟨0, Submodule.zero_mem _, by simp, ?_⟩
    have ha : D.aForm z y = 0 := by rw [hy0, map_zero]
    have hQ0 : Q ≤ 0 := by
      have h1 : ε / 2 * Q ≤ 0 := ha ▸ hlow
      by_contra hneg
      have : 0 < ε / 2 * Q := mul_pos (by positivity) (not_le.1 hneg)
      linarith
    have h2 : 2 * c ^ 2 * Q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hQ0
    have hz0 : ‖z‖ = 0 := pow_eq_zero_iff two_ne_zero |>.1
      (le_antisymm (hz2.trans h2) (sq_nonneg _))
    rw [hz0, mul_zero, map_zero]
  · have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
    refine ⟨‖y‖⁻¹ • y, Submodule.smul_mem _ _ hy, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hyn.ne']
    · rw [map_smul, smul_eq_mul, le_inv_mul_iff₀ hyn]
      calc ‖y‖ * (ε / (8 * c ^ 2) * ‖z‖) = ε / (8 * c ^ 2) * ‖z‖ * ‖y‖ := by ring
        _ ≤ _ := hmain

/-- **Transposed Brezzi condition on `Z`** (missing in the thesis): if `a(x, y) = 0` for all
`x ∈ Z` then `y = 0`. Thesis gap: Brezzi's theorem for the non-symmetric `a` needs this second
condition, which the thesis never checks. Proof: `a(y, y) = ‖τ‖² + ‖S₁v‖² + ‖d̃v‖²`; testing with
`(0, 0, d̃ψ)` gives `ψ = 0`; then `v ∈ N(S₁) ∩ N(d̃¹) = R(0 d)` by exactness at `Ṽ¹`, and testing
with `(ρ, χ, 0)`, `d̃χ = v`, gives `v = 0`. (Injectivity of `S₀` is not needed.)

Cf. [QuennevilleBelair2015, proof of Prop 5.2]; Brezzi's theorem for non-symmetric `a`:
[Brezzi1974], [BoffiBrezziFortin2013]. -/
theorem nondeg_a (h : D.Hyps) :
    ∀ z' ∈ D.Bs.ker, (∀ z ∈ D.Bs.ker, D.aForm z z' = 0) → z' = 0 := by
  intro z' hz' hall
  set τ := pσ V0 Vt0 Vt1 z' with hτ
  set ψ := pφ V0 Vt0 Vt1 z' with hψ
  set v := pu V0 Vt0 Vt1 z' with hv
  have hΓ : (τ, ψ) ∈ D.Γ := (D.mem_ker_Bs z').1 hz'
  -- step 1: a(z', z') = ‖τ‖² + ‖S₁v‖² + ‖d̃v‖²
  have h1 := hall z' hz'
  rw [aForm_apply, ← hτ, ← hψ, ← hv, real_inner_comm (D.ιt1 (D.dt0 ψ)) (D.ιt1 v),
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
  obtain ⟨hι0τ, hS1v, hdt1v⟩ := sq3_eq_zero (a := ‖D.ι0 τ‖) (b := ‖D.S1 v‖) (c := ‖D.dt1 v‖)
    (by linarith)
  rw [norm_eq_zero] at hS1v hdt1v
  -- step 2: ψ = 0
  have h2 := hall (mkX 0 0 (D.dt0 ψ)) (D.mkX_mem_ker _ (by simp [D.mem_Γ]))
  rw [aForm_apply] at h2
  simp only [pσ_mkX, pφ_mkX, pu_mkX, map_zero, inner_zero_left, ← hψ, ← hv, hS1v,
    inner_zero_right, D.dt1_dt0, zero_sub, add_zero, real_inner_self_eq_norm_sq,
    neg_eq_zero] at h2
  have hψ0 : ψ = 0 := h.dt0_injective (D.ιt1_injective (by
    rw [map_zero, map_zero]; exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)))
  -- step 3: τ = 0
  have hd0τ : D.d0 τ = 0 := by rw [D.mem_Γ.1 hΓ]; simp [hψ0]
  have hτ0 : τ = 0 := by
    have := D.norm_sq_V0 τ
    rw [hι0τ, hd0τ, map_zero, norm_zero] at this
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (by linarith))
  -- step 4: v = 0
  obtain ⟨xr, hxr, hxv⟩ := (D.mem_Z1_iff h).1 (D.mem_Z1.2 ⟨hS1v, hdt1v⟩)
  have h3 := hall (mkX xr.1 xr.2 0) (D.mkX_mem_ker _ hxr)
  rw [aForm_apply] at h3
  simp only [pσ_mkX, pφ_mkX, pu_mkX, ← hτ, ← hψ, ← hv, hτ0, hψ0, hxv, map_zero,
    inner_zero_left, inner_zero_right, sub_zero, zero_add, add_zero,
    real_inner_self_eq_norm_sq] at h3
  have hv0 : v = 0 := D.ιt1_injective (by
    rw [map_zero]; exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3))
  rw [← mkX_eta z', ← hτ, ← hψ, ← hv, hτ0, hψ0, hv0]
  rfl

/-- **Thesis Prop 5.2** (corrected), general form: the saddle point problem
`a(x, y) + b(y, λ) = ⟪F, y⟫ ∀ y ∈ X`, `b(x, μ) = ⟪G, μ⟫ ∀ μ ∈ W̌¹` on `X × W̌¹`
(`X = V⁰ × Ṽ⁰ × Ṽ¹`) is well posed: unique solvability and `‖x‖ + ‖λ‖ ≤ C (‖F‖ + ‖G‖)`.

Proof by Brezzi (M7 `brezzi_wellPosed`): inf-sup of `b` (`infSup_b`), inf-sup of `a` on
`Z = Γ × Ṽ¹` (`infSup_a`) and the transposed condition (`nondeg_a`, missing in the thesis).
Correction: neither density of `S₀Ṽ⁰` nor injectivity of `S₀` is needed for well-posedness on
`X × W̌¹`; density only serves to embed `W¹` into `W̌¹` (`jW_spec`).

See [QuennevilleBelair2015, Prop 5.2], via Brezzi's theorem [QuennevilleBelair2015, Thm 4.11],
[Brezzi1974], [BoffiBrezziFortin2013]. -/
theorem prop_5_2_wellPosed (h : D.Hyps) :
    (∀ (F : Xsp V0 Vt0 Vt1) (G : D.Wcheck), ∃! xl : Xsp V0 Vt0 Vt1 × D.Wcheck,
      (∀ y, D.aForm xl.1 y + D.bForm y xl.2 = ⟪F, y⟫) ∧ ∀ μ, D.bForm xl.1 μ = ⟪G, μ⟫) ∧
    ∃ C, ∀ (F : Xsp V0 Vt0 Vt1) (G : D.Wcheck) (x : Xsp V0 Vt0 Vt1) (l : D.Wcheck),
      (∀ y, D.aForm x y + D.bForm y l = ⟪F, y⟫) → (∀ μ, D.bForm x μ = ⟪G, μ⟫) →
        ‖x‖ + ‖l‖ ≤ C * (‖F‖ + ‖G‖) := by
  have hb : ∃ β > 0, ∀ q, β * ‖q‖ ≤ ‖adj D.Bs q‖ := ⟨1, one_pos, D.infSup_b⟩
  obtain ⟨hex, C, hC⟩ :=
    Feec.Galerkin.brezzi_wellPosed D.aForm D.Bs (D.infSup_a h) (D.nondeg_a h) hb
  simp only [inner_Bs] at hex hC
  exact ⟨hex, C, hC⟩

/-- The system (5.3) with right-hand side `f ∈ W̃¹` and multiplier `λ ∈ W̌¹`:
`a(σ,φ,u; τ,ψ,v) + b(τ,ψ,v; λ) = (f, v)` for all `(τ,ψ,v)`, and `b(σ,φ,u; μ) = 0` for all `μ`. -/
def Saddle (f : Wt1) (x : Xsp V0 Vt0 Vt1) (l : D.Wcheck) : Prop :=
  (∀ y, D.aForm x y + D.bForm y l = ⟪f, D.ιt1 (pu V0 Vt0 Vt1 y)⟫) ∧ ∀ μ, D.bForm x μ = 0

/-- **Thesis Prop 5.2**: (5.3) is well posed over `V⁰ × Ṽ⁰ × Ṽ¹ × W̌¹`: for every `f ∈ W̃¹` there
is a unique solution, and `‖(σ,φ,u)‖_V + |||λ||| ≤ C ‖f‖`.

Corrections: `λ ∈ W̌¹`, not `W¹` as (5.3) says; the density hypothesis of the thesis is not
needed here (it is used in `jW_spec`); the transposed Brezzi condition is added and proved.

See [QuennevilleBelair2015, Prop 5.2], via Brezzi's theorem [QuennevilleBelair2015, Thm 4.11],
[Brezzi1974], [BoffiBrezziFortin2013]. -/
theorem prop_5_2 (h : D.Hyps) :
    (∀ f : Wt1, ∃! xl : Xsp V0 Vt0 Vt1 × D.Wcheck, D.Saddle f xl.1 xl.2) ∧
    ∃ C, ∀ (f : Wt1) (x : Xsp V0 Vt0 Vt1) (l : D.Wcheck), D.Saddle f x l →
      ‖x‖ + ‖l‖ ≤ C * ‖f‖ := by
  obtain ⟨hex, C, hC⟩ := D.prop_5_2_wellPosed h
  set R := D.ιt1 ∘L pu V0 Vt0 Vt1
  have hF : ∀ (f : Wt1) y, ⟪adj R f, y⟫ = ⟪f, D.ιt1 (pu V0 Vt0 Vt1 y)⟫ := fun f y => by
    rw [ContinuousLinearMap.adjoint_inner_left]; rfl
  have hiff : ∀ f x l, D.Saddle f x l ↔
      ((∀ y, D.aForm x y + D.bForm y l = ⟪adj R f, y⟫) ∧ ∀ μ, D.bForm x μ = ⟪(0 : D.Wcheck), μ⟫) := by
    intro f x l
    simp only [Saddle, hF, inner_zero_left]
  refine ⟨fun f => ?_, max C 0 * ‖R‖, fun f x l hs => ?_⟩
  · obtain ⟨xl, hxl, hu⟩ := hex (adj R f) 0
    exact ⟨xl, (hiff _ _ _).2 hxl, fun xl' h' => hu xl' ((hiff _ _ _).1 h')⟩
  · have := (hiff f x l).1 hs
    have hb := hC _ _ x l this.1 this.2
    have hR : ‖adj R f‖ ≤ ‖R‖ * ‖f‖ := by
      have : ‖adj R‖ = ‖R‖ := LinearIsometryEquiv.norm_map _ _
      rw [← this]; exact (adj R).le_opNorm f
    calc ‖x‖ + ‖l‖ ≤ C * (‖adj R f‖ + ‖(0 : D.Wcheck)‖) := hb
      _ = C * ‖adj R f‖ := by rw [norm_zero, add_zero]
      _ ≤ max C 0 * ‖adj R f‖ := by gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (‖R‖ * ‖f‖) := by gcongr
      _ = _ := by ring

/-- The reduced Hodge Laplacian (5.2): `(σ, φ) ∈ Γ`, `(σ, τ) - (u, d̃ψ) = 0` for `(τ, ψ) ∈ Γ`, and
`(d̃φ, v) + (S₁u, S₁v) + (d̃u, d̃v) = (f, v)` for `v ∈ Ṽ¹`.

See [QuennevilleBelair2015, (5.2)]; the mixed Hodge Laplacian of a closed Hilbert complex as in
[AFW2010], [Arnold2018]. -/
def Reduced (f : Wt1) (x : Xsp V0 Vt0 Vt1) : Prop :=
  (pσ V0 Vt0 Vt1 x, pφ V0 Vt0 Vt1 x) ∈ D.Γ ∧
  (∀ τ ψ, (τ, ψ) ∈ D.Γ →
    ⟪D.ι0 (pσ V0 Vt0 Vt1 x), D.ι0 τ⟫ - ⟪D.ιt1 (pu V0 Vt0 Vt1 x), D.ιt1 (D.dt0 ψ)⟫ = 0) ∧
  ∀ v, ⟪D.ιt1 (D.dt0 (pφ V0 Vt0 Vt1 x)), D.ιt1 v⟫ + ⟪D.S1 (pu V0 Vt0 Vt1 x), D.S1 v⟫ +
    ⟪D.dt1 (pu V0 Vt0 Vt1 x), D.dt1 v⟫ = ⟪f, D.ιt1 v⟫

lemma aForm_split (x : Xsp V0 Vt0 Vt1) (τ : V0) (ψ : Vt0) (v : Vt1) :
    D.aForm x (mkX τ ψ v) =
      (⟪D.ι0 (pσ V0 Vt0 Vt1 x), D.ι0 τ⟫ - ⟪D.ιt1 (pu V0 Vt0 Vt1 x), D.ιt1 (D.dt0 ψ)⟫) +
      (⟪D.ιt1 (D.dt0 (pφ V0 Vt0 Vt1 x)), D.ιt1 v⟫ + ⟪D.S1 (pu V0 Vt0 Vt1 x), D.S1 v⟫ +
        ⟪D.dt1 (pu V0 Vt0 Vt1 x), D.dt1 v⟫) := by
  rw [aForm_apply]; simp only [pσ_mkX, pφ_mkX, pu_mkX]; ring

lemma bForm_mkX_of_mem {τ : V0} {ψ : Vt0} (v : Vt1) (hΓ : (τ, ψ) ∈ D.Γ) (μ : D.Wcheck) :
    D.bForm (mkX τ ψ v) μ = 0 := by
  have : pP V0 Vt0 Vt1 (mkX τ ψ v) ∈ D.Wcheckᗮ := (D.mem_orth_Wcheck_iff _).2 hΓ
  rw [bForm, Submodule.inner_left_of_mem_orthogonal μ.2 this, neg_zero]

lemma forall_bForm_eq_zero_iff (x : Xsp V0 Vt0 Vt1) :
    (∀ μ, D.bForm x μ = 0) ↔ (pσ V0 Vt0 Vt1 x, pφ V0 Vt0 Vt1 x) ∈ D.Γ := by
  rw [← D.mem_ker_Bs]
  show _ ↔ D.Bs x = 0
  constructor
  · intro hb
    exact ext_inner_right ℝ fun μ => by rw [inner_Bs, hb, inner_zero_left]
  · intro hb μ
    rw [← inner_Bs, hb, inner_zero_left]

/-- Thesis §5.1 (after (5.3)): a solution of (5.3) gives a solution of (5.2). -/
theorem reduced_of_saddle {f : Wt1} {x : Xsp V0 Vt0 Vt1} {l : D.Wcheck}
    (hs : D.Saddle f x l) : D.Reduced f x := by
  have hΓ := (D.forall_bForm_eq_zero_iff x).1 hs.2
  refine ⟨hΓ, fun τ ψ hτψ => ?_, fun v => ?_⟩
  · have e := hs.1 (mkX τ ψ 0)
    rw [D.bForm_mkX_of_mem 0 hτψ, D.aForm_split] at e
    simpa using e
  · have e := hs.1 (mkX 0 0 v)
    rw [D.bForm_mkX_of_mem v (by simp [D.mem_Γ]), D.aForm_split] at e
    simpa using e

/-- **(5.2) is a well-posed Hodge Laplacian** (thesis: asserted without proof): for every
`f ∈ W̃¹` it has exactly one solution. Uniqueness is the inf-sup of `a` on `Z`; existence comes
from (5.3).

See [QuennevilleBelair2015, §5.1, (5.2)]; cf. well-posedness of the mixed Hodge Laplacian
[AFW2010], [Arnold2018]. -/
theorem reduced_existsUnique (h : D.Hyps) (f : Wt1) : ∃! x, D.Reduced f x := by
  obtain ⟨⟨xl, hxl, -⟩, -⟩ := (D.prop_5_2 h).1 f, ()
  refine ⟨xl.1, D.reduced_of_saddle hxl, fun x' hx' => ?_⟩
  obtain ⟨γ, hγ, hZ⟩ := D.infSup_a h
  have hval : ∀ x : Xsp V0 Vt0 Vt1, D.Reduced f x → ∀ z ∈ D.Bs.ker,
      D.aForm x z = ⟪f, D.ιt1 (pu V0 Vt0 Vt1 z)⟫ := by
    intro x hx z hz
    rw [← mkX_eta z, D.aForm_split, hx.2.1 _ _ ((D.mem_ker_Bs z).1 hz), hx.2.2, zero_add]
    rfl
  have hd : x' - xl.1 ∈ D.Bs.ker := (D.mem_ker_Bs _).2 (by
    have := D.Γ.sub_mem hx'.1 (D.reduced_of_saddle hxl).1
    simpa using this)
  obtain ⟨z', hz', -, hle⟩ := hZ _ hd
  have h0 : D.aForm (x' - xl.1) z' = 0 := by
    rw [map_sub, sub_apply, hval x' hx' z' hz',
      hval xl.1 (D.reduced_of_saddle hxl) z' hz', sub_self]
  rw [h0] at hle
  have : ‖x' - xl.1‖ = 0 :=
    le_antisymm (by nlinarith [norm_nonneg (x' - xl.1)]) (norm_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- Thesis §5.1 (after (5.3)), converse direction made precise: a solution of (5.2) extends to a
solution of (5.3) with a **unique** multiplier `λ ∈ W̌¹`. -/
theorem existsUnique_multiplier (h : D.Hyps) {f : Wt1} {x : Xsp V0 Vt0 Vt1}
    (hx : D.Reduced f x) : ∃! l : D.Wcheck, D.Saddle f x l := by
  obtain ⟨xl, hxl, huniq⟩ := (D.prop_5_2 h).1 f
  have hx' : xl.1 = x :=
    (D.reduced_existsUnique h f).unique (D.reduced_of_saddle hxl) hx
  refine ⟨xl.2, hx' ▸ hxl, fun l hl => ?_⟩
  have := huniq (x, l) hl
  rw [← this]

/-- Thesis §5.1, (5.3) ↔ (5.2) plus multiplier equation: `(x, λ)` solves (5.3) iff `x` solves (5.2) and `λ` is
the (unique, `existsUnique_multiplier`) multiplier.

See [QuennevilleBelair2015, §5.1, (5.2)–(5.3)]. -/
theorem saddle_iff_reduced (f : Wt1) (x : Xsp V0 Vt0 Vt1) (l : D.Wcheck) :
    D.Saddle f x l ↔ D.Reduced f x ∧
      ∀ y, D.bForm y l = ⟪f, D.ιt1 (pu V0 Vt0 Vt1 y)⟫ - D.aForm x y := by
  constructor
  · intro hs
    exact ⟨D.reduced_of_saddle hs, fun y => by rw [← hs.1 y]; ring⟩
  · rintro ⟨hr, hm⟩
    exact ⟨fun y => by rw [hm y]; ring, (D.forall_bForm_eq_zero_iff x).2 hr.1⟩

/-- The system (5.3) *as written in the thesis*, with `λ, μ ∈ W¹`.

See [QuennevilleBelair2015, (5.3)]. -/
def Saddle53 (f : Wt1) (x : Xsp V0 Vt0 Vt1) (l : W1) : Prop :=
  (∀ y, D.aForm x y - ⟪l, D.ι1 (D.d0 (pσ V0 Vt0 Vt1 y) - D.S0 (pφ V0 Vt0 Vt1 y))⟫ =
    ⟪f, D.ιt1 (pu V0 Vt0 Vt1 y)⟫) ∧
  ∀ μ : W1, ⟪D.ι1 (D.d0 (pσ V0 Vt0 Vt1 x) - D.S0 (pφ V0 Vt0 Vt1 x)), μ⟫ = 0

/-- Consistency with the thesis' (5.3): a solution with `λ ∈ W¹` is the solution of `Saddle`
with multiplier `jW λ ∈ W̌¹` (in general no solution with `λ ∈ W¹` exists, which is why the
thesis' Prop 5.2 is stated over `W̌¹`). -/
theorem saddle_of_saddle53 {f : Wt1} {x : Xsp V0 Vt0 Vt1} {l : W1}
    (hs : D.Saddle53 f x l) : D.Saddle f x (D.jW l) := by
  refine ⟨fun y => by rw [D.bForm_jW, ← hs.1 y]; ring, (D.forall_bForm_eq_zero_iff x).2 ?_⟩
  have h0 := hs.2 (D.ι1 (D.d0 (pσ V0 Vt0 Vt1 x) - D.S0 (pφ V0 Vt0 Vt1 x)))
  rw [inner_self_eq_zero, map_sub, sub_eq_zero] at h0
  exact D.mem_Γ.2 (D.ι1_injective h0)

end BGGHilb

end Analytic

/-! ## Non-vacuity: a nontrivial instance of the hypotheses -/

section Example

/-- `c • id` on `ℝ` -/
def sc (c : ℝ) : ℝ →L[ℝ] ℝ := c • ContinuousLinearMap.id ℝ ℝ

@[simp] private lemma sc_apply (c x : ℝ) : sc c x = c * x := rfl

lemma sc_injective {c : ℝ} (hc : c ≠ 0) : Function.Injective (sc c) := fun x y h => by
  simpa [hc] using h

lemma sc_surjective {c : ℝ} (hc : c ≠ 0) : Function.Surjective (sc c) := fun y =>
  ⟨y / c, by simp [mul_div_cancel₀ _ hc]⟩

/-- A nontrivial BGG datum on `ℝ`: `ι⁰ = 3/5`, `d⁰ = 4/5` (graph norm `9/25 + 16/25 = 1`),
`d¹ = 0`, the same for the bottom complex, `S₀ = id`, `S₁ = 0`. Here `Γ = {(σ, 4σ/5)} ≠ 0`. -/
def exampleBGG : BGGHilb ℝ ℝ ℝ ℝ ℝ ℝ ℝ ℝ ℝ ℝ where
  ι0 := sc (3 / 5)
  ι1 := sc 1
  ιt0 := sc (3 / 5)
  ιt1 := sc 1
  ι0_injective := sc_injective (by norm_num)
  ι1_injective := sc_injective one_ne_zero
  ιt0_injective := sc_injective (by norm_num)
  ιt1_injective := sc_injective one_ne_zero
  dense0 := (sc_surjective (by norm_num)).denseRange
  dense1 := (sc_surjective one_ne_zero).denseRange
  denset0 := (sc_surjective (by norm_num)).denseRange
  denset1 := (sc_surjective one_ne_zero).denseRange
  d0 := sc (4 / 5)
  d1 := 0
  dt0 := sc (4 / 5)
  dt1 := 0
  S0 := sc 1
  S1 := 0
  graph0 u v := by simp; ring
  graph1 u v := by simp
  grapht0 u v := by simp; ring
  grapht1 u v := by simp
  d1_d0 _ := rfl
  dt1_dt0 _ := rfl
  anticomm _ := by simp

/-- Non-vacuity of the hypotheses of thesis Props 5.1 and 5.2: they are satisfiable with
`Γ ≠ 0`. -/
theorem exampleBGG_hyps :
    exampleBGG.Hyps ∧ Function.Injective exampleBGG.S0 ∧ ((1 : ℝ), (4 / 5 : ℝ)) ∈ exampleBGG.Γ := by
  refine ⟨⟨sc_injective (by norm_num), sc_injective (by norm_num), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    sc_injective one_ne_zero, ?_⟩
  · have : Set.range (exampleBGG.ι1 ∘L exampleBGG.d0) = Set.univ :=
      Set.range_eq_univ.2 fun y => ⟨y * (5 / 4), by simp [exampleBGG]; ring⟩
    rw [this]; exact isClosed_univ
  · have : Set.range (exampleBGG.ιt1 ∘L exampleBGG.dt0) = Set.univ :=
      Set.range_eq_univ.2 fun y => ⟨y * (5 / 4), by simp [exampleBGG]; ring⟩
    rw [this]; exact isClosed_univ
  · ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    exact ⟨fun _ => ⟨x * (5 / 4), by simp [BGGHilb.toBGGData, exampleBGG]; ring⟩, fun _ => rfl⟩
  · ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    exact ⟨fun _ => ⟨x * (5 / 4), by simp [BGGHilb.toBGGData, exampleBGG]; ring⟩, fun _ => rfl⟩
  · have : Set.range exampleBGG.d1 = {0} := by
      ext y; simp [exampleBGG]
    rw [this]; exact isClosed_singleton
  · have : Set.range exampleBGG.dt1 = {0} := by
      ext y; simp [exampleBGG]
    rw [this]; exact isClosed_singleton
  · rintro _ ⟨x, rfl⟩
    exact ⟨0, by simp [exampleBGG]⟩
  · rw [BGGHilb.mem_Γ]; simp [exampleBGG]

end Example

end Feec.Ch5.BGG
