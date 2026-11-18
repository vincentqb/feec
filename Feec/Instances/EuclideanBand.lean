module

public import Feec.HilbertComplex.Approximation.ApproxConforming
public import Feec.Fourier.SpectralGalerkin
public import Feec.Models.Euclidean.BGG
public import Feec.Models.Euclidean.DeRham
public import Feec.Instances.Maxwell
public import Feec.Instances.EinsteinBianchi

/-!
# Frequency truncation on `ℝᵈ` as a reducing family

On `ℝᵈ` a constant-coefficient complex is, after the `L²` Fourier transform (Plancherel,
`Feec.Fourier.Euclidean.fourier`), a symbol complex on `L²(ℝᵈ)` with symbols `m(2πx)`
(`Feec.Fourier.Euclidean.complex`). Its **frequency truncation** keeps the fields whose Fourier
transforms vanish at frequencies `|ξ| > N` (`ξ = 2πx`): `B_N = ∏ L²_{|ξ| ≤ N}`. This module makes
the frequency truncation a reducing family (`Feec.HilbertComplex.ReducingFamily`), for every
constant-coefficient complex on `ℝᵈ`, so that the FEEC theorem for reducing families
`Feec.HilbertComplex.ReducingFamily.feec` applies with every closed constraint, and reads it on
the linearized Einstein–Bianchi system (`ℝ³`, TSD constraint) and on Maxwell's equations (`ℝᵈ`,
every degree, Gauss laws).

**Generic layer.** A symbol bounded on a measurable band acts boundedly on band-limited fields,
and so does its fibrewise adjoint (`band_le_domain_d`, `norm_d_band_le`, `band_le_domain_adjoint`,
`norm_adjoint_band_le`); on such fields `L = 𝐝 - 𝐝†` is bounded (`norm_wave_le`, `band_wave`).
Hence every increasing exhausting sequence of measurable bands with bounded symbols is a reducing
family (`bandFamily`; reducing by `Feec.Fourier.reducingSubcomplex_band`, `P_N → 1` by
`Feec.Fourier.tendsto_totalProj_band`). On `ℝᵈ` the frequency balls
`freqBall N = {x | |2πx| ≤ N}` are compact, so continuous symbols are bounded on them (`bands`).
By `ReducingFamily.feec` the truncated solution is the truncation of the exact one, the error is
the truncation error of the datum at every time, and a reducing constraint that `P_N` maps into
itself is preserved exactly (identically zero residual). Fibrewise constraints
(`starProjection_band_mem_fibreSub`) and kernels of reduced operators (`starProjection_mem_ker`)
are such constraints.

**Sobolev rates.** `sobolev 𝕜 E s` is the class `Hˢ` on the Fourier side: `(1 + |ξ|)ˢ x̂ ∈ L²`
(`IsSobolevRep`, norm `sobolevNorm`; the weight `(1 + |ξ|)ˢ` is comparable to the Bessel weight
`(1 + |ξ|²)^{s/2}`, which is not formalized here). For `s ≥ 0` the truncation error is
`‖x - P_N x‖ ≤ (N + 1)^{-s} ‖x‖_{Hˢ}` (`norm_sub_starProjection_le`,
`norm_sub_starProjection_le_of_mem_sobolev`); with the error identity of `ReducingFamily.feec`
this is the time-uniform rate `‖e^{tL} x - ι_N e^{tL_N} π_N x‖ ≤ (N + 1)^{-s} ‖x‖_{Hˢ}`.

**Instances.**

* **The EB system on `ℝ³`** (BGG complex (5.1), TSD constraint `{0} × L²(TSD) × ({0} × L²(TSD))`):
  `ebBands`, `ebApprox`; `EuclideanEBVerdict` (`einsteinBianchi_euclidean_band`) extends the
  verdict of `ReducingFamily.feec`: TSD reduces `L` and the truncations preserve it (so the
  truncated solutions of TSD data are TSD), the truncation error on `Hˢ` is
  `≤ (N + 1)^{-s} ‖ξ₀‖_{Hˢ}`, and the exponent `s` is sharp on TSD data
  (`einsteinBianchi_euclidean_rate_optimal`, shell data `shellState N` with frequencies in
  `[N + 1, N + 1 + π]`, `shellState_nonvacuous`). Non-vacuity: the TSD fields
  `(1 + |ξ|)^r (a bᵀ + b aᵀ)(ξ)`, `a = (ξ₁, -ξ₀, 0)`, `b = ξ × a` (`ttMat`), `r < -9/2`, lie in
  `Hˢ` for `s < -r - 9/2`, are not band-limited for any `N`, and their truncated solutions have a
  positive error at every `N` and `t` (`decayState_nonvacuous`).
* **Maxwell's equations on `ℝᵈ`** (window `Λᵃ → Λᵃ⁺¹ → Λᵃ⁺²` of the de Rham complex, the Gauss
  laws `Feec.Instances.Maxwell.windowGauss`): `maxwellBands`, `maxwellApprox`;
  `EuclideanMaxwellVerdict` (`maxwell_euclidean_band`) extends the verdict of
  `ReducingFamily.feec`: the Gauss laws reduce `L` and the truncations preserve them, and the
  truncation error on `Hˢ` is `≤ (N + 1)^{-s} ‖ξ₀‖_{Hˢ}`.
  The vanishing-field constraint does not reduce `L`
  (`maxwell_euclidean_not_isReducing_potential`, `a < d`, through a cut-off constant field `u`
  with `d u ≠ 0`, `exists_band_d_ne_zero`), and its residuals along the truncated solutions tend
  to a positive limit (`maxwell_euclidean_potential_residual`, item 4 of `approxFEEC`,
  non-reducing branch).

## Scope and limits

* The bands `B_N` are reducing subcomplexes of `H` but **infinite-dimensional** (`L²` of a ball:
  the spectrum of `ℝᵈ` is continuous; this is not proved here), so the frequency truncation is
  not a `ConstrainedFEEC` discretization (finite-dimensional `Vₕ`) and `constrainedFEEC` does not
  apply to it; it is an `ApproxFEEC` through `ReducingFamily.toApprox`. It is a
  semi-discretization in frequency: a fully discrete method would also discretize the frequency
  ball (sampling or quadrature), which is not formalized.
* It commits no variational crime: `ι_N` is the inclusion and the consistency defect is `0`. The
  instances with a nonzero defect are the abstract witnesses of
  `Feec.HilbertComplex.Approximation.ApproxFEECWitness`. As `P_N` acts fibrewise and commutes
  with `d` and `d†`, it preserves TSD and the Gauss laws, so their constraint residuals vanish
  identically; only the non-reducing vanishing-field constraint of Maxwell's equations exercises
  the residual branch of `approxFEEC`.
* The sharpness of the exponent (`einsteinBianchi_euclidean_rate_optimal`) is uniform over the
  `Hˢ` data, through the shell data `shellState N` (one for each `N`); for a single datum the
  error is `o((N + 1)^{-s})`.
* The Sobolev classes are defined on the Fourier side, with the weight `(1 + |2πx|)ˢ`; the
  identification with the physical spaces `Hˢ(ℝᵈ)` (Plancherel and the equivalence of the
  weights) is not formalized here.
* The rate needs only `Hˢ` data for the order `s` (the truncation commutes with `L`); the spectral
  rows of `𝕋³` and of the mirror cube use `H^{2+s}` for the graph-norm rate of `constrainedFEEC`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.9 (Prop. 4.16), §4.12–4.13 (Galerkin approximation of the Hodge wave equation), Ch. 6
  (§6.3)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (approximation of Hilbert complexes)
* Mathlib, `Mathlib.Analysis.Fourier.LpSpace` (the `L²` Fourier transform, Plancherel)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Set Filter MeasureTheory LinearPMap Metric

@[expose] public noncomputable section

namespace Feec.Instances.EuclideanBand

open Feec.HilbertComplex Feec.Fourier

/-! ### Multipliers on band-limited fields -/

section Multiplier

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {m : α → E →L[𝕜] F} {A : Set α} {C : ℝ}

/-- A symbol bounded by `C` on `A` acts on fields vanishing off `A` with bound `max C 0`. -/
theorem ae_norm_apply_le (hC : ∀ᵐ a ∂μ, a ∈ A → ‖m a‖ ≤ C) {u : α → E}
    (hu : ∀ᵐ a ∂μ, a ∉ A → u a = 0) : ∀ᵐ a ∂μ, ‖m a (u a)‖ ≤ max C 0 * ‖u a‖ := by
  filter_upwards [hC, hu] with a h1 h2
  by_cases ha : a ∈ A
  · exact (m a).le_of_opNorm_le ((h1 ha).trans (le_max_left _ _)) _
  · rw [h2 ha, _root_.map_zero, norm_zero, norm_zero, mul_zero]

/-- Fields vanishing off a set where the symbol is bounded lie in the domain of the multiplier. -/
theorem mem_mulDomain_of_bound (hm : AEStronglyMeasurable m μ)
    (hC : ∀ᵐ a ∂μ, a ∈ A → ‖m a‖ ≤ C) {u : Lp E 2 μ} (hu : ∀ᵐ a ∂μ, a ∉ A → u a = 0) :
    u ∈ Operator.mulDomain μ m :=
  MemLp.of_le_mul (Lp.memLp u)
    (Operator.aestronglyMeasurable_clm_apply hm (Lp.aestronglyMeasurable u))
    (ae_norm_apply_le hC hu)

/-- The multiplier is bounded by `max C 0` on fields vanishing off `A`. -/
theorem norm_mulOp_le (hC : ∀ᵐ a ∂μ, a ∈ A → ‖m a‖ ≤ C) (u : (Operator.mulOp μ m).domain)
    (hu : ∀ᵐ a ∂μ, a ∉ A → (u : Lp E 2 μ) a = 0) :
    ‖Operator.mulOp μ m u‖ ≤ max C 0 * ‖(u : Lp E 2 μ)‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [Operator.coeFn_mulOp μ m u, ae_norm_apply_le hC hu] with a h1 h2
  rw [h1]; exact h2

theorem ae_norm_adjoint_le (hC : ∀ᵐ a ∂μ, a ∈ A → ‖m a‖ ≤ C) [CompleteSpace E] [CompleteSpace F] :
    ∀ᵐ a ∂μ, a ∈ A → ‖ContinuousLinearMap.adjoint (m a)‖ ≤ C :=
  hC.mono fun a h ha => by rw [LinearIsometryEquiv.norm_map]; exact h ha

end Multiplier

/-! ### Band-limited fields of symbol complexes -/

section Symbol

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
  {c : ComplexShape ι} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace 𝕜 (E i)] [∀ i, CompleteSpace (E i)] (S : SymbolComplex 𝕜 μ c E)
  {A : Set α} {C : ℝ} {i j : ι}

/-- **Band-limited fields lie in `D(d)`** where the symbol is bounded on the band. -/
theorem band_le_domain_d (hC : ∀ᵐ a ∂μ, a ∈ A → ‖S.m i j a‖ ≤ C) :
    S.band A i ≤ (S.toHilbertComplex.d i j).domain := fun _ hu =>
  mem_mulDomain_of_bound (S.meas i j) hC (mem_band_iff.1 hu)

theorem norm_d_band_le (hC : ∀ᵐ a ∂μ, a ∈ A → ‖S.m i j a‖ ≤ C)
    (u : (S.toHilbertComplex.d i j).domain) (hu : (u : Lp (E i) 2 μ) ∈ S.band A i) :
    ‖S.toHilbertComplex.d i j u‖ ≤ max C 0 * ‖(u : Lp (E i) 2 μ)‖ :=
  norm_mulOp_le hC u (mem_band_iff.1 hu)

/-- **Band-limited fields lie in `D(d†)`** where the symbol is bounded on the band. -/
theorem band_le_domain_adjoint (hC : ∀ᵐ a ∂μ, a ∈ A → ‖S.m i j a‖ ≤ C) :
    S.band A j ≤ ((S.toHilbertComplex.d i j)†).domain := fun _ hu => by
  rw [S.adjoint_d]
  exact mem_mulDomain_of_bound (Operator.aestronglyMeasurable_adjoint (S.meas i j))
    (ae_norm_adjoint_le hC) (mem_band_iff.1 hu)

theorem norm_adjoint_band_le (hC : ∀ᵐ a ∂μ, a ∈ A → ‖S.m i j a‖ ≤ C)
    (v : ((S.toHilbertComplex.d i j)†).domain) (hv : (v : Lp (E j) 2 μ) ∈ S.band A j) :
    ‖(S.toHilbertComplex.d i j)† v‖ ≤ max C 0 * ‖(v : Lp (E j) 2 μ)‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [Operator.coeFn_adjoint_mulOp (S.meas i j) v,
    ae_norm_apply_le (ae_norm_adjoint_le hC) (mem_band_iff.1 hv)] with a h1 h2
  exact (congrArg norm h1).le.trans h2

end Symbol


/-! ### Bounded wave operators on subspaces -/

section Wave

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W) (B : ∀ i, Submodule 𝕜 (W i))

/-- `∏ Bᵢ ⊆ D(L)` when every `Bᵢ` lies in the domains of the differentials and their adjoints. -/
theorem totalSub_le_wave_domain (h1 : ∀ i j, B i ≤ (H.d i j).domain)
    (h2 : ∀ i j, B j ≤ ((H.d i j)†).domain) : totalSub B ≤ H.wave.domain := fun _ hx =>
  H.mem_wave_domain.2 ⟨fun i j => h1 i j (hx i), fun i j => h2 i j (hx j)⟩

/-- **`L` is bounded on `∏ Bᵢ`** when the differentials and their adjoints are bounded by `C` on
the `Bᵢ`: `‖L x‖ ≤ 2 n² C ‖x‖`, `n = #ι`. -/
theorem norm_wave_le {C : ℝ} (hC : 0 ≤ C)
    (h1 : ∀ i j (u : (H.d i j).domain), (u : W i) ∈ B i → ‖H.d i j u‖ ≤ C * ‖(u : W i)‖)
    (h2 : ∀ i j (v : ((H.d i j)†).domain), (v : W j) ∈ B j →
      ‖(H.d i j)† v‖ ≤ C * ‖(v : W j)‖)
    (x : H.wave.domain) (hx : (x : PiLp 2 W) ∈ totalSub B) :
    ‖H.wave x‖ ≤ 2 * (Fintype.card ι : ℝ) ^ 2 * C * ‖(x : PiLp 2 W)‖ := by
  set n : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hn_def
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hX := norm_nonneg (x : PiLp 2 W)
  have hj : ∀ j, ‖(H.wave x) j‖ ≤ 2 * n * C * ‖(x : PiLp 2 W)‖ := fun j => by
    rw [wave_apply]
    have e1 : ‖∑ i, H.d i j ⟨(x : PiLp 2 W) i, x.2.1 i j⟩‖ ≤ n * (C * ‖(x : PiLp 2 W)‖) := by
      refine (norm_sum_le _ _).trans ?_
      have := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
        (h1 i j ⟨(x : PiLp 2 W) i, x.2.1 i j⟩ (hx i)).trans
          (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (x : PiLp 2 W) i) hC)
      simpa [n, Finset.sum_const, Finset.card_univ] using this
    have e2 : ‖∑ k, (H.d j k)† ⟨(x : PiLp 2 W) k, x.2.2 k j⟩‖ ≤ n * (C * ‖(x : PiLp 2 W)‖) := by
      refine (norm_sum_le _ _).trans ?_
      have := Finset.sum_le_sum (s := Finset.univ) fun k _ =>
        (h2 j k ⟨(x : PiLp 2 W) k, x.2.2 k j⟩ (hx k)).trans
          (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (x : PiLp 2 W) k) hC)
      simpa [n, Finset.sum_const, Finset.card_univ] using this
    linarith [norm_sub_le (∑ i, H.d i j ⟨(x : PiLp 2 W) i, x.2.1 i j⟩)
      (∑ k, (H.d j k)† ⟨(x : PiLp 2 W) k, x.2.2 k j⟩)]
  have hsq : ‖H.wave x‖ ^ 2 ≤ (2 * n ^ 2 * C * ‖(x : PiLp 2 W)‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    have hM : 0 ≤ 2 * n * C * ‖(x : PiLp 2 W)‖ := by positivity
    calc ∑ j, ‖(H.wave x) j‖ ^ 2 ≤ ∑ _j : ι, (2 * n * C * ‖(x : PiLp 2 W)‖) ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hj j) 2
      _ = n * (2 * n * C * ‖(x : PiLp 2 W)‖) ^ 2 := by simp [n, Finset.sum_const]
      _ ≤ n ^ 2 * (2 * n * C * ‖(x : PiLp 2 W)‖) ^ 2 := by
          have : n ≤ n ^ 2 := by
            change ((Fintype.card ι : ℕ) : ℝ) ≤ ((Fintype.card ι : ℕ) : ℝ) ^ 2
            exact_mod_cast Nat.le_self_pow two_ne_zero _
          exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = (2 * n ^ 2 * C * ‖(x : PiLp 2 W)‖) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq

end Wave

/-! ### The band family of a symbol complex -/

section BandFamily

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
  [Fintype ι] {c : ComplexShape ι} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace 𝕜 (E i)] [∀ i, CompleteSpace (E i)] (S : SymbolComplex 𝕜 μ c E)

omit [∀ i, CompleteSpace (E i)] in
/-- A uniform bound over the (finitely many) symbols on a band. -/
theorem exists_bound_band {A : Set α} (hbd : ∀ i j, ∃ C, ∀ᵐ a ∂μ, a ∈ A → ‖S.m i j a‖ ≤ C) :
    ∃ C, 0 ≤ C ∧ ∀ i j, ∀ᵐ a ∂μ, a ∈ A → ‖S.m i j a‖ ≤ C := by
  choose C hC using hbd
  refine ⟨∑ i, ∑ j, max (C i j) 0, by positivity, fun i j => (hC i j).mono fun a h ha => ?_⟩
  refine (h ha).trans ((le_max_left (C i j) 0).trans ?_)
  refine (Finset.single_le_sum (f := fun j => max (C i j) 0) (fun _ _ => le_max_right _ _)
    (Finset.mem_univ j)).trans ?_
  exact Finset.single_le_sum (f := fun i => ∑ j, max (C i j) 0)
    (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_univ i)

variable {S} in
/-- On a band where all symbols are bounded, the band-limited fields lie in `D(L)` and `L` is
bounded on them. -/
theorem band_wave {A : Set α} (hbd : ∀ i j, ∃ C, ∀ᵐ a ∂μ, a ∈ A → ‖S.m i j a‖ ≤ C) :
    totalSub (S.band A) ≤ S.toHilbertComplex.wave.domain ∧
      ∃ C, ∀ x (hx : x ∈ S.toHilbertComplex.wave.domain), x ∈ totalSub (S.band A) →
        ‖S.toHilbertComplex.wave ⟨x, hx⟩‖ ≤ C * ‖x‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_band S hbd
  refine ⟨totalSub_le_wave_domain _ _ (fun i j => band_le_domain_d S (hC i j))
    (fun i j => band_le_domain_adjoint S (hC i j)), 2 * (Fintype.card ι : ℝ) ^ 2 * C,
    fun x hx hxB => norm_wave_le _ _ hC0 (fun i j u hu => ?_) (fun i j v hv => ?_) ⟨x, hx⟩ hxB⟩
  · have := norm_d_band_le S (hC i j) u hu
    rwa [max_eq_left hC0] at this
  · have := norm_adjoint_band_le S (hC i j) v hv
    rwa [max_eq_left hC0] at this

/-- **The band-truncation family of a symbol complex**: for an increasing exhausting sequence of
measurable bands `A N` on which all symbols are bounded, the band-limited fields
`B_N = ∏ L²_{A N}` form a reducing family (closed reducing subspaces in `D(L)`, `L` bounded on
them, truncations converging strongly to `1`). The bands need not be finite-dimensional. -/
def bandFamily (A : ℕ → Set α) (hA : ∀ N, MeasurableSet (A N)) (hmono : Monotone A)
    (hcov : ∀ a, ∃ N, a ∈ A N) (hbd : ∀ N i j, ∃ C, ∀ᵐ a ∂μ, a ∈ A N → ‖S.m i j a‖ ≤ C) :
    ReducingFamily S.toHilbertComplex ℕ :=
  haveI := fun N i => hasOrthogonalProjection_band S (hA N) i
  { B := fun N => totalSub (S.band (A N))
    completeSpace := fun _ => isClosed_totalSub.completeSpace_coe
    l := atTop
    isReducing := fun N => (reducingSubcomplex_band S (hA N)).isReducing_wave
    le_domain := fun N => (band_wave (hbd N)).1
    bounded := fun N => (band_wave (hbd N)).2
    tendsto := fun x => tendsto_totalProj_band S hA hmono hcov x }

end BandFamily

/-! ### Constraints preserved by band truncation -/

section Invariance

/-- A reducing pair `(K, L)` of `T` maps `N(T)` into itself under `P_K`. -/
theorem starProjection_mem_ker {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {T : E →ₗ.[𝕜] F}
    {K : Submodule 𝕜 E} {L : Submodule 𝕜 F} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (h : T.IsReducingPair K L) {x : E} (hx : x ∈ T.ker) :
    K.starProjection x ∈ T.ker := by
  obtain ⟨y, rfl, hy⟩ := LinearPMap.mem_ker_iff.1 hx
  exact LinearPMap.mem_ker_iff.2 ⟨⟨_, h.proj_mem y⟩, rfl, by rw [h.comm, hy, _root_.map_zero]⟩

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
  {c : ComplexShape ι} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace 𝕜 (E i)] [∀ i, CompleteSpace (E i)] (S : SymbolComplex 𝕜 μ c E)
  {A : Set α} [∀ i, (S.band A i).HasOrthogonalProjection]

omit [∀ i, CompleteSpace (E i)] in
/-- **The band truncation preserves every fibrewise constraint**: `P_A` multiplies by `𝟙_A`
fibrewise, and `𝟙_A(a) u(a) ∈ {u(a), 0} ⊆ V(a)`. -/
theorem starProjection_band_mem_fibreSub (hA : MeasurableSet A) {i : ι}
    {V : α → Submodule 𝕜 (E i)} {u : Lp (E i) 2 μ} (hu : u ∈ Operator.fibreSub μ V) :
    (S.band A i).starProjection u ∈ Operator.fibreSub μ V := by
  rw [Operator.mem_fibreSub] at hu ⊢
  filter_upwards [Operator.coeFn_starProjection_fibreSub (μ := μ)
      (bandFibre (𝕜 := 𝕜) (E := E) A i) (aestronglyMeasurable_starProjection_bandFibre hA i) u,
    hu] with a h1 h2
  rw [h1, starProjection_bandFibre]
  by_cases ha : a ∈ A
  · rw [Operator.cutoff_apply_of_mem ha]; exact h2
  · rw [Operator.cutoff_apply_of_notMem ha]; exact (V a).zero_mem

omit [∀ i, CompleteSpace (E i)] in
/-- The band truncation preserves a product constraint whose factors it preserves. -/
theorem starProjection_totalSub_band_mem [Fintype ι] {F : ∀ i, Submodule 𝕜 (Lp (E i) 2 μ)}
    (hF : ∀ i, ∀ u ∈ F i, (S.band A i).starProjection u ∈ F i)
    {x : PiLp 2 fun i => Lp (E i) 2 μ} (hx : x ∈ totalSub F) :
    (totalSub (S.band A)).starProjection x ∈ totalSub F := fun i => by
  rw [totalSub_starProjection_apply]; exact hF i _ (hx i)

end Invariance

/-! ### Frequency balls of `ℝᵈ` -/

section FreqBall

variable {d : Type*} [Fintype d]

/-- The **frequency ball** `{x | |2πx| ≤ N}` of the Fourier model (`2πx` is the frequency of the
point `x` of Fourier space, `Feec.Fourier.Euclidean.scale`). -/
def freqBall (N : ℕ) : Set (EuclideanSpace ℝ d) := {x | ‖Euclidean.scale x‖ ≤ N}

theorem mem_freqBall {N : ℕ} {x : EuclideanSpace ℝ d} :
    x ∈ freqBall N ↔ ‖Euclidean.scale x‖ ≤ N := Iff.rfl

theorem norm_scale (x : EuclideanSpace ℝ d) : ‖Euclidean.scale x‖ = 2 * Real.pi * ‖x‖ := by
  rw [Euclidean.scale, norm_smul, Real.norm_of_nonneg (by positivity)]

theorem isClosed_freqBall (N : ℕ) : IsClosed (freqBall (d := d) N) :=
  isClosed_le (continuous_norm.comp Euclidean.continuous_scale) continuous_const

theorem measurableSet_freqBall (N : ℕ) : MeasurableSet (freqBall (d := d) N) :=
  (isClosed_freqBall N).measurableSet

theorem freqBall_mono : Monotone (freqBall (d := d)) := fun _ _ h _ hx =>
  mem_freqBall.2 ((mem_freqBall.1 hx).trans (by exact_mod_cast h))

theorem exists_mem_freqBall (x : EuclideanSpace ℝ d) : ∃ N, x ∈ freqBall N :=
  (exists_nat_ge ‖Euclidean.scale x‖).imp fun _ h => mem_freqBall.2 h

theorem isCompact_freqBall (N : ℕ) : IsCompact (freqBall (d := d) N) := by
  refine (isCompact_closedBall (0 : EuclideanSpace ℝ d) (N / (2 * Real.pi))).of_isClosed_subset
    (isClosed_freqBall N) fun x hx => ?_
  rw [mem_closedBall_zero_iff, le_div_iff₀ (by positivity)]
  have := hx
  rw [mem_freqBall, norm_scale] at this
  linarith

/-- Continuous functions are bounded on frequency balls. -/
theorem exists_bound_freqBall {F : Type*} [SeminormedAddCommGroup F]
    {g : EuclideanSpace ℝ d → F} (hg : Continuous g) (N : ℕ) :
    ∃ C, ∀ x ∈ freqBall N, ‖g x‖ ≤ C :=
  (isCompact_freqBall N).exists_bound_of_continuousOn hg.continuousOn

end FreqBall

/-! ### Frequency truncation of constant-coefficient complexes on `ℝᵈ` -/

section Bands

variable {𝕜 : Type*} [RCLike 𝕜] {d : Type*} [Fintype d] {ι : Type*} [Fintype ι]
  {c : ComplexShape ι} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace 𝕜 (E i)] [∀ i, CompleteSpace (E i)]

instance instHasOrthogonalProjectionBand
    (S : SymbolComplex 𝕜 (volume : Measure (EuclideanSpace ℝ d)) c E) (N : ℕ) (i : ι) :
    (S.band (freqBall N) i).HasOrthogonalProjection :=
  hasOrthogonalProjection_band S (measurableSet_freqBall N) i

/-- **The frequency-truncation family of a symbol complex on `ℝᵈ`** with continuous symbols:
`B_N = ∏ L²_{|2πx| ≤ N}`, the fields whose Fourier transforms vanish at frequencies `|ξ| > N`.
Each `B_N` is closed, reducing and infinite-dimensional (`L²` of a ball), `L` is bounded on it
(continuous symbols are bounded on the compact frequency ball), and `P_N → 1` strongly. -/
def bands (S : SymbolComplex 𝕜 (volume : Measure (EuclideanSpace ℝ d)) c E)
    (hS : ∀ i j, Continuous (S.m i j)) : ReducingFamily S.toHilbertComplex ℕ :=
  bandFamily S freqBall measurableSet_freqBall freqBall_mono exists_mem_freqBall fun N i j =>
    (exists_bound_freqBall (hS i j) N).imp fun _ hC => ae_of_all _ fun x hx => hC x hx

omit [Fintype ι] [∀ i, CompleteSpace (E i)] in
/-- The symbols of the whole-space model of a continuous fibre complex are continuous. -/
theorem continuous_symbolComplex_m [∀ i, FiniteDimensional 𝕜 (E i)]
    (S : FibreComplex 𝕜 (EuclideanSpace ℝ d) c E) (i j : ι) :
    Continuous ((Euclidean.symbolComplex S).m i j) :=
  (S.cont i j).comp Euclidean.continuous_scale

end Bands

/-! ### Sobolev classes on the Fourier side -/

section Sobolev

variable {d : Type*} [Fintype d]

/-- The Bessel-type weight `(1 + |2πx|)ˢ`, `ξ = 2πx` (comparable to `(1 + |ξ|²)^{s/2}`; the
comparison is not formalized). -/
def weight (s : ℝ) (x : EuclideanSpace ℝ d) : ℝ := (1 + ‖Euclidean.scale x‖) ^ s

theorem one_le_one_add_norm (x : EuclideanSpace ℝ d) : 1 ≤ 1 + ‖Euclidean.scale x‖ :=
  le_add_of_nonneg_right (norm_nonneg _)

theorem weight_pos (s : ℝ) (x : EuclideanSpace ℝ d) : 0 < weight s x :=
  Real.rpow_pos_of_pos (by linarith [one_le_one_add_norm x]) s

theorem continuous_weight (s : ℝ) : Continuous (weight (d := d) s) :=
  (continuous_const.add (continuous_norm.comp Euclidean.continuous_scale)).rpow_const
    fun x => Or.inl (ne_of_gt (by
      change 0 < 1 + ‖Euclidean.scale x‖; linarith [one_le_one_add_norm x]))

theorem weight_add (s s' : ℝ) (x : EuclideanSpace ℝ d) :
    weight (s + s') x = weight s x * weight s' x :=
  Real.rpow_add (by linarith [one_le_one_add_norm x]) s s'

/-- Off the frequency ball `|ξ| ≤ N` the weight of order `-s ≤ 0` is at most `(N + 1)^{-s}`. -/
theorem weight_neg_le {s : ℝ} (hs : 0 ≤ s) {N : ℕ} {x : EuclideanSpace ℝ d}
    (hx : x ∉ freqBall N) : weight (-s) x ≤ (1 / ((N : ℝ) + 1)) ^ s := by
  have hlt : (N : ℝ) < ‖Euclidean.scale x‖ := lt_of_not_ge hx
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [weight, Real.rpow_neg (by linarith [one_le_one_add_norm x]), Real.div_rpow zero_le_one hN.le,
    Real.one_rpow, one_div]
  exact inv_anti₀ (Real.rpow_pos_of_pos hN s)
    (Real.rpow_le_rpow hN.le (by linarith) hs)

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]

variable (𝕜) in
/-- `y` represents `x` in the **Sobolev class `Hˢ`** (Fourier side): `x(ξ) = (1 + |2πξ|)^{-s} y(ξ)`
with `y ∈ L²`, i.e. `(1 + |2πξ|)ˢ x ∈ L²`, with `‖x‖_{Hˢ} = ‖y‖`. -/
def IsSobolevRep (s : ℝ)
    (x y : PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d))) : Prop :=
  ∀ i, ∀ᵐ ξ ∂(volume : Measure (EuclideanSpace ℝ d)),
    (x i : EuclideanSpace ℝ d → E i) ξ =
      ((weight (-s) ξ : ℝ) : 𝕜) • (y i : EuclideanSpace ℝ d → E i) ξ

omit [Fintype ι] in
theorem IsSobolevRep.unique {s : ℝ}
    {x y y' : PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d))}
    (h : IsSobolevRep 𝕜 s x y) (h' : IsSobolevRep 𝕜 s x y') : y = y' := by
  refine PiLp.ext fun i => Lp.ext ?_
  filter_upwards [h i, h' i] with ξ h1 h2
  have hw : ((weight (-s) ξ : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (weight_pos _ ξ).ne'
  exact smul_right_injective (E i) hw (h1.symm.trans h2)

variable (𝕜 E) in
/-- **The Sobolev class `Hˢ`** of fields `x` with `(1 + |2πξ|)ˢ x̂ ∈ L²` (Fourier side). -/
def sobolev (s : ℝ) : Set (PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d))) :=
  {x | ∃ y, IsSobolevRep 𝕜 s x y}

variable (𝕜) in
open Classical in
/-- **The Sobolev norm** `‖x‖_{Hˢ} = ‖(1 + |2πξ|)ˢ x‖_{L²}` (`0` off the class). -/
def sobolevNorm (s : ℝ) (x : PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d))) :
    ℝ :=
  if h : ∃ y, IsSobolevRep 𝕜 s x y then ‖h.choose‖ else 0

theorem sobolevNorm_eq {s : ℝ}
    {x y : PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d))}
    (h : IsSobolevRep 𝕜 s x y) : sobolevNorm 𝕜 s x = ‖y‖ := by
  unfold sobolevNorm
  split_ifs with he
  · rw [he.choose_spec.unique h]
  · exact absurd ⟨y, h⟩ he

theorem sobolevNorm_nonneg (s : ℝ)
    (x : PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d))) :
    0 ≤ sobolevNorm 𝕜 s x := by
  unfold sobolevNorm; split_ifs <;> simp

omit [Fintype ι] in
/-- Sobolev representatives of single-component fields. -/
theorem isSobolevRep_single [DecidableEq ι] {s : ℝ} {i : ι}
    {u v : Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d))}
    (h : ∀ᵐ ξ ∂(volume : Measure (EuclideanSpace ℝ d)),
      (u : EuclideanSpace ℝ d → E i) ξ = ((weight (-s) ξ : ℝ) : 𝕜) • (v : _ → E i) ξ) :
    IsSobolevRep 𝕜 s (PiLp.single 2 i u) (PiLp.single 2 i v) := fun j => by
  by_cases hj : j = i
  · subst hj; rw [PiLp.single_eq_same, PiLp.single_eq_same]; exact h
  · rw [PiLp.single_eq_of_ne (p := 2) hj, PiLp.single_eq_of_ne (p := 2) hj]
    filter_upwards [Lp.coeFn_zero (E j) 2 (volume : Measure (EuclideanSpace ℝ d))] with ξ h0
    rw [h0, Pi.zero_apply, smul_zero]

variable [∀ i, CompleteSpace (E i)] {c : ComplexShape ι}
  (S : SymbolComplex 𝕜 (volume : Measure (EuclideanSpace ℝ d)) c E)

/-- **The truncation estimate**: for `x ∈ Hˢ`, `s ≥ 0`,
`‖x - P_N x‖ ≤ (N + 1)^{-s} ‖x‖_{Hˢ}` (`P_N` the frequency truncation `|ξ| ≤ N`). -/
theorem norm_sub_starProjection_le {s : ℝ} (hs : 0 ≤ s)
    {x y : PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d))}
    (h : IsSobolevRep 𝕜 s x y) (N : ℕ) :
    ‖x - (totalSub (S.band (freqBall N))).starProjection x‖ ≤ (1 / ((N : ℝ) + 1)) ^ s * ‖y‖ := by
  have := fun i => hasOrthogonalProjection_band S (measurableSet_freqBall N) i
  set c : ℝ := (1 / ((N : ℝ) + 1)) ^ s
  have hc : 0 ≤ c := by positivity
  have hi : ∀ i, ‖(x - (totalSub (S.band (freqBall N))).starProjection x) i‖ ≤ c * ‖y i‖ :=
    fun i => by
      rw [PiLp.sub_apply, totalSub_starProjection_apply]
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [Lp.coeFn_sub (x i) ((S.band (freqBall N) i).starProjection (x i)),
        Operator.coeFn_starProjection_fibreSub (μ := volume)
          (bandFibre (𝕜 := 𝕜) (E := E) (freqBall N) i)
          (aestronglyMeasurable_starProjection_bandFibre (measurableSet_freqBall N) i) (x i),
        h i] with ξ h1 h2 h3
      rw [h1, Pi.sub_apply, h2, starProjection_bandFibre]
      by_cases hξ : ξ ∈ freqBall N
      · rw [Operator.cutoff_apply_of_mem hξ, sub_self, norm_zero]; positivity
      · rw [Operator.cutoff_apply_of_notMem hξ, sub_zero, h3, norm_smul, RCLike.norm_ofReal,
          abs_of_pos (weight_pos _ ξ)]
        exact mul_le_mul_of_nonneg_right (weight_neg_le hs hξ) (norm_nonneg _)
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hi i) 2

/-- **The truncation estimate on the Sobolev class**: `‖x - P_N x‖ ≤ (N + 1)^{-s} ‖x‖_{Hˢ}` for
`x ∈ Hˢ`, `s ≥ 0`. -/
theorem norm_sub_starProjection_le_of_mem_sobolev {s : ℝ} (hs : 0 ≤ s)
    {x : PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d))}
    (hx : x ∈ sobolev 𝕜 E s) (N : ℕ) :
    ‖x - (totalSub (S.band (freqBall N))).starProjection x‖ ≤
      (1 / ((N : ℝ) + 1)) ^ s * sobolevNorm 𝕜 s x := by
  obtain ⟨y, hy⟩ := hx
  rw [sobolevNorm_eq hy]
  exact norm_sub_starProjection_le S hs hy N

end Sobolev

/-! ### Explicit band-limited fields (non-vacuity) -/

section Witness

variable {d : Type*} [Fintype d] {F : Type*} [NormedAddCommGroup F]

/-- A compact set of Fourier space lies in some frequency ball. -/
theorem exists_subset_freqBall {U : Set (EuclideanSpace ℝ d)} (hU : IsCompact U) :
    ∃ N, U ⊆ freqBall N := by
  obtain ⟨C, hC⟩ := hU.exists_bound_of_continuousOn
    (Euclidean.continuous_scale (d := d)).continuousOn
  obtain ⟨N, hN⟩ := exists_nat_ge C
  exact ⟨N, fun x hx => mem_freqBall.2 ((hC x hx).trans hN)⟩

/-- A function that does not vanish at `x₀` does not vanish on a closed ball around it. -/
theorem exists_closedBall_ne_zero {G : Type*} [TopologicalSpace G] [Zero G] [T2Space G]
    {g : EuclideanSpace ℝ d → G} (hg : Continuous g) {x₀ : EuclideanSpace ℝ d} (h : g x₀ ≠ 0) :
    ∃ r > 0, ∀ x ∈ closedBall x₀ r, g x ≠ 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_ne_fun hg continuous_const) x₀ h
  exact ⟨ε / 2, half_pos hε, fun x hx => hball (closedBall_subset_ball (half_lt_self hε) hx)⟩

theorem memLp_indicator_of_isCompact {U : Set (EuclideanSpace ℝ d)} (hU : IsCompact U)
    {g : EuclideanSpace ℝ d → F} (hg : Continuous g) :
    MemLp (U.indicator g) 2 (volume : Measure (EuclideanSpace ℝ d)) := by
  have : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ d)).restrict U) :=
    isFiniteMeasure_restrict.2 hU.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hU.exists_bound_of_continuousOn hg.continuousOn
  refine (memLp_indicator_iff_restrict hU.isClosed.measurableSet.nullMeasurableSet).2
    (MemLp.of_bound hg.aestronglyMeasurable C ?_)
  exact ae_restrict_of_forall_mem hU.isClosed.measurableSet hC

/-- The `L²` field `𝟙_U g` of a continuous `g` and a compact `U`. -/
def indicatorField (U : Set (EuclideanSpace ℝ d)) (hU : IsCompact U)
    (g : EuclideanSpace ℝ d → F) (hg : Continuous g) :
    Lp F 2 (volume : Measure (EuclideanSpace ℝ d)) :=
  (memLp_indicator_of_isCompact hU hg).toLp _

theorem coeFn_indicatorField {U : Set (EuclideanSpace ℝ d)} (hU : IsCompact U)
    {g : EuclideanSpace ℝ d → F} (hg : Continuous g) :
    (indicatorField U hU g hg : EuclideanSpace ℝ d → F) =ᵐ[volume] U.indicator g :=
  (memLp_indicator_of_isCompact hU hg).coeFn_toLp

/-- An `L²` field a.e. equal to a function not vanishing on a set of positive measure is not
zero. -/
theorem Lp_ne_zero_of_ae_eq {u : Lp F 2 (volume : Measure (EuclideanSpace ℝ d))}
    {g : EuclideanSpace ℝ d → F} (hug : (u : EuclideanSpace ℝ d → F) =ᵐ[volume] g)
    {U : Set (EuclideanSpace ℝ d)} (hpos : 0 < volume U) (hne : ∀ x ∈ U, g x ≠ 0) : u ≠ 0 := by
  rintro rfl
  have h0 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ d)), g x = 0 := by
    filter_upwards [hug, Lp.coeFn_zero F 2 (volume : Measure (EuclideanSpace ℝ d))] with x h1 h2
    rw [← h1, h2]; rfl
  exact hpos.ne' (measure_mono_null (fun x hx => hne x hx) (ae_iff.1 h0))

theorem indicatorField_ne_zero {U : Set (EuclideanSpace ℝ d)} (hU : IsCompact U)
    {g : EuclideanSpace ℝ d → F} (hg : Continuous g) (hpos : 0 < volume U)
    (hne : ∀ x ∈ U, g x ≠ 0) : indicatorField U hU g hg ≠ 0 :=
  Lp_ne_zero_of_ae_eq (coeFn_indicatorField hU hg) hpos fun x hx => by
    rw [indicator_of_mem hx]; exact hne x hx

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)] [∀ i, CompleteSpace (E i)]
  (S : SymbolComplex 𝕜 (volume : Measure (EuclideanSpace ℝ d)) c E)

omit [∀ i, CompleteSpace (E i)] in
theorem indicatorField_mem_band {U : Set (EuclideanSpace ℝ d)} (hU : IsCompact U) {i : ι}
    {g : EuclideanSpace ℝ d → E i} (hg : Continuous g) {N : ℕ} (hUN : U ⊆ freqBall N) :
    indicatorField U hU g hg ∈ S.band (freqBall N) i := by
  rw [mem_band_iff]
  filter_upwards [coeFn_indicatorField hU hg] with x hx hxN
  rw [hx, indicator_of_notMem fun h => hxN (hUN h)]

/-- The differential of a band-limited field is not zero when the symbol does not annihilate it
on a set of positive measure. -/
theorem d_ne_zero_of_ae_eq {i j : ι} (u : (S.toHilbertComplex.d i j).domain)
    {g : EuclideanSpace ℝ d → E i}
    (hug : ((u : Lp (E i) 2 volume) : EuclideanSpace ℝ d → E i) =ᵐ[volume] g)
    {U : Set (EuclideanSpace ℝ d)} (hpos : 0 < volume U) (hne : ∀ x ∈ U, S.m i j x (g x) ≠ 0) :
    S.toHilbertComplex.d i j u ≠ 0 := by
  refine Lp_ne_zero_of_ae_eq (g := fun x => S.m i j x (g x)) ?_ hpos hne
  filter_upwards [S.coeFn_d u, hug] with x h1 h2
  rw [h1, h2]

/-- **Every nonzero continuous symbol acts nontrivially on band-limited fields**: if
`m i j ≠ 0`, some band-limited `u` (a cut-off constant field) has `d u ≠ 0`. -/
theorem exists_band_d_ne_zero (hS : ∀ i j, Continuous (S.m i j)) {i j : ι}
    (hne : S.m i j ≠ 0) :
    ∃ N, ∃ u ∈ S.band (freqBall N) i, ∃ hu : u ∈ (S.toHilbertComplex.d i j).domain,
      S.toHilbertComplex.d i j ⟨u, hu⟩ ≠ 0 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, S.m i j x₀ ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  obtain ⟨v, hv⟩ : ∃ v, S.m i j x₀ v ≠ 0 := by
    by_contra h; push Not at h; exact hx₀ (ContinuousLinearMap.ext h)
  obtain ⟨r, hr, hball⟩ := exists_closedBall_ne_zero ((hS i j).clm_apply continuous_const) hv
  have hU : IsCompact (closedBall x₀ r) := isCompact_closedBall x₀ r
  obtain ⟨N, hN⟩ := exists_subset_freqBall hU
  set u := indicatorField (closedBall x₀ r) hU (fun _ => v) continuous_const
  have hub : u ∈ S.band (freqBall N) i := indicatorField_mem_band S hU continuous_const hN
  obtain ⟨C, hC⟩ := exists_bound_freqBall (hS i j) N
  have hud : u ∈ (S.toHilbertComplex.d i j).domain :=
    band_le_domain_d S (C := C) (ae_of_all _ fun x hx => hC x hx) hub
  refine ⟨N, u, hub, hud, d_ne_zero_of_ae_eq S ⟨u, hud⟩ (coeFn_indicatorField hU continuous_const)
    (Metric.measure_closedBall_pos volume x₀ hr) fun x hx => ?_⟩
  rw [indicator_of_mem hx]; exact hball x hx

end Witness

/-! ### The linearized Einstein–Bianchi system on `ℝ³` -/

section EinsteinBianchi

open Feec.Models.Euclidean.BGG Feec.Fourier.BGG Feec.Fourier.GradCurl Feec.Fourier.SymCurl
  Feec.ShortHilbertComplex

/-- **The frequency bands of the EB system on `ℝ³`**: the frequency truncation `|ξ| ≤ N` of the
BGG complex (5.1) on `ℝ³` (Fourier side), a reducing family. -/
abbrev ebBands : ReducingFamily complex ℕ :=
  bands (Euclidean.symbolComplex bggFamily) (continuous_symbolComplex_m bggFamily)

/-- **The frequency-truncation discretization of the EB system on `ℝ³`**, with the TSD constraint
`K = {0} × L²(TSD) × ({0} × L²(TSD))`. -/
abbrev ebApprox : ApproxFEEC complex ℕ := ebBands.toApprox (totalSub constraint) isClosed_totalSub

/-- The TSD constraint reduces `L` on `ℝ³`. [QuennevilleBelair2015], §6.3 -/
theorem ebApprox_isReducing : complex.wave.IsReducing ebApprox.K :=
  reducingSubcomplex.isReducing_wave

/-! #### An explicit TSD field -/

/-- `a(η) = (η₁, -η₀, 0) ⊥ η`. -/
def tvA (η : Freq) : Fin 3 → ℝ := ![η 1, -η 0, 0]

/-- `b(η) = η × a(η) = (η₀η₂, η₁η₂, -(η₀² + η₁²)) ⊥ η, a(η)`. -/
def tvB (η : Freq) : Fin 3 → ℝ := ![η 0 * η 2, η 1 * η 2, -(η 0 ^ 2 + η 1 ^ 2)]

/-- **A transverse–traceless matrix field** `a bᵀ + b aᵀ`: symmetric, trace `2 a·b = 0`, and
`(a bᵀ + b aᵀ) η = a (b·η) + b (a·η) = 0`. -/
def ttMat (η : Freq) : Mat :=
  WithLp.toLp 2 fun p => ((tvA η p.1 * tvB η p.2 + tvB η p.1 * tvA η p.2 : ℝ) : ℂ)

theorem ttMat_apply (η : Freq) (a b : Fin 3) :
    ttMat η (a, b) = ((tvA η a * tvB η b + tvB η a * tvA η b : ℝ) : ℂ) := rfl

theorem ttMat_mem_tsd (η : Freq) : ttMat η ∈ tsd η := by
  rw [mem_tsd]
  refine ⟨?_, ?_, ?_⟩
  · ext a b
    simp only [Matrix.transpose_apply, toMatrix_apply, ttMat_apply]
    ring_nf
  · simp only [Matrix.trace, Matrix.diag, toMatrix_apply, ttMat_apply, Fin.sum_univ_three,
      tvA, tvB]
    push_cast
    simp
    ring
  · ext a
    simp only [Matrix.mulVec, dotProduct, toMatrix_apply, ttMat_apply, Fin.sum_univ_three,
      cfreq, Pi.zero_apply]
    fin_cases a <;> simp [tvA, tvB] <;> ring

theorem continuous_ttMat : Continuous ttMat := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p => ?_)
  refine Complex.continuous_ofReal.comp ?_
  have h : ∀ k : Fin 3, Continuous fun η : Freq => η k := fun k =>
    (PiLp.continuous_apply 2 _ k)
  rcases p with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> simp only [tvA, tvB] <;> simp <;> fun_prop

theorem ttMat_ne_zero {η : Freq} (h : η 0 ≠ 0) : ttMat η ≠ 0 := by
  intro h0
  have h1 : ttMat η (1, 2) = 0 := by rw [h0]; rfl
  rw [ttMat_apply, Complex.ofReal_eq_zero] at h1
  have hp : 0 < η 0 ^ 2 + η 1 ^ 2 := by positivity
  simp only [tvA, tvB] at h1; simp at h1
  rcases h1 with h1 | h1
  · exact h h1
  · linarith

/-- The centre `(1, 0, 0)` of the support of the witness. -/
abbrev ebCentre : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1

/-- The support `U = B̄((1, 0, 0), 1/4)` of the witness (in Fourier space). -/
abbrev ebSupport : Set (EuclideanSpace ℝ (Fin 3)) := closedBall ebCentre (1 / 4)

/-! #### A TSD field in `H³` that is not band-limited -/

theorem ttMat_smul (t : ℝ) (η : Freq) : ttMat (t • η) = ((t ^ 3 : ℝ) : ℂ) • ttMat η := by
  ext ⟨a, b⟩
  rw [PiLp.smul_apply, ttMat_apply, ttMat_apply, smul_eq_mul, ← Complex.ofReal_mul]
  congr 1
  fin_cases a <;> fin_cases b <;> simp [tvA, tvB] <;> ring

/-- `‖a bᵀ + b aᵀ‖ ≤ C |η|³` (homogeneity of degree `3` and compactness of the sphere). -/
theorem exists_norm_ttMat_le : ∃ C, 0 ≤ C ∧ ∀ η, ‖ttMat η‖ ≤ C * ‖η‖ ^ 3 := by
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Freq) 1).exists_bound_of_continuousOn
    continuous_ttMat.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun η => ?_⟩
  by_cases hη : η = 0
  · subst hη
    have : ttMat 0 = 0 := by
      have h := ttMat_smul 0 0
      rwa [zero_smul, show ((0 : ℝ) ^ 3 : ℝ) = 0 by norm_num, Complex.ofReal_zero,
        zero_smul] at h
    rw [this, norm_zero]; positivity
  · have hn : 0 < ‖η‖ := norm_pos_iff.2 hη
    have hu : ‖η‖⁻¹ • η ∈ sphere (0 : Freq) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have he : η = ‖η‖ • (‖η‖⁻¹ • η) := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [he, ttMat_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      ← he]
    have := (hC _ hu).trans (le_max_left C 0)
    nlinarith [pow_pos hn 3]

/-- The weighted profile `ξ ↦ (1 + |2πξ|)^r (a bᵀ + b aᵀ)(2πξ)`. -/
def decayFun (r : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) : W3 ℂ Mat VM 1 :=
  (((weight r ξ : ℝ) : ℂ) • ttMat (Euclidean.scale ξ) : Mat)

theorem continuous_decayFun (r : ℝ) : Continuous (decayFun r) :=
  show Continuous fun ξ => (((weight r ξ : ℝ) : ℂ) • ttMat (Euclidean.scale ξ) : Mat) from
    (Complex.continuous_ofReal.comp (continuous_weight r)).smul
      (continuous_ttMat.comp Euclidean.continuous_scale)

theorem norm_decayFun (r : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    ‖decayFun r ξ‖ = weight r ξ * ‖ttMat (Euclidean.scale ξ)‖ :=
  show ‖(((weight r ξ : ℝ) : ℂ) • ttMat (Euclidean.scale ξ) : Mat)‖ = _ by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (weight_pos r ξ).le]

theorem decayFun_add (r r' : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    decayFun (r + r') ξ = ((weight r ξ : ℝ) : ℂ) • decayFun r' ξ :=
  show (((weight (r + r') ξ : ℝ) : ℂ) • ttMat (Euclidean.scale ξ) : Mat) =
      (((weight r ξ : ℝ) : ℂ) • (((weight r' ξ : ℝ) : ℂ) • ttMat (Euclidean.scale ξ) : Mat) : Mat)
    by rw [smul_smul, ← Complex.ofReal_mul, ← weight_add]

theorem decayFun_mem_tsd (r : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    decayFun r ξ ∈ tsd (Euclidean.scale ξ) :=
  Submodule.smul_mem _ _ (ttMat_mem_tsd _)

theorem decayFun_ne_zero (r : ℝ) {ξ : EuclideanSpace ℝ (Fin 3)} (h : Euclidean.scale ξ 0 ≠ 0) :
    decayFun r ξ ≠ 0 :=
  smul_ne_zero (RCLike.ofReal_ne_zero.2 (weight_pos _ ξ).ne') (ttMat_ne_zero h)

/-- **`(1 + |2πξ|)^r (a bᵀ + b aᵀ)(2πξ) ∈ L²(ℝ³)` for `r < -9/2`.** -/
theorem memLp_decayFun {r : ℝ} (hr : r < -9 / 2) : MemLp (decayFun r) 2 volume := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_ttMat_le
  have hm : AEStronglyMeasurable (decayFun r) volume :=
    (continuous_decayFun r).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  have hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin 3) => (1 + ‖ξ‖) ^ (-(-2 * (r + 3))))
      volume := integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; push_cast; linarith)
  refine (hint.const_mul (C ^ 2)).mono' (hm.norm.pow 2) (Eventually.of_forall fun ξ => ?_)
  have h1 : 1 ≤ 1 + ‖Euclidean.scale ξ‖ := one_le_one_add_norm ξ
  have h2 : 1 + ‖ξ‖ ≤ 1 + ‖Euclidean.scale ξ‖ := by
    rw [norm_scale]; nlinarith [norm_nonneg ξ, Real.two_le_pi]
  have hw := weight_pos r ξ
  rw [Real.norm_of_nonneg (by positivity), norm_decayFun,
    show -(-2 * (r + 3)) = 2 * (r + 3) by ring]
  have hb : weight r ξ * ‖ttMat (Euclidean.scale ξ)‖ ≤ C * weight (r + 3) ξ := by
    have h3 : ‖Euclidean.scale ξ‖ ^ 3 ≤ (1 + ‖Euclidean.scale ξ‖) ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 3
    calc weight r ξ * ‖ttMat (Euclidean.scale ξ)‖
        ≤ weight r ξ * (C * (1 + ‖Euclidean.scale ξ‖) ^ (3 : ℝ)) :=
          mul_le_mul_of_nonneg_left ((hC _).trans (mul_le_mul_of_nonneg_left h3 hC0)) hw.le
      _ = C * weight (r + 3) ξ := by rw [weight_add, weight, weight]; ring
  have hsq : (weight r ξ * ‖ttMat (Euclidean.scale ξ)‖) ^ 2 ≤ C ^ 2 * weight (2 * (r + 3)) ξ := by
    have : weight (2 * (r + 3)) ξ = weight (r + 3) ξ ^ 2 := by
      rw [two_mul, weight_add, _root_.sq]
    rw [this, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hb 2
  refine hsq.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg C))
  exact Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)

/-- The TSD field `v_r = (1 + |2πξ|)^r (a bᵀ + b aᵀ)(2πξ)` (Fourier side), `r < -9/2`. -/
def decayField (r : ℝ) (hr : r < -9 / 2) : Space 1 := (memLp_decayFun hr).toLp _

/-- **The TSD datum `(0, v_r, 0)`**, `v_r = (1 + |2πξ|)^r (a bᵀ + b aᵀ)(2πξ)`, `r < -9/2`. -/
def decayState (r : ℝ) (hr : r < -9 / 2) : PiLp 2 Space :=
  WithLp.toLp 2 (Pi.single 1 (decayField r hr))

theorem decayState_one (r : ℝ) (hr : r < -9 / 2) : decayState r hr 1 = decayField r hr := by
  simp [decayState]

theorem decayState_ne_one (r : ℝ) (hr : r < -9 / 2) {i : Fin 3} (hi : i ≠ 1) :
    decayState r hr i = 0 := by
  simp [decayState, hi]

theorem le_apply_zero {c : ℝ} {ξ : EuclideanSpace ℝ (Fin 3)}
    (hξ : ξ ∈ closedBall (c • ebCentre) (1 / 4)) : c - 1 / 4 ≤ ξ 0 := by
  have h1 : |ξ 0 - c| ≤ 1 / 4 := by
    have := (PiLp.norm_apply_le (ξ - c • ebCentre) 0).trans (mem_closedBall_iff_norm.1 hξ)
    simpa [ebCentre, Real.norm_eq_abs] using this
  linarith [neg_abs_le (ξ 0 - c)]

/-- **Non-vacuity of the Sobolev rate beyond band-limited data**: `decayState r` is TSD, lies in
`Hˢ` for every `s < -r - 9/2`, is not band-limited for any `N`, and the truncated solutions have
a positive error at every `N` and `t` (bounded by `(N + 1)^{-s} ‖ξ₀‖_{Hˢ}` for `s ≥ 0`,
`einsteinBianchi_euclidean_band`). -/
theorem decayState_nonvacuous (r : ℝ) (hr : r < -9 / 2) :
    decayState r hr ∈ totalSub constraint ∧
      (∀ s, s + r < -9 / 2 → decayState r hr ∈ sobolev ℂ (W3 ℂ Mat VM) s) ∧
      (∀ N, decayState r hr ∉
        totalSub ((Euclidean.symbolComplex bggFamily).band (freqBall N))) ∧
      ∀ (N : ℕ) (t : ℝ), 0 < ‖complex.waveGroup.S t (decayState r hr) -
        ebApprox.sol N (ebApprox.proj N (decayState r hr)) t‖ := by
  have hK : decayState r hr ∈ totalSub constraint := fun i => by
    by_cases hi : i = 1
    · subst hi
      rw [decayState_one, Operator.mem_fibreSub]
      filter_upwards [(memLp_decayFun hr).coeFn_toLp] with ξ hξ
      change (decayField r hr : EuclideanSpace ℝ (Fin 3) → W3 ℂ Mat VM 1) ξ ∈ tsd _
      rw [decayField, hξ]
      exact decayFun_mem_tsd _ _
    · rw [decayState_ne_one r hr hi]; exact Submodule.zero_mem _
  have hnb : ∀ N, decayState r hr ∉
      totalSub ((Euclidean.symbolComplex bggFamily).band (freqBall N)) := fun N hN => by
    have h1 := mem_band_iff.1 (hN 1)
    rw [decayState_one] at h1
    set U := closedBall (((N : ℝ) + 2) • ebCentre) (1 / 4)
    have hpos : 0 < volume U := Metric.measure_closedBall_pos volume _ (by norm_num)
    refine hpos.ne' (measure_mono_null (t := {ξ | ¬ (ξ ∉ freqBall N →
      (decayFun r ξ = 0))}) (fun ξ hξ => ?_) ?_)
    · have h0 := le_apply_zero hξ
      have hξ0 : 0 < ξ 0 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      have hs0 : Euclidean.scale ξ 0 ≠ 0 := by
        simp only [Euclidean.scale, PiLp.smul_apply, smul_eq_mul]; positivity
      intro h
      refine decayFun_ne_zero _ hs0 (h fun hb => ?_)
      have hb' := mem_freqBall.1 hb
      have : 2 * Real.pi * ξ 0 ≤ ‖Euclidean.scale ξ‖ := by
        have := PiLp.norm_apply_le (Euclidean.scale ξ) 0
        simp only [Euclidean.scale, PiLp.smul_apply, smul_eq_mul, Real.norm_eq_abs] at this ⊢
        exact (le_abs_self _).trans this
      nlinarith [Real.two_le_pi]
    · rw [← ae_iff]
      filter_upwards [h1, (memLp_decayFun hr).coeFn_toLp] with ξ h2 h3
      intro hξ
      rw [← h3]; exact h2 hξ
  refine ⟨hK, fun s hs => ?_, hnb, fun N t => ?_⟩
  · refine ⟨WithLp.toLp 2 (Pi.single 1 (decayField (s + r) hs)), fun i => ?_⟩
    by_cases hi : i = 1
    · subst hi
      rw [decayState_one]
      simp only [Pi.single_eq_same]
      filter_upwards [(memLp_decayFun hr).coeFn_toLp, (memLp_decayFun hs).coeFn_toLp] with ξ h1 h2
      change (decayField r hr : EuclideanSpace ℝ (Fin 3) → W3 ℂ Mat VM 1) ξ =
        _ • (decayField (s + r) hs : EuclideanSpace ℝ (Fin 3) → W3 ℂ Mat VM 1) ξ
      rw [decayField, decayField, h1, h2]
      conv_lhs => rw [show r = -s + (s + r) by ring]
      rw [decayFun_add]
      rfl
    · rw [decayState_ne_one r hr hi]
      simp only [Pi.single_eq_of_ne hi]
      filter_upwards [Lp.coeFn_zero (W3 ℂ Mat VM i) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))]
        with ξ h
      rw [h, Pi.zero_apply, smul_zero]
  · rw [ebBands.norm_sub_toApprox_sol]
    refine norm_pos_iff.2 (sub_ne_zero.2 fun h => hnb N ?_)
    exact Submodule.starProjection_eq_self_iff.1 h.symm

/-! #### Optimality of the rate: shell data -/

/-- The centre `((N + 1)/(2π) + 1/4) e₀` of the shell witness. -/
abbrev shellCentre (N : ℕ) : EuclideanSpace ℝ (Fin 3) :=
  (((N : ℝ) + 1) / (2 * Real.pi) + 1 / 4) • ebCentre

/-- The support `B̄(shellCentre N, 1/4)` of the shell witness, in Fourier space: its frequencies
`|2πξ|` lie in `[N + 1, N + 1 + π]` (`norm_scale_mem_shell`). -/
abbrev shellSupport (N : ℕ) : Set (EuclideanSpace ℝ (Fin 3)) := closedBall (shellCentre N) (1 / 4)

theorem norm_scale_mem_shell {N : ℕ} {ξ : EuclideanSpace ℝ (Fin 3)} (hξ : ξ ∈ shellSupport N) :
    (N : ℝ) + 1 ≤ ‖Euclidean.scale ξ‖ ∧ ‖Euclidean.scale ξ‖ ≤ (N : ℝ) + 1 + Real.pi := by
  have hc : ‖shellCentre N‖ = ((N : ℝ) + 1) / (2 * Real.pi) + 1 / 4 := by
    rw [norm_smul, (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 3)).1 0, mul_one,
      Real.norm_of_nonneg (by positivity)]
  have hd : ‖ξ - shellCentre N‖ ≤ 1 / 4 := mem_closedBall_iff_norm.1 hξ
  have h1 := norm_sub_norm_le (shellCentre N) ξ
  have h2 := norm_sub_norm_le ξ (shellCentre N)
  rw [norm_sub_rev] at h1
  rw [hc] at h1 h2
  have hk : 2 * Real.pi * (((N : ℝ) + 1) / (2 * Real.pi)) = (N : ℝ) + 1 := by
    field_simp
  rw [norm_scale]
  constructor <;> nlinarith [Real.pi_pos]

theorem notMem_freqBall_of_mem_shell {N : ℕ} {ξ : EuclideanSpace ℝ (Fin 3)}
    (hξ : ξ ∈ shellSupport N) : ξ ∉ freqBall N := fun h => by
  have := (norm_scale_mem_shell hξ).1
  rw [mem_freqBall] at h
  linarith

theorem scale_zero_ne_zero_of_mem_shell {N : ℕ} {ξ : EuclideanSpace ℝ (Fin 3)}
    (hξ : ξ ∈ shellSupport N) : Euclidean.scale ξ 0 ≠ 0 := by
  have h0 := le_apply_zero hξ
  have hq : 0 < ((N : ℝ) + 1) / (2 * Real.pi) := by positivity
  have : 0 < ξ 0 := by linarith
  simp only [Euclidean.scale, PiLp.smul_apply, smul_eq_mul]
  positivity

theorem weight_le_of_mem_shell {s : ℝ} (hs : 0 ≤ s) {N : ℕ} {ξ : EuclideanSpace ℝ (Fin 3)}
    (hξ : ξ ∈ shellSupport N) : weight s ξ ≤ (6 * ((N : ℝ) + 1)) ^ s := by
  refine Real.rpow_le_rpow (by linarith [one_le_one_add_norm ξ]) ?_ hs
  have := (norm_scale_mem_shell hξ).2
  linarith [Real.pi_le_four, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

/-- The TSD field `𝟙_{U_N} (a bᵀ + b aᵀ)(2πξ)` supported in the frequency shell
`N + 1 ≤ |ξ| ≤ N + 1 + π`. -/
def shellField (N : ℕ) : Space 1 :=
  indicatorField (shellSupport N) (isCompact_closedBall _ _) (decayFun 0) (continuous_decayFun 0)

theorem coeFn_shellField (N : ℕ) :
    (shellField N : EuclideanSpace ℝ (Fin 3) → W3 ℂ Mat VM 1) =ᵐ[volume]
      (shellSupport N).indicator (decayFun 0) :=
  coeFn_indicatorField _ _

/-- **The shell datum** `(0, 𝟙_{U_N} (a bᵀ + b aᵀ), 0)`: TSD, with frequencies in
`[N + 1, N + 1 + π]`. -/
def shellState (N : ℕ) : PiLp 2 Space := PiLp.single 2 1 (shellField N)

theorem shellState_mem_constraint (N : ℕ) : shellState N ∈ totalSub constraint := fun i => by
  by_cases hi : i = 1
  · subst hi
    rw [shellState, PiLp.single_eq_same, Operator.mem_fibreSub]
    filter_upwards [coeFn_shellField N] with ξ hξ
    change (shellField N : EuclideanSpace ℝ (Fin 3) → W3 ℂ Mat VM 1) ξ ∈ tsd _
    rw [hξ]
    by_cases hU : ξ ∈ shellSupport N
    · rw [indicator_of_mem hU]; exact decayFun_mem_tsd _ _
    · rw [indicator_of_notMem hU]; exact Submodule.zero_mem _
  · rw [shellState, PiLp.single_eq_of_ne (p := 2) hi]; exact Submodule.zero_mem _

/-- The shell datum is in every `Hˢ`, `s ≥ 0`, with `‖ξ₀‖_{Hˢ} ≤ (6 (N + 1))ˢ ‖ξ₀‖`. -/
theorem shellState_sobolev {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    shellState N ∈ sobolev ℂ (W3 ℂ Mat VM) s ∧
      sobolevNorm ℂ s (shellState N) ≤ (6 * ((N : ℝ) + 1)) ^ s * ‖shellState N‖ := by
  set v : Space 1 := indicatorField (shellSupport N) (isCompact_closedBall _ _) (decayFun s)
    (continuous_decayFun s)
  have hv : (v : EuclideanSpace ℝ (Fin 3) → W3 ℂ Mat VM 1) =ᵐ[volume]
      (shellSupport N).indicator (decayFun s) := coeFn_indicatorField _ _
  have hrep : IsSobolevRep ℂ s (shellState N) (PiLp.single 2 1 v) := by
    refine isSobolevRep_single ?_
    filter_upwards [coeFn_shellField N, hv] with ξ h1 h2
    rw [h1, h2]
    by_cases hU : ξ ∈ shellSupport N
    · rw [indicator_of_mem hU, indicator_of_mem hU]
      conv_lhs => rw [show (0 : ℝ) = -s + s by ring]
      rw [decayFun_add]
      rfl
    · rw [indicator_of_notMem hU, indicator_of_notMem hU, smul_zero]
  refine ⟨⟨_, hrep⟩, ?_⟩
  rw [sobolevNorm_eq hrep, shellState, PiLp.norm_single, PiLp.norm_single]
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [coeFn_shellField N, hv] with ξ h1 h2
  rw [h1, h2]
  by_cases hU : ξ ∈ shellSupport N
  · rw [indicator_of_mem hU, indicator_of_mem hU, norm_decayFun, norm_decayFun,
      show weight 0 ξ = 1 from Real.rpow_zero _, one_mul]
    exact mul_le_mul_of_nonneg_right (weight_le_of_mem_shell hs hU) (norm_nonneg _)
  · simp [indicator_of_notMem hU]

/-- The frequency truncation `P_N` annihilates the shell datum. -/
theorem starProjection_shellState (N : ℕ) :
    (totalSub ((Euclidean.symbolComplex bggFamily).band (freqBall N))).starProjection
      (shellState N) = 0 := by
  refine PiLp.ext fun i => ?_
  rw [totalSub_starProjection_apply, PiLp.zero_apply]
  have := fun i => hasOrthogonalProjection_band (Euclidean.symbolComplex bggFamily)
    (measurableSet_freqBall N) i
  by_cases hi : i = 1
  · subst hi
    rw [shellState, PiLp.single_eq_same]
    refine Lp.ext ?_
    filter_upwards [Operator.coeFn_starProjection_fibreSub (μ := volume)
        (bandFibre (𝕜 := ℂ) (E := W3 ℂ Mat VM) (freqBall N) 1)
        (aestronglyMeasurable_starProjection_bandFibre (measurableSet_freqBall N) 1)
        (shellField N), coeFn_shellField N,
      Lp.coeFn_zero (W3 ℂ Mat VM 1) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))]
      with ξ h1 h2 h3
    rw [h1, h3, starProjection_bandFibre, h2]
    by_cases hb : ξ ∈ freqBall N
    · rw [Operator.cutoff_apply_of_mem hb,
        indicator_of_notMem fun hU => notMem_freqBall_of_mem_shell hU hb]
      rfl
    · rw [Operator.cutoff_apply_of_notMem hb]; rfl
  · rw [shellState, PiLp.single_eq_of_ne (p := 2) hi, _root_.map_zero]

theorem shellState_ne_zero (N : ℕ) : shellState N ≠ 0 := fun h => by
  have h1 : shellField N = 0 := by
    have := congrArg (fun x : PiLp 2 Space => x 1) h
    simpa [shellState] using this
  exact indicatorField_ne_zero _ (continuous_decayFun 0)
    (Metric.measure_closedBall_pos volume _ (by norm_num))
    (fun ξ hξ => decayFun_ne_zero 0 (scale_zero_ne_zero_of_mem_shell hξ)) h1

/-- **The shell data attain the rate**: `shellState N` is a nonzero TSD datum in `Hˢ` (`s ≥ 0`)
cut off entirely by `P_N`, so the error of its truncated solution is `‖ξ₀‖` at every time, and
`(N + 1)^{-s} ‖ξ₀‖_{Hˢ} ≤ 6ˢ · error`. -/
theorem shellState_nonvacuous {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    shellState N ∈ totalSub constraint ∧ shellState N ∈ sobolev ℂ (W3 ℂ Mat VM) s ∧
      shellState N ≠ 0 ∧ ∀ t : ℝ,
      ‖complex.waveGroup.S t (shellState N) -
          ebApprox.sol N (ebApprox.proj N (shellState N)) t‖ = ‖shellState N‖ ∧
      (1 / ((N : ℝ) + 1)) ^ s * sobolevNorm ℂ s (shellState N) ≤
        6 ^ s * ‖complex.waveGroup.S t (shellState N) -
          ebApprox.sol N (ebApprox.proj N (shellState N)) t‖ := by
  obtain ⟨hmem, hle⟩ := shellState_sobolev hs N
  have herr : ∀ t : ℝ, ‖complex.waveGroup.S t (shellState N) -
      ebApprox.sol N (ebApprox.proj N (shellState N)) t‖ = ‖shellState N‖ := fun t => by
    rw [ebBands.norm_sub_toApprox_sol,
      show (ebBands.B N).starProjection (shellState N) = 0 from starProjection_shellState N,
      sub_zero]
  refine ⟨shellState_mem_constraint N, hmem, shellState_ne_zero N, fun t => ⟨herr t, ?_⟩⟩
  rw [herr t]
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  calc (1 / ((N : ℝ) + 1)) ^ s * sobolevNorm ℂ s (shellState N)
      ≤ (1 / ((N : ℝ) + 1)) ^ s * ((6 * ((N : ℝ) + 1)) ^ s * ‖shellState N‖) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 6 ^ s * ‖shellState N‖ := by
        rw [Real.mul_rpow (by norm_num) hN.le, one_div, Real.inv_rpow hN.le]
        field_simp

/-- **The exponent is sharp**: for `0 ≤ s < s'` and every time `t`, no bound
`‖e^{tL} ξ₀ - ι_N e^{tL_N} π_N ξ₀‖ ≤ C (N + 1)^{-s'} ‖ξ₀‖_{Hˢ}` holds for all `N` and all TSD
data in `Hˢ` (the shell data `shellState N` violate it for large `N`). -/
theorem einsteinBianchi_euclidean_rate_optimal {s s' : ℝ} (hs : 0 ≤ s) (hss : s < s') (t : ℝ) :
    ¬ ∃ C : ℝ, ∀ (N : ℕ), ∀ x ∈ totalSub constraint, x ∈ sobolev ℂ (W3 ℂ Mat VM) s →
      ‖complex.waveGroup.S t x - ebApprox.sol N (ebApprox.proj N x) t‖ ≤
        C * (1 / ((N : ℝ) + 1)) ^ s' * sobolevNorm ℂ s x := by
  rintro ⟨C, hC⟩
  set Cp := max C 0
  have key : ∀ N : ℕ, 1 ≤ Cp * 6 ^ s * ((N : ℝ) + 1) ^ (s - s') := fun N => by
    obtain ⟨hK, hmem, hne, h⟩ := shellState_nonvacuous hs N
    have hle := (shellState_sobolev hs N).2
    have hb := hC N _ hK hmem
    rw [(h t).1] at hb
    have hn : 0 < ‖shellState N‖ := norm_pos_iff.2 hne
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hm := sobolevNorm_nonneg (𝕜 := ℂ) s (shellState N)
    have e : (1 / ((N : ℝ) + 1)) ^ s' * (6 * ((N : ℝ) + 1)) ^ s =
        6 ^ s * ((N : ℝ) + 1) ^ (s - s') := by
      rw [Real.mul_rpow (by norm_num) hN.le, Real.rpow_sub hN, one_div, Real.inv_rpow hN.le]
      field_simp
    have h1 : ‖shellState N‖ ≤
        Cp * (1 / ((N : ℝ) + 1)) ^ s' * ((6 * ((N : ℝ) + 1)) ^ s * ‖shellState N‖) := by
      refine hb.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (le_max_left C 0) (by positivity)) hm).trans ?_)
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    have h2 : ‖shellState N‖ ≤ (Cp * 6 ^ s * ((N : ℝ) + 1) ^ (s - s')) * ‖shellState N‖ := by
      calc _ ≤ _ := h1
        _ = _ := by rw [mul_assoc Cp, mul_assoc Cp, ← e]; ring
    exact (le_mul_iff_one_le_left hn).1 h2
  have hlim : Tendsto (fun N : ℕ => Cp * 6 ^ s * ((N : ℝ) + 1) ^ (s - s')) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < s' - s)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have h' : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (s - s')) atTop (𝓝 0) := by
      simpa [Function.comp_def, neg_sub] using h
    simpa using h'.const_mul (Cp * 6 ^ s)
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds one_pos)).exists
  linarith [key N]

/-! #### Exact TSD preservation -/

/-- **The frequency truncation preserves TSD** (a fibrewise constraint). -/
theorem starProjection_band_mem_constraint (N : ℕ) {x : PiLp 2 Space}
    (hx : x ∈ totalSub constraint) :
    (totalSub ((Euclidean.symbolComplex bggFamily).band (freqBall N))).starProjection x ∈
      totalSub constraint :=
  starProjection_totalSub_band_mem _ (fun _ _ hu =>
    starProjection_band_mem_fibreSub _ (measurableSet_freqBall N) hu) hx

/-! #### The `ℝ³` verdict -/

/-- **The verdict of the FEEC theorem for the EB system on `ℝ³`** (frequency truncation
`|ξ| ≤ N`, TSD constraint): that of `ReducingFamily.feec` for `ebBands` (the full
`ApproxFEEC.Verdict` on all data; the error is the truncation error of the datum at every time,
`‖e^{tL} ξ₀ - ι_N e^{tL_N} π_N ξ₀‖ = ‖ξ₀ - P_N ξ₀‖`), and:
1. the TSD constraint reduces `L` and the truncations preserve it, so the truncated solutions of
   TSD data are TSD (`sol_mem`: constraint residual identically `0`);
2. on `Hˢ`, `s ≥ 0`, the truncation error is `≤ (N + 1)^{-s} ‖ξ₀‖_{Hˢ}`, hence so is the error at
   every time;
3. the exponent is sharp: for `0 ≤ s < s'` no bound `C (N + 1)^{-s'} ‖ξ₀‖_{Hˢ}` holds on TSD
   data, at any time. -/
structure EuclideanEBVerdict : Prop
    extends toReducing : ebBands.Verdict (totalSub constraint) isClosed_totalSub where
  /-- the TSD constraint reduces `L` -/
  isReducing : complex.wave.IsReducing (totalSub constraint)
  /-- the truncations preserve TSD -/
  starProjection_mem (N : ℕ) {x : PiLp 2 Space} (hx : x ∈ totalSub constraint) :
    (ebBands.B N).starProjection x ∈ totalSub constraint
  /-- the truncation error on `Hˢ` -/
  norm_sub_starProjection_le {s : ℝ} (hs : 0 ≤ s) {x : PiLp 2 Space}
    (hx : x ∈ sobolev ℂ (W3 ℂ Mat VM) s) (N : ℕ) :
    ‖x - (ebBands.B N).starProjection x‖ ≤ (1 / ((N : ℝ) + 1)) ^ s * sobolevNorm ℂ s x
  /-- the exponent is sharp -/
  rate_optimal {s s' : ℝ} (hs : 0 ≤ s) (hss : s < s') (t : ℝ) :
    ¬ ∃ C : ℝ, ∀ (N : ℕ), ∀ x ∈ totalSub constraint, x ∈ sobolev ℂ (W3 ℂ Mat VM) s →
      ‖complex.waveGroup.S t x - ebApprox.sol N (ebApprox.proj N x) t‖ ≤
        C * (1 / ((N : ℝ) + 1)) ^ s' * sobolevNorm ℂ s x

/-- **The EB system on `ℝ³` through the FEEC theorem for reducing families**, with Sobolev rates.
[QuennevilleBelair2015], §4.12–4.13, Ch. 6 -/
theorem einsteinBianchi_euclidean_band : EuclideanEBVerdict :=
  ⟨ebBands.feec _ _, ebApprox_isReducing, starProjection_band_mem_constraint,
    fun hs _ hx N => norm_sub_starProjection_le_of_mem_sobolev _ hs hx N,
    einsteinBianchi_euclidean_rate_optimal⟩

end EinsteinBianchi

/-! ### Maxwell's equations on `ℝᵈ` -/

section Maxwell

open Feec.Models.Euclidean.DeRham Feec.Instances.Maxwell Feec.Fourier.Exterior

variable (d : Type*) [Fintype d] [LinearOrder d] (a : ℤ)

/-- The index map `i ↦ a + i` of the window reflects the relation. -/
theorem window_rel (i j : Fin 3)
    (h : (ComplexShape.up ℤ).Rel (a + ((i : ℕ) : ℤ)) (a + ((j : ℕ) : ℤ))) :
    (ComplexShape.window 3).Rel i j := by
  change a + ((i : ℕ) : ℤ) + 1 = a + ((j : ℕ) : ℤ) at h
  change i.val + 1 = j.val
  omega

/-- The symbol complex of the Maxwell window `Λᵃ → Λᵃ⁺¹ → Λᵃ⁺²` of `ℝᵈ` (Fourier side). -/
abbrev maxwellSymbol :
    SymbolComplex ℂ (volume : Measure (EuclideanSpace ℝ d)) (ComplexShape.window 3)
      fun i : Fin 3 => Form ℂ d (a + i) :=
  (Euclidean.symbolComplex (deRham d)).restrict (fun i : Fin 3 => a + ((i : ℕ) : ℤ))
    (window_rel a)

theorem continuous_maxwellSymbol_m (i j : Fin 3) : Continuous ((maxwellSymbol d a).m i j) :=
  continuous_symbolComplex_m (deRham d) _ _

/-- **The frequency bands of Maxwell's equations on `ℝᵈ`** (degree `a`; `d = 3`, `a = 0` is the
classical system): the frequency truncation `|ξ| ≤ N` of the window, a reducing family. -/
abbrev maxwellBands : ReducingFamily ((complex d).window a 3) ℕ :=
  bands (maxwellSymbol d a) (continuous_maxwellSymbol_m d a)

/-- **The frequency-truncation discretization of Maxwell's equations on `ℝᵈ`**, with the Gauss
laws `σ = 0`, `d†E = 0`, `dB = 0`. -/
abbrev maxwellApprox : ApproxFEEC ((complex d).window a 3) ℕ :=
  (maxwellBands d a).toApprox (windowGauss (complex d) a) (isClosed_gauss _ _)

/-- The Gauss laws reduce the Maxwell operator of `ℝᵈ`. [QuennevilleBelair2015], Prop. 4.16 -/
theorem maxwellApprox_isReducing :
    ((complex d).window a 3).wave.IsReducing (maxwellApprox d a).K :=
  isReducing_windowGauss _ a

omit [Fintype d] [LinearOrder d] in
theorem scale_inv_smul (ξ : EuclideanSpace ℝ d) :
    Euclidean.scale ((2 * Real.pi)⁻¹ • ξ) = ξ := by
  rw [Euclidean.scale, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

/-- The electric arrow `Λᵃ → Λᵃ⁺¹` of the window is not zero for `0 ≤ a < d`. -/
theorem maxwellSymbol_m01_ne_zero (h0 : 0 ≤ a) (h : a < Fintype.card d) :
    (maxwellSymbol d a).m 0 1 ≠ 0 := by
  intro hm
  refine deRham_m_ne_zero (i := a + ((0 : Fin 3) : ℕ)) (j := a + ((1 : Fin 3) : ℕ)) (by simp)
    (by simpa using h0) (by simpa using h) ?_
  funext ξ
  have := congrFun hm ((2 * Real.pi)⁻¹ • ξ)
  change (deRham d).m _ _ (Euclidean.scale ((2 * Real.pi)⁻¹ • ξ)) = 0 at this
  rwa [scale_inv_smul] at this

/-! #### Exact preservation of the Gauss laws -/

/-- **The frequency truncation preserves the Gauss laws**: `σ = 0` trivially, and `d†E = 0`,
`dB = 0` because `P_N` reduces `d` and `d†` (`starProjection_mem_ker`), including the arrow
`Λᵃ⁺² → Λᵃ⁺³` outside the window. -/
theorem starProjection_band_mem_windowGauss (N : ℕ)
    {x : PiLp 2 fun i : Fin 3 => L2Form d (a + i)} (hx : x ∈ windowGauss (complex d) a) :
    (totalSub ((maxwellSymbol d a).band (freqBall N))).starProjection x ∈
      windowGauss (complex d) a := by
  have hR := reducingSubcomplex_band (maxwellSymbol d a) (measurableSet_freqBall N)
  have hR' := reducingSubcomplex_band (Euclidean.symbolComplex (deRham d))
    (measurableSet_freqBall N)
  rw [mem_gauss] at hx ⊢
  obtain ⟨h0, h1, h2⟩ := hx
  simp only [totalSub_starProjection_apply]
  refine ⟨by rw [h0, _root_.map_zero], ?_, ?_⟩
  · exact starProjection_mem_ker ((hR.reduces 0 1).adjoint
      ((maxwellSymbol d a).toHilbertComplex.dense 0 1)) h1
  · exact starProjection_mem_ker (hR'.reduces (a + ((2 : Fin 3) : ℕ))
      (a + ((2 : Fin 3) : ℕ) + 1)) h2

/-- **The verdict of the FEEC theorem for Maxwell's equations on `ℝᵈ`** (degree `a`, frequency
truncation `|ξ| ≤ N`, Gauss laws): that of `ReducingFamily.feec` for `maxwellBands` (the full
`ApproxFEEC.Verdict` on all data; the error is the truncation error of the datum at every time),
and:
1. the Gauss laws reduce `L` and the truncations preserve them, so the truncated solutions of
   data satisfying the Gauss laws satisfy them (`sol_mem`: Gauss-law residual identically `0`);
2. on `Hˢ`, `s ≥ 0`, the truncation error is `≤ (N + 1)^{-s} ‖ξ₀‖_{Hˢ}`, hence so is the error at
   every time. -/
structure EuclideanMaxwellVerdict : Prop
    extends toReducing : (maxwellBands d a).Verdict (windowGauss (complex d) a)
      (isClosed_gauss _ _) where
  /-- the Gauss laws reduce `L` -/
  isReducing : ((complex d).window a 3).wave.IsReducing (windowGauss (complex d) a)
  /-- the truncations preserve the Gauss laws -/
  starProjection_mem (N : ℕ) {x : PiLp 2 fun i : Fin 3 => L2Form d (a + i)}
    (hx : x ∈ windowGauss (complex d) a) :
    ((maxwellBands d a).B N).starProjection x ∈ windowGauss (complex d) a
  /-- the truncation error on `Hˢ` -/
  norm_sub_starProjection_le {s : ℝ} (hs : 0 ≤ s) {x : PiLp 2 fun i : Fin 3 => L2Form d (a + i)}
    (hx : x ∈ sobolev ℂ (fun i : Fin 3 => Form ℂ d (a + i)) s) (N : ℕ) :
    ‖x - ((maxwellBands d a).B N).starProjection x‖ ≤ (1 / ((N : ℝ) + 1)) ^ s * sobolevNorm ℂ s x

/-- **Maxwell's equations on `ℝᵈ` through the FEEC theorem for reducing families**, with Sobolev
rates. [QuennevilleBelair2015], §4.9 (Prop. 4.16), §4.12–4.13 -/
theorem maxwell_euclidean_band : EuclideanMaxwellVerdict d a :=
  ⟨(maxwellBands d a).feec _ _, maxwellApprox_isReducing d a,
    starProjection_band_mem_windowGauss d a,
    fun hs _ hx N => norm_sub_starProjection_le_of_mem_sobolev _ hs hx N⟩

/-! #### A non-reducing Maxwell constraint on `ℝᵈ` -/

/-- The frequency-truncation discretization with the **vanishing-field constraint** `E = 0`,
`B = 0` (`Feec.Instances.Maxwell.potential`), which does not reduce `L` (`a < d`). -/
abbrev maxwellPotentialApprox : ApproxFEEC ((complex d).window a 3) ℕ :=
  (maxwellBands d a).toApprox (potential ℂ fun i : Fin 3 => L2Form d (a + i)) isClosed_potential

/-- **The vanishing-field constraint does not reduce Maxwell's operator on `ℝᵈ`**
(`0 ≤ a < d`). -/
theorem maxwell_euclidean_not_isReducing_potential (h0 : 0 ≤ a) (h : a < Fintype.card d) :
    ¬ ((complex d).window a 3).wave.IsReducing (potential ℂ fun i : Fin 3 => L2Form d (a + i)) := by
  obtain ⟨N, u, -, hu, hdu⟩ := exists_band_d_ne_zero (maxwellSymbol d a)
    (continuous_maxwellSymbol_m d a) (maxwellSymbol_m01_ne_zero d a h0 h)
  exact not_isReducing_potential _ ⟨⟨u, hu⟩, hdu⟩

/-- **Item 4 of `approxFEEC`, non-reducing branch, on `ℝᵈ`** (`0 ≤ a < d`): for the vanishing-field
constraint, for every `T > 0` some datum of `D(L) ∩ K` leaves `K` at some `t ∈ [0, T]`, and the
residuals of the truncated solutions `ι_N e^{tL_N} π_N ξ₀` tend to `dist(e^{tL} ξ₀, K) > 0`,
eventually staying above half of it. -/
theorem maxwell_euclidean_potential_residual (h0 : 0 ≤ a) (h : a < Fintype.card d) {T : ℝ}
    (hT : 0 < T) :
    ∃ x : ((complex d).window a 3).wave.domain,
      (x : PiLp 2 _) ∈ potential ℂ (fun i : Fin 3 => L2Form d (a + i)) ∧ ∃ t ∈ Icc 0 T,
      ((complex d).window a 3).waveGroup.S t x ∉ potential ℂ (fun i : Fin 3 => L2Form d (a + i)) ∧
      0 < infDist (((complex d).window a 3).waveGroup.S t x)
        (potential ℂ (fun i : Fin 3 => L2Form d (a + i)) : Set _) ∧
      Tendsto (fun N => infDist ((maxwellPotentialApprox d a).sol N
          ((maxwellPotentialApprox d a).proj N x) t)
          (potential ℂ (fun i : Fin 3 => L2Form d (a + i)) : Set _)) atTop
        (𝓝 (infDist (((complex d).window a 3).waveGroup.S t x)
          (potential ℂ (fun i : Fin 3 => L2Form d (a + i)) : Set _))) ∧
      ∀ᶠ N in atTop, infDist (((complex d).window a 3).waveGroup.S t x)
          (potential ℂ (fun i : Fin 3 => L2Form d (a + i)) : Set _) / 2 <
        infDist ((maxwellPotentialApprox d a).sol N ((maxwellPotentialApprox d a).proj N x) t)
          (potential ℂ (fun i : Fin 3 => L2Form d (a + i)) : Set _) := by
  have V := ((maxwellBands d a).feec _ isClosed_potential).toApprox
  obtain ⟨x, ⟨hxD, hxK⟩, t, ht, hout⟩ := V.leaves_smooth isClosed_potential
    (fun hk => maxwell_euclidean_not_isReducing_potential d a h0 h
      ((V.isReducing_iff_keeps (p := fun i : Fin 3 => decide (Odd i.val))
        (fun _ _ h => ComplexShape.window_parity h) (fun _ hx => reversal_mem_totalSub hx)
        (dense_potential _)).2 hk)) (dense_potential _) hT
  have hx : x ∈ ((maxwellBands d a).toCore _ isClosed_potential).Data.topologicalClosure :=
    Submodule.le_topologicalClosure _ Submodule.mem_top
  obtain ⟨hpos, hdet⟩ := V.detects isClosed_potential ⟨0, Submodule.zero_mem _⟩ ht.1 hout
  obtain ⟨hlim, hev⟩ := hdet hx _ (V.tendsto_incl_proj hx)
  rw [ApproxFEEC.S_eq_waveGroup _ ht.1] at hout hpos hlim hev
  exact ⟨⟨x, hxD⟩, hxK, t, ht, hout, hpos, hlim, hev⟩

/-! #### The classical system: `d = 3`, `a = 0` -/

end Maxwell

end Feec.Instances.EuclideanBand
