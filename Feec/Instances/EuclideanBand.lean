module

public import Feec.HilbertComplex.Approximation.ApproxConforming
public import Feec.Fourier.SpectralGalerkin
public import Feec.Models.Euclidean.BGG
public import Feec.Models.Euclidean.DeRham
public import Feec.Instances.Maxwell

/-!
# Frequency truncation on `ℝᵈ` as an approximating FEEC discretization

On `ℝᵈ` a constant-coefficient complex is, after the `L²` Fourier transform (Plancherel,
`Feec.Fourier.Euclidean.fourier`), a symbol complex on `L²(ℝᵈ)` with symbols `m(2πx)`
(`Feec.Fourier.Euclidean.complex`). Its **frequency truncation** keeps the fields whose Fourier
transforms vanish at frequencies `|ξ| > N` (`ξ = 2πx`): `B_N = ∏ L²_{|ξ| ≤ N}`. This module makes
the frequency truncation an instance of the approximating FEEC theorem
`Feec.HilbertComplex.approxFEEC`, for every constant-coefficient complex on `ℝᵈ` and every closed
constraint, and reads it on the linearized Einstein–Bianchi system (`ℝ³`, TSD constraint) and on
Maxwell's equations (`ℝᵈ`, every degree, Gauss laws).

**Generic layer.** A symbol bounded on a measurable band acts boundedly on band-limited fields,
and so does its fibrewise adjoint (`band_le_domain_d`, `norm_d_band_le`, `band_le_domain_adjoint`,
`norm_adjoint_band_le`); on such fields `L = 𝐝 - 𝐝†` is bounded (`norm_wave_le`, `band_wave`).
Hence every increasing exhausting sequence of measurable bands with bounded symbols is a
`Feec.HilbertComplex.ReducingFamily` (`bandFamily`; reducing by
`Feec.Fourier.reducingSubcomplex_band`, `P_N → 1` by `Feec.Fourier.tendsto_totalProj_band`). On
`ℝᵈ` the frequency balls `freqBall N = {x | |2πx| ≤ N}` are compact, so continuous symbols are
bounded on them (`bands`). `bandApprox` (`ReducingFamily.toApprox`: `X_N = B_N`, `ι_N` the
inclusion, `π_N` the Fourier truncation, `L_N = L|_{B_N}`) with the core `bandCore` (all data, zero
consistency defect) gives `bandApprox_verdict : (bandApprox …).Verdict (bandCore …)`, a one-line
application of `approxFEEC`; the truncated solution is the truncation of the exact one
(`bandApprox_sol`).

**Sobolev rates.** `sobolev 𝕜 E s` is the class `Hˢ` on the Fourier side: `(1 + |ξ|)ˢ x̂ ∈ L²`
(`IsSobolevRep`, norm `sobolevNorm`; the weight `(1 + |ξ|)ˢ` is equivalent to
`(1 + |ξ|²)^{s/2}`). For `s ≥ 0` the truncation error is `‖x - P_N x‖ ≤ (N + 1)^{-s} ‖x‖_{Hˢ}`
(`norm_sub_starProjection_le`), which is a rate class of `approxFEEC` with `C = 1`, `C' = 0`
(`sobolevRate`) and gives, for all `t ≥ 0`,
`‖e^{tL} x - ι_N e^{tL_N} π_N x‖ ≤ (N + 1)^{-s} ‖x‖_{Hˢ}` (`bandApprox_rate`) and, for a reducing
constraint `K ∋ x`, the same bound on the constraint residual (`bandApprox_residual_rate`).
Band-limited fields are in every class (`mem_sobolev_of_mem_band`), so each class is dense
(`dense_sobolev`), and the classes decrease (`sobolev_anti`).

**Instances.**

* **The EB system on `ℝ³`** (BGG complex (5.1), TSD constraint `{0} × L²(TSD) × ({0} × L²(TSD))`):
  `ebApprox`, `ebCore`, headline `einsteinBianchi_euclidean_approxFEEC`; with rates,
  `EuclideanEBVerdict` (`einsteinBianchi_euclidean_band`): TSD reduces `L`, error and TSD residual
  `≤ (N + 1)^{-s} ‖ξ₀‖_{Hˢ}`, residual `→ 0` uniformly on `[0, T]` for every TSD datum;
  `einsteinBianchi_euclidean_rate_two_add`: `H^{2+s}` data converge at rate `(N + 1)^{-s}`.
  Non-vacuity (`ebWitness_nonvacuous`): the explicit TSD field
  `𝟙_U · (a bᵀ + b aᵀ)(ξ)`, `a = (ξ₁, -ξ₀, 0)`, `b = ξ × a` (`ttMat`), is nonzero, band-limited
  (so in every `Hˢ`), in `D(L)` and non-stationary (`curl_ξ ≠ 0` on TSD matrices,
  `Feec.Fourier.SymCurl.mul_norm_le_two_norm_curl`); the TSD field
  `(1 + |ξ|)^{-8} (a bᵀ + b aᵀ)(ξ)` lies in `Hˢ` for `0 ≤ s ≤ 3`, is not band-limited for any `N`,
  and its truncated solutions have a positive error at every `N` and `t`
  (`decayWitness_nonvacuous`).
* **Maxwell's equations on `ℝᵈ`** (window `Λᵃ → Λᵃ⁺¹ → Λᵃ⁺²` of the de Rham complex, the Gauss
  laws `Feec.Instances.Maxwell.windowGauss`): `maxwellApprox`, `maxwellCore`, headline
  `maxwell_euclidean_approxFEEC`; with rates, `EuclideanMaxwellVerdict` (`maxwell_euclidean_band`).
  Non-vacuity (`maxwell_nonvacuous`, `a + 1 < d`): `(0, 0, d u)` for a cut-off constant field `u`,
  nonzero, band-limited and non-stationary (`exists_band_d_ne_zero`). The vanishing-field
  constraint does not reduce `L` (`maxwell_euclidean_not_isReducing_potential`, `a < d`), and its
  residuals along the truncated solutions tend to a positive limit
  (`maxwell_euclidean_potential_residual`, item 4 of `approxFEEC`, non-reducing branch).

## Scope and limits

* The bands `B_N` are reducing subcomplexes of `H` but **infinite-dimensional** (`L²` of a ball:
  the spectrum of `ℝᵈ` is continuous), so the frequency truncation is not a `ConstrainedFEEC`
  discretization (finite-dimensional `Vₕ`) and `constrainedFEEC` does not apply to it; it is an
  `ApproxFEEC` through `ReducingFamily.toApprox`. It is a semi-discretization in frequency: a
  fully discrete method would also discretize the frequency ball (sampling or quadrature), which
  is not formalized.
* It commits no variational crime: `ι_N` is the inclusion and the consistency defect is `0`. The
  instances with a nonzero defect are the abstract witnesses of
  `Feec.HilbertComplex.Approximation.ApproxFEECWitness`.
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

@[simp] theorem bandFamily_B (A : ℕ → Set α) hA hmono hcov hbd (N : ℕ) :
    (bandFamily S A hA hmono hcov hbd).B N = totalSub (S.band (A N)) := rfl

@[simp] theorem bandFamily_l (A : ℕ → Set α) hA hmono hcov hbd :
    (bandFamily S A hA hmono hcov hbd).l = atTop := rfl

end BandFamily

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

@[simp] theorem bands_B (S : SymbolComplex 𝕜 (volume : Measure (EuclideanSpace ℝ d)) c E)
    (hS : ∀ i j, Continuous (S.m i j)) (N : ℕ) :
    (bands S hS).B N = totalSub (S.band (freqBall N)) := rfl

@[simp] theorem bands_l (S : SymbolComplex 𝕜 (volume : Measure (EuclideanSpace ℝ d)) c E)
    (hS : ∀ i j, Continuous (S.m i j)) : (bands S hS).l = atTop := rfl

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

/-- The Bessel-type weight `(1 + |2πx|)ˢ` (equivalent to `(1 + |ξ|²)^{s/2}`, `ξ = 2πx`). -/
def weight (s : ℝ) (x : EuclideanSpace ℝ d) : ℝ := (1 + ‖Euclidean.scale x‖) ^ s

theorem one_le_one_add_norm (x : EuclideanSpace ℝ d) : 1 ≤ 1 + ‖Euclidean.scale x‖ :=
  le_add_of_nonneg_right (norm_nonneg _)

theorem weight_pos (s : ℝ) (x : EuclideanSpace ℝ d) : 0 < weight s x :=
  Real.rpow_pos_of_pos (by linarith [one_le_one_add_norm x]) s

theorem continuous_weight (s : ℝ) : Continuous (weight (d := d) s) :=
  (continuous_const.add (continuous_norm.comp Euclidean.continuous_scale)).rpow_const
    fun x => Or.inl (ne_of_gt (by
      change 0 < 1 + ‖Euclidean.scale x‖; linarith [one_le_one_add_norm x]))

theorem weight_mul_weight_neg (s : ℝ) (x : EuclideanSpace ℝ d) :
    weight (-s) x * weight s x = 1 := by
  rw [weight, Real.rpow_neg (by linarith [one_le_one_add_norm x])]
  exact inv_mul_cancel₀ (weight_pos s x).ne'

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

theorem weight_le_one {s : ℝ} (hs : s ≤ 0) (x : EuclideanSpace ℝ d) : weight s x ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_one_add_norm x) hs

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

omit [Fintype ι] in
/-- A field is in `Hˢ` when its weighted transform is in `L²`. -/
theorem isSobolevRep_of_memLp {s : ℝ}
    {x : PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d))}
    (h : ∀ i, MemLp (fun ξ => ((weight s ξ : ℝ) : 𝕜) • (x i : EuclideanSpace ℝ d → E i) ξ) 2
      volume) :
    IsSobolevRep 𝕜 s x (WithLp.toLp 2 fun i => (h i).toLp _) := fun i => by
  filter_upwards [(h i).coeFn_toLp] with ξ hξ
  change _ = _ • ((h i).toLp _ : EuclideanSpace ℝ d → E i) ξ
  rw [hξ, smul_smul, ← RCLike.ofReal_mul, weight_mul_weight_neg, RCLike.ofReal_one, one_smul]

omit [Fintype ι] in
theorem memLp_weight_smul {s : ℝ} {i : ι}
    {u : Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d))} {C : ℝ}
    (hC : ∀ᵐ ξ ∂(volume : Measure (EuclideanSpace ℝ d)), u ξ ≠ 0 → weight s ξ ≤ C) :
    MemLp (fun ξ => ((weight s ξ : ℝ) : 𝕜) • (u : EuclideanSpace ℝ d → E i) ξ) 2 volume := by
  refine MemLp.of_le_mul (Lp.memLp u) ?_ (c := C) ?_
  · exact ((RCLike.continuous_ofReal.comp (continuous_weight s)).aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable u)
  · filter_upwards [hC] with ξ h
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (weight_pos s ξ)]
    by_cases hu : u ξ = 0
    · rw [hu, norm_zero, mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right (h hu) (norm_nonneg _)

omit [Fintype ι] in
theorem zero_mem_sobolev (s : ℝ) :
    (0 : PiLp 2 fun i => Lp (E i) 2 volume) ∈ sobolev 𝕜 E (d := d) s :=
  ⟨0, fun i => by
    filter_upwards [Lp.coeFn_zero (E i) 2 (volume : Measure (EuclideanSpace ℝ d))] with ξ h
    simp only [PiLp.zero_apply]
    rw [h, Pi.zero_apply, smul_zero]⟩

/-- **The Sobolev classes decrease**: `Hˢ' ⊆ Hˢ` for `s ≤ s'`, with `‖x‖_{Hˢ} ≤ ‖x‖_{Hˢ'}`. -/
theorem sobolev_anti {s s' : ℝ} (hss : s ≤ s')
    {x : PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d))}
    (hx : x ∈ sobolev 𝕜 E s') : x ∈ sobolev 𝕜 E s ∧ sobolevNorm 𝕜 s x ≤ sobolevNorm 𝕜 s' x := by
  obtain ⟨y, hy⟩ := hx
  have hm : ∀ i, MemLp (fun ξ => ((weight (s - s') ξ : ℝ) : 𝕜) •
      (y i : EuclideanSpace ℝ d → E i) ξ) 2 volume := fun i =>
    memLp_weight_smul (C := 1) (ae_of_all _ fun ξ _ => weight_le_one (by linarith) ξ)
  set y' : PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d)) :=
    WithLp.toLp 2 fun i => (hm i).toLp _
  have hy' : IsSobolevRep 𝕜 s x y' := fun i => by
    filter_upwards [hy i, (hm i).coeFn_toLp] with ξ h1 h2
    change _ = _ • ((hm i).toLp _ : EuclideanSpace ℝ d → E i) ξ
    rw [h1, h2, smul_smul, ← RCLike.ofReal_mul, ← weight_add]
    ring_nf
  refine ⟨⟨y', hy'⟩, ?_⟩
  rw [sobolevNorm_eq hy', sobolevNorm_eq hy]
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  refine (Lp.norm_le_mul_norm_of_ae_le_mul (c := 1) ?_).trans (one_mul _).le
  filter_upwards [(hm i).coeFn_toLp] with ξ h
  change ‖((hm i).toLp _ : EuclideanSpace ℝ d → E i) ξ‖ ≤ _
  rw [h, norm_smul, RCLike.norm_ofReal, abs_of_pos (weight_pos _ ξ)]
  exact mul_le_mul_of_nonneg_right (weight_le_one (by linarith) ξ) (norm_nonneg _)

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

omit [Fintype ι] [∀ i, CompleteSpace (E i)] in
/-- **Band-limited fields are in every Sobolev class.** -/
theorem mem_sobolev_of_mem_band {M : ℕ}
    {x : PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d))}
    (hx : x ∈ totalSub (S.band (freqBall M))) (s : ℝ) : x ∈ sobolev 𝕜 E s := by
  obtain ⟨C, hC⟩ := exists_bound_freqBall (continuous_weight (d := d) s) M
  refine ⟨_, isSobolevRep_of_memLp fun i => memLp_weight_smul (C := C) ?_⟩
  filter_upwards [mem_band_iff.1 (hx i)] with ξ hξ hne
  have hm : ξ ∈ freqBall M := by by_contra h; exact hne (hξ h)
  have := hC ξ hm
  rwa [Real.norm_of_nonneg (weight_pos s ξ).le] at this

/-- **The Sobolev classes are dense** (they contain the band-limited fields `P_N x → x`). -/
theorem tendsto_starProjection_freqBall
    (x : PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d))) :
    Tendsto (fun N => (totalSub (S.band (freqBall N))).starProjection x) atTop (𝓝 x) :=
  tendsto_totalProj_band S measurableSet_freqBall freqBall_mono exists_mem_freqBall x

include S in
theorem dense_sobolev (s : ℝ) :
    Dense (sobolev 𝕜 E (d := d) s) := fun x =>
  mem_closure_of_tendsto (tendsto_starProjection_freqBall S x) (Eventually.of_forall fun _ =>
    mem_sobolev_of_mem_band S (Submodule.starProjection_apply_mem _ x) s)

end Sobolev

/-! ### The approximating FEEC discretization by frequency truncation -/

section Approx

variable {𝕜 : Type*} [RCLike 𝕜] {d : Type*} [Fintype d] {ι : Type*} [Fintype ι]
  {c : ComplexShape ι} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace 𝕜 (E i)] [∀ i, CompleteSpace (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, IsScalarTower ℝ 𝕜 (E i)]
  (S : SymbolComplex 𝕜 (volume : Measure (EuclideanSpace ℝ d)) c E)
  (hS : ∀ i j, Continuous (S.m i j))
  (K : Submodule 𝕜 (PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d))))
  (hK : IsClosed (K : Set (PiLp 2 fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d)))))

/-- **The frequency-truncation discretization** of the Hodge wave equation on `ℝᵈ` with a closed
constraint `K`: `X_N = B_N` (fields with `|ξ| ≤ N`), `ι_N` the inclusion, `π_N` the orthogonal
projection (the Fourier truncation), `L_N = L|_{B_N}`. -/
abbrev bandApprox : ApproxFEEC S.toHilbertComplex ℕ := (bands S hS).toApprox K hK

/-- Its core: all data, with zero consistency defect (the truncation commutes with `L`). -/
abbrev bandCore : (bandApprox S hS K hK).Core := (bands S hS).toCore K hK

theorem bandCore_data : (bandCore S hS K hK).Data = ⊤ := rfl

/-- **The approximating FEEC theorem for frequency truncation on `ℝᵈ`.** -/
theorem bandApprox_verdict : (bandApprox S hS K hK).Verdict (bandCore S hS K hK) :=
  approxFEEC _ _

/-- The truncated solution is the truncation of the exact solution:
`ι_N e^{tL_N} P_N x = P_N e^{tL} x`. -/
theorem bandApprox_sol (N : ℕ) (x : PiLp 2 fun i => Lp (E i) 2 volume) (t : ℝ) :
    (bandApprox S hS K hK).sol N ((bandApprox S hS K hK).proj N x) t =
      (totalSub (S.band (freqBall N))).starProjection (S.toHilbertComplex.waveGroup.S t x) :=
  (bands S hS).toApprox_sol K hK N x t

/-- **The Sobolev rate classes** on `[0, T]`: `Hˢ`, `s ≥ 0`, with `h_N = 1/(N + 1)`, order `s`,
`C = 1`, `C' = 0`. -/
def sobolevRate (T : ℝ) {s : ℝ} (hs : 0 ≤ s) : (bandApprox S hS K hK).RateClass T :=
  (bands S hS).rateClass K hK T (sobolev 𝕜 E s) (sobolevNorm 𝕜 s) (fun N => 1 / ((N : ℝ) + 1))
    s 1 fun x hx N => by
      obtain ⟨y, hy⟩ := hx
      rw [one_mul, sobolevNorm_eq hy]
      exact norm_sub_starProjection_le S hs hy N

theorem sobolevRate_data (T : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (sobolevRate S hS K hK T hs).Data = sobolev 𝕜 E s := rfl

/-- **The Sobolev rate** (item 3c of `approxFEEC` for the class `Hˢ`): for `x ∈ Hˢ`, `s ≥ 0`,
`‖e^{tL} x - ι_N e^{tL_N} π_N x‖ ≤ (N + 1)^{-s} ‖x‖_{Hˢ}` for all `t ≥ 0`. -/
theorem bandApprox_rate {s : ℝ} (hs : 0 ≤ s) {x : PiLp 2 fun i => Lp (E i) 2 volume}
    (hx : x ∈ sobolev 𝕜 E s) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖S.toHilbertComplex.waveGroup.S t x -
        (bandApprox S hS K hK).sol N ((bandApprox S hS K hK).proj N x) t‖ ≤
      (1 / ((N : ℝ) + 1)) ^ s * sobolevNorm 𝕜 s x := by
  set R := sobolevRate S hS K hK t hs
  have h := (bandApprox_verdict S hS K hK).2.2.2.2.1 t R x hx N
    ((bandApprox S hS K hK).proj N x) t ⟨ht, le_rfl⟩
  have hp : R.p x N 0 = (bandApprox S hS K hK).proj N x := by
    change ((bands S hS).B N).orthogonalProjectionOnto (S.toHilbertComplex.waveGroup.S 0 x) = _
    rw [C0Group.S_zero_apply]; rfl
  have hC : R.C = 1 := rfl
  have hC' : R.C' = 0 := rfl
  have hm : R.meshSize N = 1 / ((N : ℝ) + 1) := rfl
  have hα : R.α = s := rfl
  have hn : R.classNorm x = sobolevNorm 𝕜 s x := rfl
  rw [hp, sub_self, norm_zero, mul_zero, add_zero, hC, hC', hm, hα, hn, mul_zero, zero_mul,
    add_zero, one_mul] at h
  exact h

/-- **The constraint residual rate** for a reducing constraint: for `x ∈ K ∩ Hˢ`, `s ≥ 0`,
`dist(ι_N e^{tL_N} π_N x, K) ≤ (N + 1)^{-s} ‖x‖_{Hˢ}` for all `t ≥ 0`. -/
theorem bandApprox_residual_rate (hKr : S.toHilbertComplex.wave.IsReducing K) {s : ℝ}
    (hs : 0 ≤ s) {x : PiLp 2 fun i => Lp (E i) 2 volume} (hxK : x ∈ K)
    (hx : x ∈ sobolev 𝕜 E s) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    infDist ((bandApprox S hS K hK).sol N ((bandApprox S hS K hK).proj N x) t) (K : Set _) ≤
      (1 / ((N : ℝ) + 1)) ^ s * sobolevNorm 𝕜 s x :=
  (((bandApprox_verdict S hS K hK).2.2.2.2.2.1 hKr x hxK).1 N _ t).trans
    (bandApprox_rate S hS K hK hs hx N ht)

/-- **Convergence and vanishing residual for all data** (the core is all of `W`): for every `x`,
`ι_N e^{tL_N} π_N x → e^{tL} x` uniformly on `[0, T]`, and for a reducing `K` and `x ∈ K` the
residual tends to `0` uniformly on `[0, T]`. -/
theorem bandApprox_converges (T : ℝ) (x : PiLp 2 fun i => Lp (E i) 2 volume) :
    TendstoUniformlyOn (fun N t => (bandApprox S hS K hK).sol N ((bandApprox S hS K hK).proj N x) t)
      (fun t => S.toHilbertComplex.waveGroup.S t x) atTop (Icc 0 T) := by
  have hx : x ∈ (bandCore S hS K hK).Data.topologicalClosure :=
    Submodule.le_topologicalClosure _ (by rw [bandCore_data]; trivial)
  have h := ((bandApprox_verdict S hS K hK).2.2.2.1 T x hx)
  exact h.2 _ h.1

theorem bandApprox_residual (hKr : S.toHilbertComplex.wave.IsReducing K) (T : ℝ)
    {x : PiLp 2 fun i => Lp (E i) 2 volume} (hxK : x ∈ K) :
    TendstoUniformlyOn (fun N t => infDist
        ((bandApprox S hS K hK).sol N ((bandApprox S hS K hK).proj N x) t) (K : Set _))
      (fun _ => 0) atTop (Icc 0 T) := by
  have hx : x ∈ (bandCore S hS K hK).Data.topologicalClosure :=
    Submodule.le_topologicalClosure _ (by rw [bandCore_data]; trivial)
  exact ((bandApprox_verdict S hS K hK).2.2.2.2.2.1 hKr x hxK).2 hx T _
    ((bandApprox_verdict S hS K hK).2.2.2.1 T x hx).1

end Approx

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

/-- **The frequency-truncation discretization of the EB system on `ℝ³`**: the BGG complex (5.1)
on `ℝ³` (Fourier side) with the TSD constraint `K = {0} × L²(TSD) × ({0} × L²(TSD))`. -/
abbrev ebApprox : ApproxFEEC complex ℕ :=
  bandApprox (Euclidean.symbolComplex bggFamily) (continuous_symbolComplex_m bggFamily)
    (totalSub constraint) isClosed_totalSub

/-- Its core: all data, with zero consistency defect. -/
abbrev ebCore : ebApprox.Core :=
  bandCore (Euclidean.symbolComplex bggFamily) (continuous_symbolComplex_m bggFamily)
    (totalSub constraint) isClosed_totalSub

/-- **The approximating FEEC theorem for the EB system on `ℝ³`**, frequency truncation
`|ξ| ≤ N`. -/
theorem einsteinBianchi_euclidean_approxFEEC : ebApprox.Verdict ebCore := approxFEEC _ _

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

theorem ttMat_mem_symSub (η : Freq) : ttMat η ∈ symSub := fun a b => by
  simp only [ttMat_apply]; ring_nf

theorem ttMat_quad (η : Freq) :
    ∑ a, ∑ b, (η a : ℂ) * (η b : ℂ) * ttMat η (a, b) = 0 := by
  simp only [ttMat_apply, Fin.sum_univ_three, tvA, tvB]
  push_cast
  simp
  ring

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

theorem bgg_ttMat_ne_zero {η : Freq} (h : η 0 ≠ 0) : bgg η (ttMat η) ≠ 0 := by
  have hη : 0 < ‖η‖ := norm_pos_iff.2 fun h0 => h (by rw [h0]; rfl)
  have hM : 0 < ‖ttMat η‖ := norm_pos_iff.2 (ttMat_ne_zero h)
  have hc := mul_norm_le_two_norm_curl (ttMat_mem_symSub η) (ttMat_quad η)
  have hcurl : curl η (ttMat η) ≠ 0 := fun h0 => by
    rw [h0, norm_zero, mul_zero] at hc
    exact absurd hc (not_le.2 (mul_pos hη hM))
  intro h0
  apply hcurl
  have := congrArg (fun v : VM => (WithLp.ofLp v).2) h0
  simpa [bgg_apply] using this

/-- The centre `(1, 0, 0)` of the support of the witness. -/
abbrev ebCentre : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1

/-- The support `U = B̄((1, 0, 0), 1/4)` of the witness (in Fourier space). -/
abbrev ebSupport : Set (EuclideanSpace ℝ (Fin 3)) := closedBall ebCentre (1 / 4)

theorem isCompact_ebSupport : IsCompact ebSupport := isCompact_closedBall _ _

theorem scale_zero_ne_zero {ξ : EuclideanSpace ℝ (Fin 3)} (hξ : ξ ∈ ebSupport) :
    Euclidean.scale ξ 0 ≠ 0 := by
  have h1 : |ξ 0 - 1| ≤ 1 / 4 := by
    have := (PiLp.norm_apply_le (ξ - ebCentre) 0).trans (mem_closedBall_iff_norm.1 hξ)
    simpa [ebCentre, Real.norm_eq_abs] using this
  have h2 : 0 < ξ 0 := by linarith [neg_abs_le (ξ 0 - 1)]
  simp only [Euclidean.scale, PiLp.smul_apply, smul_eq_mul]
  positivity

/-- The profile `ξ ↦ (a bᵀ + b aᵀ)(2πξ)`. -/
def ebFun (ξ : EuclideanSpace ℝ (Fin 3)) : W3 ℂ Mat VM 1 := ttMat (Euclidean.scale ξ)

theorem continuous_ebFun : Continuous ebFun := continuous_ttMat.comp Euclidean.continuous_scale

/-- The TSD field `u = 𝟙_U · (a bᵀ + b aᵀ)(2πξ)` (Fourier side). -/
def ebField : Space 1 := indicatorField ebSupport isCompact_ebSupport ebFun continuous_ebFun

theorem coeFn_ebField :
    (ebField : EuclideanSpace ℝ (Fin 3) → W3 ℂ Mat VM 1) =ᵐ[volume] ebSupport.indicator ebFun :=
  coeFn_indicatorField isCompact_ebSupport continuous_ebFun

/-- **The TSD witness** `(0, u, 0)`. -/
def ebWitness : PiLp 2 Space := WithLp.toLp 2 (Pi.single 1 ebField)

theorem ebWitness_one : ebWitness 1 = ebField := by simp [ebWitness]

theorem ebWitness_ne_one {i : Fin 3} (hi : i ≠ 1) : ebWitness i = 0 := by
  simp [ebWitness, hi]

theorem ebWitness_mem_constraint : ebWitness ∈ totalSub constraint := fun i => by
  by_cases hi : i = 1
  · subst hi
    rw [ebWitness_one, Operator.mem_fibreSub]
    filter_upwards [coeFn_ebField] with ξ hξ
    rw [hξ]
    by_cases hU : ξ ∈ ebSupport
    · rw [indicator_of_mem hU]; exact ttMat_mem_tsd _
    · rw [indicator_of_notMem hU]; exact Submodule.zero_mem _
  · rw [ebWitness_ne_one hi]; exact Submodule.zero_mem _

theorem exists_ebWitness_mem_band :
    ∃ N, ebWitness ∈ totalSub ((Euclidean.symbolComplex bggFamily).band (freqBall N)) := by
  obtain ⟨N, hN⟩ := exists_subset_freqBall isCompact_ebSupport
  refine ⟨N, fun i => ?_⟩
  by_cases hi : i = 1
  · subst hi
    rw [ebWitness_one]
    exact indicatorField_mem_band (Euclidean.symbolComplex bggFamily) isCompact_ebSupport _ hN
  · rw [ebWitness_ne_one hi]; exact Submodule.zero_mem _

theorem ebWitness_ne_zero : ebWitness ≠ 0 := fun h => by
  have h1 : ebField = 0 := by rw [← ebWitness_one, h]; rfl
  exact indicatorField_ne_zero isCompact_ebSupport continuous_ebFun
    (Metric.measure_closedBall_pos volume _ (by norm_num))
    (fun ξ hξ => ttMat_ne_zero (scale_zero_ne_zero hξ)) h1

/-- **Non-vacuity of the `ℝ³` row**: a nonzero TSD datum in every Sobolev class (band-limited),
in `D(L)` and non-stationary (`L x ≠ 0`). -/
theorem ebWitness_nonvacuous :
    ebWitness ∈ totalSub constraint ∧ (∀ s, ebWitness ∈ sobolev ℂ (W3 ℂ Mat VM) s) ∧
      ebWitness ≠ 0 ∧ ∃ hx : ebWitness ∈ complex.wave.domain, complex.wave ⟨_, hx⟩ ≠ 0 := by
  obtain ⟨N, hN⟩ := exists_ebWitness_mem_band
  have hD : ebWitness ∈ complex.wave.domain :=
    (bands (Euclidean.symbolComplex bggFamily) (continuous_symbolComplex_m bggFamily)).le_domain
      N hN
  refine ⟨ebWitness_mem_constraint, fun s => mem_sobolev_of_mem_band _ hN s, ebWitness_ne_zero,
    hD, fun h0 => ?_⟩
  have hsq := complex.norm_wave_sq ⟨_, hD⟩
  rw [h0, norm_zero] at hsq
  have hd := complex.norm_d_le_norm_totalD ⟨_, hD.1⟩ 1 2
  have hz : ‖complex.d 1 2 ⟨ebWitness 1, hD.1 1 2⟩‖ = 0 := by
    have h1 : ‖complex.totalD ⟨_, hD.1⟩‖ = 0 := by
      nlinarith [sq_nonneg ‖complex.totalD ⟨_, hD.1⟩‖,
        sq_nonneg ‖complex.dual.totalD ⟨_, hD.2⟩‖, norm_nonneg (complex.totalD ⟨_, hD.1⟩)]
    exact le_antisymm (hd.trans h1.le) (norm_nonneg _)
  have hne : complex.d 1 2 ⟨ebWitness 1, hD.1 1 2⟩ ≠ 0 := by
    refine d_ne_zero_of_ae_eq (Euclidean.symbolComplex bggFamily) ⟨ebWitness 1, hD.1 1 2⟩
      (g := ebSupport.indicator ebFun) ?_
      (Metric.measure_closedBall_pos volume ebCentre (by norm_num : (0 : ℝ) < 1 / 4))
      fun ξ hξ => ?_
    · change ((ebWitness 1 : Space 1) : EuclideanSpace ℝ (Fin 3) → W3 ℂ Mat VM 1) =ᵐ[volume] _
      rw [ebWitness_one]
      exact coeFn_ebField
    · rw [indicator_of_mem hξ]
      exact bgg_ttMat_ne_zero (scale_zero_ne_zero hξ)
  exact hne (norm_eq_zero.1 hz)

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

/-- The TSD field `v = (1 + |2πξ|)^{-8} (a bᵀ + b aᵀ)(2πξ)` (Fourier side). -/
def decayField (r : ℝ) (hr : r < -9 / 2) : Space 1 := (memLp_decayFun hr).toLp _

/-- **The TSD witness `(0, v, 0)`, `v = (1 + |2πξ|)^{-8} (a bᵀ + b aᵀ)(2πξ)`.** -/
def decayWitness : PiLp 2 Space := WithLp.toLp 2 (Pi.single 1 (decayField (-8) (by norm_num)))

theorem decayWitness_one : decayWitness 1 = decayField (-8) (by norm_num) := by
  simp [decayWitness]

theorem decayWitness_ne_one {i : Fin 3} (hi : i ≠ 1) : decayWitness i = 0 := by
  simp [decayWitness, hi]

theorem le_apply_zero {c : ℝ} {ξ : EuclideanSpace ℝ (Fin 3)}
    (hξ : ξ ∈ closedBall (c • ebCentre) (1 / 4)) : c - 1 / 4 ≤ ξ 0 := by
  have h1 : |ξ 0 - c| ≤ 1 / 4 := by
    have := (PiLp.norm_apply_le (ξ - c • ebCentre) 0).trans (mem_closedBall_iff_norm.1 hξ)
    simpa [ebCentre, Real.norm_eq_abs] using this
  linarith [neg_abs_le (ξ 0 - c)]

/-- **Non-vacuity of the Sobolev rate beyond band-limited data**: `decayWitness` is TSD, lies in
`Hˢ` for every `0 ≤ s ≤ 3` (so in the class `H^{2+s}` for `s ≤ 1`), is not band-limited for any
`N`, and the truncated solutions have a positive error at every `N` and `t` (bounded by
`(N + 1)^{-s} ‖ξ₀‖_{Hˢ}`, `einsteinBianchi_euclidean_band`). -/
theorem decayWitness_nonvacuous :
    decayWitness ∈ totalSub constraint ∧
      (∀ s, 0 ≤ s → s ≤ 3 → decayWitness ∈ sobolev ℂ (W3 ℂ Mat VM) s) ∧
      (∀ N, decayWitness ∉ totalSub ((Euclidean.symbolComplex bggFamily).band (freqBall N))) ∧
      ∀ (N : ℕ) (t : ℝ), 0 < ‖complex.waveGroup.S t decayWitness -
        ebApprox.sol N (ebApprox.proj N decayWitness) t‖ := by
  have hK : decayWitness ∈ totalSub constraint := fun i => by
    by_cases hi : i = 1
    · subst hi
      rw [decayWitness_one, Operator.mem_fibreSub]
      filter_upwards [(memLp_decayFun (r := -8) (by norm_num)).coeFn_toLp] with ξ hξ
      change (decayField (-8) _ : EuclideanSpace ℝ (Fin 3) → W3 ℂ Mat VM 1) ξ ∈ tsd _
      rw [decayField, hξ]
      exact decayFun_mem_tsd _ _
    · rw [decayWitness_ne_one hi]; exact Submodule.zero_mem _
  have hnb : ∀ N, decayWitness ∉
      totalSub ((Euclidean.symbolComplex bggFamily).band (freqBall N)) := fun N hN => by
    have h1 := mem_band_iff.1 (hN 1)
    rw [decayWitness_one] at h1
    set U := closedBall (((N : ℝ) + 2) • ebCentre) (1 / 4)
    have hpos : 0 < volume U := Metric.measure_closedBall_pos volume _ (by norm_num)
    refine hpos.ne' (measure_mono_null (t := {ξ | ¬ (ξ ∉ freqBall N →
      (decayFun (-8) ξ = 0))}) (fun ξ hξ => ?_) ?_)
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
      filter_upwards [h1, (memLp_decayFun (r := -8) (by norm_num)).coeFn_toLp] with ξ h2 h3
      intro hξ
      rw [← h3]; exact h2 hξ
  refine ⟨hK, fun s hs hs3 => ?_, hnb, fun N t => ?_⟩
  · have hr : s - 8 < -9 / 2 := by linarith
    refine ⟨WithLp.toLp 2 (Pi.single 1 (decayField (s - 8) hr)), fun i => ?_⟩
    by_cases hi : i = 1
    · subst hi
      rw [decayWitness_one]
      simp only [Pi.single_eq_same]
      filter_upwards [(memLp_decayFun (r := -8) (by norm_num)).coeFn_toLp,
        (memLp_decayFun hr).coeFn_toLp] with ξ h1 h2
      change (decayField (-8) _ : EuclideanSpace ℝ (Fin 3) → W3 ℂ Mat VM 1) ξ =
        _ • (decayField (s - 8) hr : EuclideanSpace ℝ (Fin 3) → W3 ℂ Mat VM 1) ξ
      rw [decayField, decayField, h1, h2, show (-8 : ℝ) = -s + (s - 8) by ring, decayFun_add]
      rfl
    · rw [decayWitness_ne_one hi]
      simp only [Pi.single_eq_of_ne hi]
      filter_upwards [Lp.coeFn_zero (W3 ℂ Mat VM i) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))]
        with ξ h
      rw [h, Pi.zero_apply, smul_zero]
  · set F := bands (Euclidean.symbolComplex bggFamily) (continuous_symbolComplex_m bggFamily)
    have hs := bandApprox_sol (Euclidean.symbolComplex bggFamily)
      (continuous_symbolComplex_m bggFamily) (totalSub constraint) isClosed_totalSub N
      decayWitness t
    have hcomm : (Euclidean.symbolComplex bggFamily).toHilbertComplex.waveGroup.S t
        ((totalSub ((Euclidean.symbolComplex bggFamily).band (freqBall N))).starProjection
          decayWitness) =
        (totalSub ((Euclidean.symbolComplex bggFamily).band (freqBall N))).starProjection
          ((Euclidean.symbolComplex bggFamily).toHilbertComplex.waveGroup.S t decayWitness) :=
      F.waveGroup_starProjection N t decayWitness
    change 0 < ‖(Euclidean.symbolComplex bggFamily).toHilbertComplex.waveGroup.S t decayWitness -
      ebApprox.sol N (ebApprox.proj N decayWitness) t‖
    rw [show ebApprox.sol N (ebApprox.proj N decayWitness) t = _ from hs, ← hcomm,
      ← _root_.map_sub,
      (Euclidean.symbolComplex bggFamily).toHilbertComplex.isIsometric_waveGroup t]
    refine norm_pos_iff.2 (sub_ne_zero.2 fun h => hnb N ?_)
    have h' : (F.B N).starProjection decayWitness = decayWitness := h.symm
    exact Submodule.starProjection_eq_self_iff.1 h'

/-! #### The `ℝ³` verdict with Sobolev rates -/

/-- **The verdict of the approximating FEEC theorem for the EB system on `ℝ³`** (frequency
truncation `|ξ| ≤ N`): the full `ApproxFEEC.Verdict` (core = all data, so items 3b and 4 apply to
every datum); the TSD constraint reduces `L`; for data in `Hˢ`, `s ≥ 0`, the error and (for TSD
data) the constraint residual are `≤ (N + 1)^{-s} ‖ξ₀‖_{Hˢ}` for all `t ≥ 0`; for every TSD
datum the residual of `ι_N e^{tL_N} π_N ξ₀` tends to `0` uniformly on `[0, T]`. -/
abbrev EuclideanEBVerdict : Prop :=
    ebApprox.Verdict ebCore ∧
    complex.wave.IsReducing (totalSub constraint) ∧
    (∀ s : ℝ, 0 ≤ s → ∀ x ∈ sobolev ℂ (W3 ℂ Mat VM) s, ∀ (N : ℕ) (t : ℝ), 0 ≤ t →
      ‖complex.waveGroup.S t x - ebApprox.sol N (ebApprox.proj N x) t‖ ≤
        (1 / ((N : ℝ) + 1)) ^ s * sobolevNorm ℂ s x) ∧
    (∀ s : ℝ, 0 ≤ s → ∀ x ∈ totalSub constraint, x ∈ sobolev ℂ (W3 ℂ Mat VM) s →
      ∀ (N : ℕ) (t : ℝ), 0 ≤ t →
      infDist (ebApprox.sol N (ebApprox.proj N x) t) (totalSub constraint : Set (PiLp 2 Space)) ≤
        (1 / ((N : ℝ) + 1)) ^ s * sobolevNorm ℂ s x) ∧
    (∀ T : ℝ, ∀ x ∈ totalSub constraint, TendstoUniformlyOn
      (fun N t => infDist (ebApprox.sol N (ebApprox.proj N x) t)
        (totalSub constraint : Set (PiLp 2 Space))) (fun _ => 0) atTop (Icc 0 T))

/-- **The EB system on `ℝ³` through the approximating FEEC theorem**, with Sobolev rates.
[QuennevilleBelair2015], §4.12–4.13, Ch. 6 -/
theorem einsteinBianchi_euclidean_band : EuclideanEBVerdict :=
  ⟨einsteinBianchi_euclidean_approxFEEC, ebApprox_isReducing,
    fun _ hs _ hx N _ ht => bandApprox_rate (Euclidean.symbolComplex bggFamily)
      (continuous_symbolComplex_m bggFamily) (totalSub constraint) isClosed_totalSub hs hx N ht,
    fun _ hs _ hxK hx N _ ht => bandApprox_residual_rate (Euclidean.symbolComplex bggFamily)
      (continuous_symbolComplex_m bggFamily) (totalSub constraint) isClosed_totalSub
      ebApprox_isReducing hs hxK hx N ht,
    fun T _ hxK => bandApprox_residual (Euclidean.symbolComplex bggFamily)
      (continuous_symbolComplex_m bggFamily) (totalSub constraint) isClosed_totalSub
      ebApprox_isReducing T hxK⟩

/-- **`H^{2+s}` data converge at rate `(N + 1)^{-s}`** (as for the spectral rows of `𝕋³` and the
mirror cube, which need `H^{2+s}` for the graph-norm rate of `constrainedFEEC`; here the truncation
is exact on the bands and the rate is in fact `(N + 1)^{-(2+s)}`). -/
theorem einsteinBianchi_euclidean_rate_two_add {s : ℝ} (hs : 0 ≤ s) {x : PiLp 2 Space}
    (hx : x ∈ sobolev ℂ (W3 ℂ Mat VM) (2 + s)) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖complex.waveGroup.S t x - ebApprox.sol N (ebApprox.proj N x) t‖ ≤
      (1 / ((N : ℝ) + 1)) ^ s * sobolevNorm ℂ (2 + s) x := by
  refine (einsteinBianchi_euclidean_band.2.2.1 (2 + s) (by linarith) x hx N t ht).trans ?_
  have hN : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  have hN1 : 1 / ((N : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hnorm : 0 ≤ sobolevNorm ℂ (2 + s) x := by
    obtain ⟨y, hy⟩ := hx; rw [sobolevNorm_eq hy]; exact norm_nonneg _
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hN hN1 (by linarith)) hnorm

end EinsteinBianchi

/-! ### Maxwell's equations on `ℝᵈ` -/

section Maxwell

open Feec.Models.Euclidean.DeRham Feec.Instances.Maxwell Feec.Fourier.Exterior

variable (d : Type*) [Fintype d] [LinearOrder d] (a : ℕ)

/-- The index map `i ↦ a + i` of the window reflects the relation. -/
theorem window_rel (i j : Fin 3) (h : (ComplexShape.up ℕ).Rel (a + (i : ℕ)) (a + (j : ℕ))) :
    (ComplexShape.window 3).Rel i j := by
  change a + (i : ℕ) + 1 = a + j at h
  change i.val + 1 = j.val
  omega

/-- The symbol complex of the Maxwell window `Λᵃ → Λᵃ⁺¹ → Λᵃ⁺²` of `ℝᵈ` (Fourier side). -/
abbrev maxwellSymbol :
    SymbolComplex ℂ (volume : Measure (EuclideanSpace ℝ d)) (ComplexShape.window 3)
      fun i : Fin 3 => Form ℂ d (a + i) :=
  (Euclidean.symbolComplex (deRham d)).restrict (fun i : Fin 3 => a + (i : ℕ)) (window_rel a)

theorem maxwellSymbol_toHilbertComplex :
    (maxwellSymbol d a).toHilbertComplex = (complex d).window a 3 := rfl

theorem continuous_maxwellSymbol_m (i j : Fin 3) : Continuous ((maxwellSymbol d a).m i j) :=
  continuous_symbolComplex_m (deRham d) _ _

/-- **The frequency-truncation discretization of Maxwell's equations on `ℝᵈ`** (degree `a`;
`d = 3`, `a = 0` is the classical system), with the Gauss laws `σ = 0`, `d†E = 0`, `dB = 0`. -/
abbrev maxwellApprox : ApproxFEEC ((complex d).window a 3) ℕ :=
  bandApprox (maxwellSymbol d a) (continuous_maxwellSymbol_m d a) (windowGauss (complex d) a)
    (isClosed_gauss _ _)

/-- Its core: all data, with zero consistency defect. -/
abbrev maxwellCore : (maxwellApprox d a).Core :=
  bandCore (maxwellSymbol d a) (continuous_maxwellSymbol_m d a) (windowGauss (complex d) a)
    (isClosed_gauss _ _)

/-- **The approximating FEEC theorem for Maxwell's equations on `ℝᵈ`**, frequency truncation
`|ξ| ≤ N`. -/
theorem maxwell_euclidean_approxFEEC : (maxwellApprox d a).Verdict (maxwellCore d a) :=
  approxFEEC _ _

/-- The Gauss laws reduce the Maxwell operator of `ℝᵈ`. [QuennevilleBelair2015], Prop. 4.16 -/
theorem maxwellApprox_isReducing :
    ((complex d).window a 3).wave.IsReducing (maxwellApprox d a).K :=
  isReducing_windowGauss _ a

omit [Fintype d] [LinearOrder d] in
theorem scale_inv_smul (ξ : EuclideanSpace ℝ d) :
    Euclidean.scale ((2 * Real.pi)⁻¹ • ξ) = ξ := by
  rw [Euclidean.scale, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

/-- The magnetic arrow `Λᵃ⁺¹ → Λᵃ⁺²` of the window is not zero for `a + 1 < d`. -/
theorem maxwellSymbol_m12_ne_zero (h : a + 1 < Fintype.card d) :
    (maxwellSymbol d a).m 1 2 ≠ 0 := by
  intro h0
  apply deRham_m_ne_zero h
  funext ξ
  have := congrFun h0 ((2 * Real.pi)⁻¹ • ξ)
  change (deRham d).m (a + 1) (a + 1 + 1) (Euclidean.scale ((2 * Real.pi)⁻¹ • ξ)) = 0 at this
  rw [scale_inv_smul] at this
  exact this

/-- The electric arrow `Λᵃ → Λᵃ⁺¹` of the window is not zero for `a < d`. -/
theorem maxwellSymbol_m01_ne_zero (h : a < Fintype.card d) :
    (maxwellSymbol d a).m 0 1 ≠ 0 := by
  intro h0
  apply deRham_m_ne_zero h
  funext ξ
  have := congrFun h0 ((2 * Real.pi)⁻¹ • ξ)
  change (deRham d).m (a + 0) (a + 1) (Euclidean.scale ((2 * Real.pi)⁻¹ • ξ)) = 0 at this
  rw [scale_inv_smul] at this
  exact this

/-- **Non-vacuity of the `ℝᵈ` Maxwell row** (`a + 1 < d`; e.g. `d = 3`, `a = 0`): a nonzero
datum `(0, 0, B)`, `B = d u` for a cut-off constant field `u`, satisfying the Gauss laws, in every
Sobolev class (band-limited), in `D(L)` and non-stationary (`L x ≠ 0`, as `d† B ≠ 0`). -/
theorem maxwell_nonvacuous (h : a + 1 < Fintype.card d) :
    ∃ x : PiLp 2 (fun i : Fin 3 => L2Form d (a + i)), x ∈ windowGauss (complex d) a ∧
      (∀ s, x ∈ sobolev ℂ (fun i : Fin 3 => Form ℂ d (a + i)) s) ∧ x ≠ 0 ∧
      ∃ hx : x ∈ ((complex d).window a 3).wave.domain,
        ((complex d).window a 3).wave ⟨x, hx⟩ ≠ 0 := by
  set H := (complex d).window a 3
  obtain ⟨N, u, hub, hu, hdu⟩ := exists_band_d_ne_zero (maxwellSymbol d a)
    (continuous_maxwellSymbol_m d a) (maxwellSymbol_m12_ne_zero d a h)
  set B : L2Form d (a + ((2 : Fin 3) : ℕ)) := H.d 1 2 ⟨u, hu⟩
  set x : PiLp 2 (fun i : Fin 3 => L2Form d (a + i)) := PiLp.single 2 (2 : Fin 3) B
  have x0 : x 0 = 0 := PiLp.single_eq_of_ne (p := 2) (by decide) _
  have x1 : x 1 = 0 := PiLp.single_eq_of_ne (p := 2) (by decide) _
  have x2 : x 2 = B := PiLp.single_eq_same (p := 2) _ _
  have hBband : B ∈ (maxwellSymbol d a).band (freqBall N) 2 :=
    (reducingSubcomplex_band (maxwellSymbol d a) (measurableSet_freqBall N)).mapsTo ⟨u, hu⟩ hub
  have hband : x ∈ totalSub ((maxwellSymbol d a).band (freqBall N)) := fun i => by
    fin_cases i
    · change x 0 ∈ _; rw [x0]; exact Submodule.zero_mem _
    · change x 1 ∈ _; rw [x1]; exact Submodule.zero_mem _
    · change x 2 ∈ _; rw [x2]; exact hBband
  have hD : x ∈ H.wave.domain :=
    (bands (maxwellSymbol d a) (continuous_maxwellSymbol_m d a)).le_domain N hband
  refine ⟨x, (mem_gauss _ _).2 ⟨x0, by rw [x1]; exact Submodule.zero_mem _,
    by rw [x2]; exact d_mem_magnetic (complex d) a ⟨u, hu⟩⟩,
    fun s => mem_sobolev_of_mem_band _ hband s, fun h0 => hdu ?_, hD, fun h0 => ?_⟩
  · change B = 0; rw [← x2, h0]; rfl
  · -- `‖(d₁₂)† B‖ ≤ ‖𝐝† x‖ ≤ ‖L x‖ = 0`, but `⟪(d₁₂)† B, u⟫ = ‖B‖² ≠ 0`
    have hsq := H.norm_wave_sq ⟨_, hD⟩
    rw [h0, norm_zero] at hsq
    have hd := H.dual.norm_d_le_norm_totalD ⟨_, hD.2⟩ 2 1
    have h1 : ‖H.dual.totalD ⟨_, hD.2⟩‖ = 0 := by
      nlinarith [sq_nonneg ‖H.totalD ⟨_, hD.1⟩‖, sq_nonneg ‖H.dual.totalD ⟨_, hD.2⟩‖,
        norm_nonneg (H.dual.totalD ⟨_, hD.2⟩)]
    have hz : (H.d 1 2)† ⟨x 2, hD.2 2 1⟩ = 0 :=
      norm_eq_zero.1 (le_antisymm (hd.trans h1.le) (norm_nonneg _))
    have hf := adjoint_isFormalAdjoint (H.dense 1 2) ⟨x 2, hD.2 2 1⟩ ⟨u, hu⟩
    rw [hz, inner_zero_left] at hf
    change 0 = ⟪x 2, B⟫_ℂ at hf
    rw [x2] at hf
    exact hdu (inner_self_eq_zero.1 hf.symm)

/-- **The verdict of the approximating FEEC theorem for Maxwell's equations on `ℝᵈ`** (degree
`a`, frequency truncation `|ξ| ≤ N`): the full `ApproxFEEC.Verdict` (core = all data); the Gauss
laws reduce `L`; for data in `Hˢ`, `s ≥ 0`, the error and (for data satisfying the Gauss laws) the
Gauss-law residual are `≤ (N + 1)^{-s} ‖ξ₀‖_{Hˢ}` for all `t ≥ 0`; for every datum satisfying the
Gauss laws the residual tends to `0` uniformly on `[0, T]`. -/
abbrev EuclideanMaxwellVerdict : Prop :=
    (maxwellApprox d a).Verdict (maxwellCore d a) ∧
    ((complex d).window a 3).wave.IsReducing (windowGauss (complex d) a) ∧
    (∀ s : ℝ, 0 ≤ s → ∀ x ∈ sobolev ℂ (fun i : Fin 3 => Form ℂ d (a + i)) s,
      ∀ (N : ℕ) (t : ℝ), 0 ≤ t →
      ‖((complex d).window a 3).waveGroup.S t x -
          (maxwellApprox d a).sol N ((maxwellApprox d a).proj N x) t‖ ≤
        (1 / ((N : ℝ) + 1)) ^ s * sobolevNorm ℂ s x) ∧
    (∀ s : ℝ, 0 ≤ s → ∀ x ∈ windowGauss (complex d) a,
      x ∈ sobolev ℂ (fun i : Fin 3 => Form ℂ d (a + i)) s → ∀ (N : ℕ) (t : ℝ), 0 ≤ t →
      infDist ((maxwellApprox d a).sol N ((maxwellApprox d a).proj N x) t)
          (windowGauss (complex d) a : Set _) ≤
        (1 / ((N : ℝ) + 1)) ^ s * sobolevNorm ℂ s x) ∧
    (∀ T : ℝ, ∀ x ∈ windowGauss (complex d) a, TendstoUniformlyOn
      (fun N t => infDist ((maxwellApprox d a).sol N ((maxwellApprox d a).proj N x) t)
        (windowGauss (complex d) a : Set _)) (fun _ => 0) atTop (Icc 0 T))

/-- **Maxwell's equations on `ℝᵈ` through the approximating FEEC theorem**, with Sobolev rates.
[QuennevilleBelair2015], §4.9 (Prop. 4.16), §4.12–4.13 -/
theorem maxwell_euclidean_band : EuclideanMaxwellVerdict d a :=
  ⟨maxwell_euclidean_approxFEEC d a, maxwellApprox_isReducing d a,
    fun _ hs _ hx N _ ht => bandApprox_rate (maxwellSymbol d a) (continuous_maxwellSymbol_m d a)
      (windowGauss (complex d) a) (isClosed_gauss _ _) hs hx N ht,
    fun _ hs _ hxK hx N _ ht => bandApprox_residual_rate (maxwellSymbol d a)
      (continuous_maxwellSymbol_m d a) (windowGauss (complex d) a) (isClosed_gauss _ _)
      (maxwellApprox_isReducing d a) hs hxK hx N ht,
    fun T _ hxK => bandApprox_residual (maxwellSymbol d a) (continuous_maxwellSymbol_m d a)
      (windowGauss (complex d) a) (isClosed_gauss _ _) (maxwellApprox_isReducing d a) T hxK⟩

/-! #### A non-reducing Maxwell constraint on `ℝᵈ` -/

/-- The frequency-truncation discretization with the **vanishing-field constraint** `E = 0`,
`B = 0` (`Feec.Instances.Maxwell.potential`), which does not reduce `L` (`a < d`). -/
abbrev maxwellPotentialApprox : ApproxFEEC ((complex d).window a 3) ℕ :=
  bandApprox (maxwellSymbol d a) (continuous_maxwellSymbol_m d a)
    (potential ℂ fun i : Fin 3 => L2Form d (a + i)) isClosed_potential

/-- Its core: all data, with zero consistency defect. -/
abbrev maxwellPotentialCore : (maxwellPotentialApprox d a).Core :=
  bandCore (maxwellSymbol d a) (continuous_maxwellSymbol_m d a)
    (potential ℂ fun i : Fin 3 => L2Form d (a + i)) isClosed_potential

/-- The approximating FEEC theorem for the vanishing-field constraint on `ℝᵈ`. -/
theorem maxwell_euclidean_potential_approxFEEC :
    (maxwellPotentialApprox d a).Verdict (maxwellPotentialCore d a) := approxFEEC _ _

/-- **The vanishing-field constraint does not reduce Maxwell's operator on `ℝᵈ`** (`a < d`). -/
theorem maxwell_euclidean_not_isReducing_potential (h : a < Fintype.card d) :
    ¬ ((complex d).window a 3).wave.IsReducing (potential ℂ fun i : Fin 3 => L2Form d (a + i)) := by
  obtain ⟨N, u, -, hu, hdu⟩ := exists_band_d_ne_zero (maxwellSymbol d a)
    (continuous_maxwellSymbol_m d a) (maxwellSymbol_m01_ne_zero d a h)
  exact not_isReducing_potential _ ⟨⟨u, hu⟩, hdu⟩

/-- **Item 4 of `approxFEEC`, non-reducing branch, on `ℝᵈ`** (`a < d`): for the vanishing-field
constraint, for every `T > 0` some datum of `D(L) ∩ K` leaves `K` at some `t ∈ [0, T]`, and the
residuals of the truncated solutions `ι_N e^{tL_N} π_N ξ₀` tend to `dist(e^{tL} ξ₀, K) > 0`,
eventually staying above half of it. -/
theorem maxwell_euclidean_potential_residual (h : a < Fintype.card d) {T : ℝ} (hT : 0 < T) :
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
  have V := maxwell_euclidean_potential_approxFEEC d a
  obtain ⟨x, hxK, t, ht, hout, hpos, hlim⟩ := V.2.2.2.2.2.2.2.2.2
    (fun i : Fin 3 => decide (Odd i.val)) (fun _ _ h => ComplexShape.window_parity h)
    (fun _ hx => reversal_mem_totalSub hx) (dense_potential _)
    (maxwell_euclidean_not_isReducing_potential d a h) T hT
  have hx : (x : PiLp 2 _) ∈ (maxwellPotentialCore d a).Data.topologicalClosure :=
    Submodule.le_topologicalClosure _ (by rw [bandCore_data]; trivial)
  obtain ⟨h1, h2⟩ := hlim hx _ (V.2.2.2.1 T x hx).1
  exact ⟨x, hxK, t, ht, hout, hpos, h1, h2⟩

end Maxwell

end Feec.Instances.EuclideanBand
