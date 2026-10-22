module

public import Mathlib.Analysis.InnerProductSpace.MeanErgodic
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Feec.Semigroup.Stone
public import Feec.Semigroup.Invariance

/-!
# Spectral mechanisms for isometric groups

For an isometric group `G` with generator `A` on a Hilbert space over `𝕜 = ℝ` or `ℂ`:

* `C0Group.periodic G τ = {x | S τ x = x}`, `C0Group.stationary G = {x | S t x = x ∀ t}`, and
  `C0Group.IsPurePoint G`: the periodic vectors span a dense subspace.
* `LinearPMap.IsEigenSq A ω v`: `v ∈ D(A²)` and `A² v = -ω² v`; `C0Group.EigenDense G`: such
  vectors span a dense subspace.

## Main results

* `C0Group.IsIsometric.starProjection_periodic_mem_invariantCore` (no spectral hypothesis): if
  `S t x ∈ K` for all `t ≥ 0`, the projection of `x` on the `τ`-periodic vectors lies in the
  invariant core (von Neumann's mean ergodic theorem for `S τ`).
* **`C0Group.IsIsometric.mem_invariantCore_of_forward_invariant`**: under `IsPurePoint`,
  forward invariance of a closed `K` (`S t x ∈ K` for `t ≥ 0`) gives `x ∈ invariantCore G K`
  (invariance for all `t ∈ ℝ`). Without a spectral hypothesis this is false (transport).
* `C0Group.IsIsometric.S_eq_of_isEigenSq`: the orbit of an eigenvector of `A²` is
  `cos(ωt) v + (sin(ωt)/ω) A v`; hence `isPurePoint_of_eigenDense`.
* `LinearPMap.IsSkewSymmetric.exists_isEigenSq`: an eigenvector of `A²` of a skew-symmetric `A`
  has eigenvalue `-ω²`, `ω` real.
* **`LinearPMap.IsSkewAdjoint.dense_span_isEigenSq`** and
  **`C0Group.eigenDense_of_compactResolvent`**: if `(1 - A)⁻¹` is compact, the eigenvectors of
  `A²` are dense (Mathlib's spectral theorem for the compact self-adjoint operator
  `(1 - A)⁻¹ (1 + A)⁻¹ = (1 - A²)⁻¹`), so `EigenDense` is a theorem, not a hypothesis;
  `LinearPMap.IsSkewAdjoint.mem_invariantCore_of_forward_invariant` combines both.
* `LinearPMap.IsSkewSymmetric.dense_span_isEigenSq_of_reducing`: finite-dimensional reducing
  subspaces spanning a dense subspace give an eigenbasis (Fourier models);
  `C0Group.IsIsometric.invariantCore_le_stationary_of_eigenDense`,
  `C0Group.IsIsometric.exists_isEigenSq_mem_invariantCore`,
  `C0Group.IsIsometric.mem_invariantCore_iff_of_isEigenSq`: spectral extraction from the
  invariant core.
* `C0Group.not_mem_stationary_of_isEigenSq`: a nonzero eigenvector of `A²` with eigenvalue
  `-ω² ≠ 0` is not stationary.
* `C0Group.rescale`, `C0Group.generator_rescale`: the group `t ↦ S (a t)` has generator `a A`.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.10
* [M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*][ReedSimon1980],
  Thm VI.16 (Hilbert–Schmidt theorem), §VII.3 (mean ergodic theorem)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter Topology LinearPMap Feec.Operator

@[expose] public noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace Feec

/-! ### Periodic and stationary vectors -/

namespace C0Group

variable (G : C0Group 𝕜 E)

/-- The `τ`-periodic vectors `{x | S τ x = x}`. -/
def periodic (τ : ℝ) : Submodule 𝕜 E := (G.S τ).eqLocus (1 : E →L[𝕜] E)

/-- The stationary vectors `{x | S t x = x for all t}`. -/
def stationary : Submodule 𝕜 E := ⨅ t, G.periodic t

/-- Pure point spectrum, in group form: the periodic vectors span a dense subspace. -/
def IsPurePoint : Prop := Dense ((⨆ τ : Ioi (0 : ℝ), G.periodic τ : Submodule 𝕜 E) : Set E)

variable {G}

theorem mem_periodic {τ : ℝ} {x : E} : x ∈ G.periodic τ ↔ G.S τ x = x := by
  simp [periodic]

theorem mem_stationary {x : E} : x ∈ G.stationary ↔ ∀ t, G.S t x = x := by
  simp [stationary, mem_periodic]

theorem stationary_le_periodic (τ : ℝ) : G.stationary ≤ G.periodic τ := fun _ hx =>
  mem_periodic.2 (mem_stationary.1 hx τ)

theorem isClosed_periodic (τ : ℝ) : IsClosed (G.periodic τ : Set E) :=
  ContinuousLinearMap.isClosed_eqLocus (G.S τ) 1

theorem isClosed_stationary : IsClosed (G.stationary : Set E) := by
  have e : (G.stationary : Set E) = ⋂ t, (G.periodic t : Set E) := by ext; simp [stationary]
  rw [e]; exact isClosed_iInter fun t => isClosed_periodic t

theorem iterate_S (τ : ℝ) (n : ℕ) (x : E) : (G.S τ)^[n] x = G.S (n * τ) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, ← map_add_apply]
    congr 2; push_cast; ring

theorem S_nat_mul_of_mem_periodic {τ : ℝ} {x : E} (hx : x ∈ G.periodic τ) (n : ℕ) :
    G.S (n * τ) x = x := by
  rw [← iterate_S]
  exact Function.iterate_fixed (mem_periodic.1 hx) n

variable [CompleteSpace E]

instance (τ : ℝ) : (G.periodic τ).HasOrthogonalProjection := by
  have : CompleteSpace (G.periodic τ) := (isClosed_periodic τ).completeSpace_coe
  infer_instance

instance : G.stationary.HasOrthogonalProjection := by
  have : CompleteSpace G.stationary := isClosed_stationary.completeSpace_coe
  infer_instance

/-- **Mean ergodic theorem for the time-`τ` map**: `N⁻¹ Σ_{n<N} S(nτ) x → P_{periodic τ} x`. -/
theorem IsIsometric.tendsto_birkhoffAverage (hG : G.IsIsometric) (τ : ℝ) (x : E) :
    Tendsto (fun N => birkhoffAverage 𝕜 (G.S τ) _root_.id N x) atTop
      (𝓝 ((G.periodic τ).starProjection x)) :=
  (G.S τ).tendsto_birkhoffAverage_orthogonalProjection (hG.norm_S_le τ) x

/-- **The periodic part of a forward-invariant datum lies in the invariant core.** If `K` is
closed and `S t x ∈ K` for all `t ≥ 0`, then `P_{periodic τ} x ∈ invariantCore G K` for every
`τ > 0`. No spectral hypothesis. -/
theorem IsIsometric.starProjection_periodic_mem_invariantCore (hG : G.IsIsometric)
    {K : Submodule 𝕜 E} (hK : IsClosed (K : Set E)) {τ : ℝ} (hτ : 0 < τ) {x : E}
    (hx : ∀ t, 0 ≤ t → G.S t x ∈ K) :
    (G.periodic τ).starProjection x ∈ G.invariantCore K := by
  set p := (G.periodic τ).starProjection x
  have hfwd : ∀ s, 0 ≤ s → G.S s p ∈ K := by
    intro s hs
    have ht := ((G.S s).continuous.tendsto _).comp (hG.tendsto_birkhoffAverage τ x)
    refine hK.mem_of_tendsto ht (Eventually.of_forall fun N => ?_)
    simp only [Function.comp_apply, birkhoffAverage, birkhoffSum, _root_.map_smul, _root_.map_sum,
      id]
    refine K.smul_mem _ (K.sum_mem fun n _ => ?_)
    rw [iterate_S, ← map_add_apply]
    exact hx _ (by have := hτ.le; positivity)
  refine mem_invariantCore.2 fun t => ?_
  obtain ⟨n, hn⟩ := exists_nat_ge (-t / τ)
  have hp : p ∈ G.periodic τ := (G.periodic τ).starProjection_apply_mem x
  rw [← S_nat_mul_of_mem_periodic hp n, ← map_add_apply]
  refine hfwd _ ?_
  have := (div_le_iff₀ hτ).1 hn
  linarith

theorem IsPurePoint.eq_zero_of_starProjection (hPP : G.IsPurePoint) {z : E}
    (h : ∀ τ, 0 < τ → (G.periodic τ).starProjection z = 0) : z = 0 := by
  let Z : Submodule 𝕜 E := LinearMap.ker (innerSL 𝕜 z).toLinearMap
  have hle : (⨆ τ : Ioi (0 : ℝ), G.periodic τ : Submodule 𝕜 E) ≤ Z := by
    refine iSup_le fun τ y hy => ?_
    have hz : z ∈ (G.periodic τ)ᗮ := by
      simpa [h τ τ.2] using (G.periodic τ).sub_starProjection_mem_orthogonal z
    simp only [Z, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    rw [← inner_conj_symm, Submodule.inner_right_of_mem_orthogonal hy hz, _root_.map_zero]
  have hZ : IsClosed (Z : Set E) := (innerSL 𝕜 z).isClosed_ker
  have : z ∈ Z := by
    have := closure_mono hle (hPP z)
    rwa [hZ.closure_eq] at this
  simpa [Z] using this

omit [CompleteSpace E] in
theorem starProjection_eq_zero_of_mem {N P : Submodule 𝕜 E} [P.HasOrthogonalProjection] {z : E}
    (hz : z ∈ Nᗮ) (hP : P.starProjection z ∈ N) : P.starProjection z = 0 := by
  have h1 : ⟪P.starProjection z, z - P.starProjection z⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (P.starProjection_apply_mem z)
      (P.sub_starProjection_mem_orthogonal z)
  have h2 : ⟪P.starProjection z, z⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hP hz
  rw [inner_sub_right, h2, zero_sub, neg_eq_zero] at h1
  exact inner_self_eq_zero.1 h1

/-- **Forward invariance gives the invariant core under pure point spectrum**: if `K` is closed
and `S t x ∈ K` for all `t ≥ 0`, then `S t x ∈ K` for all `t ∈ ℝ`. -/
theorem IsIsometric.mem_invariantCore_of_forward_invariant (hG : G.IsIsometric)
    (hPP : G.IsPurePoint) {K : Submodule 𝕜 E} (hK : IsClosed (K : Set E)) {x : E}
    (hx : ∀ t, 0 ≤ t → G.S t x ∈ K) : x ∈ G.invariantCore K := by
  have hN : IsClosed (G.invariantCore K : Set E) := isClosed_invariantCore hK
  have : CompleteSpace (G.invariantCore K) := hN.completeSpace_coe
  set N := G.invariantCore K
  set z := x - N.starProjection x
  have hz : z ∈ Nᗮ := N.sub_starProjection_mem_orthogonal x
  have h0 : z = 0 := by
    refine hPP.eq_zero_of_starProjection fun τ hτ => starProjection_eq_zero_of_mem hz ?_
    rw [_root_.map_sub]
    refine N.sub_mem (hG.starProjection_periodic_mem_invariantCore hK hτ hx)
      (invariantCore_le (G := G) (K := N) ?_)
    exact hG.starProjection_periodic_mem_invariantCore hN hτ fun t _ =>
      S_mem_invariantCore (N.starProjection_apply_mem x) t
  have := N.starProjection_apply_mem x
  rwa [← sub_eq_zero.1 h0] at this

end C0Group

/-! ### Eigenvectors of `A²` -/

end Feec

namespace LinearPMap

open Feec

variable [NormedSpace ℝ E]

/-- `v` is an eigenvector of `A²` with eigenvalue `-ω²`: `v ∈ D(A)`, `A v ∈ D(A)`,
`A (A v) = -ω² v`. For skew-adjoint `A` these are the real parts of the eigenvectors of `A` with
eigenvalues `± i ω` (over `ℂ`, also the eigenvectors themselves). -/
def IsEigenSq (A : E →ₗ.[𝕜] E) (ω : ℝ) (v : E) : Prop :=
  ∃ (h : v ∈ A.domain) (h' : A ⟨v, h⟩ ∈ A.domain), A ⟨A ⟨v, h⟩, h'⟩ = -(ω ^ 2) • v

variable {A : E →ₗ.[𝕜] E}

variable (A) in
/-- `0` is (trivially) an eigenvector of `A²`. -/
theorem isEigenSq_zero_right (ω : ℝ) : A.IsEigenSq ω 0 := by
  have e0 : A ⟨0, A.domain.zero_mem⟩ = 0 := A.map_zero
  have h' : A ⟨0, A.domain.zero_mem⟩ ∈ A.domain := by rw [e0]; exact A.domain.zero_mem
  have e1 : (⟨A ⟨0, A.domain.zero_mem⟩, h'⟩ : A.domain) = 0 := Subtype.ext e0
  exact ⟨A.domain.zero_mem, h', by rw [e1, LinearPMap.map_zero, smul_zero]⟩

theorem IsEigenSq.abs {ω : ℝ} {v : E} (hv : A.IsEigenSq ω v) : A.IsEigenSq |ω| v := by
  obtain ⟨h, h', e⟩ := hv
  exact ⟨h, h', by rw [e, sq_abs]⟩

variable [IsScalarTower ℝ 𝕜 E]

/-- For skew-symmetric `A`, every eigenvector of `A²` has eigenvalue `-ω²` with `ω` real
(`⟪A² v, v⟫ = -‖A v‖²`). -/
theorem IsSkewSymmetric.exists_isEigenSq (hA : A.IsSkewSymmetric) {v : E} (h : v ∈ A.domain)
    (h' : A ⟨v, h⟩ ∈ A.domain) {c : 𝕜} (hc : A ⟨A ⟨v, h⟩, h'⟩ = c • v) :
    ∃ ω : ℝ, A.IsEigenSq ω v := by
  rcases eq_or_ne v 0 with rfl | hv
  · exact ⟨0, h, h', by rw [hc, smul_zero, smul_zero]⟩
  set w := A ⟨v, h⟩
  have hn : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
  have key : (starRingEnd 𝕜) c * ((‖v‖ ^ 2 : ℝ) : 𝕜) = -((‖w‖ ^ 2 : ℝ) : 𝕜) := by
    have h1 := hA ⟨w, h'⟩ ⟨v, h⟩
    rw [hc, inner_smul_left, inner_self_eq_norm_sq_to_K] at h1
    change _ = -⟪w, w⟫ at h1
    rw [inner_self_eq_norm_sq_to_K] at h1
    push_cast; exact h1
  have hc' : c = ((-(‖w‖ ^ 2 / ‖v‖ ^ 2) : ℝ) : 𝕜) := by
    have hconj : (starRingEnd 𝕜) c = ((-(‖w‖ ^ 2 / ‖v‖ ^ 2) : ℝ) : 𝕜) := by
      have hn' : ((‖v‖ ^ 2 : ℝ) : 𝕜) ≠ 0 := by exact_mod_cast hn.ne'
      rw [← mul_div_cancel_right₀ ((starRingEnd 𝕜) c) hn', key]
      push_cast; ring
    rw [← RCLike.conj_conj c, hconj, RCLike.conj_ofReal]
  refine ⟨‖w‖ / ‖v‖, h, h', ?_⟩
  rw [hc, hc', ← RCLike.real_smul_eq_coe_smul, div_pow]

end LinearPMap

namespace Feec

namespace C0Group

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] {G : C0Group 𝕜 E}

/-- `EigenDense G`: the eigenvectors of `A²` (`A` the generator) span a dense subspace. -/
def EigenDense (G : C0Group 𝕜 E) : Prop :=
  Dense (Submodule.span 𝕜 {v | ∃ ω, G.generator.IsEigenSq ω v} : Set E)

/-- **The orbit of an eigenvector of `A²`**: if `A (A v) = -ω² v`, `ω > 0`, then
`S t v = cos(ω t) v + (sin(ω t) / ω) A v` (both sides solve `u' = A u`). -/
theorem IsIsometric.S_eq_of_isEigenSq (hG : G.IsIsometric) {ω : ℝ} (hω : 0 < ω) {v : E}
    (h : v ∈ G.generator.domain) (h' : G.generator ⟨v, h⟩ ∈ G.generator.domain)
    (e : G.generator ⟨G.generator ⟨v, h⟩, h'⟩ = -(ω ^ 2) • v) (t : ℝ) :
    G.S t v = Real.cos (ω * t) • v + (Real.sin (ω * t) / ω) • G.generator ⟨v, h⟩ := by
  set A := G.generator
  set w := A ⟨v, h⟩
  let y : ℝ → E := fun s => Real.cos (ω * s) • v + (Real.sin (ω * s) / ω) • w
  have hm : ∀ s, y s ∈ A.domain := fun s =>
    A.domain.add_mem (Submodule.smul_of_tower_mem _ _ h) (Submodule.smul_of_tower_mem _ _ h')
  have hLy : ∀ s, A ⟨y s, hm s⟩ = Real.cos (ω * s) • w - (ω * Real.sin (ω * s)) • v := by
    intro s
    have : (⟨y s, hm s⟩ : A.domain) =
        ((Real.cos (ω * s) : ℝ) : 𝕜) • (⟨v, h⟩ : A.domain) +
          ((Real.sin (ω * s) / ω : ℝ) : 𝕜) • ⟨w, h'⟩ := by
      ext
      simp only [y, Submodule.coe_add, Submodule.coe_smul, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    rw [this, A.map_add, A.map_smul, A.map_smul, e, ← RCLike.real_smul_eq_coe_smul,
      ← RCLike.real_smul_eq_coe_smul, smul_smul, sub_eq_add_neg, ← neg_smul]
    congr 2
    field_simp
  have hdy : ∀ s, HasDerivAt y (A ⟨y s, hm s⟩) s := by
    intro s
    rw [hLy]
    have h1 : HasDerivAt (fun s => ω * s) ω s := by
      simpa using (hasDerivAt_id s).const_mul ω
    have hd : HasDerivAt y ((-Real.sin (ω * s) * ω) • v + (Real.cos (ω * s) * ω / ω) • w) s :=
      (h1.cos.smul_const v).add ((h1.sin.div_const ω).smul_const w)
    refine hd.congr_deriv ?_
    rw [mul_div_cancel_right₀ _ hω.ne']
    module
  set f : ℝ → E := fun s => G.S s v - y s
  have hm1 : ∀ s, G.S s v ∈ A.domain := fun s => G.mapsTo_domain ⟨v, h⟩ s
  have hfm : ∀ s, f s ∈ A.domain := fun s => A.domain.sub_mem (hm1 s) (hm s)
  have hdf : ∀ s, HasDerivAt f (A ⟨f s, hfm s⟩) s := by
    intro s
    have e1 : (⟨f s, hfm s⟩ : A.domain) = ⟨G.S s v, hm1 s⟩ - ⟨y s, hm s⟩ := rfl
    rw [e1, LinearPMap.map_sub]
    exact (G.hasDerivAt_apply' ⟨v, h⟩ s).sub (hdy s)
  have h0 := hG.isSkewSymmetric_generator.eq_zero_of_hasDerivAt hfm hdf (by simp [f, y]) t
  exact sub_eq_zero.1 h0

/-- Eigenvectors of `A²` with eigenvalue `-ω²`, `ω > 0`, are `2π/ω`-periodic. -/
theorem IsIsometric.mem_periodic_of_isEigenSq (hG : G.IsIsometric) {ω : ℝ} (hω : 0 < ω) {v : E}
    (hv : G.generator.IsEigenSq ω v) : v ∈ G.periodic (2 * Real.pi / ω) := by
  obtain ⟨h, h', e⟩ := hv
  rw [mem_periodic, hG.S_eq_of_isEigenSq hω h h' e]
  have : ω * (2 * Real.pi / ω) = 2 * Real.pi := by field_simp
  simp [this]

/-- An eigenvector of `A²` with eigenvalue `0` is stationary (`‖A v‖² = -⟪A² v, v⟫ = 0`). -/
theorem IsIsometric.mem_stationary_of_isEigenSq_zero (hG : G.IsIsometric) {v : E}
    (hv : G.generator.IsEigenSq 0 v) : v ∈ G.stationary := by
  obtain ⟨h, h', e⟩ := hv
  have hs := hG.isSkewSymmetric_generator ⟨G.generator ⟨v, h⟩, h'⟩ ⟨v, h⟩
  simp only [e, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_smul,
    inner_zero_left] at hs
  have h0 : G.generator ⟨v, h⟩ = 0 := inner_self_eq_zero.1 (neg_eq_zero.1 hs.symm)
  exact mem_stationary.2 (S_apply_eq_of_generator_eq_zero ⟨v, h⟩ h0)

/-- **An eigenbasis gives pure point spectrum.** -/
theorem IsIsometric.isPurePoint_of_eigenDense (hG : G.IsIsometric) (hD : G.EigenDense) :
    G.IsPurePoint := by
  refine hD.mono (Submodule.span_le.2 ?_)
  rintro v ⟨ω, hv⟩
  by_cases h0 : ω = 0
  · have := hG.mem_stationary_of_isEigenSq_zero (h0 ▸ hv)
    exact (le_iSup (fun τ : Ioi (0 : ℝ) => G.periodic τ) ⟨1, one_pos⟩)
      (stationary_le_periodic 1 this)
  · have hp := abs_pos.2 h0
    exact (le_iSup (fun τ : Ioi (0 : ℝ) => G.periodic τ)
      ⟨2 * Real.pi / |ω|, Set.mem_Ioi.2 (by positivity)⟩) (hG.mem_periodic_of_isEigenSq hp hv.abs)

end C0Group

/-! ### Compact resolvent ⇒ eigenbasis -/

end Feec

namespace LinearPMap

open Feec

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] {A : E →ₗ.[𝕜] E}

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] in
theorem _root_.Feec.Operator.IsResolvent.injective {z : 𝕜} {R : E →L[𝕜] E}
    (hR : IsResolvent A z R) : Function.Injective R := by
  refine (injective_iff_map_eq_zero R).2 fun y hy => ?_
  have h := hR.sub_apply y
  have h0 : (⟨R y, hR.mem_domain y⟩ : A.domain) = 0 := Subtype.ext hy
  rw [h0, LinearPMap.map_zero] at h
  change z • R y - 0 = y at h
  rw [show R y = 0 from hy, smul_zero, sub_zero] at h
  exact h.symm

/-- **Compact resolvent ⇒ the eigenvectors of `A²` are dense.** For skew-adjoint `A` with
`(1 - A)⁻¹` compact, `T = (1 - A)⁻¹ ((1 - A)⁻¹)† = (1 - A)⁻¹ (1 + A)⁻¹` is compact, self-adjoint
and injective; by the spectral theorem its eigenvectors span a dense subspace, and each is an
eigenvector of `A²` (`A² v = (1 - μ⁻¹) v` when `T v = μ v`). -/
theorem IsSkewAdjoint.dense_span_isEigenSq (hA : A.IsSkewAdjoint)
    (hK : IsCompactOperator (resolvent A 1)) :
    Dense (Submodule.span 𝕜 {v | ∃ ω, A.IsEigenSq ω v} : Set E) := by
  set R := resolvent A (1 : 𝕜)
  set R' := resolvent A (-1 : 𝕜)
  have hR : IsResolvent A 1 R := isResolvent_resolvent hA (by simp)
  have hR' : IsResolvent A (-1) R' := isResolvent_resolvent hA (by simp)
  have hadj : ContinuousLinearMap.adjoint R = -R' := by
    have := adjoint_resolvent hA (z := (1 : 𝕜)) (by simp)
    simpa using this
  set T : E →L[𝕜] E := R ∘L ContinuousLinearMap.adjoint R
  have hTc : IsCompactOperator T := hK.comp_clm (ContinuousLinearMap.adjoint R)
  have hTs : (T : E →ₗ[𝕜] E).IsSymmetric := fun x y => by
    change ⟪R (ContinuousLinearMap.adjoint R x), y⟫ = ⟪x, R (ContinuousLinearMap.adjoint R y)⟫
    exact (ContinuousLinearMap.adjoint_inner_right R _ y).symm.trans
      (ContinuousLinearMap.adjoint_inner_left R _ x)
  have hspec := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hTc hTs
  have hdense : Dense ((⨆ μ, Module.End.eigenspace (T : Module.End 𝕜 E) μ : Submodule 𝕜 E) :
      Set E) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
    exact hspec
  refine hdense.mono (show (⨆ μ, Module.End.eigenspace (T : Module.End 𝕜 E) μ : Submodule 𝕜 E) ≤
    Submodule.span 𝕜 {v | ∃ ω, A.IsEigenSq ω v} from iSup_le fun μ => ?_)
  intro v hv
  refine Submodule.subset_span ?_
  rw [Module.End.mem_eigenspace_iff] at hv
  change R (ContinuousLinearMap.adjoint R v) = μ • v at hv
  rw [hadj, _root_.neg_apply] at hv
  by_cases hμ : μ = 0
  · rw [hμ, zero_smul] at hv
    have h1 : -R' v = 0 := hR.injective (by rw [hv, _root_.map_zero])
    have h2 : v = 0 := hR'.injective (by rw [neg_eq_zero.1 h1, _root_.map_zero])
    exact ⟨0, h2 ▸ isEigenSq_zero_right A 0⟩
  -- `u = (1 + A)⁻¹ v`-type element `-R' v`, and `μ v = R u`
  set u := -R' v
  have hu : u ∈ A.domain := A.domain.neg_mem (hR'.mem_domain v)
  have hAu : A ⟨u, hu⟩ = v - u := by
    have : (⟨u, hu⟩ : A.domain) = -hR'.toDomain v := rfl
    rw [this, LinearPMap.map_neg, hR'.apply_resolvent]
    simp only [u, neg_smul, one_smul]
    abel
  have hvw : v = μ⁻¹ • R u := by rw [hv, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hvD : v ∈ A.domain := hvw ▸ A.domain.smul_mem _ (hR.mem_domain u)
  have hAv : A ⟨v, hvD⟩ = v - μ⁻¹ • u := by
    have : (⟨v, hvD⟩ : A.domain) = μ⁻¹ • hR.toDomain u := Subtype.ext hvw
    rw [this, LinearPMap.map_smul, hR.apply_resolvent, one_smul, smul_sub, ← hvw]
  have hAvD : A ⟨v, hvD⟩ ∈ A.domain := by
    rw [hAv]; exact A.domain.sub_mem hvD (A.domain.smul_mem _ hu)
  have hAAv : A ⟨A ⟨v, hvD⟩, hAvD⟩ = (1 - μ⁻¹) • v := by
    have : (⟨A ⟨v, hvD⟩, hAvD⟩ : A.domain) = ⟨v, hvD⟩ - μ⁻¹ • ⟨u, hu⟩ := Subtype.ext hAv
    rw [this, LinearPMap.map_sub, LinearPMap.map_smul, hAv, hAu]
    module
  exact hA.isSkewSymmetric.exists_isEigenSq hvD hAvD hAAv

end LinearPMap

namespace Feec

namespace C0Group

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] {G : C0Group 𝕜 E}
  {A : E →ₗ.[𝕜] E}

/-- An isometric group whose generator has compact resolvent satisfies `EigenDense`. -/
theorem IsIsometric.eigenDense_of_compactResolvent (hG : G.IsIsometric)
    (hK : IsCompactOperator (resolvent G.generator 1)) : G.EigenDense :=
  LinearPMap.IsSkewAdjoint.dense_span_isEigenSq hG.isSkewAdjoint_generator hK

/-- **Compact resolvent ⇒ `EigenDense`** for the Stone group of a skew-adjoint operator. -/
theorem eigenDense_of_compactResolvent (hA : A.IsSkewAdjoint)
    (hK : IsCompactOperator (resolvent A 1)) : hA.group.EigenDense := by
  unfold EigenDense
  rw [hA.generator_group]
  exact LinearPMap.IsSkewAdjoint.dense_span_isEigenSq hA hK

end C0Group

end Feec

namespace LinearPMap

open Feec

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] {A : E →ₗ.[𝕜] E}

/-- **Forward invariance under a compact resolvent**: if `A` is skew-adjoint with compact
resolvent and `K` is closed, a datum whose Stone orbit stays in `K` for `t ≥ 0` stays in `K`
for all `t ∈ ℝ`. -/
theorem IsSkewAdjoint.mem_invariantCore_of_forward_invariant (hA : A.IsSkewAdjoint)
    (hK : IsCompactOperator (resolvent A 1)) {K : Submodule 𝕜 E} (hKc : _root_.IsClosed (K : Set E))
    {x : E} (hx : ∀ t, 0 ≤ t → hA.group.S t x ∈ K) : x ∈ hA.group.invariantCore K :=
  hA.isIsometric_group.mem_invariantCore_of_forward_invariant
    (hA.isIsometric_group.isPurePoint_of_eigenDense (C0Group.eigenDense_of_compactResolvent hA hK))
    hKc hx

end LinearPMap

/-! ### Invariant cores under an eigenbasis

The abstract mechanism behind "only stationary data propagate": the invariant core `K*` of a
closed `K` reduces the generator `A`, so its projection maps eigenvectors of `A²` to eigenvectors
of `A²` with the same eigenvalue. Under `EigenDense`, `K*` is stationary as soon as it contains no
nonzero eigenvector of `A²` with eigenvalue `-ω²`, `ω > 0`. -/

namespace LinearPMap

open Feec

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {A : E →ₗ.[𝕜] E}

/-- **The projection onto a reducing subspace maps eigenvectors of `A²` to eigenvectors** with
the same eigenvalue. -/
theorem IsEigenSq.starProjection {N : Submodule 𝕜 E} [N.HasOrthogonalProjection]
    (hN : A.IsReducing N) {ω : ℝ} {v : E} (hv : A.IsEigenSq ω v) :
    A.IsEigenSq ω (N.starProjection v) := by
  obtain ⟨h, h', e⟩ := hv
  have hP : N.starProjection v ∈ A.domain := hN.proj_mem ⟨v, h⟩
  have e1 : A ⟨_, hP⟩ = N.starProjection (A ⟨v, h⟩) := hN.comm ⟨v, h⟩
  have hP' : A ⟨_, hP⟩ ∈ A.domain := e1 ▸ hN.proj_mem ⟨_, h'⟩
  refine ⟨hP, hP', ?_⟩
  have e2 : (⟨_, hP'⟩ : A.domain) = ⟨_, hN.proj_mem ⟨_, h'⟩⟩ := Subtype.ext e1
  rw [e2, hN.comm ⟨_, h'⟩, e]
  exact N.starProjection.map_smul_of_tower _ _

/-- **Eigenvectors of `A²` and the kernel of a skew-symmetric `A`**: an eigenvector of `A²` with
eigenvalue `-ω²`, `ω ≠ 0`, is orthogonal to every `s ∈ ker A`. -/
theorem IsSkewSymmetric.inner_eq_zero_of_isEigenSq (hA : A.IsSkewSymmetric) {ω : ℝ} (hω : ω ≠ 0)
    {v : E} (hv : A.IsEigenSq ω v) (s : A.domain) (hs : A s = 0) : ⟪v, (s : E)⟫ = 0 := by
  obtain ⟨h, h', e⟩ := hv
  have h1 := hA ⟨_, h'⟩ s
  rw [hs, inner_zero_right, neg_zero, e, RCLike.real_smul_eq_coe_smul (K := 𝕜),
    inner_smul_left] at h1
  have hω2 : (starRingEnd 𝕜) ((-(ω ^ 2) : ℝ) : 𝕜) ≠ 0 := by
    rw [RCLike.conj_ofReal]; exact_mod_cast neg_ne_zero.2 (pow_ne_zero 2 hω)
  exact (mul_eq_zero.1 h1).resolve_left hω2

/-- **Finite-dimensional reducing subspaces give an eigenbasis**: if `A` is skew-symmetric and
densely defined, and finite-dimensional subspaces `B n` reducing `A` span a dense subspace, then
the eigenvectors of `A²` span a dense subspace. (Each `B n` lies in `D(A)` and is invariant, so
`A²` restricts to a symmetric operator of `B n`, which is diagonalizable.) This is the mode-wise
spectral theorem of Fourier models, with no compactness of the resolvent. -/
theorem IsSkewSymmetric.dense_span_isEigenSq_of_reducing (hA : A.IsSkewSymmetric)
    (hdense : Dense (A.domain : Set E)) {κ : Type*} (B : κ → Submodule 𝕜 E)
    [∀ n, FiniteDimensional 𝕜 (B n)] [∀ n, (B n).HasOrthogonalProjection]
    (hB : ∀ n, A.IsReducing (B n)) (hspan : Dense ((⨆ n, B n : Submodule 𝕜 E) : Set E)) :
    Dense (Submodule.span 𝕜 {v | ∃ ω, A.IsEigenSq ω v} : Set E) := by
  refine hspan.mono (show (⨆ n, B n : Submodule 𝕜 E) ≤ _ from iSup_le fun n => ?_)
  -- `B n ⊆ D(A)`
  have hdom : B n ≤ A.domain := by
    intro b hb
    set M : Submodule 𝕜 E := A.domain ⊓ B n
    have hMc : _root_.IsClosed (M : Set E) := Submodule.closed_of_finiteDimensional M
    have hsub : (B n).starProjection '' (A.domain : Set E) ⊆ M := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨(hB n).proj_mem ⟨x, hx⟩, (B n).starProjection_apply_mem x⟩
    have hb' :
        (B n).starProjection b ∈ _root_.closure ((B n).starProjection '' (A.domain : Set E)) :=
      map_mem_closure (B n).starProjection.continuous (hdense b) fun x hx => mem_image_of_mem _ hx
    rw [(B n).starProjection_eq_self_iff.2 hb] at hb'
    exact (hMc.closure_subset_iff.2 hsub hb').1
  -- `A (B n) ⊆ B n`
  have hinv : ∀ x : A.domain, (x : E) ∈ B n → A x ∈ B n := fun x hx => (hB n).mapsTo x hx
  -- `A²` as a symmetric operator of `B n`
  let A1 : B n →ₗ[𝕜] B n :=
    { toFun := fun b => ⟨A ⟨b, hdom b.2⟩, hinv ⟨b, hdom b.2⟩ b.2⟩
      map_add' := fun a b => by
        ext; simp only [Submodule.coe_add]
        rw [← LinearPMap.map_add]; rfl
      map_smul' := fun c b => by
        ext; simp only [Submodule.coe_smul, RingHom.id_apply]
        rw [← LinearPMap.map_smul]; rfl }
  have hA1 : ∀ a b : B n, ⟪(A1 a : E), (b : E)⟫ = -⟪(a : E), (A1 b : E)⟫ := fun a b =>
    hA ⟨a, hdom a.2⟩ ⟨b, hdom b.2⟩
  set T : B n →ₗ[𝕜] B n := A1 ∘ₗ A1
  have hT : T.IsSymmetric := fun a b => by
    change ⟪((A1 (A1 a)) : E), (b : E)⟫ = ⟪(a : E), (A1 (A1 b) : E)⟫
    rw [hA1, hA1, neg_neg]
  have htop : (⨆ μ, Module.End.eigenspace T μ : Submodule 𝕜 (B n)) = ⊤ := by
    have := hT.orthogonalComplement_iSup_eigenspaces_eq_bot
    rwa [Submodule.orthogonal_eq_bot_iff] at this
  intro b hb
  have hmem : (⟨b, hb⟩ : B n) ∈ (⨆ μ, Module.End.eigenspace T μ : Submodule 𝕜 (B n)) :=
    htop ▸ Submodule.mem_top
  have hmap : (⨆ μ, Module.End.eigenspace T μ : Submodule 𝕜 (B n)).map (B n).subtype ≤
      Submodule.span 𝕜 {v | ∃ ω, A.IsEigenSq ω v} := by
    rw [Submodule.map_iSup]
    refine iSup_le fun μ => ?_
    rintro _ ⟨w, hw, rfl⟩
    refine Submodule.subset_span ?_
    have hw : w ∈ Module.End.eigenspace T μ := hw
    rw [Module.End.mem_eigenspace_iff] at hw
    have hw' : A ⟨A ⟨w, hdom w.2⟩, hdom (A1 w).2⟩ = μ • (w : E) := congrArg Subtype.val hw
    exact hA.exists_isEigenSq (hdom w.2) (hdom (A1 w).2) hw'
  exact hmap ⟨_, hmem, rfl⟩

end LinearPMap

namespace Feec

namespace C0Group

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] {G : C0Group 𝕜 E}

/-- A stationary vector lies in the domain of the generator and is killed by it. -/
theorem mem_domain_generator_of_mem_stationary {x : E} (hx : x ∈ G.stationary) :
    ∃ h : x ∈ G.generator.domain, G.generator ⟨x, h⟩ = 0 := by
  have e : (fun t => G.S t x) = fun _ => x := funext (mem_stationary.1 hx)
  have hd : HasDerivAt (fun t => G.S t x) 0 0 := by rw [e]; exact hasDerivAt_const _ _
  have hD : x ∈ G.generator.domain := (G.mem_domain_generator_iff x).2 hd.differentiableAt
  exact ⟨hD, G.generator_apply_eq (x := ⟨x, hD⟩) hd⟩

/-- **A vector orthogonal to every non-stationary eigenvector of `A²` is stationary** (under
`EigenDense`): eigenvectors with eigenvalue `0` are stationary, those with eigenvalue `-ω²`,
`ω ≠ 0`, are orthogonal to the stationary vectors. -/
theorem IsIsometric.mem_stationary_of_inner_isEigenSq (hG : G.IsIsometric) (hD : G.EigenDense)
    {x : E} (hx : ∀ ω, 0 < ω → ∀ v, G.generator.IsEigenSq ω v → ⟪v, x⟫ = 0) :
    x ∈ G.stationary := by
  set z := x - G.stationary.starProjection x
  have hz : z ∈ G.stationaryᗮ := G.stationary.sub_starProjection_mem_orthogonal x
  have hperp : ∀ v ∈ {v | ∃ ω, G.generator.IsEigenSq ω v}, ⟪v, z⟫ = 0 := by
    rintro v ⟨ω, hv⟩
    by_cases h0 : ω = 0
    · subst h0
      exact Submodule.inner_right_of_mem_orthogonal (hG.mem_stationary_of_isEigenSq_zero hv) hz
    · obtain ⟨hs, hs0⟩ := mem_domain_generator_of_mem_stationary
        (G.stationary.starProjection_apply_mem x)
      rw [inner_sub_right, hx |ω| (abs_pos.2 h0) v hv.abs,
        hG.isSkewSymmetric_generator.inner_eq_zero_of_isEigenSq h0 hv ⟨_, hs⟩ hs0, sub_zero]
  have hz' : z ∈ (Submodule.span 𝕜 {v | ∃ ω, G.generator.IsEigenSq ω v})ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction (fun v hv => hperp v hv) (inner_zero_left _)
      (fun a b _ _ ha hb => by rw [inner_add_left, ha, hb, add_zero])
      (fun c a _ ha => by rw [inner_smul_left, ha, mul_zero]) hu
  have hbot : (Submodule.span 𝕜 {v | ∃ ω, G.generator.IsEigenSq ω v})ᗮ = ⊥ := by
    rw [← Submodule.topologicalClosure_eq_top_iff, ← Submodule.dense_iff_topologicalClosure_eq_top]
    exact hD
  rw [hbot, Submodule.mem_bot] at hz'
  have := G.stationary.starProjection_apply_mem x
  rwa [← sub_eq_zero.1 hz'] at this

/-- **Under an eigenbasis, the invariant core is stationary unless it contains a moving
eigenvector**: if `K` is closed and every eigenvector of `A²` with eigenvalue `-ω²`, `ω > 0`,
lying in the invariant core of `K` vanishes, then the invariant core consists of stationary
vectors. (The projection onto the invariant core commutes with `A`, so it maps eigenvectors of
`A²` to eigenvectors in the core.) -/
theorem IsIsometric.invariantCore_le_stationary_of_eigenDense (hG : G.IsIsometric)
    (hD : G.EigenDense) {K : Submodule 𝕜 E} (hK : IsClosed (K : Set E))
    (hkey : ∀ ω, 0 < ω → ∀ v ∈ G.invariantCore K, G.generator.IsEigenSq ω v → v = 0) :
    G.invariantCore K ≤ G.stationary := by
  have : CompleteSpace (G.invariantCore K) := (isClosed_invariantCore hK).completeSpace_coe
  have : K.HasOrthogonalProjection := by
    have : CompleteSpace K := hK.completeSpace_coe
    infer_instance
  intro x hx
  refine hG.mem_stationary_of_inner_isEigenSq hD fun ω hω v hv => ?_
  set N := G.invariantCore K
  have hPv := hkey ω hω _ (N.starProjection_apply_mem v)
    (hv.starProjection hG.isReducing_invariantCore)
  rw [← N.starProjection_eq_self_iff.2 hx, ← Submodule.inner_starProjection_left_eq_right, hPv,
    inner_zero_left]

/-- **A non-stationary invariant core contains a moving eigenvector** (under an eigenbasis): if
the invariant core of a closed `K` is not stationary, it contains a nonzero eigenvector of `A²`
with eigenvalue `-ω²`, `ω > 0`. -/
theorem IsIsometric.exists_isEigenSq_mem_invariantCore (hG : G.IsIsometric) (hD : G.EigenDense)
    {K : Submodule 𝕜 E} (hK : IsClosed (K : Set E)) (h : ¬ G.invariantCore K ≤ G.stationary) :
    ∃ ω, 0 < ω ∧ ∃ v ∈ G.invariantCore K, G.generator.IsEigenSq ω v ∧ v ≠ 0 := by
  by_contra hne
  refine h (hG.invariantCore_le_stationary_of_eigenDense hD hK fun ω hω v hv hev => ?_)
  by_contra hv0
  exact hne ⟨ω, hω, v, hv, hev, hv0⟩

/-- **When an eigenvector of `A²` lies in the invariant core**: for `A (A v) = -ω² v`, `ω > 0`,
`v` lies in the invariant core of `K` iff `v ∈ K` and `A v ∈ K` (the orbit is
`cos(ωt) v + (sin(ωt)/ω) A v`). -/
theorem IsIsometric.mem_invariantCore_iff_of_isEigenSq (hG : G.IsIsometric) {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] {ω : ℝ} (hω : 0 < ω) {v : E} (h : v ∈ G.generator.domain)
    (h' : G.generator ⟨v, h⟩ ∈ G.generator.domain)
    (e : G.generator ⟨G.generator ⟨v, h⟩, h'⟩ = -(ω ^ 2) • v) :
    v ∈ G.invariantCore K ↔ v ∈ K ∧ G.generator ⟨v, h⟩ ∈ K := by
  refine ⟨fun hv => ⟨invariantCore_le hv,
    invariantCore_le (hG.apply_mem_invariantCore ⟨v, h⟩ hv)⟩, fun ⟨h1, h2⟩ => ?_⟩
  refine mem_invariantCore.2 fun t => ?_
  rw [hG.S_eq_of_isEigenSq hω h h' e t]
  exact K.add_mem (K.smul_of_tower_mem _ h1) (K.smul_of_tower_mem _ h2)

end C0Group

end Feec

/-! ### Rescaling time -/

namespace Feec

namespace C0Group

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **The group with rescaled time** `t ↦ S (a t)`. -/
def rescale (G : C0Group 𝕜 E) (a : ℝ) : C0Group 𝕜 E where
  S t := G.S (a * t)
  map_zero := by rw [mul_zero, G.map_zero]
  map_add s t := by rw [mul_add, G.map_add]
  strongCont x := (G.strongCont x).comp (continuous_const.mul continuous_id)

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
@[simp] theorem rescale_S (G : C0Group 𝕜 E) (a t : ℝ) : (G.rescale a).S t = G.S (a * t) := rfl

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem IsIsometric.rescale {G : C0Group 𝕜 E} (hG : G.IsIsometric) (a : ℝ) :
    (G.rescale a).IsIsometric := fun _ x => hG _ x

variable [CompleteSpace E]

/-- The rescaled orbit of `x ∈ D(A)` has derivative `a A x` at `0`. -/
theorem hasDerivAt_rescale (G : C0Group 𝕜 E) (a : ℝ) (x : G.generator.domain) :
    HasDerivAt (fun t => G.S (a * t) x) (a • G.generator x) 0 := by
  have h : HasDerivAt (fun t => G.S t x) (G.generator x) (a * 0) := by
    rw [mul_zero]; exact G.hasDerivAt_generator x
  have h2 : HasDerivAt (fun t : ℝ => a * t) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul a
  exact h.scomp (0 : ℝ) h2

/-- **The generator of the rescaled group** is `a A` (`a ≠ 0`). -/
theorem generator_rescale (G : C0Group 𝕜 E) {a : ℝ} (ha : a ≠ 0) :
    (G.rescale a).generator = (a : 𝕜) • G.generator := by
  have hdom : ∀ x, x ∈ (G.rescale a).generator.domain ↔ x ∈ G.generator.domain := by
    intro x
    rw [mem_domain_generator_iff, mem_domain_generator_iff]
    change DifferentiableAt ℝ (fun t => G.S (a * t) x) 0 ↔ _
    constructor
    · intro h
      have h0 : DifferentiableAt ℝ (fun t => G.S (a * t) x) (a⁻¹ * 0) := by
        rw [mul_zero]; exact h
      have h' := h0.comp (0 : ℝ) ((differentiableAt_id (x := (0 : ℝ))).const_mul a⁻¹)
      refine h'.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
      simp [← mul_assoc, mul_inv_cancel₀ ha]
    · intro h
      exact (G.hasDerivAt_rescale a ⟨x, (G.mem_domain_generator_iff x).2 h⟩).differentiableAt
  refine LinearPMap.ext (Submodule.ext hdom) fun x hx hx' => ?_
  refine (G.rescale a).generator_apply_eq ?_
  rw [LinearPMap.smul_apply, ← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  exact G.hasDerivAt_rescale a ⟨x, hx'⟩

end C0Group

end Feec

/-! ### Eigenvectors and stationary vectors -/

namespace Feec

namespace C0Group

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {G : C0Group 𝕜 E}

variable [CompleteSpace E]

/-- **A nonzero eigenvector of `A²` with eigenvalue `-ω² ≠ 0` is not stationary.** -/
theorem not_mem_stationary_of_isEigenSq {ω : ℝ} (hω : ω ≠ 0) {v : E}
    (hv : G.generator.IsEigenSq ω v) (hv0 : v ≠ 0) : v ∉ G.stationary := by
  intro hs
  obtain ⟨h, h', e⟩ := hv
  obtain ⟨h'', e0⟩ := mem_domain_generator_of_mem_stationary hs
  have : (⟨G.generator ⟨v, h⟩, h'⟩ : G.generator.domain) = 0 := Subtype.ext e0
  rw [this, LinearPMap.map_zero] at e
  exact hv0 (smul_eq_zero.1 e.symm |>.resolve_left (by simpa using hω))

/-- **Stationarity of the invariant core is checked on the domain**: if every element of
`D(A) ∩ invariantCore K` is stationary, so is every element of `invariantCore K`. -/
theorem IsIsometric.invariantCore_le_stationary_of_domain (hG : G.IsIsometric)
    {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    (h : ∀ x : G.generator.domain, (x : E) ∈ G.invariantCore K → (x : E) ∈ G.stationary) :
    G.invariantCore K ≤ G.stationary := by
  intro k hk
  refine closure_minimal ?_ isClosed_stationary (hG.mem_closure_domain_inter_invariantCore hk)
  rintro y ⟨hy1, hy2⟩
  exact h ⟨y, hy1⟩ hy2

end C0Group

end Feec
