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

## References

* [Pazy1983], §1.10
* [ReedSimon1980], Thm VI.16 (Hilbert–Schmidt theorem), §VII.3 (mean ergodic theorem)
* [QuennevilleBelair2015], §4.10 (Prop 4.17)
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

/-- Under pure point spectrum, the invariant core is stationary iff its periodic elements are. -/
theorem IsIsometric.invariantCore_le_stationary (hG : G.IsIsometric) (hPP : G.IsPurePoint)
    {K : Submodule 𝕜 E} (hK : IsClosed (K : Set E))
    (hkey : ∀ τ, 0 < τ → ∀ x ∈ G.invariantCore K, x ∈ G.periodic τ → x ∈ G.stationary) :
    G.invariantCore K ≤ G.stationary := by
  intro x hx
  set z := x - G.stationary.starProjection x
  have hz : z ∈ G.stationaryᗮ := G.stationary.sub_starProjection_mem_orthogonal x
  have h0 : z = 0 := by
    refine hPP.eq_zero_of_starProjection fun τ hτ => starProjection_eq_zero_of_mem hz ?_
    rw [_root_.map_sub, (G.periodic τ).starProjection_eq_self_iff.2
      (stationary_le_periodic τ (G.stationary.starProjection_apply_mem x))]
    refine G.stationary.sub_mem (hkey τ hτ _ (invariantCore_le (G := G)
      (K := G.invariantCore K) ?_) ((G.periodic τ).starProjection_apply_mem x))
      (G.stationary.starProjection_apply_mem x)
    exact hG.starProjection_periodic_mem_invariantCore (isClosed_invariantCore hK) hτ
      fun t _ => S_mem_invariantCore hx t
  have := G.stationary.starProjection_apply_mem x
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
      ext; simp only [y, Submodule.coe_add, Submodule.coe_smul, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
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
