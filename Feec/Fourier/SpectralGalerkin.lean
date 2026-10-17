module

public import Feec.Fourier.FibreReducing
public import Feec.Fourier.Torus

/-!
# Spectral Galerkin approximation of symbol complexes

For a symbol complex and a measurable set `A` of frequencies, the band-limited fields
`L²_A = {u | u = 0 a.e. off A}` form a reducing subcomplex: every multiplier preserves them, and
their orthogonal projection (the Fourier truncation) commutes with every differential. Hence the
**spectral Galerkin method** (truncate the data to the band, solve the Hodge wave equation) is
exact on band-limited data, and its error for general data is the truncation error of the data,
uniformly in time (`norm_waveGroup_sub_waveGroup_band`). For an exhausting sequence of bands the
truncations converge to the identity (`tendsto_totalProj_band`).

On the torus the bands `|k|_∞ ≤ N` are finite sets of modes: this is the Fourier spectral method.

## Main results

* `bandFibre A`, `band A i = L²_A`, `mem_band_iff`; `starProjection_bandFibre` (the fibre
  projection is the cut-off `𝟙_A`).
* **`fibreReducing_band`**, `reducingSubcomplex_band`: band-limited fields reduce every symbol
  complex.
* `band_propagates`: band-limited data and forcing give band-limited strong solutions.
* `waveGroup_totalProj_band`: the wave group commutes with the Fourier truncation.
* **`norm_waveGroup_sub_waveGroup_band`**: `‖S(t) U₀ - S(t) P_A U₀‖ = ‖U₀ - P_A U₀‖` for all `t`.
* **`tendsto_totalProj_band`**: `P_{A_N} U₀ → U₀` for an increasing exhausting sequence of bands,
  so the spectral Galerkin solutions converge uniformly in time.
* `Torus.bandN N = {k | ∀ j, |k j| ≤ N}`: finite bands exhausting `ℤᵈ`.

## References

* [QuennevilleBelair2015], §4.12–4.13 (Galerkin approximation of the Hodge wave equation)
* [Arnold2018], Ch. 5 (approximation of Hilbert complexes)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace Topology
open MeasureTheory LinearPMap Set Filter

namespace Feec.Fourier

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
  {c : ComplexShape ι} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace 𝕜 (E i)] [∀ i, CompleteSpace (E i)]

open Classical in
/-- The band fibres: everything on `A`, nothing off `A`. -/
def bandFibre (A : Set α) (i : ι) (a : α) : Submodule 𝕜 (E i) := if a ∈ A then ⊤ else ⊥

instance (A : Set α) (i : ι) (a : α) : (bandFibre (𝕜 := 𝕜) (E := E) A i a).HasOrthogonalProjection := by
  unfold bandFibre; split_ifs <;> infer_instance

omit [MeasurableSpace α] [∀ i, CompleteSpace (E i)] in
theorem starProjection_bandFibre (A : Set α) (i : ι) (a : α) :
    (bandFibre (𝕜 := 𝕜) (E := E) A i a).starProjection = Operator.cutoff 𝕜 (E i) A a := by
  by_cases h : a ∈ A
  · have e : bandFibre (𝕜 := 𝕜) (E := E) A i a = ⊤ := by simp [bandFibre, h]
    simp only [e, Submodule.starProjection_top']
    simp [Operator.cutoff, h]; rfl
  · have e : bandFibre (𝕜 := 𝕜) (E := E) A i a = ⊥ := by simp [bandFibre, h]
    simp only [e, Submodule.starProjection_bot]
    simp [Operator.cutoff, h]

omit [∀ i, CompleteSpace (E i)] in
theorem aestronglyMeasurable_starProjection_bandFibre {A : Set α} (hA : MeasurableSet A) (i : ι) :
    AEStronglyMeasurable (fun a => (bandFibre (𝕜 := 𝕜) (E := E) A i a).starProjection) μ := by
  simp_rw [starProjection_bandFibre]
  exact Operator.aestronglyMeasurable_cutoff hA

/-- **Band-limited fields reduce every symbol complex.** -/
theorem fibreReducing_band (S : SymbolComplex 𝕜 μ c E) {A : Set α} (hA : MeasurableSet A) :
    FibreReducing S (bandFibre A) where
  map i j a := by
    by_cases h : a ∈ A
    · simp [bandFibre, h]
    · simp [bandFibre, h]
  map_adj i j a := by
    by_cases h : a ∈ A
    · simp [bandFibre, h]
    · simp [bandFibre, h]
  meas i := aestronglyMeasurable_starProjection_bandFibre hA i

/-- The band-limited fields `L²_A = {u | u a = 0 for a.e. a ∉ A}` of a symbol complex. -/
abbrev SymbolComplex.band (_S : SymbolComplex 𝕜 μ c E) (A : Set α) (i : ι) :
    Submodule 𝕜 (Lp (E i) 2 μ) :=
  Operator.fibreSub μ (bandFibre (𝕜 := 𝕜) (E := E) A i)

omit [∀ i, CompleteSpace (E i)] in
theorem mem_band_iff {S : SymbolComplex 𝕜 μ c E} {A : Set α} {i : ι} {u : Lp (E i) 2 μ} :
    u ∈ S.band A i ↔ ∀ᵐ a ∂μ, a ∉ A → u a = 0 := by
  rw [Operator.mem_fibreSub]
  refine Filter.eventually_congr (Filter.Eventually.of_forall fun a => ?_)
  by_cases h : a ∈ A
  · simp [bandFibre, h]
  · simp [bandFibre, h]

section Band

variable (S : SymbolComplex 𝕜 μ c E) {A : Set α} (hA : MeasurableSet A)
include hA

theorem hasOrthogonalProjection_band (i : ι) : (S.band A i).HasOrthogonalProjection :=
  (fibreReducing_band S hA).hasOrthogonalProjection i

theorem reducingSubcomplex_band [∀ i, (S.band A i).HasOrthogonalProjection] :
    S.toHilbertComplex.ReducingSubcomplex (S.band A) :=
  (fibreReducing_band S hA).toReducingSubcomplex

variable [Fintype ι] [∀ i, (S.band A i).HasOrthogonalProjection]
  [∀ i, NormedSpace ℝ (E i)] [∀ i, IsScalarTower ℝ 𝕜 (E i)]

/-- **Band-limited data stay band-limited**: strong solutions of the Hodge wave equation with
band-limited data and forcing are band-limited for all times. -/
theorem band_propagates {a b : ℝ} {F U : ℝ → PiLp 2 fun i => Lp (E i) 2 μ}
    (hU : Evolution.IsStrongSolution S.toHilbertComplex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub (S.band A))
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub (S.band A)) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub (S.band A) :=
  (fibreReducing_band S hA).propagates hU h0 hF

/-- The wave group commutes with the Fourier truncation. -/
theorem waveGroup_totalProj_band (t : ℝ) (x : PiLp 2 fun i => Lp (E i) 2 μ) :
    S.toHilbertComplex.waveGroup.S t
        ((HilbertComplex.totalSub (S.band A)).starProjection x) =
      (HilbertComplex.totalSub (S.band A)).starProjection
        (S.toHilbertComplex.waveGroup.S t x) :=
  S.toHilbertComplex.isIsometric_waveGroup.S_starProjection
    (fun s _ hy => (fibreReducing_band S hA).waveGroup_mem s hy) t x

omit hA in
/-- **The error of the spectral Galerkin method is the truncation error of the data**, uniformly
in time: `‖S(t) U₀ - S(t) P_A U₀‖ = ‖U₀ - P_A U₀‖`. -/
theorem norm_waveGroup_sub_waveGroup_band (t : ℝ) (x : PiLp 2 fun i => Lp (E i) 2 μ) :
    ‖S.toHilbertComplex.waveGroup.S t x - S.toHilbertComplex.waveGroup.S t
        ((HilbertComplex.totalSub (S.band A)).starProjection x)‖ =
      ‖x - (HilbertComplex.totalSub (S.band A)).starProjection x‖ := by
  rw [← _root_.map_sub]
  exact S.toHilbertComplex.isIsometric_waveGroup t _

end Band

/-! ### Convergence of the truncations -/

/-- **Fourier truncations converge to the identity** along an increasing exhausting sequence of
bands. -/
theorem tendsto_starProjection_band (S : SymbolComplex 𝕜 μ c E) {A : ℕ → Set α} (hA : ∀ N, MeasurableSet (A N))
    (hmono : Monotone A) (hcov : ∀ a, ∃ N, a ∈ A N) (i : ι)
    [∀ N, (S.band (A N) i).HasOrthogonalProjection] (u : Lp (E i) 2 μ) :
    Tendsto (fun N => (S.band (A N) i).starProjection u) atTop (𝓝 u) := by
  refine Submodule.starProjection_tendsto_self _ (fun N M hNM => ?_) u ?_
  · intro v hv
    rw [mem_band_iff] at hv ⊢
    filter_upwards [hv] with a ha hM
    exact ha fun hN => hM (hmono hNM hN)
  · rw [top_le_iff, Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro w hw
    have h0 : ∀ N, (S.band (A N) i).starProjection w = 0 := fun N => by
      refine (Submodule.starProjection_apply_eq_zero_iff _).2 ?_
      rw [Submodule.mem_orthogonal] at hw ⊢
      exact fun v hv => hw v (Submodule.mem_iSup_of_mem N hv)
    have hP := fun N => Operator.coeFn_starProjection_fibreSub (μ := μ)
      (bandFibre (𝕜 := 𝕜) (E := E) (A N) i) (aestronglyMeasurable_starProjection_bandFibre (hA N) i) w
    have hw0 : ∀ N, ∀ᵐ a ∂μ, a ∈ A N → w a = 0 := fun N => by
      filter_upwards [hP N, Lp.ext_iff.1 (h0 N), Lp.coeFn_zero (E i) 2 μ] with a h1 h2 h3 ha
      have : (bandFibre (𝕜 := 𝕜) (E := E) (A N) i a).starProjection (w a) = 0 := by
        rw [← h1]; exact h2.trans h3
      rwa [starProjection_bandFibre, Operator.cutoff_apply_of_mem ha] at this
    have hw' : (w : α → E i) =ᵐ[μ] 0 := by
      refine Operator.ae_of_forall_mem_cover hcov ?_
      filter_upwards [ae_all_iff.2 hw0] with a ha N hN
      exact ha N hN
    exact Lp.ext (hw'.trans (Lp.coeFn_zero (E i) 2 μ).symm)

/-- The total truncation converges to the identity. -/
theorem tendsto_totalProj_band [Fintype ι] (S : SymbolComplex 𝕜 μ c E) {A : ℕ → Set α} (hA : ∀ N, MeasurableSet (A N))
    (hmono : Monotone A) (hcov : ∀ a, ∃ N, a ∈ A N)
    [∀ N i, (S.band (A N) i).HasOrthogonalProjection]
    (x : PiLp 2 fun i => Lp (E i) 2 μ) :
    Tendsto (fun N => (HilbertComplex.totalSub (S.band (A N))).starProjection x)
      atTop (𝓝 x) := by
  have e : (fun N => (HilbertComplex.totalSub (S.band (A N))).starProjection x) =
      fun N => WithLp.toLp 2 fun i => (S.band (A N) i).starProjection (x i) := by
    funext N; exact PiLp.ext fun i => HilbertComplex.totalSub_starProjection_apply (S := S.band (A N)) x i
  rw [e, show x = WithLp.toLp 2 (WithLp.ofLp x) from rfl]
  exact ((PiLp.continuous_toLp 2 _).tendsto _).comp
    (tendsto_pi_nhds.2 fun i => tendsto_starProjection_band S hA hmono hcov i (x i))

/-! ### Torus bands -/

namespace Torus

variable {d : Type*} [Fintype d]

/-- The finite band `|k|_∞ ≤ N` of Fourier modes on `𝕋ᵈ`. -/
def bandN (N : ℕ) : Set (d → ℤ) := {k | ∀ j, |k j| ≤ N}

omit [Fintype d] in
theorem bandN_mono : Monotone (bandN (d := d)) := fun N M h k hk j =>
  (hk j).trans (by exact_mod_cast h)

theorem exists_mem_bandN (k : d → ℤ) : ∃ N, k ∈ bandN N := by
  refine ⟨(Finset.univ.sup fun j => (k j).natAbs), fun j => ?_⟩
  have h : (k j).natAbs ≤ Finset.univ.sup fun j => (k j).natAbs :=
    Finset.le_sup (f := fun j => (k j).natAbs) (Finset.mem_univ j)
  rw [Int.abs_eq_natAbs]; exact_mod_cast h

theorem finite_bandN (N : ℕ) : (bandN (d := d) N).Finite := by
  have : bandN (d := d) N ⊆ Set.pi Set.univ fun _ => Set.Icc (-(N : ℤ)) N := fun k hk j _ =>
    abs_le.1 (hk j)
  exact (Set.Finite.pi fun _ => Set.finite_Icc _ _).subset this

end Torus

end Feec.Fourier
