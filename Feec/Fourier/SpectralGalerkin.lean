module

public import Feec.Fourier.FibreReducing
public import Feec.Fourier.Torus
public import Feec.HilbertComplex.Compactness

/-!
# Spectral Galerkin approximation of symbol complexes

For measurable `A`, the band-limited fields `L²_A = {u | u = 0 a.e. off A}` form a reducing
subcomplex of a symbol complex, so the spectral Galerkin solution `S(t) P_A U₀` has the error
`‖U₀ - P_A U₀‖` at all times; on the torus, `‖u - P_N u‖ ≤ (2π (N + 1))^{-s} ‖u‖_{Hˢ}` for `s ≥ 0`
and the bands `|k|_∞ ≤ N`.
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

theorem band_propagates {a b : ℝ} {F U : ℝ → PiLp 2 fun i => Lp (E i) 2 μ}
    (hU : Evolution.IsStrongSolution S.toHilbertComplex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub (S.band A))
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub (S.band A)) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub (S.band A) :=
  (fibreReducing_band S hA).propagates hU h0 hF

theorem waveGroup_totalProj_band (t : ℝ) (x : PiLp 2 fun i => Lp (E i) 2 μ) :
    S.toHilbertComplex.waveGroup.S t
        ((HilbertComplex.totalSub (S.band A)).starProjection x) =
      (HilbertComplex.totalSub (S.band A)).starProjection
        (S.toHilbertComplex.waveGroup.S t x) :=
  S.toHilbertComplex.isIsometric_waveGroup.S_starProjection
    (fun s _ hy => (fibreReducing_band S hA).waveGroup_mem s hy) t x

omit hA in
/-- The spectral Galerkin error: `‖S(t) U₀ - S(t) P_A U₀‖ = ‖U₀ - P_A U₀‖`. -/
theorem norm_waveGroup_sub_waveGroup_band (t : ℝ) (x : PiLp 2 fun i => Lp (E i) 2 μ) :
    ‖S.toHilbertComplex.waveGroup.S t x - S.toHilbertComplex.waveGroup.S t
        ((HilbertComplex.totalSub (S.band A)).starProjection x)‖ =
      ‖x - (HilbertComplex.totalSub (S.band A)).starProjection x‖ := by
  rw [← _root_.map_sub]
  exact S.toHilbertComplex.isIsometric_waveGroup t _

end Band

/-! ### Convergence of the truncations -/

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

/-! ### Compactness from coercive symbols (counting measure) -/

section Compact

variable {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]

omit [∀ i, CompleteSpace (E i)] in
include 𝕜 in
theorem hasSum_norm_sq_count {i : ι} (u : Lp (E i) 2 (Measure.count : Measure β)) :
    HasSum (fun a => ‖u a‖ ^ 2) (‖u‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) ((lp.equivLpCount 𝕜 β (E i) 2).symm u)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, lp.equivLpCount_symm_apply,
    LinearIsometryEquiv.norm_map] at h
  exact h

omit [∀ i, CompleteSpace (E i)] in
theorem coeFn_starProjection_band_count (S : SymbolComplex 𝕜 (Measure.count : Measure β) c E)
    (A : Set β) (i : ι) [(S.band A i).HasOrthogonalProjection]
    (u : Lp (E i) 2 (Measure.count : Measure β)) :
    ⇑((S.band A i).starProjection u) = A.indicator ⇑u := by
  funext a
  rw [Measure.ae_count_iff.1 (Operator.coeFn_starProjection_fibreSub (μ := Measure.count)
    (bandFibre (𝕜 := 𝕜) (E := E) A i) AEStronglyMeasurable.of_discrete u) a]
  dsimp only
  rw [starProjection_bandFibre]
  by_cases ha : a ∈ A
  · simp [ha, Operator.cutoff_apply_of_mem ha]
  · simp [ha, Operator.cutoff_apply_of_notMem ha]

variable [∀ i, FiniteDimensional 𝕜 (E i)]

omit [MeasurableSingletonClass β] [Countable β] [∀ i, FiniteDimensional 𝕜 (E i)] in
theorem coeFn_d_count (S : SymbolComplex 𝕜 (Measure.count : Measure β) c E) {i j : ι}
    (u : (S.toHilbertComplex.d i j).domain) (a : β) :
    (S.toHilbertComplex.d i j u : β → E j) a =
      S.m i j a ((u : Lp (E i) 2 (Measure.count : Measure β)) a) :=
  Operator.coeFn_mulOp_count (S.m i j) u a

omit [MeasurableSingletonClass β] [Countable β] [∀ i, FiniteDimensional 𝕜 (E i)] in
theorem coeFn_adjoint_d_count (S : SymbolComplex 𝕜 (Measure.count : Measure β) c E) {i j : ι}
    (u : ((S.toHilbertComplex.d i j)†).domain) (a : β) :
    ((S.toHilbertComplex.d i j)† u : β → E i) a =
      ContinuousLinearMap.adjoint (S.m i j a) ((u : Lp (E j) 2 (Measure.count : Measure β)) a) :=
  Measure.ae_count_iff.1 (Operator.coeFn_adjoint_mulOp (S.meas i j) u) a

omit [∀ i, CompleteSpace (E i)] [MeasurableSingletonClass β] [Countable β] in
theorem finiteDimensional_band (S : SymbolComplex 𝕜 (Measure.count : Measure β) c E)
    {A : Set β} (hA : A.Finite) (i : ι) : FiniteDimensional 𝕜 (S.band A i) := by
  have : Fintype A := hA.fintype
  let Φ : S.band A i →ₗ[𝕜] (A → E i) :=
    { toFun := fun u a => (u : Lp (E i) 2 (Measure.count : Measure β)) (a : β)
      map_add' := fun u v => by
        funext a
        exact Measure.ae_count_iff.1 (Lp.coeFn_add (u : Lp (E i) 2 (Measure.count : Measure β))
          (v : Lp (E i) 2 (Measure.count : Measure β))) (a : β)
      map_smul' := fun r u => by
        funext a
        exact Measure.ae_count_iff.1
          (Lp.coeFn_smul r (u : Lp (E i) 2 (Measure.count : Measure β))) (a : β) }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h0 := (mem_band_iff (S := S)).1 u.2
    rw [Measure.ae_count_iff] at h0
    refine Subtype.ext (Lp.ext_count fun a => ?_)
    rw [ZeroMemClass.coe_zero, Measure.ae_count_iff.1 (Lp.coeFn_zero (E i) 2 _) a]
    by_cases ha : a ∈ A
    · exact congrFun hu ⟨a, ha⟩
    · exact h0 a ha
  exact Module.Finite.of_injective Φ hinj

/-- For the counting measure and finite-dimensional fibres, a coercive symbol with finite sublevel
sets gives the compactness property. -/
theorem hasCompactPropertyAt_of_coercive (S : SymbolComplex 𝕜 (Measure.count : Measure β) c E)
    (i : ι) (lam : β → ℝ)
    (hcoer : ∀ a (v : E i), lam a * ‖v‖ ^ 2 ≤ ‖S.m i (c.next i) a v‖ ^ 2 +
      ‖ContinuousLinearMap.adjoint (S.m (c.prev i) i a) v‖ ^ 2)
    (hfin : ∀ R, {a | lam a ≤ R}.Finite) : S.toHilbertComplex.HasCompactPropertyAt i := by
  set H := S.toHilbertComplex
  set B : Set (Lp (E i) 2 (Measure.count : Measure β)) :=
    {x | ∃ (hx : x ∈ (H.d i (c.next i)).domain) (hx' : x ∈ ((H.d (c.prev i) i)†).domain),
      ‖x‖ ≤ 1 ∧ ‖H.d i (c.next i) ⟨x, hx⟩‖ ≤ 1 ∧ ‖(H.d (c.prev i) i)† ⟨x, hx'⟩‖ ≤ 1}
  have hB : TotallyBounded B := by
    refine Metric.totallyBounded_iff.2 fun ε hε => ?_
    set R : ℝ := 8 / ε ^ 2 + 1 with hR
    have hRpos : 0 < R := by positivity
    set A := {a | lam a ≤ R}
    have hAm : MeasurableSet A := MeasurableSet.of_discrete
    have := hasOrthogonalProjection_band S hAm i
    set P := (S.band A i).starProjection
    have hfd := finiteDimensional_band S (hfin R) i
    -- the truncations of the box are in a compact set
    have hK : IsCompact ((S.band A i).subtype '' Metric.closedBall (0 : S.band A i) 1) :=
      (ProperSpace.isCompact_closedBall _ _).image (S.band A i).subtypeL.continuous
    have hPB : P '' B ⊆ (S.band A i).subtype '' Metric.closedBall (0 : S.band A i) 1 := by
      rintro _ ⟨x, ⟨hx, hx', h1, -, -⟩, rfl⟩
      refine ⟨(S.band A i).orthogonalProjectionOnto x, ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖(S.band A i).orthogonalProjectionOnto x‖ ≤ 1 * ‖x‖ :=
            (S.band A i).orthogonalProjectionOnto.le_of_opNorm_le
              (S.band A i).orthogonalProjectionOnto_norm_le x
        _ ≤ 1 := by rw [one_mul]; exact h1
    obtain ⟨t, ht, hcov⟩ := Metric.totallyBounded_iff.1 (hK.totallyBounded.subset hPB) (ε / 2)
      (by positivity)
    refine ⟨t, ht, fun x hxB => ?_⟩
    obtain ⟨hx, hx', h1, h2, h3⟩ := hxB
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov ⟨x, ⟨hx, hx', h1, h2, h3⟩, rfl⟩)
    refine Set.mem_iUnion₂.2 ⟨y, hy, ?_⟩
    -- the tail estimate
    have hPx : ∀ a, (P x : β → E i) a = if a ∈ A then x a else 0 := fun a => by
      rw [coeFn_starProjection_band_count, Set.indicator_apply]
    have hdiff : ∀ a, ‖(x - P x : Lp (E i) 2 _) a‖ ^ 2 ≤
        R⁻¹ * (‖(H.d i (c.next i) ⟨x, hx⟩ : β → E (c.next i)) a‖ ^ 2 +
          ‖((H.d (c.prev i) i)† ⟨x, hx'⟩ : β → E (c.prev i)) a‖ ^ 2) := fun a => by
      rw [Measure.ae_count_iff.1 (Lp.coeFn_sub x (P x)) a, Pi.sub_apply, hPx,
        coeFn_d_count S ⟨x, hx⟩ a, coeFn_adjoint_d_count S ⟨x, hx'⟩ a]
      by_cases ha : a ∈ A
      · simp only [ha, ↓reduceIte, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow]; positivity
      · simp only [ha, ↓reduceIte, sub_zero]
        have hla : R < lam a := lt_of_not_ge ha
        have := hcoer a (x a)
        rw [le_inv_mul_iff₀ hRpos]
        nlinarith [sq_nonneg ‖(x : β → E i) a‖]
    have hsum := hasSum_le hdiff (hasSum_norm_sq_count (𝕜 := 𝕜) (x - P x))
      (((hasSum_norm_sq_count (𝕜 := 𝕜) (H.d i (c.next i) ⟨x, hx⟩)).add
        (hasSum_norm_sq_count (𝕜 := 𝕜) ((H.d (c.prev i) i)† ⟨x, hx'⟩))).mul_left R⁻¹)
    have hsq : ‖x - P x‖ ^ 2 < (ε / 2) ^ 2 := by
      refine hsum.trans_lt ?_
      have h22 : ‖H.d i (c.next i) ⟨x, hx⟩‖ ^ 2 + ‖(H.d (c.prev i) i)† ⟨x, hx'⟩‖ ^ 2 ≤ 2 := by
        nlinarith [norm_nonneg (H.d i (c.next i) ⟨x, hx⟩),
          norm_nonneg ((H.d (c.prev i) i)† ⟨x, hx'⟩)]
      calc R⁻¹ * (‖H.d i (c.next i) ⟨x, hx⟩‖ ^ 2 + ‖(H.d (c.prev i) i)† ⟨x, hx'⟩‖ ^ 2)
          ≤ R⁻¹ * 2 := mul_le_mul_of_nonneg_left h22 (by positivity)
        _ < (ε / 2) ^ 2 := by
          rw [hR, inv_mul_eq_div, div_lt_iff₀ (by positivity)]
          field_simp
          nlinarith [sq_nonneg ε, hε]
    have hlt : dist x (P x) < ε / 2 := by
      rw [dist_eq_norm]
      exact (sq_lt_sq₀ (norm_nonneg _) (by positivity)).1 hsq
    exact (dist_triangle x (P x) y).trans_lt (by linarith [show dist (P x) y < ε / 2 from hxy])
  exact ⟨closure B, hB.closure.isCompact_of_isClosed isClosed_closure,
    fun x hx hx' h1 h2 h3 => subset_closure ⟨hx, hx', h1, h2, h3⟩⟩

end Compact

/-! ### Torus bands -/

namespace Torus

variable {d : Type*} [Fintype d]

/-- The finite band `|k|_∞ ≤ N` of Fourier modes on `𝕋ᵈ`. -/
def bandN (N : ℕ) : Set (d → ℤ) := {k | ∀ j, |k j| ≤ N}

omit [Fintype d] in
theorem mem_bandN {N : ℕ} {k : d → ℤ} : k ∈ bandN N ↔ ∀ j, |k j| ≤ N := Iff.rfl

omit [Fintype d] in
theorem flipAt_mem_bandN [DecidableEq d] {N : ℕ} {k : d → ℤ} (j : d) :
    flipAt j k ∈ bandN N ↔ k ∈ bandN N := by
  simp only [mem_bandN, flipAt_apply]
  refine forall_congr' fun a => ?_
  split_ifs <;> simp

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

theorem two_pi_mul_add_one_le_norm_freq_of_notMem {N : ℕ} {k : d → ℤ} (hk : k ∉ bandN N) :
    2 * Real.pi * (N + 1) ≤ ‖freq k‖ := by
  obtain ⟨j, hj⟩ := not_forall.1 (mt mem_bandN.2 hk)
  have h1 : (N : ℝ) + 1 ≤ |(k j : ℝ)| := by
    have : (N : ℤ) + 1 ≤ |k j| := by omega
    exact_mod_cast this
  have h2 := PiLp.norm_apply_le (freq k) j
  rw [freq_apply, Real.norm_eq_abs, abs_mul, abs_of_pos Real.two_pi_pos] at h2
  exact (mul_le_mul_of_nonneg_left h1 Real.two_pi_pos.le).trans h2

omit [∀ i, CompleteSpace (E i)] in
theorem sobolev_sub_starProjection_band_le
    (S : SymbolComplex 𝕜 (Measure.count : Measure (d → ℤ)) c E) {s t : ℝ} (hts : t ≤ s) (N : ℕ)
    {i : ι} [(S.band (bandN N) i).HasOrthogonalProjection]
    {u : Lp (E i) 2 (Measure.count : Measure (d → ℤ))}
    (hu : Summable fun k => (1 + ‖freq k‖ ^ 2) ^ s * ‖u k‖ ^ 2) :
    Summable (fun k => (1 + ‖freq k‖ ^ 2) ^ t * ‖(u - (S.band (bandN N) i).starProjection u :
        Lp (E i) 2 (Measure.count : Measure (d → ℤ))) k‖ ^ 2) ∧
      ∑' k, (1 + ‖freq k‖ ^ 2) ^ t * ‖(u - (S.band (bandN N) i).starProjection u :
          Lp (E i) 2 (Measure.count : Measure (d → ℤ))) k‖ ^ 2 ≤
        (1 + (2 * Real.pi * (N + 1)) ^ 2) ^ (t - s) *
          ∑' k, (1 + ‖freq k‖ ^ 2) ^ s * ‖u k‖ ^ 2 := by
  set B : ℝ := (1 + (2 * Real.pi * (N + 1)) ^ 2) ^ (t - s)
  have hle : ∀ k, (1 + ‖freq k‖ ^ 2) ^ t * ‖(u - (S.band (bandN N) i).starProjection u :
      Lp (E i) 2 (Measure.count : Measure (d → ℤ))) k‖ ^ 2 ≤
        B * ((1 + ‖freq k‖ ^ 2) ^ s * ‖u k‖ ^ 2) := fun k => by
    rw [Measure.ae_count_iff.1 (Lp.coeFn_sub u _) k, Pi.sub_apply,
      coeFn_starProjection_band_count]
    by_cases hk : k ∈ bandN N
    · rw [Set.indicator_of_mem hk, sub_self, norm_zero, zero_pow two_ne_zero, mul_zero]
      positivity
    · have hb : 0 < 1 + ‖freq k‖ ^ 2 := by positivity
      have hf : (2 * Real.pi * (N + 1)) ^ 2 ≤ ‖freq k‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) (two_pi_mul_add_one_le_norm_freq_of_notMem hk) 2
      have e : (1 + ‖freq k‖ ^ 2) ^ t = (1 + ‖freq k‖ ^ 2) ^ (t - s) * (1 + ‖freq k‖ ^ 2) ^ s := by
        rw [← Real.rpow_add hb, sub_add_cancel]
      rw [Set.indicator_of_notMem hk, sub_zero, e, mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)) (by positivity)
  have hsum := Summable.of_nonneg_of_le (fun k => by positivity) hle (hu.mul_left B)
  exact ⟨hsum, (Summable.tsum_le_tsum hle hsum (hu.mul_left B)).trans_eq tsum_mul_left⟩

omit [∀ i, CompleteSpace (E i)] in
/-- `‖u - P_N u‖ ≤ (2π (N + 1))^{-s} ‖u‖_{Hˢ}` on `𝕋ᵈ` for `s ≥ 0`. -/
theorem norm_sub_starProjection_band_le (S : SymbolComplex 𝕜 (Measure.count : Measure (d → ℤ)) c E)
    {s : ℝ} (hs : 0 ≤ s) (N : ℕ) {i : ι} [(S.band (bandN N) i).HasOrthogonalProjection]
    {u : Lp (E i) 2 (Measure.count : Measure (d → ℤ))}
    (hu : Summable fun k => (1 + ‖freq k‖ ^ 2) ^ s * ‖u k‖ ^ 2) :
    ‖u - (S.band (bandN N) i).starProjection u‖ ≤
      (2 * Real.pi * (N + 1))⁻¹ ^ s * √(∑' k, (1 + ‖freq k‖ ^ 2) ^ s * ‖u k‖ ^ 2) := by
  have ha : 0 < 2 * Real.pi * (N + 1) := by positivity
  have hT : 0 ≤ ∑' k, (1 + ‖freq k‖ ^ 2) ^ s * ‖u k‖ ^ 2 := tsum_nonneg fun k => by positivity
  have h := (sobolev_sub_starProjection_band_le S hs N hu).2
  simp only [Real.rpow_zero, one_mul, zero_sub] at h
  rw [(hasSum_norm_sq_count (𝕜 := 𝕜) _).tsum_eq] at h
  have hc : (1 + (2 * Real.pi * (N + 1)) ^ 2) ^ (-s) ≤ ((2 * Real.pi * (N + 1))⁻¹ ^ s) ^ 2 := by
    rw [Real.rpow_pow_comm (inv_nonneg.2 ha.le), inv_pow, Real.inv_rpow (sq_nonneg _),
      ← Real.rpow_neg (sq_nonneg _)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (le_add_of_nonneg_left zero_le_one)
      (neg_nonpos.2 hs)
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [mul_pow, Real.sq_sqrt hT]
  exact h.trans (mul_le_mul_of_nonneg_right hc hT)

end Torus

end Feec.Fourier
