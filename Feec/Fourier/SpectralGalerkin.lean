module

public import Feec.Fourier.FibreReducing
public import Feec.Fourier.Torus
public import Feec.HilbertComplex.Compactness

/-!
# Spectral Galerkin approximation of symbol complexes

For a symbol complex and a measurable set `A` of frequencies, the band-limited fields
`L²_A = {u | u = 0 a.e. off A}` form a reducing subcomplex: every multiplier preserves them, and
their orthogonal projection (the Fourier truncation) commutes with every differential. Hence the
**spectral Galerkin method** (truncate the data to the band, solve the Hodge wave equation) is a
reducing-subcomplex discretization. For an exhausting sequence of bands the truncations converge
to the identity (`tendsto_totalProj_band`).

On the torus the bands `|k|_∞ ≤ N` are finite sets of modes: this is the Fourier spectral method.

## Main results

* `bandFibre A`, `band A i = L²_A`, `mem_band_iff`; `starProjection_bandFibre` (the fibre
  projection is the cut-off `𝟙_A`).
* **`fibreReducing_band`**, `reducingSubcomplex_band`: band-limited fields reduce every symbol
  complex.
* **`tendsto_totalProj_band`**: `P_{A_N} U₀ → U₀` for an increasing exhausting sequence of bands,
  so the spectral Galerkin solutions converge uniformly in time.
* `Torus.bandN N = {k | ∀ j, |k j| ≤ N}`: finite bands exhausting `ℤᵈ`.
* `finiteDimensional_band` (finite bands are finite-dimensional) and
  **`hasCompactPropertyAt_of_coercive`**: for the counting measure, a coercive symbol
  `λ(a) ‖v‖² ≤ ‖m v‖² + ‖m'* v‖²` with finite sublevel sets gives the compactness property
  (truncation to finitely many modes plus a uniformly small tail).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.12–4.13 (Galerkin approximation of the Hodge wave equation)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 5 (approximation of Hilbert
  complexes)

Bibliography: [references.bib](../../docs/references.bib)
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

/-! ### Compactness from coercive symbols (counting measure) -/

section Compact

variable {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]

omit [∀ i, CompleteSpace (E i)] in
include 𝕜 in
/-- The `ℓ²` norm identity on `L²(count)`: `‖u‖² = Σ_a ‖u a‖²`. -/
theorem hasSum_norm_sq_count {i : ι} (u : Lp (E i) 2 (Measure.count : Measure β)) :
    HasSum (fun a => ‖u a‖ ^ 2) (‖u‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) ((lp.equivLpCount 𝕜 β (E i) 2).symm u)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, lp.equivLpCount_symm_apply,
    LinearIsometryEquiv.norm_map] at h
  exact h

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
/-- Band-limited fields on a finite set of frequencies form a finite-dimensional space. -/
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

/-- **The compactness property from a coercive symbol.** If
`λ(a) ‖v‖² ≤ ‖m_{i → next} v‖² + ‖m_{prev → i}* v‖²` with finite sublevel sets of `λ`, the
symbol complex has the compactness property at `i` (Rellich: the box of `D(d) ∩ D(d*)` is
uniformly small off a finite set of frequencies). -/
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
    have hR1 : 1 ≤ R := by rw [hR]; have : 0 ≤ 8 / ε ^ 2 := by positivity
                           linarith
    have hRpos : 0 < R := by linarith
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
      have := Measure.ae_count_iff.1 (Operator.coeFn_starProjection_fibreSub (μ := Measure.count)
        (bandFibre (𝕜 := 𝕜) (E := E) A i) AEStronglyMeasurable.of_discrete x) a
      rw [this]
      dsimp only
      rw [starProjection_bandFibre]
      by_cases ha : a ∈ A
      · simp [ha, Operator.cutoff_apply_of_mem ha]
      · simp [ha, Operator.cutoff_apply_of_notMem ha]
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
    calc dist x y ≤ dist x (P x) + dist (P x) y := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hlt hxy
      _ = ε := by ring
  refine ⟨closure B, hB.closure.isCompact_of_isClosed isClosed_closure, ?_⟩
  intro x hx hx' h1 h2 h3
  exact subset_closure ⟨hx, hx', h1, h2, h3⟩

end Compact

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
