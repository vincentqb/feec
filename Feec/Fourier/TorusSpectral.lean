module

public import Feec.Fourier.SpectralGalerkin
public import Feec.Semigroup.Spectral
public import Feec.HilbertComplex.RestrictScalars

/-!
# Pure point spectrum of Fourier models

A Hilbert complex whose total space is exhausted by finite-dimensional reducing subcomplexes has
an eigenbasis for its wave operator: on each finite-dimensional reducing subspace the wave
operator `L` is a skew-symmetric matrix, so `L²` is diagonalizable there
(`LinearPMap.IsSkewSymmetric.dense_span_isEigenSq_of_reducing`). Fourier models are of this
kind: for a symbol complex on a countable set of frequencies with the counting measure (the
torus `𝕋ᵈ`, frequencies `ℤᵈ`) and finite-dimensional fibres, the band-limited fields on finite
sets of frequencies are finite-dimensional reducing subcomplexes. Hence **every torus symbol
complex with finite-dimensional fibres has a wave group with pure point spectrum**, and forward
invariance of a closed subspace is full invariance
(`Feec.C0Group.IsIsometric.mem_invariantCore_of_forward_invariant`). The resolvent need not be
compact (the harmonic fields may form an infinite-dimensional space, e.g. `ker curl` for the
grad–curl complex), so `Feec.C0Group.eigenDense_of_compactResolvent` does not apply; the
Fourier modes replace it.

On the Fourier side the wave operator acts frequency by frequency through the **wave symbol**
`W(a)` (`SymbolComplex.waveSym`, `(L x)(a) = W(a) x(a)`), so an eigenvector of `L²` with
eigenvalue `-ω²` is, at every frequency, an eigenvector of `W(a)²`
(`SymbolComplex.waveSym_sq_of_isEigenSq`).

## Main results

* `HilbertComplex.eigenDense_waveGroup_of_reducing`, `isPurePoint_waveGroup_of_reducing`, and
  the real form `eigenDense_restrictScalars_waveGroup_of_reducing`: finite-dimensional
  reducing subcomplexes spanning a dense subspace give an eigenbasis.
* **`SymbolComplex.eigenDense_waveGroup`**, `SymbolComplex.isPurePoint_waveGroup`,
  `SymbolComplex.mem_invariantCore_of_forward_invariant` (counting measure, finite-dimensional
  fibres); `SymbolComplex.mem_closure_iUnion_band` (finite bands are dense).
* **`Torus.eigenDense_waveGroup`**, `Torus.isPurePoint_waveGroup`,
  `Torus.mem_invariantCore_of_forward_invariant`: every constant-coefficient complex on `𝕋ᵈ`.
* `SymbolComplex.waveSym`, `SymbolComplex.wave_apply_count`,
  `SymbolComplex.waveSym_sq_of_isEigenSq`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17 on the cube: only stationary data propagate)
* [M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*][ReedSimon1980],
  §VII.3 (mean ergodic theorem)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace Topology
open MeasureTheory LinearPMap Set Filter

/-! ### Finite-dimensional reducing subcomplexes -/

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

omit [∀ i, CompleteSpace (W i)] in
/-- A family of finite-dimensional subspaces has a finite-dimensional total subspace. -/
theorem finiteDimensional_totalSub (S : ∀ i, Submodule 𝕜 (W i))
    [∀ i, FiniteDimensional 𝕜 (S i)] : FiniteDimensional 𝕜 (totalSub S) := by
  let Φ : totalSub S →ₗ[𝕜] ∀ i, S i :=
    { toFun := fun x i => ⟨(x : PiLp 2 W) i, x.2 i⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ fun x y h => Subtype.ext (PiLp.ext fun i => ?_)
  exact congrArg Subtype.val (congrFun h i)

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] (H : HilbertComplex 𝕜 c W)

/-- **An eigenbasis from finite-dimensional reducing subcomplexes**: if finite-dimensional
reducing subcomplexes `B n` of `H` span a dense subspace of the total space, the eigenvectors of
`L²` span a dense subspace (`EigenDense`). -/
theorem eigenDense_waveGroup_of_reducing {κ : Type*} (B : κ → ∀ i, Submodule 𝕜 (W i))
    [∀ n i, FiniteDimensional 𝕜 (B n i)] (hB : ∀ n, H.ReducingSubcomplex (B n))
    (hspan : Dense ((⨆ n, totalSub (B n) : Submodule 𝕜 (PiLp 2 W)) : Set (PiLp 2 W))) :
    H.waveGroup.EigenDense := by
  have : ∀ n, FiniteDimensional 𝕜 (totalSub (B n)) := fun n => finiteDimensional_totalSub _
  unfold C0Group.EigenDense
  rw [generator_waveGroup]
  exact H.isSkewAdjoint_wave.isSkewSymmetric.dense_span_isEigenSq_of_reducing
    H.isSkewAdjoint_wave.dense_domain (fun n => totalSub (B n))
    (fun n => (hB n).isReducing_wave) hspan

/-- **Pure point spectrum** from finite-dimensional reducing subcomplexes. -/
theorem isPurePoint_waveGroup_of_reducing {κ : Type*} (B : κ → ∀ i, Submodule 𝕜 (W i))
    [∀ n i, FiniteDimensional 𝕜 (B n i)] (hB : ∀ n, H.ReducingSubcomplex (B n))
    (hspan : Dense ((⨆ n, totalSub (B n) : Submodule 𝕜 (PiLp 2 W)) : Set (PiLp 2 W))) :
    H.waveGroup.IsPurePoint :=
  H.isIsometric_waveGroup.isPurePoint_of_eigenDense (H.eigenDense_waveGroup_of_reducing B hB hspan)

end Feec.HilbertComplex

/-! ### Complex complexes viewed over `ℝ` -/

namespace Feec.HilbertComplex

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℂ (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, InnerProductSpace ℝ (W i)] [∀ i, IsScalarTower ℝ ℂ (W i)] {H : HilbertComplex ℂ c W}

/-- **An eigenbasis over `ℝ`**: finite-dimensional complex reducing subcomplexes spanning a dense
subspace give an eigenbasis for the wave group of the complex viewed over `ℝ`
(`HilbertComplex.restrictScalars`), provided the real inner products are the real parts of the
complex ones. Density is asked of the union of the total subspaces, which lies in their real and
in their complex span. -/
theorem eigenDense_restrictScalars_waveGroup_of_reducing
    (hre : ∀ i (x y : W i), ⟪x, y⟫_ℝ = RCLike.re ⟪x, y⟫_ℂ) {κ : Type*}
    (B : κ → ∀ i, Submodule ℂ (W i)) [∀ n i, FiniteDimensional ℂ (B n i)]
    (hB : ∀ n, H.ReducingSubcomplex (B n))
    (hspan : ∀ x : PiLp 2 W, x ∈ closure (⋃ n, (totalSub (B n) : Set (PiLp 2 W)))) :
    H.restrictScalars.waveGroup.EigenDense := by
  have hfin : ∀ n i, FiniteDimensional ℝ ((B n i).restrictScalars ℝ) := fun n i => by
    have : Module.Finite ℂ ((B n i).restrictScalars ℝ) := inferInstanceAs (Module.Finite ℂ (B n i))
    exact Module.Finite.trans ℂ ((B n i).restrictScalars ℝ)
  refine H.restrictScalars.eigenDense_waveGroup_of_reducing (fun n i => (B n i).restrictScalars ℝ)
    (fun n => (hB n).restrictScalars hre) ?_
  intro x
  refine closure_mono ?_ (hspan x)
  refine iUnion_subset fun n y hy => ?_
  exact (le_iSup (fun n => totalSub fun i => (B n i).restrictScalars ℝ) n) hy

end Feec.HilbertComplex

/-! ### Symbol complexes with the counting measure -/

namespace Feec.Fourier.SymbolComplex

variable {𝕜 : Type*} [RCLike 𝕜] {β : Type*} [MeasurableSpace β]
  {ι : Type*} {c : ComplexShape ι} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace 𝕜 (E i)]

section Fibre

/-- The fibre of a field at the frequency `a`. -/
def fibre (x : PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β)) (a : β) : PiLp 2 E :=
  WithLp.toLp 2 fun i => (x i : β → E i) a

@[simp] theorem fibre_apply (x : PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β)) (a : β)
    (i : ι) : fibre x a i = (x i : β → E i) a := rfl

theorem fibre_add (x y : PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β)) (a : β) :
    fibre (x + y) a = fibre x a + fibre y a := by
  ext i
  simp only [fibre_apply, PiLp.add_apply]
  exact Measure.ae_count_iff.1 (Lp.coeFn_add (x i) (y i)) a

theorem fibre_smul (r : 𝕜) (x : PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β)) (a : β) :
    fibre (r • x) a = r • fibre x a := by
  ext i
  simp only [fibre_apply, PiLp.smul_apply]
  exact Measure.ae_count_iff.1 (Lp.coeFn_smul r (x i)) a

/-- Two fields with the same fibres are equal. -/
theorem ext_fibre {x y : PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β)}
    (h : ∀ a, fibre x a = fibre y a) : x = y :=
  PiLp.ext fun i => Lp.ext_count fun a => congrArg (fun v : PiLp 2 E => v i) (h a)

end Fibre

variable [∀ i, CompleteSpace (E i)] [Fintype ι]
  (S : SymbolComplex 𝕜 (Measure.count : Measure β) c E)

/-- **The wave symbol** `W(a) = Σ m(a) - Σ m(a)*` at the frequency `a`: the fibre matrix of the
wave operator, `(W(a) v)_j = Σ_i m_{ij}(a) v_i - Σ_k m_{jk}(a)* v_k`. -/
def waveSym (a : β) : PiLp 2 E →L[𝕜] PiLp 2 E :=
  ((PiLp.continuousLinearEquiv 2 𝕜 E).symm : (∀ i, E i) →L[𝕜] PiLp 2 E).comp
    ((ContinuousLinearMap.pi fun j =>
        ∑ i, (S.m i j a).comp (ContinuousLinearMap.proj (R := 𝕜) (φ := E) i) -
          ∑ k, (ContinuousLinearMap.adjoint (S.m j k a)).comp
            (ContinuousLinearMap.proj (R := 𝕜) (φ := E) k)).comp
      (PiLp.continuousLinearEquiv 2 𝕜 E : PiLp 2 E →L[𝕜] ∀ i, E i))

theorem waveSym_apply (a : β) (v : PiLp 2 E) (j : ι) :
    S.waveSym a v j =
      ∑ i, S.m i j a (v i) - ∑ k, ContinuousLinearMap.adjoint (S.m j k a) (v k) := by
  simp [waveSym]

/-- **The wave operator acts fibrewise**: `(L x)(a) = W(a) x(a)`. -/
theorem wave_apply_count (x : S.toHilbertComplex.wave.domain) (a : β) :
    fibre (S.toHilbertComplex.wave x) a = S.waveSym a (fibre x a) := by
  ext j
  rw [fibre_apply, waveSym_apply, HilbertComplex.wave_apply]
  rw [Measure.ae_count_iff.1 (Lp.coeFn_sub _ _) a, Pi.sub_apply]
  congr 1
  · rw [Measure.ae_count_iff.1 (Lp.coeFn_finsetSum _ _) a, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => coeFn_d_count S ⟨_, x.2.1 i j⟩ a
  · rw [Measure.ae_count_iff.1 (Lp.coeFn_finsetSum _ _) a, Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => coeFn_adjoint_d_count S ⟨_, x.2.2 k j⟩ a

/-- **Fibrewise annihilated fields are harmonic**: if every symbol and every adjoint symbol kills
the fibres of `x`, then `x ∈ D(L)` and `L x = 0`. -/
theorem exists_wave_eq_zero_of_fibre {x : PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β)}
    (h : ∀ i j a, S.m i j a ((x i : β → E i) a) = 0 ∧
      ContinuousLinearMap.adjoint (S.m i j a) ((x j : β → E j) a) = 0) :
    ∃ hx : x ∈ S.toHilbertComplex.wave.domain, S.toHilbertComplex.wave ⟨x, hx⟩ = 0 := by
  have hx : x ∈ S.toHilbertComplex.wave.domain := by
    refine (HilbertComplex.mem_wave_domain _).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · change MemLp (fun a => S.m i j a ((x i : β → E i) a)) 2 Measure.count
      simp only [fun a => (h i j a).1]
      exact MemLp.zero
    · rw [adjoint_d]
      change MemLp (fun a => ContinuousLinearMap.adjoint (S.m i j a) ((x j : β → E j) a)) 2
        Measure.count
      simp only [fun a => (h i j a).2]
      exact MemLp.zero
  refine ⟨hx, ext_fibre fun a => ?_⟩
  rw [wave_apply_count S ⟨x, hx⟩ a]
  ext j
  rw [waveSym_apply]
  simp only [fibre_apply, (h _ _ a).1, (h _ _ a).2, Finset.sum_const_zero, sub_zero]
  exact (Measure.ae_count_iff.1 (Lp.coeFn_zero (E j) 2 _) a).symm

/-- **Eigenvectors of `L²` are fibrewise eigenvectors of `W(a)²`.** -/
theorem waveSym_sq_of_isEigenSq [∀ i, NormedSpace ℝ (E i)] [∀ i, IsScalarTower ℝ 𝕜 (E i)]
    {ω : ℝ} {x : PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β)}
    (hx : S.toHilbertComplex.wave.IsEigenSq ω x) (a : β) :
    S.waveSym a (S.waveSym a (fibre x a)) = -(ω ^ 2) • fibre x a := by
  obtain ⟨h, h', e⟩ := hx
  rw [← wave_apply_count S ⟨x, h⟩, ← wave_apply_count S ⟨_, h'⟩, e]
  ext j
  simp only [fibre_apply, PiLp.smul_apply]
  exact Measure.ae_count_iff.1 (Lp.coeFn_smul (𝕜 := ℝ) (-(ω ^ 2)) (x j)) a

/-! #### Band-limited fields: the eigenbasis -/

section Bands

variable [MeasurableSingletonClass β]

/-- Band-limited fields on finite sets of frequencies span a dense subspace (they contain the
Fourier truncations along an exhausting sequence). -/
theorem mem_closure_iUnion_band {A : ℕ → Set β} (hfin : ∀ N, (A N).Finite) (hmono : Monotone A)
    (hcov : ∀ a, ∃ N, a ∈ A N) [∀ N i, (S.band (A N) i).HasOrthogonalProjection]
    (x : PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β)) :
    x ∈ closure (⋃ N, (HilbertComplex.totalSub (S.band (A N)) :
      Set (PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β)))) :=
  mem_closure_of_tendsto (tendsto_totalProj_band S (fun N => (hfin N).measurableSet) hmono hcov x)
    (Eventually.of_forall fun N => mem_iUnion.2 ⟨N, Submodule.starProjection_apply_mem _ x⟩)

variable [∀ i, FiniteDimensional 𝕜 (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, IsScalarTower ℝ 𝕜 (E i)]

/-- **Every symbol complex on a countable set of frequencies with finite-dimensional fibres has an
eigenbasis for its wave operator**, given an exhausting increasing sequence of finite sets of
frequencies (e.g. the cubes `|k|_∞ ≤ N` in `ℤᵈ`): the band-limited fields are finite-dimensional
reducing subcomplexes. -/
theorem eigenDense_waveGroup {A : ℕ → Set β} (hfin : ∀ N, (A N).Finite) (hmono : Monotone A)
    (hcov : ∀ a, ∃ N, a ∈ A N) : S.toHilbertComplex.waveGroup.EigenDense := by
  have := fun N i => hasOrthogonalProjection_band S (hfin N).measurableSet i
  have := fun N i => finiteDimensional_band S (hfin N) i
  refine S.toHilbertComplex.eigenDense_waveGroup_of_reducing (fun N => S.band (A N))
    (fun N => reducingSubcomplex_band S (hfin N).measurableSet) ?_
  intro x
  refine closure_mono ?_ (mem_closure_iUnion_band S hfin hmono hcov x)
  exact iUnion_subset fun N y hy =>
    (le_iSup (fun N => HilbertComplex.totalSub (S.band (A N))) N) hy

/-- **Pure point spectrum of Fourier models.** -/
theorem isPurePoint_waveGroup {A : ℕ → Set β} (hfin : ∀ N, (A N).Finite) (hmono : Monotone A)
    (hcov : ∀ a, ∃ N, a ∈ A N) : S.toHilbertComplex.waveGroup.IsPurePoint :=
  S.toHilbertComplex.isIsometric_waveGroup.isPurePoint_of_eigenDense
    (S.eigenDense_waveGroup hfin hmono hcov)

/-- **In a Fourier model, forward invariance is invariance**: if the forward orbit (`t ≥ 0`) of `x`
stays in a closed subspace `K`, then so does its whole orbit. -/
theorem mem_invariantCore_of_forward_invariant {A : ℕ → Set β} (hfin : ∀ N, (A N).Finite)
    (hmono : Monotone A) (hcov : ∀ a, ∃ N, a ∈ A N)
    {K : Submodule 𝕜 (PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β))}
    (hK : IsClosed (K : Set (PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β))))
    {x : PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β)}
    (hx : ∀ t, 0 ≤ t → S.toHilbertComplex.waveGroup.S t x ∈ K) :
    x ∈ S.toHilbertComplex.waveGroup.invariantCore K :=
  S.toHilbertComplex.isIsometric_waveGroup.mem_invariantCore_of_forward_invariant
    (S.isPurePoint_waveGroup hfin hmono hcov) hK hx

end Bands

end Feec.Fourier.SymbolComplex

/-! ### Constant-coefficient complexes on the torus -/

namespace Feec.Fourier.Torus

variable {d : Type*} [Fintype d] {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]
  {c : ComplexShape ι} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace 𝕜 (E i)] [∀ i, FiniteDimensional 𝕜 (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, NormedSpace ℝ (E i)] [∀ i, IsScalarTower ℝ 𝕜 (E i)]
  (S : FibreComplex 𝕜 (EuclideanSpace ℝ d) c E)

/-- **Every constant-coefficient complex on `𝕋ᵈ` with finite-dimensional fibres has an eigenbasis
for its wave operator** (the Fourier modes; the cubes `|k|_∞ ≤ N` exhaust `ℤᵈ`). -/
theorem eigenDense_waveGroup : (complex S).waveGroup.EigenDense :=
  (symbolComplex S).eigenDense_waveGroup finite_bandN bandN_mono exists_mem_bandN

/-- **Pure point spectrum on the torus.** -/
theorem isPurePoint_waveGroup : (complex S).waveGroup.IsPurePoint :=
  (complex S).isIsometric_waveGroup.isPurePoint_of_eigenDense (eigenDense_waveGroup S)

/-- **On the torus, forward invariance of a closed subspace is invariance for all times.** -/
theorem mem_invariantCore_of_forward_invariant
    {K : Submodule 𝕜 (PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure (d → ℤ)))}
    (hK : IsClosed (K : Set (PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure (d → ℤ)))))
    {x : PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure (d → ℤ))}
    (hx : ∀ t, 0 ≤ t → (complex S).waveGroup.S t x ∈ K) :
    x ∈ (complex S).waveGroup.invariantCore K :=
  (complex S).isIsometric_waveGroup.mem_invariantCore_of_forward_invariant
    (isPurePoint_waveGroup S) hK hx

end Feec.Fourier.Torus
