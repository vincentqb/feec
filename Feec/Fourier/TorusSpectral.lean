module

public import Feec.Fourier.SpectralGalerkin
public import Feec.Semigroup.Spectral
public import Feec.HilbertComplex.RestrictScalars

/-!
# Pure point spectrum of Fourier models

In a Hilbert complex exhausted by finite-dimensional reducing subcomplexes, the eigenvectors of
`L²`, `L` the wave operator, span a dense subspace; so do those of every symbol complex on a
countable set of frequencies with the counting measure and finite-dimensional fibres, in
particular of every constant-coefficient complex on `𝕋ᵈ`, whose wave group then has pure point
spectrum.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace Topology
open MeasureTheory LinearPMap Set Filter

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

omit [∀ i, CompleteSpace (W i)] in
theorem finiteDimensional_totalSub (S : ∀ i, Submodule 𝕜 (W i))
    [∀ i, FiniteDimensional 𝕜 (S i)] : FiniteDimensional 𝕜 (totalSub S) := by
  let Φ : totalSub S →ₗ[𝕜] ∀ i, S i :=
    { toFun := fun x i => ⟨(x : PiLp 2 W) i, x.2 i⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ fun x y h => Subtype.ext (PiLp.ext fun i => ?_)
  exact congrArg Subtype.val (congrFun h i)

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] (H : HilbertComplex 𝕜 c W)

/-- If finite-dimensional reducing subcomplexes span a dense subspace, so do the eigenvectors of
`L²`. -/
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

theorem waveGroup_S_eq_of_wave_eq_smul {x : PiLp 2 W} (hx : x ∈ H.wave.domain) {c : 𝕜}
    (e : H.wave ⟨x, hx⟩ = c • x) (t : ℝ) :
    H.waveGroup.S t x = NormedSpace.exp (t • c) • x := by
  have key : ∀ A : PiLp 2 W →ₗ.[𝕜] PiLp 2 W, H.waveGroup.toC0Semigroup.generator = A →
      ∀ hA : x ∈ A.domain, A ⟨x, hA⟩ = c • x →
        H.waveGroup.S t x = NormedSpace.exp (t • c) • x := by
    rintro _ rfl hA e
    exact H.isIsometric_waveGroup.S_eq_of_generator_eq_smul hA e t
  exact key _ H.generator_waveGroup hx e

end Feec.HilbertComplex

namespace Feec.HilbertComplex

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℂ (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, InnerProductSpace ℝ (W i)] [∀ i, IsScalarTower ℝ ℂ (W i)] {H : HilbertComplex ℂ c W}

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

theorem ext_fibre {x y : PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β)}
    (h : ∀ a, fibre x a = fibre y a) : x = y :=
  PiLp.ext fun i => Lp.ext_count fun a => congrArg (fun v : PiLp 2 E => v i) (h a)

theorem fibre_smul (r : 𝕜) (x : PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β)) (a : β) :
    fibre (r • x) a = r • fibre x a := by
  ext i
  exact Measure.ae_count_iff.1 (Lp.coeFn_smul r (x i)) a

variable [MeasurableSingletonClass β] [Countable β] [DecidableEq β]

omit [∀ i, InnerProductSpace 𝕜 (E i)] in
theorem memLp_single {i : ι} (k : β) (v : E i) :
    MemLp (Pi.single k v : β → E i) 2 (Measure.count : Measure β) :=
  (memLp_count_iff two_ne_zero).2 (memℓp_gen (summable_of_ne_finset_zero (s := {k}) fun a ha => by
    simp [Finset.mem_singleton.not.1 ha]))

/-- The single-mode field `δ_k v`: its only nonzero fibre is `v`, at the frequency `k`. -/
def modeField (k : β) (v : PiLp 2 E) : PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β) :=
  WithLp.toLp 2 fun i => (memLp_single k (v i)).toLp _

theorem coe_modeField (k : β) (v : PiLp 2 E) (i : ι) :
    ((modeField k v i : Lp (E i) 2 (Measure.count : Measure β)) : β → E i) =
      Pi.single k (v i) :=
  (memLp_single k (v i)).coeFn_toLp_count

theorem fibre_modeField (k : β) (v : PiLp 2 E) (a : β) :
    fibre (modeField k v) a = if a = k then v else 0 := by
  ext i
  rw [fibre_apply, coe_modeField, Pi.single_apply]
  split_ifs <;> rfl

theorem modeField_smul (k : β) (r : 𝕜) (v : PiLp 2 E) :
    modeField k (r • v) = r • modeField k v :=
  ext_fibre fun a => by
    rw [fibre_smul, fibre_modeField, fibre_modeField]
    split_ifs <;> simp

end Fibre

variable [∀ i, CompleteSpace (E i)] [Fintype ι]
  (S : SymbolComplex 𝕜 (Measure.count : Measure β) c E)

/-- The wave symbol `W(a)`, the fibre matrix of the wave operator at the frequency `a`. -/
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

section Mode

variable [MeasurableSingletonClass β] [Countable β] [DecidableEq β]

theorem modeField_mem_wave_domain (k : β) (v : PiLp 2 E) :
    modeField k v ∈ S.toHilbertComplex.wave.domain := by
  have hm : ∀ {i j : ι} (m : β → E i →L[𝕜] E j),
      MemLp (fun a => m a ((modeField k v i : Lp (E i) 2 (Measure.count : Measure β)) a)) 2
        Measure.count := fun {i j} m => by
    convert memLp_single k (m k (v i)) using 1
    funext a
    rw [coe_modeField, Pi.single_apply, Pi.single_apply]
    split_ifs with h
    · rw [h]
    · exact map_zero _
  refine (HilbertComplex.mem_wave_domain _).2 ⟨fun i j => hm (S.m i j), fun i j => ?_⟩
  rw [adjoint_d]
  exact hm fun a => ContinuousLinearMap.adjoint (S.m i j a)

theorem wave_modeField (k : β) (v : PiLp 2 E) :
    S.toHilbertComplex.wave ⟨modeField k v, S.modeField_mem_wave_domain k v⟩ =
      modeField k (S.waveSym k v) :=
  ext_fibre fun a => by
    rw [wave_apply_count, fibre_modeField, fibre_modeField]
    split_ifs with h
    · rw [h]
    · exact map_zero _

theorem waveGroup_modeField [∀ i, NormedSpace ℝ (E i)] [∀ i, IsScalarTower ℝ 𝕜 (E i)] (k : β)
    {v : PiLp 2 E} {c : 𝕜} (h : S.waveSym k v = c • v) (t : ℝ) :
    S.toHilbertComplex.waveGroup.S t (modeField k v) = NormedSpace.exp (t • c) • modeField k v :=
  S.toHilbertComplex.waveGroup_S_eq_of_wave_eq_smul (S.modeField_mem_wave_domain k v)
    (by rw [wave_modeField, h, modeField_smul]) t

end Mode

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

theorem waveSym_sq_of_isEigenSq [∀ i, NormedSpace ℝ (E i)] [∀ i, IsScalarTower ℝ 𝕜 (E i)]
    {ω : ℝ} {x : PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β)}
    (hx : S.toHilbertComplex.wave.IsEigenSq ω x) (a : β) :
    S.waveSym a (S.waveSym a (fibre x a)) = -(ω ^ 2) • fibre x a := by
  obtain ⟨h, h', e⟩ := hx
  rw [← wave_apply_count S ⟨x, h⟩, ← wave_apply_count S ⟨_, h'⟩, e]
  ext j
  simp only [fibre_apply, PiLp.smul_apply]
  exact Measure.ae_count_iff.1 (Lp.coeFn_smul (𝕜 := ℝ) (-(ω ^ 2)) (x j)) a

section Bands

variable [MeasurableSingletonClass β]

theorem mem_closure_iUnion_band {A : ℕ → Set β} (hfin : ∀ N, (A N).Finite) (hmono : Monotone A)
    (hcov : ∀ a, ∃ N, a ∈ A N) [∀ N i, (S.band (A N) i).HasOrthogonalProjection]
    (x : PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β)) :
    x ∈ closure (⋃ N, (HilbertComplex.totalSub (S.band (A N)) :
      Set (PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure β)))) :=
  mem_closure_of_tendsto (tendsto_totalProj_band S (fun N => (hfin N).measurableSet) hmono hcov x)
    (Eventually.of_forall fun N => mem_iUnion.2 ⟨N, Submodule.starProjection_apply_mem _ x⟩)

variable [∀ i, FiniteDimensional 𝕜 (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, IsScalarTower ℝ 𝕜 (E i)]

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

theorem isPurePoint_waveGroup {A : ℕ → Set β} (hfin : ∀ N, (A N).Finite) (hmono : Monotone A)
    (hcov : ∀ a, ∃ N, a ∈ A N) : S.toHilbertComplex.waveGroup.IsPurePoint :=
  S.toHilbertComplex.isIsometric_waveGroup.isPurePoint_of_eigenDense
    (S.eigenDense_waveGroup hfin hmono hcov)

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

namespace Feec.Fourier.Torus

variable {d : Type*} [Fintype d] {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]
  {c : ComplexShape ι} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace 𝕜 (E i)] [∀ i, FiniteDimensional 𝕜 (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, NormedSpace ℝ (E i)] [∀ i, IsScalarTower ℝ 𝕜 (E i)]
  (S : FibreComplex 𝕜 (EuclideanSpace ℝ d) c E)

/-- For every constant-coefficient complex on `𝕋ᵈ` with finite-dimensional fibres, the
eigenvectors of `L²`, `L` the wave operator, span a dense subspace. -/
theorem eigenDense_waveGroup : (complex S).waveGroup.EigenDense :=
  (symbolComplex S).eigenDense_waveGroup finite_bandN bandN_mono exists_mem_bandN

theorem isPurePoint_waveGroup : (complex S).waveGroup.IsPurePoint :=
  (complex S).isIsometric_waveGroup.isPurePoint_of_eigenDense (eigenDense_waveGroup S)

/-- On the torus, forward invariance of a closed subspace is invariance for all times. -/
theorem mem_invariantCore_of_forward_invariant
    {K : Submodule 𝕜 (PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure (d → ℤ)))}
    (hK : IsClosed (K : Set (PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure (d → ℤ)))))
    {x : PiLp 2 fun i => Lp (E i) 2 (Measure.count : Measure (d → ℤ))}
    (hx : ∀ t, 0 ≤ t → (complex S).waveGroup.S t x ∈ K) :
    x ∈ (complex S).waveGroup.invariantCore K :=
  (complex S).isIsometric_waveGroup.mem_invariantCore_of_forward_invariant
    (isPurePoint_waveGroup S) hK hx

end Feec.Fourier.Torus
