module

public import Feec.HilbertComplex.Transport
public import Feec.HilbertComplex.Equivariant
public import Feec.Semigroup.Spectral
public import Feec.Semigroup.Invariance

/-!
# Hilbert-complex facts used by the mirror cube models

Small general statements about the constructions behind the mirror cube complexes
(`Feec.Models.Cube.Mirror`, `MirrorSym`, `MirrorBGG`): projections onto action-invariant
subspaces preserve the fixed vectors, the inverse of a transport is a scaled embedding, the wave
domains of compressions and of transports along uniformly scaled isometries, the components of
the wave operator of a window complex `W₀ → W₁ → W₂`, and the fact that vectors not killed by the
wave operator are not stationary for the wave group.

## Main results

* `Feec.HilbertComplex.Action.starProjection_mem_fixed`.
* `Feec.HilbertComplex.ScaledEmbedding.ofTransportSymm`: `e⁻¹` embeds `H.transport e κ` in `H`.
* `Feec.HilbertComplex.mem_wave_domain_compress_iff`, `mem_wave_domain_transport_iff`.
* `Feec.HilbertComplex.wave_apply_fin3_zero`, `_one`, `_two`.
* `Feec.HilbertComplex.not_mem_stationary_of_wave_ne_zero`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate
open LinearPMap Set

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W}

/-! ### Invariant subspaces and fixed vectors -/

/-- If a closed subspace `K` is invariant under a unitary action, its orthogonal projection
maps fixed vectors to fixed vectors. -/
theorem Action.starProjection_mem_fixed {Γ : Type*} [Group Γ] (A : H.Action Γ) {i : ι}
    {K : Submodule 𝕜 (W i)} [K.HasOrthogonalProjection] (hA : ∀ g, ∀ x ∈ K, A.act g i x ∈ K)
    {x : W i} (hx : x ∈ A.fixed i) : K.starProjection x ∈ A.fixed i := fun g => by
  have e : K.starProjection (A.act g i x) = A.act g i (K.starProjection x) := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (hA g _ (K.starProjection_apply_mem x)) fun k hk => ?_
    rw [← A.act_act_inv g i k, ← _root_.map_sub, LinearIsometryEquiv.inner_map_map]
    exact K.starProjection_inner_eq_zero _ _ (hA g⁻¹ _ hk)
  rw [← e, hx g]

/-! ### Restricting an isomorphism to subspaces -/

/-- An isomorphism mapping `S` onto `T` restricts to an isomorphism `S ≃ T`. -/
def _root_.ContinuousLinearEquiv.restrictSub {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (e : X ≃L[𝕜] Y)
    (S : Submodule 𝕜 X) (T : Submodule 𝕜 Y) (h₁ : ∀ x ∈ S, e x ∈ T)
    (h₂ : ∀ y ∈ T, e.symm y ∈ S) : S ≃L[𝕜] T where
  toFun x := ⟨e x.1, h₁ x.1 x.2⟩
  invFun y := ⟨e.symm y.1, h₂ y.1 y.2⟩
  map_add' x y := Subtype.ext (_root_.map_add e x.1 y.1)
  map_smul' a x := Subtype.ext (_root_.map_smul e a x.1)
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

/-! ### The inverse of a transport -/

variable {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)]
  [∀ i, CompleteSpace (W' i)]

/-- **The inverse of a transport is a scaled embedding**: `e⁻¹` maps `H.transport e κ` into `H`,
with scales `s⁻¹` and chain-rule factors `κ⁻¹`. -/
def ScaledEmbedding.ofTransportSymm (e : ∀ i, W i ≃L[𝕜] W' i) (κ : ι → ι → 𝕜)
    (hκ : ∀ i j, κ i j ≠ 0) (s : ι → ℝ) (hs : ∀ i, 0 < s i)
    (he : ∀ i (x y : W i), ⟪e i x, e i y⟫_𝕜 = (s i : 𝕜) * ⟪x, y⟫_𝕜) :
    ScaledEmbedding (H.transport e κ hκ) H where
  J i := ((e i).symm : W' i →L[𝕜] W i)
  scale i := (s i)⁻¹
  scale_pos i := inv_pos.2 (hs i)
  inner_J i x y := by
    have h := he i ((e i).symm x) ((e i).symm y)
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply] at h
    have hs' : (s i : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (hs i).ne'
    change ⟪(e i).symm x, (e i).symm y⟫_𝕜 = (((s i)⁻¹ : ℝ) : 𝕜) * ⟪x, y⟫_𝕜
    rw [h, RCLike.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hs', one_mul]
  dScale i j := (κ i j)⁻¹
  dScale_ne_zero i j := inv_ne_zero (hκ i j)
  mapsTo i j x := x.2
  comm i j x := by
    have hx : (e i).symm (x : W' i) ∈ (H.d i j).domain := x.2
    have h : ((H.transport e κ hκ).d i j x : W' j) = κ i j • e j (H.d i j ⟨(e i).symm x, hx⟩) :=
      rfl
    change H.d i j ⟨(e i).symm x, hx⟩ = (κ i j)⁻¹ • (e j).symm ((H.transport e κ hκ).d i j x)
    rw [h, _root_.map_smul, ContinuousLinearEquiv.symm_apply_apply, inv_smul_smul₀ (hκ i j)]
  mem_domain_of_map i j x h := h

/-- A scaled embedding maps the kernel of `d` into the kernel of `d'`. -/
theorem ScaledEmbedding.apply_eq_zero {H' : HilbertComplex 𝕜 c W'} (E : ScaledEmbedding H H')
    {i j : ι} (x : (H.d i j).domain) (h : H.d i j x = 0) :
    H'.d i j ⟨E.J i x, E.mapsTo i j x⟩ = 0 := by
  rw [E.comm, h, _root_.map_zero, smul_zero]

/-! ### Wave domains of compressions and transports -/

variable [Fintype ι]

/-- **The wave domain of a compression** is the preimage of the wave domain. -/
theorem mem_wave_domain_compress_iff {J : ∀ i, W' i →L[𝕜] W i} {s : ℝ} (hs : 0 < s)
    (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    [∀ i, (LinearMap.range (J i : W' i →ₗ[𝕜] W i)).HasOrthogonalProjection]
    (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : W' i →ₗ[𝕜] W i))
    {y : PiLp 2 W'} : y ∈ (H.compress J hs hJ hR).wave.domain ↔ totalJ J y ∈ H.wave.domain := by
  rw [mem_wave_domain, mem_wave_domain]
  refine and_congr (forall_congr' fun i => forall_congr' fun j => ?_)
    (forall_congr' fun i => forall_congr' fun j => ?_)
  · exact mem_compress_domain_iff hs hJ hR
  · exact mem_adjoint_compress_iff hs hJ hR

/-- **The wave domain of a transport** along uniformly scaled isometries is the image of the
wave domain. -/
theorem mem_wave_domain_transport_iff {e : ∀ i, W i ≃L[𝕜] W' i} {κ : ι → ι → 𝕜}
    (hκ : ∀ i j, κ i j ≠ 0) {s : ℝ} (hs : 0 < s)
    (he : ∀ i (x y : W i), ⟪e i x, e i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜) {y : PiLp 2 W'} :
    y ∈ (H.transport e κ hκ).wave.domain ↔
      totalMap (fun i => (e i).symm) y ∈ H.wave.domain := by
  rw [mem_wave_domain, mem_wave_domain]
  refine and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun j => ?_)
  change y j ∈ (transportD H e κ i j)†.domain ↔ _
  rw [adjoint_transportD hs he (hκ i j)]
  exact Iff.rfl

/-- An intertwining map sends vectors with `B (J x) ≠ 0` to vectors with `A x ≠ 0`. -/
theorem _root_.LinearPMap.Intertwines.apply_ne_zero {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {T : E →L[𝕜] F}
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} (h : Intertwines T A B) (x : A.domain)
    (hx : B ⟨T x, h.mapsTo x⟩ ≠ 0) : A x ≠ 0 := fun h0 => hx (by rw [h.comm, h0, _root_.map_zero])

/-- **The wave domain of a compressed complex** (a reducing subcomplex as a complex) is the
preimage of the wave domain. -/
theorem ReducingSubcomplex.mem_wave_domain_iff {S : ∀ i, Submodule 𝕜 (W i)}
    [∀ i, CompleteSpace (S i)] [∀ i, (S i).HasOrthogonalProjection] (h : H.ReducingSubcomplex S)
    {y : PiLp 2 fun i => S i} :
    y ∈ h.toHilbertComplex.wave.domain ↔ ReducingSubcomplex.totalIncl S y ∈ H.wave.domain := by
  rw [mem_wave_domain, mem_wave_domain]
  refine and_congr (forall_congr' fun i => forall_congr' fun j => ?_)
    (forall_congr' fun i => forall_congr' fun j => ?_)
  · exact (h.reduces i j).mem_part_domain
  · change y j ∈ (h.toHilbertComplex.dual.d j i).domain ↔ _
    rw [h.dual_toHilbertComplex_d]
    exact (h.dual.reduces j i).mem_part_domain

/-! ### Window complexes `W₀ → W₁ → W₂` -/

section Fin3

variable {W : Fin 3 → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
  [∀ i, CompleteSpace (W i)] (H : HilbertComplex 𝕜 ComplexShape.fin3 W)

/-- `(L x)₀ = -d₀† x₁`. -/
theorem wave_apply_fin3_zero (x : H.wave.domain) :
    (H.wave x) 0 = -(H.d 0 1)† ⟨(x : PiLp 2 W) 1, x.2.2 1 0⟩ := by
  rw [wave_apply, Fin.sum_univ_three, Fin.sum_univ_three,
    H.apply_eq_zero_of_not_rel (i := 0) (j := 0) (by simp),
    H.apply_eq_zero_of_not_rel (i := 1) (j := 0) (by simp),
    H.apply_eq_zero_of_not_rel (i := 2) (j := 0) (by simp),
    adjoint_apply_eq_zero_of_eq_zero (H.shape 0 0 (by simp)),
    adjoint_apply_eq_zero_of_eq_zero (H.shape 0 2 (by simp))]
  simp

/-- `(L x)₁ = d₀ x₀ - d₁† x₂`. -/
theorem wave_apply_fin3_one (x : H.wave.domain) :
    (H.wave x) 1 = H.d 0 1 ⟨(x : PiLp 2 W) 0, x.2.1 0 1⟩ -
      (H.d 1 2)† ⟨(x : PiLp 2 W) 2, x.2.2 2 1⟩ := by
  rw [wave_apply, Fin.sum_univ_three, Fin.sum_univ_three,
    H.apply_eq_zero_of_not_rel (i := 1) (j := 1) (by simp),
    H.apply_eq_zero_of_not_rel (i := 2) (j := 1) (by simp),
    adjoint_apply_eq_zero_of_eq_zero (H.shape 1 0 (by simp)),
    adjoint_apply_eq_zero_of_eq_zero (H.shape 1 1 (by simp))]
  simp

/-- `(L x)₂ = d₁ x₁`. -/
theorem wave_apply_fin3_two (x : H.wave.domain) :
    (H.wave x) 2 = H.d 1 2 ⟨(x : PiLp 2 W) 1, x.2.1 1 2⟩ := by
  rw [wave_apply, Fin.sum_univ_three, Fin.sum_univ_three,
    H.apply_eq_zero_of_not_rel (i := 0) (j := 2) (by simp),
    H.apply_eq_zero_of_not_rel (i := 2) (j := 2) (by simp),
    adjoint_apply_eq_zero_of_eq_zero (H.shape 2 0 (by simp)),
    adjoint_apply_eq_zero_of_eq_zero (H.shape 2 1 (by simp)),
    adjoint_apply_eq_zero_of_eq_zero (H.shape 2 2 (by simp))]
  simp

/-- **Membership in the wave domain of a window complex**: `x₀ ∈ D(d₀)`, `x₁ ∈ D(d₁) ∩ D(d₀†)`,
`x₂ ∈ D(d₁†)`. -/
theorem mem_wave_domain_fin3 {x : PiLp 2 W} (h0 : x 0 ∈ (H.d 0 1).domain)
    (h1 : x 1 ∈ (H.d 1 2).domain) (h1' : x 1 ∈ ((H.d 0 1)†).domain)
    (h2 : x 2 ∈ ((H.d 1 2)†).domain) : x ∈ H.wave.domain := by
  have htop : ∀ {i j : Fin 3}, ¬ ComplexShape.fin3.Rel i j → ∀ v, v ∈ (H.d i j).domain :=
    fun h v => H.domain_eq_top_of_not_rel h ▸ Submodule.mem_top
  have htop' : ∀ {i j : Fin 3}, ¬ ComplexShape.fin3.Rel i j → ∀ v, v ∈ ((H.d i j)†).domain :=
    fun h v => by rw [H.shape _ _ h, adjoint_zero]; exact Submodule.mem_top
  refine (mem_wave_domain _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact htop (by simp) _
    · exact h0
    · exact htop (by simp) _
    · exact htop (by simp) _
    · exact htop (by simp) _
    · exact h1
    · exact htop (by simp) _
    · exact htop (by simp) _
    · exact htop (by simp) _
  · fin_cases i <;> fin_cases j
    · exact htop' (by simp) _
    · exact h1'
    · exact htop' (by simp) _
    · exact htop' (by simp) _
    · exact htop' (by simp) _
    · exact h2
    · exact htop' (by simp) _
    · exact htop' (by simp) _
    · exact htop' (by simp) _

end Fin3

/-! ### Non-stationary vectors -/

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **A vector of `D(L)` with `L x ≠ 0` is not stationary** for the wave group. -/
theorem not_mem_stationary_of_wave_ne_zero (x : H.wave.domain) (hx : H.wave x ≠ 0) :
    (x : PiLp 2 W) ∉ H.waveGroup.stationary := by
  intro hs
  apply hx
  have hx' : (x : PiLp 2 W) ∈ H.waveGroup.generator.domain := by
    rw [generator_waveGroup]; exact x.2
  have h0 : H.waveGroup.generator ⟨x, hx'⟩ = 0 := by
    refine H.waveGroup.generator_apply_eq ?_
    have e : (fun t => H.waveGroup.S t (x : PiLp 2 W)) = fun _ => (x : PiLp 2 W) :=
      funext (C0Group.mem_stationary.1 hs)
    rw [e]
    exact hasDerivAt_const _ _
  rw [← h0]
  exact apply_eq_of_eq (generator_waveGroup (H := H)).symm x ⟨x, hx'⟩ rfl

/-- **Non-stationary vectors of a reducing subcomplex**: if the inclusion of `y` lies in `D(L)`
and is not killed by `L`, then `y` is not stationary for the compressed wave group. -/
theorem ReducingSubcomplex.not_mem_stationary {S : ∀ i, Submodule 𝕜 (W i)}
    [∀ i, CompleteSpace (S i)] [∀ i, (S i).HasOrthogonalProjection] (h : H.ReducingSubcomplex S)
    {y : PiLp 2 fun i => S i} (hy : ReducingSubcomplex.totalIncl S y ∈ H.wave.domain)
    (hne : H.wave ⟨_, hy⟩ ≠ 0) :
    y ∈ h.toHilbertComplex.wave.domain ∧ y ∉ h.toHilbertComplex.waveGroup.stationary := by
  have hy' := h.mem_wave_domain_iff.2 hy
  exact ⟨hy', not_mem_stationary_of_wave_ne_zero ⟨y, hy'⟩
    (h.wave_toHilbertComplex.apply_ne_zero ⟨y, hy'⟩ hne)⟩

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- **Non-stationary vectors of a compression**: if `J y ∈ D(L)` and `L (J y) ≠ 0`, then `y` lies
in the wave domain of the compression and is not stationary. -/
theorem not_mem_stationary_compress {J : ∀ i, W' i →L[𝕜] W i} {s : ℝ} (hs : 0 < s)
    (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    [∀ i, (LinearMap.range (J i : W' i →ₗ[𝕜] W i)).HasOrthogonalProjection]
    (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : W' i →ₗ[𝕜] W i))
    [∀ i, NormedSpace ℝ (W' i)] [∀ i, IsScalarTower ℝ 𝕜 (W' i)]
    {y : PiLp 2 W'} (hy : totalJ J y ∈ H.wave.domain) (hne : H.wave ⟨_, hy⟩ ≠ 0) :
    y ∈ (H.compress J hs hJ hR).wave.domain ∧
      y ∉ (H.compress J hs hJ hR).waveGroup.stationary := by
  have hy' := (mem_wave_domain_compress_iff hs hJ hR).2 hy
  exact ⟨hy', not_mem_stationary_of_wave_ne_zero ⟨y, hy'⟩
    ((wave_compress hs hJ hR).apply_ne_zero ⟨y, hy'⟩ hne)⟩

end Feec.HilbertComplex
