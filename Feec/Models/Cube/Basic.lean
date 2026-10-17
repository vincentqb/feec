module

public import Feec.Fourier.TorusWeak
public import Feec.HilbertComplex.Equivariant
public import Feec.Semigroup.Spectral

/-!
# Shared infrastructure of the cube models

The cube `Q = (0, ½)³` is a fundamental domain of the reflection group `(ℤ/2)³` of the torus
`𝕋³ = ℝ³/ℤ³`, and the cube models (`Feec.Models.Cube.Parity`, `Feec.Models.Cube.Static` for the
thesis' row-wise boundary conditions; `Feec.Models.Cube.Mirror`, `MirrorSym`, `MirrorBGG` for the
mirror conditions) are compressions of torus complexes. This file holds what both families share
and does not depend on either.

## Main definitions and results

* `halfArc`, `boxSet`: the box `(0, ½)ᵈ` in `𝕋ᵈ` (any dimension); `ZeroOnBox f`: the function
  with Fourier coefficients `f` vanishes a.e. on the box, characterized by orthogonality to the
  functions supported off the box (`zeroOnBox_iff`), a closed subspace (`boxZero`);
  **`eq_zero_of_zeroOnBox_of_finite`**: a trigonometric polynomial vanishing a.e. on the box is
  zero (`Feec.Fourier.TorusWeak.eq_zero_of_ae_eq_zero_of_finite`).
* `sub3`, `reducingSubcomplex_sub3`: families of three subspaces of a short complex, and the
  reducing subcomplex `({0}, K₁, K₂)` from two reducing pairs.
* `compSub`, `mem_invariantCore_compSub_iff`, `mem_stationary_compSub_iff`,
  `forward_compSub_iff`, `mem_wave_domain_compress_iff`: invariant cores, stationary vectors and
  wave domains of a compression are those of the big complex.
* **`reducingSubcomplex_compSub_fixed`**: a reducing subcomplex invariant under a finite unitary
  action descends to the fixed (method-of-images) complex.
* `comm_of_eq_zero`, `generator_eq_zero_of_mem_stationary`.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17 on the cube)
* [Brezis2011], §9.2 (extension by reflection)
-/

open scoped InnerProductSpace ENNReal
open Set LinearPMap MeasureTheory Filter

@[expose] public noncomputable section

universe u

namespace Feec.Models.Cube

open Feec.ShortHilbertComplex

/- Over `ℝ`, the real structure of `W3` is the one of its inner product space; the instance
`instNormedSpaceRealW3` (meant for `𝕜 = ℂ`) would be a second, non-reducibly-equal one. -/
attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

/-! ### The box `(0, ½)ᵈ` in the torus -/

section Box

open UnitAddTorus Feec.Fourier.TorusWeak

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Fourier.TorusWeak`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {d : Type*} [Fintype d]

/-- The open arc `(0, ½)` of `ℝ/ℤ`. -/
def halfArc : Set UnitAddCircle := ((↑) : ℝ → UnitAddCircle) '' Ioo 0 (1 / 2)

variable (d) in
/-- The open box `(0, ½)ᵈ` in `𝕋ᵈ`. -/
def boxSet : Set (UnitAddTorus d) := univ.pi fun _ => halfArc

omit [Fintype d] in
theorem isOpen_boxSet [Finite d] : IsOpen (boxSet d) :=
  isOpen_set_pi finite_univ fun _ _ => QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

theorem measurableSet_boxSet : MeasurableSet (boxSet d) := isOpen_boxSet.measurableSet

omit [Fintype d] in
/-- Points of `(0, ½)ᵈ ⊂ ℝᵈ` project into the box. -/
theorem proj_mem_boxSet {y : d → ℝ} (hy : ∀ i, y i ∈ Ioo (0 : ℝ) (1 / 2)) : proj y ∈ boxSet d :=
  fun i _ => ⟨y i, hy i, rfl⟩

omit [Fintype d] in
theorem boxSet_nonempty : (boxSet d).Nonempty :=
  ⟨proj fun _ => 1 / 4, proj_mem_boxSet fun _ => ⟨by norm_num, by norm_num⟩⟩

/-- `ZeroOnBox f`: the `L²(𝕋ᵈ)` function with Fourier coefficients `f` vanishes almost
everywhere on the box `(0, ½)ᵈ`. -/
def ZeroOnBox (f : lp (fun _ : d → ℤ => ℂ) 2) : Prop :=
  (ofCoeff f : UnitAddTorus d → ℂ) =ᵐ[volume.restrict (boxSet d)] 0

/-- Functions vanishing a.e. on `s` and functions vanishing a.e. off `s` are orthogonal. -/
theorem inner_eq_zero_of_ae {s : Set (UnitAddTorus d)}
    {g φ : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    (hg : (g : UnitAddTorus d → ℂ) =ᵐ[volume.restrict s] 0)
    (hφ : (φ : UnitAddTorus d → ℂ) =ᵐ[volume.restrict sᶜ] 0) : ⟪g, φ⟫_ℂ = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have h : (fun x => ⟪g x, φ x⟫_ℂ) =ᵐ[volume] 0 := by
    have hu : ∀ᵐ x ∂volume.restrict (s ∪ sᶜ), ⟪g x, φ x⟫_ℂ = 0 := by
      rw [ae_restrict_union_iff]
      exact ⟨hg.mono fun x hx => by simp [hx], hφ.mono fun x hx => by simp [hx]⟩
    rwa [union_compl_self, Measure.restrict_univ] at hu
  rw [integral_congr_ae h]
  simp

/-- **Characterization of `ZeroOnBox`** by orthogonality to every `L²` function supported off the
box. -/
theorem zeroOnBox_iff (f : lp (fun _ : d → ℤ => ℂ) 2) :
    ZeroOnBox f ↔ ∀ φ : Lp ℂ 2 (volume : Measure (UnitAddTorus d)),
      (φ : UnitAddTorus d → ℂ) =ᵐ[volume.restrict (boxSet d)ᶜ] 0 → ⟪ofCoeff f, φ⟫_ℂ = 0 := by
  refine ⟨fun h φ hφ => inner_eq_zero_of_ae h hφ, fun h => ?_⟩
  set g : Lp ℂ 2 (volume : Measure (UnitAddTorus d)) := ofCoeff f
  have hm : MemLp ((boxSet d).indicator (g : UnitAddTorus d → ℂ)) 2 volume :=
    (Lp.memLp g).indicator measurableSet_boxSet.nullMeasurableSet
  set φ : Lp ℂ 2 (volume : Measure (UnitAddTorus d)) := hm.toLp _
  have hφ : (φ : UnitAddTorus d → ℂ) =ᵐ[volume] (boxSet d).indicator g := hm.coeFn_toLp
  have hoff : (φ : UnitAddTorus d → ℂ) =ᵐ[volume.restrict (boxSet d)ᶜ] 0 := by
    refine EventuallyEq.trans (ae_restrict_of_ae hφ) ?_
    filter_upwards [ae_restrict_mem measurableSet_boxSet.compl] with x hx
    simp [indicator_of_notMem hx]
  have h0 := h φ hoff
  rw [MeasureTheory.L2.inner_def] at h0
  have e : (fun x => ⟪(g : UnitAddTorus d → ℂ) x, (φ : UnitAddTorus d → ℂ) x⟫_ℂ) =ᵐ[volume]
      (boxSet d).indicator fun x => ((‖(g : UnitAddTorus d → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [hφ] with x hx
    rw [hx]
    by_cases hb : x ∈ boxSet d
    · rw [indicator_of_mem hb, indicator_of_mem hb, RCLike.inner_apply, Complex.mul_conj']
      push_cast; rfl
    · rw [indicator_of_notMem hb, indicator_of_notMem hb, inner_zero_right]
  rw [integral_congr_ae e, integral_indicator measurableSet_boxSet, integral_complex_ofReal]
    at h0
  have hint : Integrable (fun x => ‖(g : UnitAddTorus d → ℂ) x‖ ^ 2) (volume.restrict (boxSet d)) :=
    ((Lp.memLp g).integrable_norm_pow two_ne_zero).restrict
  have h1 := (integral_eq_zero_iff_of_nonneg (fun _ => by positivity) hint).1
    (Complex.ofReal_eq_zero.1 h0)
  filter_upwards [h1] with x hx
  simpa using hx

/-- `ZeroOnBox` as a (complex) subspace of `ℓ²(ℤᵈ)`. -/
def boxZero : Submodule ℂ (lp (fun _ : d → ℤ => ℂ) 2) where
  carrier := {f | ZeroOnBox f}
  zero_mem' := by
    simp only [mem_ofPred_eq, zeroOnBox_iff, ofCoeff, _root_.map_zero, inner_zero_left, implies_true]
  add_mem' := by
    intro f g hf hg
    simp only [mem_ofPred_eq, zeroOnBox_iff] at hf hg ⊢
    intro φ hφ
    rw [ofCoeff, _root_.map_add, inner_add_left, ← ofCoeff, ← ofCoeff, hf φ hφ, hg φ hφ, add_zero]
  smul_mem' := by
    intro c f hf
    simp only [mem_ofPred_eq, zeroOnBox_iff] at hf ⊢
    intro φ hφ
    rw [ofCoeff, _root_.map_smul, inner_smul_left, ← ofCoeff, hf φ hφ, mul_zero]

theorem mem_boxZero {f : lp (fun _ : d → ℤ => ℂ) 2} : f ∈ boxZero ↔ ZeroOnBox f := Iff.rfl

/-- `boxZero` is closed. -/
theorem isClosed_boxZero : IsClosed (boxZero (d := d) : Set (lp (fun _ : d → ℤ => ℂ) 2)) := by
  have e : (boxZero (d := d) : Set (lp (fun _ : d → ℤ => ℂ) 2)) =
      ⋂ φ : {φ : Lp ℂ 2 (volume : Measure (UnitAddTorus d)) //
        (φ : UnitAddTorus d → ℂ) =ᵐ[volume.restrict (boxSet d)ᶜ] 0},
      {f | ⟪ofCoeff f, (φ : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))⟫_ℂ = 0} := by
    ext f
    simp only [SetLike.mem_coe, mem_boxZero, zeroOnBox_iff, mem_iInter, mem_ofPred_eq,
      Subtype.forall]
  rw [e]
  refine isClosed_iInter fun φ => isClosed_eq ?_ continuous_const
  exact (continuous_id.inner continuous_const).comp (mFourierBasis.repr.symm.continuous)

/-- **A trigonometric polynomial vanishing a.e. on the box is zero.** -/
theorem eq_zero_of_zeroOnBox_of_finite {f : lp (fun _ : d → ℤ => ℂ) 2} (S : Finset (d → ℤ))
    (hS : ∀ k ∉ S, f k = 0) (hf : ZeroOnBox f) : f = 0 :=
  eq_zero_of_ae_eq_zero_of_finite S hS isOpen_boxSet boxSet_nonempty hf

end Box

/-! ### Families of three subspaces -/

section Sub3

variable {𝕜 : Type*} [RCLike 𝕜] {W0 W1 W2 : Type u}
  [NormedAddCommGroup W0] [InnerProductSpace 𝕜 W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace 𝕜 W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace 𝕜 W2] [CompleteSpace W2]

/-- Three subspaces `K₀ ⊆ W0`, `K₁ ⊆ W1`, `K₂ ⊆ W2` as a family on `Fin 3`. -/
def sub3 (K₀ : Submodule 𝕜 W0) (K₁ : Submodule 𝕜 W1) (K₂ : Submodule 𝕜 W2) :
    ∀ i : Fin 3, Submodule 𝕜 (W3 W0 W1 W2 i)
  | 0 => K₀
  | 1 => K₁
  | 2 => K₂

instance instHasOrthogonalProjectionSub3 (K₀ : Submodule 𝕜 W0) (K₁ : Submodule 𝕜 W1)
    (K₂ : Submodule 𝕜 W2) [K₀.HasOrthogonalProjection] [K₁.HasOrthogonalProjection]
    [K₂.HasOrthogonalProjection] : ∀ i, (sub3 K₀ K₁ K₂ i).HasOrthogonalProjection
  | 0 => inferInstanceAs K₀.HasOrthogonalProjection
  | 1 => inferInstanceAs K₁.HasOrthogonalProjection
  | 2 => inferInstanceAs K₂.HasOrthogonalProjection

omit [CompleteSpace W0] [CompleteSpace W1] [CompleteSpace W2] in
theorem mem_totalSub_sub3 {K₀ : Submodule 𝕜 W0} {K₁ : Submodule 𝕜 W1} {K₂ : Submodule 𝕜 W2}
    {x : PiLp 2 (W3 W0 W1 W2)} :
    x ∈ HilbertComplex.totalSub (sub3 K₀ K₁ K₂) ↔
      (x 0 : W0) ∈ K₀ ∧ (x 1 : W1) ∈ K₁ ∧ (x 2 : W2) ∈ K₂ := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    exacts [h0, h1, h2]

/-- A reducing subcomplex of a short complex from the two reducing pairs. -/
theorem reducingSubcomplex_sub3 (S : ShortHilbertComplex 𝕜 W0 W1 W2) {K₀ : Submodule 𝕜 W0}
    {K₁ : Submodule 𝕜 W1} {K₂ : Submodule 𝕜 W2} [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] [K₂.HasOrthogonalProjection]
    (h₀ : S.d₀.IsReducingPair K₀ K₁) (h₁ : S.d₁.IsReducingPair K₁ K₂) :
    S.toHilbertComplex.ReducingSubcomplex (sub3 K₀ K₁ K₂) := by
  refine HilbertComplex.ReducingSubcomplex.of_rel fun i j hij => ?_
  fin_cases i <;> fin_cases j <;> simp at hij
  exacts [h₀, h₁]

end Sub3

/-! ### Window total spaces of short complexes -/

section Slots

variable {W0 W1 W2 : Type u}

theorem ext3 {V0 V1 V2 : Type u} {x y : PiLp 2 (W3 V0 V1 V2)}
    (h0 : (x 0 : V0) = y 0) (h1 : (x 1 : V1) = y 1) (h2 : (x 2 : V2) = y 2) : x = y := by
  refine PiLp.ext fun i => ?_
  fin_cases i
  exacts [h0, h1, h2]

/-- The first slot of the window total space, with its own type. -/
abbrev slot0 (y : PiLp 2 (W3 W0 W1 W2)) : W0 := y 0

/-- The second slot of the window total space, with its own type. -/
abbrev slot1 (y : PiLp 2 (W3 W0 W1 W2)) : W1 := y 1

/-- The third slot of the window total space, with its own type. -/
abbrev slot2 (y : PiLp 2 (W3 W0 W1 W2)) : W2 := y 2


end Slots

/-! ### Invariant cores of compressions -/

section Compression

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex ℝ c W} {S : ∀ i, Submodule ℝ (W i)} [∀ i, (S i).HasOrthogonalProjection]
  [∀ i, CompleteSpace (S i)]

omit [∀ i, CompleteSpace (W i)] in
theorem totalIncl_injective (S : ∀ i, Submodule ℝ (W i)) :
    Function.Injective (HilbertComplex.ReducingSubcomplex.totalIncl S) :=
  (HilbertComplex.ReducingSubcomplex.totalIncl S).injective

/-- The constraint family `K` seen inside the compressed spaces `S i`. -/
def compSub (S : ∀ i, Submodule ℝ (W i)) (K : ∀ i, Submodule ℝ (W i)) :
    ∀ i, Submodule ℝ (S i) := fun i => (K i).comap (S i).subtype

omit [∀ i, CompleteSpace (W i)] [∀ i, (S i).HasOrthogonalProjection] [∀ i, CompleteSpace (S i)] in
theorem mem_totalSub_compSub {K : ∀ i, Submodule ℝ (W i)} {y : PiLp 2 fun i => S i} :
    y ∈ HilbertComplex.totalSub (compSub S K) ↔
      HilbertComplex.ReducingSubcomplex.totalIncl S y ∈ HilbertComplex.totalSub K :=
  Iff.rfl

/-- **Invariant cores of a compression are invariant cores of the big complex**: for a reducing
subcomplex `S` of `H` and any family `K`, `y` lies in the invariant core of `∏ (K i ∩ S i)` for
the compressed wave group iff its inclusion lies in the invariant core of `∏ K i` for the wave
group of `H`. -/
theorem mem_invariantCore_compSub_iff (h : H.ReducingSubcomplex S) (K : ∀ i, Submodule ℝ (W i))
    (y : PiLp 2 fun i => S i) :
    y ∈ h.toHilbertComplex.waveGroup.invariantCore (HilbertComplex.totalSub (compSub S K)) ↔
      HilbertComplex.ReducingSubcomplex.totalIncl S y ∈
        H.waveGroup.invariantCore (HilbertComplex.totalSub K) := by
  simp only [C0Group.mem_invariantCore, mem_totalSub_compSub, h.waveGroup_toHilbertComplex]

/-- Stationary vectors of a compression are the stationary vectors of the big complex. -/
theorem mem_stationary_compSub_iff (h : H.ReducingSubcomplex S) (y : PiLp 2 fun i => S i) :
    y ∈ h.toHilbertComplex.waveGroup.stationary ↔
      HilbertComplex.ReducingSubcomplex.totalIncl S y ∈ H.waveGroup.stationary := by
  simp only [C0Group.mem_stationary]
  refine forall_congr' fun t => ?_
  rw [← h.waveGroup_toHilbertComplex, (totalIncl_injective S).eq_iff]

/-- Forward orbits of a compression are the forward orbits of the big complex. -/
theorem forward_compSub_iff (h : H.ReducingSubcomplex S) (K : ∀ i, Submodule ℝ (W i))
    (y : PiLp 2 fun i => S i) :
    (∀ t, 0 ≤ t → h.toHilbertComplex.waveGroup.S t y ∈ HilbertComplex.totalSub (compSub S K)) ↔
      ∀ t, 0 ≤ t → H.waveGroup.S t (HilbertComplex.ReducingSubcomplex.totalIncl S y) ∈
        HilbertComplex.totalSub K := by
  simp only [mem_totalSub_compSub, h.waveGroup_toHilbertComplex]

/-- The domain of the wave operator of a compression. -/
theorem mem_wave_domain_compress_iff (h : H.ReducingSubcomplex S) (y : PiLp 2 fun i => S i) :
    y ∈ h.toHilbertComplex.wave.domain ↔
      HilbertComplex.ReducingSubcomplex.totalIncl S y ∈ H.wave.domain := by
  rw [HilbertComplex.mem_wave_domain, HilbertComplex.mem_wave_domain]
  refine and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun j => ?_)
  change y j ∈ (h.toHilbertComplex.dual.d j i).domain ↔ _
  rw [HilbertComplex.ReducingSubcomplex.dual_toHilbertComplex_d]
  exact Iff.rfl

end Compression

/-! ### Constraints invariant under a unitary action -/

section Action

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex ℝ c W} {Γ : Type*} [Group Γ] [Fintype Γ]

/-- A unitary preserving a closed subspace `K` and its inverse commutes with `P_K`. -/
theorem starProjection_comm_of_invariant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (U : E ≃ₗᵢ[ℝ] E) (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (hU : ∀ x ∈ K, U x ∈ K) (hU' : ∀ x ∈ K, U.symm x ∈ K) (x : E) :
    K.starProjection (U x) = U (K.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (u := U x)
    (hU _ (K.starProjection_apply_mem x)) fun k hk => ?_
  rw [← _root_.map_sub, show k = U (U.symm k) from (U.apply_symm_apply k).symm,
    U.inner_map_map]
  exact K.starProjection_inner_eq_zero x _ (hU' k hk)

instance instHasOrthogonalProjectionCompSub (S : ∀ i, Submodule ℝ (W i))
    [∀ i, CompleteSpace (S i)] (K : ∀ i, Submodule ℝ (W i)) [∀ i, (K i).HasOrthogonalProjection]
    (i : ι) : (compSub S K i).HasOrthogonalProjection := by
  have hc : IsClosed (compSub S K i : Set (S i)) :=
    ((K i).isClosed_of_hasOrthogonalProjection).preimage continuous_subtype_val
  have : CompleteSpace (compSub S K i) := hc.completeSpace_coe
  infer_instance

omit [Fintype ι] in
/-- **Invariant constraints descend to the fixed complex**: if `K` is a reducing subcomplex of `H`
whose spaces are preserved by a finite unitary action, then `K ∩ Fix` is a reducing subcomplex
of the fixed (method-of-images) complex. -/
theorem reducingSubcomplex_compSub_fixed (A : H.Action Γ) {K : ∀ i, Submodule ℝ (W i)}
    [∀ i, (K i).HasOrthogonalProjection] (hK : H.ReducingSubcomplex K)
    (hA : ∀ g i, ∀ x ∈ K i, A.act g i x ∈ K i) :
    A.fixedComplex.ReducingSubcomplex (compSub A.fixed K) := by
  have hS : ∀ i (x : A.fixed i), ∃ y : A.fixed i,
      A.reducingSubcomplex_fixed.toScaledEmbedding.J i y = (K i).starProjection
        (A.reducingSubcomplex_fixed.toScaledEmbedding.J i x) := by
    intro i x
    refine ⟨⟨(K i).starProjection x, fun g => ?_⟩, rfl⟩
    have hinv : ∀ y ∈ K i, (A.act g i).symm y ∈ K i := fun y hy => by
      have e : (A.act g i).symm y = A.act g⁻¹ i y := by
        apply (A.act g i).injective
        rw [LinearIsometryEquiv.apply_symm_apply, A.act_act_inv]
      rw [e]; exact hA g⁻¹ i y hy
    rw [← starProjection_comm_of_invariant (A.act g i) (K i) (hA g i) hinv, x.2 g]
  exact A.reducingSubcomplex_fixed.toScaledEmbedding.reducingSubcomplex_comap hK hS

end Action

/-! ### Zero differentials -/

/-- Two zero differentials commute with any pair of maps. -/
theorem comm_of_eq_zero {E F E' F' : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] [AddCommGroup E'] [Module ℝ E'] [AddCommGroup F'] [Module ℝ F']
    {T : E →ₗ.[ℝ] F} {T' : E' →ₗ.[ℝ] F'} (hT : T = 0) (hT' : T' = 0) (J : E →ₗ[ℝ] E')
    (J' : F →ₗ[ℝ] F') (κ : ℝ) (x : T.domain) (h : J x ∈ T'.domain) :
    T' ⟨J x, h⟩ = κ • J' (T x) := by
  rw [LinearPMap.apply_eq_zero_of_eq_zero hT', LinearPMap.apply_eq_zero_of_eq_zero hT x,
    _root_.map_zero, smul_zero]

/-! ### Stationary vectors -/

/-- A stationary vector in the domain of the generator is killed by the generator. -/
theorem generator_eq_zero_of_mem_stationary {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (G : C0Group ℝ E) (x : G.generator.domain)
    (hx : (x : E) ∈ G.stationary) : G.generator x = 0 := by
  refine G.generator_apply_eq ?_
  have e : (fun t => G.S t x) = fun _ => (x : E) := funext (C0Group.mem_stationary.1 hx)
  rw [e]
  exact hasDerivAt_const _ _

end Feec.Models.Cube
