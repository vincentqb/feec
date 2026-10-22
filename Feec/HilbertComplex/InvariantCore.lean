module

public import Feec.HilbertComplex.Reducing

/-!
# The largest propagating constraint space of the Hodge wave equation

Thesis Props 4.17/4.19 assume that a product constraint `K = {0} × S₁ × S₂` reduces the wave
operator `L` (the projection hypothesis `P_K D(L) ⊆ D(L)`). When it does not (on bounded domains
it fails, `Feec.Counterexamples.BoundedDomainTSD`), the thesis' argument still runs on the
**invariant core** `K* = {x | e^{tL} x ∈ K for all t}` (`Feec.C0Group.invariantCore`), the
largest closed subspace of `K` reducing `L`. This file shows that `K*` is again a product
constraint of the same shape and characterizes it.

## Graded complexes

For a Hilbert complex graded by a parity `p` (flipping along every arrow), the grading operator
`R` reverses time, `R e^{tL} = e^{-tL} R` (`Feec.HilbertComplex.reversal_waveGroup`). Hence:

* `R` preserves the invariant core of every `R`-invariant `K` (`reversal_mem_invariantCore`),
  in particular of every product `totalSub S` (`reversal_mem_totalSub`).

## Short complexes

For a short complex and `K = {0} × S₁ × S₂` (`Feec.ShortHilbertComplex.coreSub`):

* `K* = {0} × S₁* × S₂*` (`coreSub_eq`), where `S₁* = {E | (0, E, 0) ∈ K*}` and
  `S₂* = {B | (0, 0, B) ∈ K*}` (`invariantCore₁`, `invariantCore₂`): the even and odd parts
  `(x ± R x)/2` of `x ∈ K*` lie in `K*`;
* `{0} × S₁* × S₂*` reduces `L` (`isReducing_wave_coreSub`), so strong solutions with data in it
  exist, are unique and stay in it (`existsUnique_mem_coreSub`, the corrected Prop 4.17); when
  `S₁ ⊆ N(d₀†)` it is even a reducing subcomplex (`reducingSubcomplex_coreSub`):
  `d₁ (D(d₁) ∩ S₁*) ⊆ S₂*`, `d₁† (D(d₁†) ∩ S₂*) ⊆ S₁*`;
* **maximality** (`le_invariantCore_of_isReducing`): every closed `S₁' ⊆ S₁`, `S₂' ⊆ S₂` whose
  product reduces `L` lies in `(S₁*, S₂*)`;
* stationary data of degree `2` lie in `K*` (`mem_invariantCore₂_of_eq_zero`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.3 (Thm 4.4), §4.10 (Props 4.16–4.18), §4.11 (Prop 4.19)
* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §III.5.6 (reducing subspaces)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.10 (groups of isometries)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

/-! ### Graded complexes -/

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [Fintype ι] {p : ι → Bool}

omit [∀ i, CompleteSpace (W i)] in
/-- The grading operator preserves every product subspace. -/
theorem reversal_mem_totalSub {S : ∀ i, Submodule 𝕜 (W i)} {x : PiLp 2 W}
    (hx : x ∈ totalSub S) : reversal 𝕜 p x ∈ totalSub S := fun i => by
  rw [reversal_apply]; exact (S i).smul_mem _ (hx i)

variable (H : HilbertComplex 𝕜 c W) [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  (hp : ∀ i j, c.Rel i j → p j ≠ p i)
include hp

/-- **The grading preserves invariant cores**: if `R K ⊆ K`, then `R K* ⊆ K*`, since
`e^{tL} R x = R e^{-tL} x`. -/
theorem reversal_mem_invariantCore {K : Submodule 𝕜 (PiLp 2 W)}
    (hRK : ∀ x ∈ K, reversal 𝕜 p x ∈ K) {x : PiLp 2 W} (hx : x ∈ H.waveGroup.invariantCore K) :
    reversal 𝕜 p x ∈ H.waveGroup.invariantCore K :=
  C0Group.mem_invariantCore.2 fun t => by
    have e := H.reversal_waveGroup hp (-t) x
    rw [neg_neg] at e
    rw [← e]
    exact hRK _ (C0Group.mem_invariantCore.1 hx _)

omit hp in
/-- Strong solutions of `U' = L U` from `x ∈ D(L)` are the orbit `t ↦ e^{tL} x`. -/
theorem eq_waveGroup_of_isStrongSolution {x : PiLp 2 W} (hx : x ∈ H.wave.domain) {T : ℝ}
    {U : ℝ → PiLp 2 W} (h0 : U 0 = x) (hU : Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U)
    {t : ℝ} (ht : t ∈ Icc 0 T) : U t = H.waveGroup.S t x := by
  have hg : H.waveGroup.toC0Semigroup.generator = H.wave := H.generator_waveGroup
  have hO := H.waveGroup.toC0Semigroup.isClassicalSolution_orbit (U₀ := x) (by rw [hg]; exact hx)
    0 T
  rw [hg] at hO
  have := hU.unique H.isSkewAdjoint_wave.isDissipative hO.toIsStrongSolution (by simp [h0]) ht
  simpa using this

omit hp in
/-- The orbit `t ↦ e^{tL} x` of `x ∈ D(L)` is a strong solution of `U' = L U` on `[0, T]`. -/
theorem isStrongSolution_waveGroup {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (T : ℝ) :
    Evolution.IsStrongSolution H.wave (Icc 0 T) 0 fun t => H.waveGroup.S t x := by
  have hg : H.waveGroup.toC0Semigroup.generator = H.wave := H.generator_waveGroup
  have hO := H.waveGroup.toC0Semigroup.isClassicalSolution_orbit (U₀ := x) (by rw [hg]; exact hx)
    0 T
  rw [hg] at hO
  simpa using hO.toIsStrongSolution

end Feec.HilbertComplex

/-! ### Short complexes: product constraints -/

namespace Feec.ShortHilbertComplex

universe u

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ W₂ : Type u}
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]

/-- A constraint family `K₀ × K₁ × K₂` on the three spaces of a short complex. -/
def family3 (K₀ : Submodule 𝕜 W₀) (K₁ : Submodule 𝕜 W₁) (K₂ : Submodule 𝕜 W₂) :
    ∀ i : Fin 3, Submodule 𝕜 (W3 W₀ W₁ W₂ i)
  | 0 => K₀
  | 1 => K₁
  | 2 => K₂

instance instHasOrthogonalProjectionFamily3 (K₀ : Submodule 𝕜 W₀) (K₁ : Submodule 𝕜 W₁)
    (K₂ : Submodule 𝕜 W₂) [K₀.HasOrthogonalProjection] [K₁.HasOrthogonalProjection]
    [K₂.HasOrthogonalProjection] : ∀ i, (family3 K₀ K₁ K₂ i).HasOrthogonalProjection
  | 0 => inferInstanceAs K₀.HasOrthogonalProjection
  | 1 => inferInstanceAs K₁.HasOrthogonalProjection
  | 2 => inferInstanceAs K₂.HasOrthogonalProjection

omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
theorem mem_totalSub_family3 {K₀ : Submodule 𝕜 W₀} {K₁ : Submodule 𝕜 W₁}
    {K₂ : Submodule 𝕜 W₂} {x : PiLp 2 (W3 W₀ W₁ W₂)} :
    x ∈ HilbertComplex.totalSub (family3 K₀ K₁ K₂) ↔
      (x 0 : W₀) ∈ K₀ ∧ (x 1 : W₁) ∈ K₁ ∧ (x 2 : W₂) ∈ K₂ := by
  refine ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨h0, h1, h2⟩ i => ?_⟩
  fin_cases i
  exacts [h0, h1, h2]

omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
theorem totalSub_family3_mono {K₀ K₀' : Submodule 𝕜 W₀} {K₁ K₁' : Submodule 𝕜 W₁}
    {K₂ K₂' : Submodule 𝕜 W₂} (h₀ : K₀ ≤ K₀') (h₁ : K₁ ≤ K₁') (h₂ : K₂ ≤ K₂') :
    HilbertComplex.totalSub (family3 K₀ K₁ K₂) ≤ HilbertComplex.totalSub (family3 K₀' K₁' K₂') :=
  HilbertComplex.totalSub_mono fun i => by fin_cases i; exacts [h₀, h₁, h₂]

omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
/-- A single nonzero component in the constraint family. -/
theorem single_two_mem_totalSub_family3 (K₀ : Submodule 𝕜 W₀) (K₁ : Submodule 𝕜 W₁)
    (K₂ : Submodule 𝕜 W₂) {v : W₂} (hv : v ∈ K₂) :
    WithLp.toLp 2 (Pi.single (M := W3 W₀ W₁ W₂) 2 v) ∈
      HilbertComplex.totalSub (family3 K₀ K₁ K₂) := by
  intro i
  match i with
  | 0 => exact K₀.zero_mem
  | 1 => exact K₁.zero_mem
  | 2 => exact hv

omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
theorem single_one_mem_totalSub_family3 (K₀ : Submodule 𝕜 W₀) (K₁ : Submodule 𝕜 W₁)
    (K₂ : Submodule 𝕜 W₂) {v : W₁} (hv : v ∈ K₁) :
    WithLp.toLp 2 (Pi.single (M := W3 W₀ W₁ W₂) 1 v) ∈
      HilbertComplex.totalSub (family3 K₀ K₁ K₂) := by
  intro i
  match i with
  | 0 => exact K₀.zero_mem
  | 1 => exact hv
  | 2 => exact K₂.zero_mem

/-! ### The embeddings `E ↦ (0, E, 0)` and `B ↦ (0, 0, B)` -/

variable (W₀ W₁ W₂) in
/-- The embedding `E ↦ (0, E, 0)`. -/
def inj₁ : W₁ →L[𝕜] PiLp 2 (W3 W₀ W₁ W₂) :=
  (PiLp.continuousLinearEquiv 2 𝕜 (W3 W₀ W₁ W₂)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single 𝕜 (W3 W₀ W₁ W₂) 1

variable (W₀ W₁ W₂) in
/-- The embedding `B ↦ (0, 0, B)`. -/
def inj₂ : W₂ →L[𝕜] PiLp 2 (W3 W₀ W₁ W₂) :=
  (PiLp.continuousLinearEquiv 2 𝕜 (W3 W₀ W₁ W₂)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single 𝕜 (W3 W₀ W₁ W₂) 2

omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
@[simp] theorem inj₁_apply_zero (v : W₁) : (inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ v 0 : W₀) = 0 := rfl
omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
@[simp] theorem inj₁_apply_one (v : W₁) : (inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ v 1 : W₁) = v := rfl
omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
@[simp] theorem inj₁_apply_two (v : W₁) : (inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ v 2 : W₂) = 0 := rfl
omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
@[simp] theorem inj₂_apply_zero (v : W₂) : (inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ v 0 : W₀) = 0 := rfl
omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
@[simp] theorem inj₂_apply_one (v : W₂) : (inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ v 1 : W₁) = 0 := rfl
omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
@[simp] theorem inj₂_apply_two (v : W₂) : (inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ v 2 : W₂) = v := rfl

/-! ### The time reversal `(x₀, x₁, x₂) ↦ (x₀, -x₁, x₂)` -/

/-- The grading of the window `Fin 3`: `R (x₀, x₁, x₂) = (x₀, -x₁, x₂)`. -/
abbrev reversal3 : PiLp 2 (W3 W₀ W₁ W₂) ≃ₗᵢ[𝕜] PiLp 2 (W3 W₀ W₁ W₂) :=
  HilbertComplex.reversal 𝕜 fun i : Fin 3 => decide (Odd i.val)

omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
theorem reversal3_apply_zero (x : PiLp 2 (W3 W₀ W₁ W₂)) :
    (reversal3 (𝕜 := 𝕜) x 0 : W₀) = x 0 := by
  rw [HilbertComplex.reversal_apply]
  simp [HilbertComplex.paritySign]

omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
theorem reversal3_apply_one (x : PiLp 2 (W3 W₀ W₁ W₂)) :
    (reversal3 (𝕜 := 𝕜) x 1 : W₁) = -(x 1 : W₁) := by
  rw [HilbertComplex.reversal_apply]
  simp [HilbertComplex.paritySign]

omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
theorem reversal3_apply_two (x : PiLp 2 (W3 W₀ W₁ W₂)) :
    (reversal3 (𝕜 := 𝕜) x 2 : W₂) = x 2 := by
  rw [HilbertComplex.reversal_apply]
  simp [HilbertComplex.paritySign]

/-! ### The invariant core of `{0} × S₁ × S₂` -/

variable (S : ShortHilbertComplex 𝕜 W₀ W₁ W₂)
  [∀ i, NormedSpace ℝ (W3 W₀ W₁ W₂ i)] [∀ i, IsScalarTower ℝ 𝕜 (W3 W₀ W₁ W₂ i)]
  (S₁ : Submodule 𝕜 W₁) (S₂ : Submodule 𝕜 W₂)

/-- `K* = {x | e^{tL} x ∈ {0} × S₁ × S₂ for all t}`: the invariant core of the product constraint
under the wave group. -/
def coreSub : Submodule 𝕜 (PiLp 2 (W3 W₀ W₁ W₂)) :=
  S.toHilbertComplex.waveGroup.invariantCore
    (HilbertComplex.totalSub (family3 (⊥ : Submodule 𝕜 W₀) S₁ S₂))

/-- The electric slot `S₁* = {E | (0, E, 0) ∈ K*}`. -/
def invariantCore₁ : Submodule 𝕜 W₁ := (S.coreSub S₁ S₂).comap (inj₁ (𝕜 := 𝕜) W₀ W₁ W₂).toLinearMap

/-- The magnetic slot `S₂* = {B | (0, 0, B) ∈ K*}`. -/
def invariantCore₂ : Submodule 𝕜 W₂ := (S.coreSub S₁ S₂).comap (inj₂ (𝕜 := 𝕜) W₀ W₁ W₂).toLinearMap

variable {S S₁ S₂}

theorem mem_invariantCore₁ {v : W₁} :
    v ∈ S.invariantCore₁ S₁ S₂ ↔ inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ v ∈ S.coreSub S₁ S₂ := Iff.rfl

theorem coreSub_le :
    S.coreSub S₁ S₂ ≤ HilbertComplex.totalSub (family3 (⊥ : Submodule 𝕜 W₀) S₁ S₂) :=
  C0Group.invariantCore_le

theorem invariantCore₁_le : S.invariantCore₁ S₁ S₂ ≤ S₁ := fun _ hv =>
  (mem_totalSub_family3.1 (coreSub_le hv)).2.1

theorem invariantCore₂_le : S.invariantCore₂ S₁ S₂ ≤ S₂ := fun _ hv =>
  (mem_totalSub_family3.1 (coreSub_le hv)).2.2

/-- **`K*` is a product**: `K* = {0} × S₁* × S₂*`. The even and odd parts `(x ± R x)/2` of
`x ∈ K*` for the time reversal `R` lie in `K*`. -/
theorem coreSub_eq : S.coreSub S₁ S₂ = HilbertComplex.totalSub
    (family3 (⊥ : Submodule 𝕜 W₀) (S.invariantCore₁ S₁ S₂) (S.invariantCore₂ S₁ S₂)) := by
  ext x
  constructor
  · intro hx
    have hK := mem_totalSub_family3.1 (coreSub_le hx)
    have h0 : (x 0 : W₀) = 0 := (Submodule.mem_bot 𝕜 (M := W₀)).1 hK.1
    have hR := S.toHilbertComplex.reversal_mem_invariantCore
      (fun _ _ h => ComplexShape.window_parity h)
      (fun y hy => HilbertComplex.reversal_mem_totalSub hy) hx
    have hR' : reversal3 (𝕜 := 𝕜) x ∈ S.coreSub S₁ S₂ := hR
    refine mem_totalSub_family3.2 ⟨hK.1, ?_, ?_⟩
    · show inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ (x 1 : W₁) ∈ S.coreSub S₁ S₂
      have e : inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ (x 1 : W₁) = (2⁻¹ : 𝕜) • (x - reversal3 (𝕜 := 𝕜) x) := by
        refine PiLp.ext fun i => ?_
        fin_cases i
        · show (0 : W₀) = (2⁻¹ : 𝕜) • ((x 0 : W₀) - (reversal3 (𝕜 := 𝕜) x 0 : W₀))
          rw [reversal3_apply_zero, sub_self, smul_zero]
          rfl
        · show (x 1 : W₁) = (2⁻¹ : 𝕜) • ((x 1 : W₁) - (reversal3 (𝕜 := 𝕜) x 1 : W₁))
          rw [reversal3_apply_one, sub_neg_eq_add, ← two_smul 𝕜, smul_smul,
            inv_mul_cancel₀ two_ne_zero, one_smul]
        · show (0 : W₂) = (2⁻¹ : 𝕜) • ((x 2 : W₂) - (reversal3 (𝕜 := 𝕜) x 2 : W₂))
          rw [reversal3_apply_two, sub_self, smul_zero]
          rfl
      rw [e]
      exact (S.coreSub S₁ S₂).smul_mem _ ((S.coreSub S₁ S₂).sub_mem hx hR')
    · show inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ (x 2 : W₂) ∈ S.coreSub S₁ S₂
      have e : inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ (x 2 : W₂) = (2⁻¹ : 𝕜) • (x + reversal3 (𝕜 := 𝕜) x) := by
        refine PiLp.ext fun i => ?_
        fin_cases i
        · show (0 : W₀) = (2⁻¹ : 𝕜) • ((x 0 : W₀) + (reversal3 (𝕜 := 𝕜) x 0 : W₀))
          rw [reversal3_apply_zero, h0, add_zero, smul_zero]
          rfl
        · show (0 : W₁) = (2⁻¹ : 𝕜) • ((x 1 : W₁) + (reversal3 (𝕜 := 𝕜) x 1 : W₁))
          rw [reversal3_apply_one, add_neg_cancel, smul_zero]
          rfl
        · show (x 2 : W₂) = (2⁻¹ : 𝕜) • ((x 2 : W₂) + (reversal3 (𝕜 := 𝕜) x 2 : W₂))
          rw [reversal3_apply_two, ← two_smul 𝕜, smul_smul, inv_mul_cancel₀ two_ne_zero,
            one_smul]
      rw [e]
      exact (S.coreSub S₁ S₂).smul_mem _ ((S.coreSub S₁ S₂).add_mem hx hR')
  · intro hx
    obtain ⟨h0, h1, h2⟩ := mem_totalSub_family3.1 hx
    have e : x = inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ (x 1 : W₁) + inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ (x 2 : W₂) := by
      refine PiLp.ext fun i => ?_
      fin_cases i
      · show (x 0 : W₀) = 0 + 0
        rw [(Submodule.mem_bot 𝕜 (M := W₀)).1 h0, add_zero]
        rfl
      · show (x 1 : W₁) = (x 1 : W₁) + 0
        rw [add_zero]
      · show (x 2 : W₂) = 0 + (x 2 : W₂)
        rw [zero_add]
    rw [e]
    exact (S.coreSub S₁ S₂).add_mem h1 h2

theorem mem_coreSub_iff {x : PiLp 2 (W3 W₀ W₁ W₂)} : x ∈ S.coreSub S₁ S₂ ↔
    (x 0 : W₀) = 0 ∧ (x 1 : W₁) ∈ S.invariantCore₁ S₁ S₂ ∧
      (x 2 : W₂) ∈ S.invariantCore₂ S₁ S₂ := by
  rw [coreSub_eq, mem_totalSub_family3]
  exact and_congr (Submodule.mem_bot 𝕜 (M := W₀)) Iff.rfl

variable [S₁.HasOrthogonalProjection] [S₂.HasOrthogonalProjection]

theorem isClosed_coreSub : IsClosed (S.coreSub S₁ S₂ : Set (PiLp 2 (W3 W₀ W₁ W₂))) :=
  C0Group.isClosed_invariantCore HilbertComplex.isClosed_totalSub

theorem isClosed_invariantCore₁ : IsClosed (S.invariantCore₁ S₁ S₂ : Set W₁) :=
  isClosed_coreSub.preimage (inj₁ (𝕜 := 𝕜) W₀ W₁ W₂).continuous

theorem isClosed_invariantCore₂ : IsClosed (S.invariantCore₂ S₁ S₂ : Set W₂) :=
  isClosed_coreSub.preimage (inj₂ (𝕜 := 𝕜) W₀ W₁ W₂).continuous

instance : (S.invariantCore₁ S₁ S₂).HasOrthogonalProjection := by
  have : CompleteSpace (S.invariantCore₁ S₁ S₂) := isClosed_invariantCore₁.completeSpace_coe
  infer_instance

instance : (S.invariantCore₂ S₁ S₂).HasOrthogonalProjection := by
  have : CompleteSpace (S.invariantCore₂ S₁ S₂) := isClosed_invariantCore₂.completeSpace_coe
  infer_instance

instance : (S.coreSub S₁ S₂).HasOrthogonalProjection := by
  unfold coreSub; infer_instance

/-- **`{0} × S₁* × S₂*` reduces the wave operator** (the projection hypothesis of Prop 4.17 holds
for `K*`). -/
theorem isReducing_wave_coreSub : S.wave.IsReducing (HilbertComplex.totalSub
    (family3 (⊥ : Submodule 𝕜 W₀) (S.invariantCore₁ S₁ S₂) (S.invariantCore₂ S₁ S₂))) := by
  have h := S.toHilbertComplex.isReducing_invariantCore_waveGroup
    (HilbertComplex.totalSub (family3 (⊥ : Submodule 𝕜 W₀) S₁ S₂))
  have e := (coreSub_eq (S := S) (S₁ := S₁) (S₂ := S₂))
  unfold coreSub at e
  convert h using 1
  exact e.symm

/-- `D(L) ∩ K*` is dense in `K*`. -/
theorem mem_closure_wave_domain_inter_coreSub {k : PiLp 2 (W3 W₀ W₁ W₂)}
    (hk : k ∈ S.coreSub S₁ S₂) :
    k ∈ closure ((S.wave.domain : Set (PiLp 2 (W3 W₀ W₁ W₂))) ∩ S.coreSub S₁ S₂) := by
  have := S.toHilbertComplex.isIsometric_waveGroup.mem_closure_domain_inter_invariantCore hk
  rwa [HilbertComplex.generator_waveGroup] at this

omit [S₁.HasOrthogonalProjection] [S₂.HasOrthogonalProjection] in
/-- **Corrected Prop 4.17 with existence**: for `U₀ ∈ D(L) ∩ K*` and every `[a, b]`,
`U' = L U`, `U a = U₀` has a classical solution, unique among strong solutions, and it stays in
`K* ⊆ {0} × S₁ × S₂`. -/
theorem existsUnique_mem_coreSub {U₀ : PiLp 2 (W3 W₀ W₁ W₂)} (hU₀ : U₀ ∈ S.wave.domain)
    (hU₀K : U₀ ∈ S.coreSub S₁ S₂) (a b : ℝ) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution S.wave (Icc a b) 0 U ∧
      (∀ t ∈ Icc a b, U t ∈ S.coreSub S₁ S₂) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution S.wave (Icc a b) 0 V → EqOn V U (Icc a b) := by
  have hg : S.toHilbertComplex.waveGroup.toC0Semigroup.generator = S.wave :=
    S.toHilbertComplex.generator_waveGroup
  have hO := S.toHilbertComplex.waveGroup.toC0Semigroup.isClassicalSolution_orbit (U₀ := U₀)
    (by rw [hg]; exact hU₀) a b
  rw [hg] at hO
  refine ⟨_, by simp, hO, fun t _ => ?_, fun V hV0 hV => ?_⟩
  · exact C0Group.S_mem_invariantCore hU₀K _
  · exact hV.unique S.isSkewAdjoint_wave.isDissipative hO.toIsStrongSolution (by simp [hV0])

/-! ### Maximality -/

omit [S₁.HasOrthogonalProjection] [S₂.HasOrthogonalProjection] in
/-- **Maximality of `K*`**: if closed `S₁' ⊆ S₁`, `S₂' ⊆ S₂` and `{0} × S₁' × S₂'` reduces `L`,
then `S₁' ⊆ S₁*` and `S₂' ⊆ S₂*`. -/
theorem le_invariantCore_of_isReducing {S₁' : Submodule 𝕜 W₁} {S₂' : Submodule 𝕜 W₂}
    [S₁'.HasOrthogonalProjection] [S₂'.HasOrthogonalProjection] (h₁ : S₁' ≤ S₁) (h₂ : S₂' ≤ S₂)
    (hred : S.wave.IsReducing
      (HilbertComplex.totalSub (family3 (⊥ : Submodule 𝕜 W₀) S₁' S₂'))) :
    S₁' ≤ S.invariantCore₁ S₁ S₂ ∧ S₂' ≤ S.invariantCore₂ S₁ S₂ := by
  have hK : HilbertComplex.totalSub (family3 (⊥ : Submodule 𝕜 W₀) S₁' S₂') ≤ S.coreSub S₁ S₂ :=
    S.toHilbertComplex.le_invariantCore_waveGroup (totalSub_family3_mono le_rfl h₁ h₂) hred
  exact ⟨fun v hv => hK (single_one_mem_totalSub_family3 _ _ _ hv),
    fun v hv => hK (single_two_mem_totalSub_family3 _ _ _ hv)⟩

/-! ### The differentials on the slots of `K*` -/

omit [S₁.HasOrthogonalProjection] [S₂.HasOrthogonalProjection]
  [∀ i, NormedSpace ℝ (W3 W₀ W₁ W₂ i)] [∀ i, IsScalarTower ℝ 𝕜 (W3 W₀ W₁ W₂ i)] in
theorem inj₁_mem_wave_domain {v : W₁} (h1 : v ∈ S.d₁.domain) (h1' : v ∈ (S.d₀†).domain) :
    inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ v ∈ S.wave.domain :=
  S.mem_wave_domain.2 ⟨S.d₀.domain.zero_mem, h1, h1', (S.d₁†).domain.zero_mem⟩

omit [S₁.HasOrthogonalProjection] [S₂.HasOrthogonalProjection]
  [∀ i, NormedSpace ℝ (W3 W₀ W₁ W₂ i)] [∀ i, IsScalarTower ℝ 𝕜 (W3 W₀ W₁ W₂ i)] in
theorem inj₂_mem_wave_domain {v : W₂} (h2 : v ∈ (S.d₁†).domain) :
    inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ v ∈ S.wave.domain :=
  S.mem_wave_domain.2 ⟨S.d₀.domain.zero_mem, S.d₁.domain.zero_mem, (S.d₀†).domain.zero_mem, h2⟩

omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
/-- A partial map vanishes at a point of its domain whose underlying vector is `0`. -/
theorem _root_.LinearPMap.apply_eq_zero_of_coe_eq_zero {E F : Type*} [AddCommGroup E]
    [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] {T : E →ₗ.[𝕜] F} (x : T.domain)
    (h : (x : E) = 0) : T x = 0 := by
  rw [show x = 0 from Subtype.ext h, LinearPMap.map_zero]

omit [S₁.HasOrthogonalProjection] [S₂.HasOrthogonalProjection]
  [∀ i, NormedSpace ℝ (W3 W₀ W₁ W₂ i)] [∀ i, IsScalarTower ℝ 𝕜 (W3 W₀ W₁ W₂ i)] in
/-- `L (0, 0, B) = (0, -d₁† B, 0)`. -/
theorem wave_inj₂ (ρ : S.d₁†.domain) :
    S.wave ⟨_, inj₂_mem_wave_domain (S := S) ρ.2⟩ = inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ (-(S.d₁† ρ)) := by
  refine PiLp.ext fun i => ?_
  fin_cases i
  · show ((S.wave ⟨_, inj₂_mem_wave_domain (S := S) ρ.2⟩ : PiLp 2 (W3 W₀ W₁ W₂)) 0 : W₀) = 0
    rw [S.wave_apply_zero, LinearPMap.apply_eq_zero_of_coe_eq_zero _ rfl, neg_zero]
    rfl
  · show ((S.wave ⟨_, inj₂_mem_wave_domain (S := S) ρ.2⟩ : PiLp 2 (W3 W₀ W₁ W₂)) 1 : W₁) =
      -(S.d₁† ρ)
    rw [S.wave_apply_one, LinearPMap.apply_eq_zero_of_coe_eq_zero (T := S.d₀) _ rfl,
      zero_sub]
    rfl
  · show ((S.wave ⟨_, inj₂_mem_wave_domain (S := S) ρ.2⟩ : PiLp 2 (W3 W₀ W₁ W₂)) 2 : W₂) = 0
    rw [S.wave_apply_two, LinearPMap.apply_eq_zero_of_coe_eq_zero _ rfl]
    rfl

omit [S₁.HasOrthogonalProjection] [S₂.HasOrthogonalProjection]
  [∀ i, NormedSpace ℝ (W3 W₀ W₁ W₂ i)] [∀ i, IsScalarTower ℝ 𝕜 (W3 W₀ W₁ W₂ i)] in
/-- `L (0, E, 0) = (-d₀† E, 0, d₁ E)`: its components. -/
theorem wave_inj₁_zero (u : S.d₁.domain) (hu : (u : W₁) ∈ (S.d₀†).domain) :
    ((S.wave ⟨_, inj₁_mem_wave_domain (S := S) u.2 hu⟩ : PiLp 2 (W3 W₀ W₁ W₂)) 0 : W₀) =
      -(S.d₀† ⟨u, hu⟩) := by
  rw [S.wave_apply_zero]; rfl

omit [S₁.HasOrthogonalProjection] [S₂.HasOrthogonalProjection]
  [∀ i, NormedSpace ℝ (W3 W₀ W₁ W₂ i)] [∀ i, IsScalarTower ℝ 𝕜 (W3 W₀ W₁ W₂ i)] in
theorem wave_inj₁_one (u : S.d₁.domain) (hu : (u : W₁) ∈ (S.d₀†).domain) :
    ((S.wave ⟨_, inj₁_mem_wave_domain (S := S) u.2 hu⟩ : PiLp 2 (W3 W₀ W₁ W₂)) 1 : W₁) = 0 := by
  rw [S.wave_apply_one, LinearPMap.apply_eq_zero_of_coe_eq_zero (T := S.d₀) _ rfl,
    LinearPMap.apply_eq_zero_of_coe_eq_zero (T := S.d₁†) _ rfl, sub_zero]
  rfl

omit [S₁.HasOrthogonalProjection] [S₂.HasOrthogonalProjection]
  [∀ i, NormedSpace ℝ (W3 W₀ W₁ W₂ i)] [∀ i, IsScalarTower ℝ 𝕜 (W3 W₀ W₁ W₂ i)] in
theorem wave_inj₁_two (u : S.d₁.domain) (hu : (u : W₁) ∈ (S.d₀†).domain) :
    ((S.wave ⟨_, inj₁_mem_wave_domain (S := S) u.2 hu⟩ : PiLp 2 (W3 W₀ W₁ W₂)) 2 : W₂) =
      S.d₁ u := by
  rw [S.wave_apply_two]; rfl

/-- `d₁† (D(d₁†) ∩ S₂*) ⊆ S₁*`. -/
theorem adjoint_mem_invariantCore₁ (ρ : S.d₁†.domain) (hρ : (ρ : W₂) ∈ S.invariantCore₂ S₁ S₂) :
    S.d₁† ρ ∈ S.invariantCore₁ S₁ S₂ := by
  have hm := (isReducing_wave_coreSub (S := S) (S₁ := S₁) (S₂ := S₂)).mapsTo
    ⟨_, inj₂_mem_wave_domain (S := S) ρ.2⟩ (single_two_mem_totalSub_family3 _ _ _ hρ)
  rw [wave_inj₂] at hm
  have h1 : -(S.d₁† ρ) ∈ S.invariantCore₁ S₁ S₂ := (mem_totalSub_family3.1 hm).2.1
  exact (Submodule.neg_mem_iff _).1 h1

/-- **`{0} × S₁* × S₂*` is a reducing subcomplex** when `S₁ ⊆ N(d₀†)`: `(⊥, S₁*)` reduces `d₀`
because `R(d₀) ⊥ N(d₀†) ⊇ S₁*`, and `(S₁*, S₂*)` reduces `d₁` since `L` is reduced by `K*` on
the fields `(0, P_{N(d₀†)} u, 0) ∈ D(L)`. -/
theorem reducingSubcomplex_coreSub (hS₁ : S₁ ≤ (S.d₀†).ker) :
    S.toHilbertComplex.ReducingSubcomplex
      (family3 (⊥ : Submodule 𝕜 W₀) (S.invariantCore₁ S₁ S₂) (S.invariantCore₂ S₁ S₂)) := by
  have hker := hasOrthogonalProjection_ker S.d₀† (adjoint_isClosed S.dense₀)
  set N : Submodule 𝕜 W₁ := (S.d₀†).ker
  set S₁' := S.invariantCore₁ S₁ S₂
  set S₂' := S.invariantCore₂ S₁ S₂
  have hS₁' : S₁' ≤ N := invariantCore₁_le.trans hS₁
  -- `(N, ⊤)` reduces `d₁`: `Nᗮ ⊆ N(d₁)`
  have hN : S.d₁.IsReducingPair N (⊤ : Submodule 𝕜 W₂) :=
    isReducingPair_of_orthogonal_le_ker (S.toHilbertComplex.orthogonal_ker_adjoint_le_ker 0 1 2)
      fun _ => Submodule.mem_top
  have hred := isReducing_wave_coreSub (S := S) (S₁ := S₁) (S₂ := S₂)
  refine HilbertComplex.ReducingSubcomplex.of_rel fun i j hij => ?_
  fin_cases i <;> fin_cases j <;> simp at hij
  · change S.d₀.IsReducingPair (⊥ : Submodule 𝕜 W₀) S₁'
    refine isReducingPair_of_le_ker bot_le fun x => ?_
    rw [Submodule.mem_orthogonal]
    intro y hy
    obtain ⟨z, hz, hz0⟩ := mem_ker_iff.1 (hS₁' hy)
    have h := adjoint_isFormalAdjoint S.dense₀ z x
    rw [hz0, inner_zero_left] at h
    rw [hz]; exact h.symm
  · change S.d₁.IsReducingPair S₁' S₂'
    -- reduce to `y = P_N u ∈ D(d₁) ∩ N`
    have hPy : ∀ u : S.d₁.domain, S₁'.starProjection (N.starProjection (u : W₁)) =
        S₁'.starProjection (u : W₁) := fun u => by
      rw [← sub_eq_zero, ← _root_.map_sub]
      refine (Submodule.starProjection_apply_eq_zero_iff S₁').2
        (Submodule.orthogonal_le hS₁' ?_)
      rw [← neg_sub]
      exact Nᗮ.neg_mem (N.sub_starProjection_mem_orthogonal _)
    let y : S.d₁.domain → S.d₁.domain := fun u => ⟨_, hN.proj_mem u⟩
    have hyk : ∀ u, ((y u : S.d₁.domain) : W₁) ∈ (S.d₀†).domain :=
      fun u => (S.d₀†).ker_le_domain (N.starProjection_apply_mem _)
    have hP : ∀ u : S.d₁.domain, ((HilbertComplex.totalSub
        (family3 (⊥ : Submodule 𝕜 W₀) S₁' S₂')).starProjection
          (inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ (y u)) : PiLp 2 (W3 W₀ W₁ W₂)) 1 =
        S₁'.starProjection (u : W₁) := fun u => by
      rw [HilbertComplex.totalSub_starProjection_apply]
      exact hPy u
    have hd₁y : ∀ u, S.d₁ (y u) = S.d₁ u := fun u => by
      have := hN.comm u
      rw [Submodule.starProjection_top] at this
      exact this
    refine ⟨fun u => ?_, fun u => ?_⟩
    · have := ((S.mem_wave_domain).1
        (hred.proj_mem ⟨_, inj₁_mem_wave_domain (S := S) (y u).2 (hyk u)⟩)).2.1
      rwa [hP u] at this
    · have hc := hred.comm ⟨_, inj₁_mem_wave_domain (S := S) (y u).2 (hyk u)⟩
      have h2 := congrArg (fun z : PiLp 2 (W3 W₀ W₁ W₂) => (z 2 : W₂)) hc
      simp only at h2
      rw [HilbertComplex.totalSub_starProjection_apply, wave_inj₁_two (y u) (hyk u), hd₁y,
        S.wave_apply_two] at h2
      exact (LinearPMap.apply_congr' _ _ _ (hP u).symm).trans h2

/-! ### Stationary data and propagation -/

omit [S₁.HasOrthogonalProjection] [S₂.HasOrthogonalProjection] in
/-- A zero of the wave operator in `{0} × S₁ × S₂` lies in `K*`. -/
theorem mem_coreSub_of_wave_eq_zero (x : S.wave.domain)
    (hx : (x : PiLp 2 (W3 W₀ W₁ W₂)) ∈
      HilbertComplex.totalSub (family3 (⊥ : Submodule 𝕜 W₀) S₁ S₂))
    (h0 : S.wave x = 0) : (x : PiLp 2 (W3 W₀ W₁ W₂)) ∈ S.coreSub S₁ S₂ := by
  have key : ∀ (A : PiLp 2 (W3 W₀ W₁ W₂) →ₗ.[𝕜] PiLp 2 (W3 W₀ W₁ W₂)) (hA : A = S.wave),
      ∃ hx' : (x : PiLp 2 (W3 W₀ W₁ W₂)) ∈ A.domain, A ⟨_, hx'⟩ = 0 := by
    rintro _ rfl; exact ⟨x.2, h0⟩
  obtain ⟨hx', e⟩ := key _ S.toHilbertComplex.generator_waveGroup
  exact C0Group.mem_invariantCore_of_generator_eq_zero ⟨_, hx'⟩ hx e

omit [S₁.HasOrthogonalProjection] [S₂.HasOrthogonalProjection] in
/-- **Stationary magnetic data lie in `K*`**: if `B ∈ D(d₁†) ∩ S₂` and `d₁† B = 0`, then
`(0, 0, B)` is a stationary point of `U' = L U` in `K`, so `B ∈ S₂*`. -/
theorem mem_invariantCore₂_of_eq_zero (ρ : S.d₁†.domain) (hρ : (ρ : W₂) ∈ S₂)
    (h0 : S.d₁† ρ = 0) : (ρ : W₂) ∈ S.invariantCore₂ S₁ S₂ :=
  mem_coreSub_of_wave_eq_zero ⟨_, inj₂_mem_wave_domain (S := S) ρ.2⟩
    (single_two_mem_totalSub_family3 _ _ _ hρ) (by rw [wave_inj₂, h0, neg_zero, _root_.map_zero])

end Feec.ShortHilbertComplex
