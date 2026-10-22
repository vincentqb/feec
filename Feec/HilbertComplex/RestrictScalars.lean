module

public import Feec.ForMathlib.LinearPMap.RestrictScalars
public import Feec.HilbertComplex.Transport
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Complex Hilbert complexes viewed over `ℝ`

A Hilbert complex over `ℂ` whose spaces carry compatible real inner products
(`⟪x, y⟫_ℝ = re ⟪x, y⟫_ℂ`, e.g. `L²` spaces of `ℂⁿ`-valued fields) is a Hilbert complex over `ℝ`
with the same domains and differentials (`HilbertComplex.restrictScalars`). The adjoints commute
with the restriction of scalars (`LinearPMap.adjoint_restrictScalars`), so the dual complex, the
wave operator and the reducing subcomplexes are the same over `ℝ` and over `ℂ`. Over `ℝ`, the
real fields of a conjugation (an antilinear symmetry) form a reducing subcomplex, which they do
not over `ℂ`.

## Main definitions and results

* `HilbertComplex.restrictScalars H : HilbertComplex ℝ c W`.
* **`dual_restrictScalars`**: `(H_ℝ)* = (H*)_ℝ`; **`wave_restrictScalars`**: `L_ℝ = (L)_ℝ`.
* `Submodule.starProjection_restrictScalars`: the real and complex projections onto a complex
  subspace agree; **`ReducingSubcomplex.restrictScalars`**.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (real fields)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexConjugate
open RCLike LinearPMap

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [CompleteSpace E]

instance restrictScalars_hasOrthogonalProjection (K : Submodule ℂ E) [K.HasOrthogonalProjection] :
    (K.restrictScalars ℝ).HasOrthogonalProjection := by
  have hc : IsClosed ((K.restrictScalars ℝ : Submodule ℝ E) : Set E) := by
    rw [← Submodule.orthogonal_orthogonal K]; exact Submodule.isClosed_orthogonal _
  have : CompleteSpace (K.restrictScalars ℝ) := hc.completeSpace_coe
  infer_instance

/-- **The real and the complex orthogonal projections onto a complex subspace agree.** -/
theorem starProjection_restrictScalars (hre : ∀ x y : E, ⟪x, y⟫_ℝ = re ⟪x, y⟫_ℂ)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (x : E) :
    (K.restrictScalars ℝ).starProjection x = K.starProjection x := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (K := K.restrictScalars ℝ) (K.starProjection_apply_mem x) fun w hw => ?_
  rw [hre, K.starProjection_inner_eq_zero x w hw]
  simp

end Submodule

/-! ### Compatible real inner products -/

theorem EuclideanSpace.real_inner_eq_re_inner {ι : Type*} [Fintype ι]
    (v w : EuclideanSpace ℂ ι) : ⟪v, w⟫_ℝ = re ⟪v, w⟫_ℂ := by
  simp only [PiLp.inner_apply, Complex.inner, RCLike.inner_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]; rfl

/-- On `L²(μ; E)`, the real inner product is the real part of the complex one when this holds on
the fibre. -/
theorem MeasureTheory.L2.real_inner_eq_re_inner {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] (hE : ∀ v w : E, ⟪v, w⟫_ℝ = re ⟪v, w⟫_ℂ)
    (f g : MeasureTheory.Lp E 2 μ) : ⟪f, g⟫_ℝ = re ⟪f, g⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  simp_rw [hE]
  exact integral_re (MeasureTheory.L2.integrable_inner f g)

namespace Feec.HilbertComplex

variable {ι : Type*} {c : ComplexShape ι} {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace ℂ (W i)] [∀ i, CompleteSpace (W i)] [∀ i, InnerProductSpace ℝ (W i)]
  [∀ i, IsScalarTower ℝ ℂ (W i)] (H : HilbertComplex ℂ c W)

/-- **A complex Hilbert complex as a real one**: same domains and differentials. -/
def restrictScalars : HilbertComplex ℝ c W where
  d i j := (H.d i j).restrictScalars
  shape i j h := by rw [H.shape i j h]; exact LinearPMap.restrictScalars_zero
  dense i j := H.dense i j
  closed i j := (H.d i j).isClosed_restrictScalars (H.closed i j)
  mapsTo i j k x := H.mapsTo i j k ⟨x.1, x.2⟩
  d_comp_d i j k x := H.d_comp_d i j k ⟨x.1, x.2⟩

variable {H}

/-- **The dual of the real complex is the real dual complex.** -/
theorem dual_restrictScalars (hre : ∀ i (x y : W i), ⟪x, y⟫_ℝ = re ⟪x, y⟫_ℂ) :
    H.restrictScalars.dual = H.dual.restrictScalars :=
  ext_d (funext fun i => funext fun j =>
    (H.d j i).adjoint_restrictScalars (hre j) (hre i) (H.dense j i))

/-- The boundaries and cycles do not depend on the scalars. -/
theorem mem_cycles_restrictScalars {i : ι} {x : W i} :
    x ∈ H.restrictScalars.cycles i ↔ x ∈ H.cycles i := by
  simp only [cycles, LinearPMap.mem_ker_iff]
  exact ⟨fun ⟨y, h1, h2⟩ => ⟨⟨y.1, y.2⟩, h1, h2⟩, fun ⟨y, h1, h2⟩ => ⟨⟨y.1, y.2⟩, h1, h2⟩⟩

/-- **Reducing subcomplexes over `ℂ` are reducing over `ℝ`.** -/
theorem ReducingSubcomplex.restrictScalars (hre : ∀ i (x y : W i), ⟪x, y⟫_ℝ = re ⟪x, y⟫_ℂ)
    {S : ∀ i, Submodule ℂ (W i)} [∀ i, (S i).HasOrthogonalProjection]
    (h : H.ReducingSubcomplex S) :
    H.restrictScalars.ReducingSubcomplex fun i => (S i).restrictScalars ℝ := by
  refine ⟨fun i j => ⟨fun x => ?_, fun x => ?_⟩⟩
  · rw [Submodule.starProjection_restrictScalars (hre i)]
    exact (h.reduces i j).proj_mem ⟨x.1, x.2⟩
  · change H.d i j ⟨((S i).restrictScalars ℝ).starProjection (x : W i), _⟩ =
      ((S j).restrictScalars ℝ).starProjection (H.d i j ⟨x.1, x.2⟩)
    rw [Submodule.starProjection_restrictScalars (hre j)]
    refine Eq.trans ?_ ((h.reduces i j).comm ⟨x.1, x.2⟩)
    exact LinearPMap.apply_congr' _ _ _ (Submodule.starProjection_restrictScalars (hre i) _ _)

variable [Fintype ι]

/-- **The real wave operator is the complex one** (same domain, same values). -/
theorem wave_restrictScalars (hre : ∀ i (x y : W i), ⟪x, y⟫_ℝ = re ⟪x, y⟫_ℂ) :
    H.restrictScalars.wave = H.wave.restrictScalars := by
  have hdual := dual_restrictScalars (H := H) hre
  have hadj : ∀ i j, (H.restrictScalars.d i j)† = ((H.d i j)†).restrictScalars := fun i j =>
    (H.d i j).adjoint_restrictScalars (hre i) (hre j) (H.dense i j)
  have hdom : H.restrictScalars.wave.domain = H.wave.restrictScalars.domain := by
    ext x
    rw [mem_wave_domain, LinearPMap.mem_restrictScalars_domain, mem_wave_domain]
    refine and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun j => ?_)
    rw [hadj]; exact Iff.rfl
  refine LinearPMap.ext hdom fun x hx hx' => PiLp.ext fun j => ?_
  rw [wave_apply, LinearPMap.restrictScalars_apply, wave_apply]
  refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun i _ => rfl)
    (Finset.sum_congr rfl fun k _ => ?_)
  exact apply_eq_of_eq (hadj j k) _ ⟨_, (show x ∈ H.wave.domain from hx').2 k j⟩ rfl

end Feec.HilbertComplex
