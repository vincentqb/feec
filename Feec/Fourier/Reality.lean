module

public import Feec.Fourier.SymbolComplex
public import Feec.HilbertComplex.Reality

/-!
# Real fields in a symbol complex

A field `f` on `𝕋ᵈ` or `ℝᵈ` is real iff its Fourier coefficients satisfy `f̂(-ξ) = conj f̂(ξ)`. In
the symbol picture this is the antilinear involution `(C u)(a) = c (u (σ a))` with `σ` the
reflection `ξ ↦ -ξ` (measure preserving) and `c` a fibre conjugation. If the symbols are real,
`m (σ a) (c v) = c (m a v)`, the involutions form a conjugation of the Hilbert complex
(`Feec.HilbertComplex.Conj`), so real data give real solutions of the Hodge wave equation and the
wave group preserves real fields (`Feec.HilbertComplex.Conj.conj_eq`,
`Feec.HilbertComplex.Conj.totalConj_waveGroup`).

Reality is an antilinear condition: the real fields are not a `ℂ`-subspace, so this is not a
reducing subcomplex. It combines with any reducing subcomplex (constraint propagation) because
both properties hold for the same solution.

## Main definitions and results

* `Fourier.Reflection μ`: a measure-preserving involution; `Reflection.count_neg` (`k ↦ -k` on
  `ℤᵈ`) and `Reflection.neg` (`ξ ↦ -ξ` for a negation-invariant measure, e.g. Lebesgue).
* `Fourier.conjLp R c`: `u ↦ c ∘ u ∘ σ` on `L²(μ; E)`, with `coeFn_conjLp`.
* `SymbolComplex.RealStructure S R`: fibre conjugations with `m (σ a) ∘ c = c ∘ m a`, and
  **`RealStructure.toConj`**: the conjugation of the symbol Hilbert complex.
* `RealStructure.conj_eq`: **real data and forcing give real strong solutions**;
  `RealStructure.waveGroup_conj`: the wave group commutes with the conjugation.
* `Fourier.entryConj`: entrywise complex conjugation on `EuclideanSpace ℂ ι`.

## References

* [QuennevilleBelair2015], §4.10 (real-valued fields in Prop 4.17)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexConjugate ENNReal
open MeasureTheory LinearPMap Set

namespace Feec.Fourier

/-! ### Reflections of the frequency space -/

/-- A **reflection** of the frequency space: a measure-preserving involution (`ξ ↦ -ξ`). -/
structure Reflection {α : Type*} [MeasurableSpace α] (μ : Measure α) where
  /-- the involution -/
  σ : α → α
  measurePreserving : MeasurePreserving σ μ μ
  invol : ∀ a, σ (σ a) = a

namespace Reflection

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} (R : Reflection μ)

theorem measurable : Measurable R.σ := R.measurePreserving.measurable

/-- A reflection is a measurable equivalence. -/
def toMeasurableEquiv : α ≃ᵐ α where
  toFun := R.σ
  invFun := R.σ
  left_inv := R.invol
  right_inv := R.invol
  measurable_toFun := R.measurable
  measurable_invFun := R.measurable

theorem measurableEmbedding : MeasurableEmbedding R.σ := R.toMeasurableEquiv.measurableEmbedding

/-- Pull an a.e. property back along the reflection. -/
theorem ae_comp {p : α → Prop} (h : ∀ᵐ a ∂μ, p a) : ∀ᵐ a ∂μ, p (R.σ a) :=
  R.measurePreserving.quasiMeasurePreserving.ae h

theorem integral_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (g : α → G) :
    ∫ a, g (R.σ a) ∂μ = ∫ a, g a ∂μ :=
  R.measurePreserving.integral_comp R.measurableEmbedding g

/-- `k ↦ -k` on a countable additive group with the counting measure (`ℤᵈ`). -/
def count_neg {β : Type*} [AddGroup β] [MeasurableSpace β] [MeasurableSingletonClass β]
    [Countable β] : Reflection (Measure.count : Measure β) where
  σ := Neg.neg
  measurePreserving := by
    refine ⟨measurable_neg, ?_⟩
    ext s hs
    rw [Measure.map_apply measurable_neg hs, Measure.count_apply (hs.preimage measurable_neg),
      Measure.count_apply hs]
    have e : Neg.neg ⁻¹' s = Neg.neg '' s :=
      congrFun (Set.image_eq_preimage_of_inverse (f := (Neg.neg : β → β)) (g := Neg.neg)
        (fun x => neg_neg x) (fun x => neg_neg x)).symm s
    rw [e, neg_injective.encard_image]
  invol := neg_neg

/-- `ξ ↦ -ξ` for a negation-invariant measure (Lebesgue measure on `ℝᵈ`). -/
def neg {β : Type*} [AddGroup β] [MeasurableSpace β] [MeasurableNeg β] (ν : Measure β)
    [ν.IsNegInvariant] : Reflection ν where
  σ := Neg.neg
  measurePreserving := Measure.measurePreserving_neg ν
  invol := neg_neg

end Reflection

/-! ### The conjugation of `L²` -/

section ConjLp

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E]

/-- `u ↦ c ∘ u ∘ σ` on `L²(μ; E)`, for a reflection `σ` and a real-linear map `c`. -/
def conjLp (R : Reflection μ) (c : E →L[ℝ] E) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  (c.compLpL 2 μ).comp (Lp.compMeasurePreservingₗᵢ ℝ R.σ R.measurePreserving).toContinuousLinearMap

theorem coeFn_conjLp (R : Reflection μ) (c : E →L[ℝ] E) (u : Lp E 2 μ) :
    conjLp R c u =ᵐ[μ] fun a => c (u (R.σ a)) := by
  have h1 := c.coeFn_compLpL (p := 2) (μ := μ)
    (Lp.compMeasurePreservingₗᵢ ℝ R.σ R.measurePreserving u)
  have h2 := Lp.coeFn_compMeasurePreserving u R.measurePreserving
  filter_upwards [h1, h2] with a h1 h2
  change (c.compLpL 2 μ (Lp.compMeasurePreservingₗᵢ ℝ R.σ R.measurePreserving u)) a = _
  rw [h1]
  exact congrArg c h2

/-- The reflected conjugate, a.e. at the reflected point. -/
theorem coeFn_conjLp_comp (R : Reflection μ) (c : E →L[ℝ] E) (u : Lp E 2 μ) :
    ∀ᵐ a ∂μ, conjLp R c u (R.σ a) = c (u a) := by
  filter_upwards [R.ae_comp (coeFn_conjLp R c u)] with a h
  rw [h, R.invol]

end ConjLp

/-! ### Real structures of symbol complexes -/

namespace SymbolComplex

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
  {c : ComplexShape ι} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace 𝕜 (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- A **real structure** on a symbol complex: fibre conjugations `c i` (antilinear involutions
with `⟪c x, c y⟫ = ⟪y, x⟫`) and a reflection `σ` with `m (σ a) (c v) = c (m a v)` (real
symbols). -/
structure RealStructure (S : SymbolComplex 𝕜 μ c E) (R : Reflection μ) where
  /-- the fibre conjugations -/
  cj : ∀ i, E i →L[ℝ] E i
  antilinear : ∀ i (a : 𝕜) (v : E i), cj i (a • v) = (starRingEnd 𝕜) a • cj i v
  invol : ∀ i (v : E i), cj i (cj i v) = v
  inner_cj : ∀ i (v w : E i), ⟪cj i v, cj i w⟫_𝕜 = ⟪w, v⟫_𝕜
  symm : ∀ i j a (v : E i), S.m i j (R.σ a) (cj i v) = cj j (S.m i j a v)

variable {S : SymbolComplex 𝕜 μ c E} {R : Reflection μ} (K : S.RealStructure R)

/-- The symbol relation read at the reflected point. -/
theorem RealStructure.symm' (i j : ι) (a : α) (v : E i) :
    S.m i j a (K.cj i v) = K.cj j (S.m i j (R.σ a) v) := by
  have := K.symm i j (R.σ a) v
  rwa [R.invol] at this

variable [∀ i, CompleteSpace (E i)]

/-- The domains are preserved, with `d (C u) = C (d u)` a.e. -/
theorem RealStructure.ae_mulOp (i j : ι) (u : (S.toHilbertComplex.d i j).domain) :
    (fun a => S.m i j a (conjLp R (K.cj i) (u : Lp (E i) 2 μ) a)) =ᵐ[μ]
      conjLp R (K.cj j) (S.toHilbertComplex.d i j u) := by
  filter_upwards [coeFn_conjLp R (K.cj i) (u : Lp (E i) 2 μ),
    coeFn_conjLp R (K.cj j) (S.toHilbertComplex.d i j u),
    R.ae_comp (S.coeFn_d u)] with a h1 h2 h3
  rw [h1, h2, h3, K.symm']

/-- **The conjugation of the symbol Hilbert complex** defined by a real structure. -/
def RealStructure.toConj : S.toHilbertComplex.Conj where
  C i := conjLp R (K.cj i)
  antilinear i a u := by
    refine Lp.ext ?_
    filter_upwards [coeFn_conjLp R (K.cj i) (a • u), coeFn_conjLp R (K.cj i) u,
      Lp.coeFn_smul ((starRingEnd 𝕜) a) (conjLp R (K.cj i) u),
      R.ae_comp (Lp.coeFn_smul a u)] with x h1 h2 h3 h4
    rw [h1, h3, Pi.smul_apply, h2, h4, Pi.smul_apply, K.antilinear]
  invol i u := by
    refine Lp.ext ?_
    filter_upwards [coeFn_conjLp R (K.cj i) (conjLp R (K.cj i) u),
      coeFn_conjLp_comp R (K.cj i) u] with x h1 h2
    rw [h1, h2, K.invol]
  inner_C i u w := by
    rw [L2.inner_def, L2.inner_def]
    have : (fun a => ⟪conjLp R (K.cj i) u a, conjLp R (K.cj i) w a⟫_𝕜) =ᵐ[μ]
        fun a => ⟪(w : Lp (E i) 2 μ) (R.σ a), u (R.σ a)⟫_𝕜 := by
      filter_upwards [coeFn_conjLp R (K.cj i) u, coeFn_conjLp R (K.cj i) w] with a h1 h2
      rw [h1, h2, K.inner_cj]
    rw [integral_congr_ae this]
    exact R.integral_comp fun a => ⟪(w : Lp (E i) 2 μ) a, u a⟫_𝕜
  mapsTo i j u := (Lp.memLp _).ae_eq (K.ae_mulOp i j u).symm
  comm i j u := (Operator.mulOp_apply_eq_iff _ _).2 (K.ae_mulOp i j u)

@[simp] theorem RealStructure.toConj_C (i : ι) :
    K.toConj.C i = conjLp R (K.cj i) := rfl

variable [Fintype ι]

/-- **Real data give real solutions**: if the data and the forcing are fixed by the conjugation,
so is every strong solution of the Hodge wave equation of the symbol complex. -/
theorem RealStructure.conj_eq {a b : ℝ} {F U : ℝ → PiLp 2 fun i => Lp (E i) 2 μ}
    (hU : Evolution.IsStrongSolution S.toHilbertComplex.wave (Icc a b) F U)
    (h0 : K.toConj.totalConj (U a) = U a)
    (hF : ∀ t ∈ Icc a b, K.toConj.totalConj (F t) = F t) :
    ∀ t ∈ Icc a b, K.toConj.totalConj (U t) = U t :=
  K.toConj.conj_eq hU h0 hF

variable [∀ i, IsScalarTower ℝ 𝕜 (E i)]

/-- The wave group of a symbol complex with a real structure maps real data to real data. -/
theorem RealStructure.waveGroup_conj (t : ℝ) (x : PiLp 2 fun i => Lp (E i) 2 μ) :
    K.toConj.totalConj (S.toHilbertComplex.waveGroup.S t x) =
      S.toHilbertComplex.waveGroup.S t (K.toConj.totalConj x) :=
  K.toConj.totalConj_waveGroup t x

end SymbolComplex

/-! ### Entrywise conjugation -/

section Entry

variable {ι : Type*} [Fintype ι]

/-- Entrywise complex conjugation on `ℂ^ι`, a real-linear involution. -/
def entryConj : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 fun i => conj (v i)
      map_add' := fun v w => by ext i; simp
      map_smul' := fun r v => by ext i; simp [Complex.real_smul] }

@[simp] theorem entryConj_apply (v : EuclideanSpace ℂ ι) (i : ι) :
    entryConj v i = conj (v i) := rfl

theorem entryConj_smul (a : ℂ) (v : EuclideanSpace ℂ ι) :
    entryConj (a • v) = conj a • entryConj v := by
  ext i; simp

theorem entryConj_entryConj (v : EuclideanSpace ℂ ι) : entryConj (entryConj v) = v := by
  ext i; simp

theorem inner_entryConj (v w : EuclideanSpace ℂ ι) :
    ⟪entryConj v, entryConj w⟫_ℂ = ⟪w, v⟫_ℂ := by
  simp only [PiLp.inner_apply, entryConj_apply, RCLike.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

end Entry

end Feec.Fourier
