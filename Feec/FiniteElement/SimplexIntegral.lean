module

public import Feec.FiniteElement.SmoothForm
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Integration of differential forms over affine simplices

The reference `k`-simplex is `T̂_k = {x̂ ∈ ℝᵏ | x̂ᵢ ≥ 0, Σᵢ x̂ᵢ ≤ 1}`, with vertices
`v̂₀ = 0`, `v̂ᵢ₊₁ = eᵢ` and barycentric coordinates `λ̂(x̂) = (1 - Σᵢ x̂ᵢ, x̂₀, …, x̂_{k-1})`. An
oriented affine `k`-simplex in `ℝⁿ` is an ordered family of vertices `p₀, …, p_k`
(e.g. the points of a Mathlib `Affine.Simplex ℝ (Fin n → ℝ) k`); it is parametrized by the affine
map `F_p(x̂) = Σᵢ λ̂ᵢ(x̂) pᵢ = p₀ + Σᵢ x̂ᵢ (pᵢ₊₁ - p₀)` of `T̂_k` onto its convex hull. The integral
of a `k`-form `ω` over it is defined by pullback, without any surface measure:

  `∫_p ω = ∫_{T̂_k} (F_p^* ω)_{univ} dx̂`.

This is the integral of [AFW2006], §2 and [Arnold2018], Ch. 6 for a simplex oriented by the
order of its vertices. For degenerate (affinely dependent) vertex families the pullback vanishes
and so does the integral.

## Main definitions

* `Feec.FiniteElement.refSimplex k`, `refBary`, `refVertex`;
* `Feec.FiniteElement.simplexMatrix p`, `simplexMap p`: the parametrization `F_p`;
* `Feec.FiniteElement.simplexIntegral p ω`: the integral of the form `ω` over the oriented
  simplex `p`.

## Main results

* `setIntegral_refSimplex_succ`: Fubini on the reference simplex, slicing along any coordinate;
* `volume_real_refSimplex`: `|T̂_k| = 1 / k!`;
* `simplexIntegral_comp_affine`: invariance under affine maps, `∫_{G ∘ p} ω = ∫_p G^* ω`;
* `simplexIntegral_comp_perm`: **independence of the parametrization**, up to the orientation:
  `∫_{p ∘ π} ω = sign π · ∫_p ω` for every permutation `π` of the vertices;
* `simplexIntegral_add`, `simplexIntegral_smul`, `simplexIntegral_sum`: linearity, and
  `simplexIntegral_add_of_simplexIntegrable` under the integrability hypothesis
  `SimplexIntegrable`;
* `abs_simplexIntegral_le`: `|∫_p ω| ≤ (Σ_s |minor_s(F_p)|) · sup |ω| / k!` (by Cauchy–Binet
  `Σ_s |minor_s| ≥ k! vol_k`, so this is weaker than `vol_k · sup |ω|` when `k < n`);
* `volume_real_image_simplexMap`: `|F_p(T̂)| = |det B_p| / n!`, and
  `abs_simplexIntegral_le_volume_mul`: `|∫_T ω| ≤ |T| · sup_T |ω|` for `n`-simplices in `ℝⁿ`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §2 (integration of differential forms)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MeasureTheory

@[expose] public noncomputable section

namespace Feec.FiniteElement

open ExteriorFibre

variable {n m k : ℕ}

/-! ### The reference simplex -/

/-- The barycentric coordinates `λ̂(x̂) = (1 - Σᵢ x̂ᵢ, x̂₀, …, x̂_{k-1})` on `ℝᵏ`. -/
def refBary (x : Fin k → ℝ) : Fin (k + 1) → ℝ := Fin.cons (1 - ∑ i, x i) x

@[simp] theorem refBary_zero (x : Fin k → ℝ) : refBary x 0 = 1 - ∑ i, x i := rfl

@[simp] theorem refBary_succ (x : Fin k → ℝ) (i : Fin k) : refBary x i.succ = x i := rfl

theorem sum_refBary (x : Fin k → ℝ) : ∑ i, refBary x i = 1 := by
  rw [Fin.sum_univ_succ]; simp

/-- The reference `k`-simplex `T̂_k = {x̂ | λ̂ᵢ(x̂) ≥ 0}`. -/
def refSimplex (k : ℕ) : Set (Fin k → ℝ) := {x | ∀ i, 0 ≤ refBary x i}

theorem mem_refSimplex_iff {x : Fin k → ℝ} :
    x ∈ refSimplex k ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 := by
  change (∀ i, 0 ≤ refBary x i) ↔ _
  simp only [Fin.forall_fin_succ, refBary_zero, refBary_succ, sub_nonneg]
  tauto

theorem continuous_refBary_apply (i : Fin (k + 1)) :
    Continuous fun x : Fin k → ℝ => refBary x i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [refBary_zero]; fun_prop
  · simp only [refBary_succ]; fun_prop

theorem isClosed_refSimplex (k : ℕ) : IsClosed (refSimplex k) := by
  have : refSimplex k = ⋂ i, {x : Fin k → ℝ | 0 ≤ refBary x i} := by
    ext x; simp [refSimplex]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_refBary_apply i)

theorem measurableSet_refSimplex (k : ℕ) : MeasurableSet (refSimplex k) :=
  (isClosed_refSimplex k).measurableSet

theorem refSimplex_subset_pi (k : ℕ) :
    refSimplex k ⊆ Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1 := by
  intro x hx i _
  obtain ⟨h0, h1⟩ := mem_refSimplex_iff.1 hx
  refine ⟨h0 i, le_trans ?_ h1⟩
  exact single_le_sum (fun j _ => h0 j) (mem_univ i)

theorem isCompact_refSimplex (k : ℕ) : IsCompact (refSimplex k) :=
  (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset (isClosed_refSimplex k)
    (refSimplex_subset_pi k)

/-- The vertices `v̂₀ = 0`, `v̂ᵢ₊₁ = eᵢ` of the reference simplex. -/
def refVertex (k : ℕ) : Fin (k + 1) → Fin k → ℝ := Fin.cons 0 fun i => Pi.single i 1

@[simp] theorem refVertex_zero : refVertex k 0 = 0 := rfl

@[simp] theorem refVertex_succ (i : Fin k) : refVertex k i.succ = Pi.single i 1 := rfl

/-- `λ̂ⱼ(v̂ᵢ) = δᵢⱼ`. -/
theorem refBary_refVertex (i j : Fin (k + 1)) :
    refBary (refVertex k i) j = if i = j then 1 else 0 := by
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [(Fin.succ_ne_zero j).symm]
  · simp [Fin.succ_ne_zero i]
  · simp [Pi.single_apply, eq_comm]

/-- The point with barycentric coordinates `c` (`Σ c = 1`) is `Σᵢ cᵢ v̂ᵢ`. -/
theorem refBary_sum_smul_refVertex {c : Fin (k + 1) → ℝ} (hc : ∑ i, c i = 1) :
    refBary (∑ i, c i • refVertex k i) = c := by
  have h : ∑ i, c i • refVertex k i = fun j => c j.succ := by
    funext j
    rw [Fin.sum_univ_succ]
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h]
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Fin.sum_univ_succ] at hc
    simp only [refBary_zero]; linarith
  · rfl

theorem refVertex_mem_refSimplex (i : Fin (k + 1)) : refVertex k i ∈ refSimplex k := by
  intro j; rw [refBary_refVertex]; split_ifs <;> norm_num

/-! ### Fubini on the reference simplex -/

theorem sum_insertNth (j : Fin (m + 1)) (t : ℝ) (y : Fin m → ℝ) :
    ∑ i, Fin.insertNth j t y i = t + ∑ i, y i := by
  rw [Fin.sum_univ_succAbove _ j]; simp

theorem insertNth_mem_refSimplex_iff (j : Fin (m + 1)) (t : ℝ) (y : Fin m → ℝ) :
    Fin.insertNth j t y ∈ refSimplex (m + 1) ↔
      y ∈ refSimplex m ∧ t ∈ Set.Icc (0 : ℝ) (1 - ∑ i, y i) := by
  rw [mem_refSimplex_iff, mem_refSimplex_iff, Fin.forall_iff_succAbove j, sum_insertNth]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Set.mem_Icc]
  constructor
  · rintro ⟨⟨ht, hy⟩, hs⟩
    exact ⟨⟨hy, by linarith⟩, ht, by linarith⟩
  · rintro ⟨⟨hy, -⟩, ht, hs⟩
    exact ⟨⟨ht, hy⟩, by linarith⟩

/-- **Fubini on the reference simplex**, slicing along the coordinate `j`:
`∫_{T̂_{m+1}} g = ∫_{ŷ ∈ T̂_m} ∫_0^{1 - Σ ŷ} g(ŷ with t inserted at j) dt dŷ`. -/
theorem setIntegral_refSimplex_succ (j : Fin (m + 1)) {g : (Fin (m + 1) → ℝ) → ℝ}
    (hg : IntegrableOn g (refSimplex (m + 1))) :
    ∫ x in refSimplex (m + 1), g x =
      ∫ y in refSimplex m, ∫ t in (0 : ℝ)..(1 - ∑ i, y i), g (Fin.insertNth j t y) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j
  have he : MeasurePreserving e.symm := (volume_preserving_piFinSuccAbove _ j).symm e
  have hes : ∀ z : ℝ × (Fin m → ℝ), e.symm z = Fin.insertNth j z.1 z.2 := fun z => rfl
  set G := (refSimplex (m + 1)).indicator g
  have hG : Integrable G := (integrable_indicator_iff (measurableSet_refSimplex _)).2 hg
  have hGe : Integrable (fun z => G (e.symm z)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (he.integrable_comp_emb e.symm.measurableEmbedding).2 hG
  rw [← integral_indicator (measurableSet_refSimplex _), ← he.integral_comp' G,
    Measure.volume_eq_prod, integral_prod_symm _ hGe,
    ← integral_indicator (measurableSet_refSimplex _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hes, G]
  by_cases hy : y ∈ refSimplex m
  · rw [Set.indicator_of_mem hy]
    have : (fun t => (refSimplex (m + 1)).indicator g (Fin.insertNth j t y)) =
        (Set.Icc (0 : ℝ) (1 - ∑ i, y i)).indicator fun t => g (Fin.insertNth j t y) := by
      funext t
      by_cases ht : t ∈ Set.Icc (0 : ℝ) (1 - ∑ i, y i)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem
          ((insertNth_mem_refSimplex_iff j t y).2 ⟨hy, ht⟩)]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem
          (fun h => ht ((insertNth_mem_refSimplex_iff j t y).1 h).2)]
    rw [this, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le]
    obtain ⟨-, h1⟩ := mem_refSimplex_iff.1 hy
    linarith
  · rw [Set.indicator_of_notMem hy]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t => ?_)
    exact Set.indicator_of_notMem (fun h => hy ((insertNth_mem_refSimplex_iff j t y).1 h).1) _

/-- `∫_{T̂_m} (1 - Σ x̂)^r dx̂ = r! / (r + m)!`. -/
theorem setIntegral_refSimplex_one_sub_sum_pow (m r : ℕ) :
    ∫ x in refSimplex m, (1 - ∑ i, x i) ^ r = (r.factorial : ℝ) / (r + m).factorial := by
  induction m generalizing r with
  | zero =>
    have : refSimplex 0 = Set.univ := by
      ext x; simp [mem_refSimplex_iff]
    rw [this, Measure.restrict_univ, show (volume : Measure (Fin 0 → ℝ)) = Measure.dirac 0 from
      Measure.pi_of_empty _ 0]
    simp
    exact (div_self (by positivity)).symm
  | succ m ih =>
    have hc : Continuous fun x : Fin (m + 1) → ℝ => (1 - ∑ i, x i) ^ r := by fun_prop
    rw [setIntegral_refSimplex_succ (Fin.last m)
      (hc.continuousOn.integrableOn_compact (isCompact_refSimplex _))]
    have hin : ∀ y : Fin m → ℝ, ∫ t in (0 : ℝ)..(1 - ∑ i, y i),
        (1 - ∑ i, Fin.insertNth (Fin.last m) t y i) ^ r =
          (1 - ∑ i, y i) ^ (r + 1) / (r + 1) := by
      intro y
      simp only [sum_insertNth]
      have : ∀ t : ℝ, (1 - (t + ∑ i, y i)) ^ r = (1 - ∑ i, y i - t) ^ r := fun t => by ring_nf
      simp only [this]
      rw [intervalIntegral.integral_comp_sub_left (fun t => t ^ r), integral_pow]
      simp
    simp only [hin]
    rw [integral_div, ih (r + 1)]
    rw [show r + 1 + m = r + (m + 1) by ring, Nat.factorial_succ r]
    push_cast
    field_simp

/-- **The volume of the reference simplex**: `|T̂_k| = 1 / k!`. -/
theorem volume_real_refSimplex (k : ℕ) : volume.real (refSimplex k) = 1 / k.factorial := by
  have := setIntegral_refSimplex_one_sub_sum_pow k 0
  simpa using this

theorem volume_refSimplex_lt_top (k : ℕ) : volume (refSimplex k) < ⊤ :=
  (isCompact_refSimplex k).measure_lt_top

/-! ### Parametrization of an affine simplex and the integral of a form -/

/-- The edge matrix of an ordered vertex family: its columns are the edges `pₗ₊₁ - p₀`. -/
def simplexMatrix (p : Fin (k + 1) → Fin n → ℝ) : Fin n → Fin k → ℝ :=
  fun i l => p l.succ i - p 0 i

/-- The affine parametrization `F_p(x̂) = p₀ + Σₗ x̂ₗ (pₗ₊₁ - p₀)` of the simplex `p` by `T̂_k`. -/
def simplexMap (p : Fin (k + 1) → Fin n → ℝ) : (Fin k → ℝ) → Fin n → ℝ :=
  affine (simplexMatrix p) (p 0)

/-- `F_p(x̂) = Σᵢ λ̂ᵢ(x̂) pᵢ`. -/
theorem simplexMap_eq_sum (p : Fin (k + 1) → Fin n → ℝ) (x : Fin k → ℝ) :
    simplexMap p x = ∑ i, refBary x i • p i := by
  funext j
  simp only [simplexMap, affine_apply, simplexMatrix, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Fin.sum_univ_succ, refBary_zero, refBary_succ, Finset.sum_sub_distrib,
    sub_mul, one_mul, Finset.sum_mul]
  simp only [mul_comm (x _) _]
  ring

/-- `F_p(T̂_k)` lies in the convex hull of the vertices. -/
theorem simplexMap_mem_convexHull (p : Fin (k + 1) → Fin n → ℝ) {x : Fin k → ℝ}
    (hx : x ∈ refSimplex k) : simplexMap p x ∈ convexHull ℝ (Set.range p) := by
  rw [simplexMap_eq_sum]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hx i) (sum_refBary x)
    fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩

/-- `F_p(v̂ᵢ) = pᵢ`. -/
theorem simplexMap_refVertex (p : Fin (k + 1) → Fin n → ℝ) (i : Fin (k + 1)) :
    simplexMap p (refVertex k i) = p i := by
  rw [simplexMap_eq_sum]
  simp_rw [refBary_refVertex, ite_smul, one_smul, zero_smul]
  simp

theorem continuous_simplexMap (p : Fin (k + 1) → Fin n → ℝ) : Continuous (simplexMap p) :=
  continuous_affine _ _

/-- The edge matrix of an affine image `G ∘ q` (`G(y) = C y + c`) is `C` times that of `q`. -/
theorem simplexMatrix_comp_affine (C : Fin m → Fin n → ℝ) (c : Fin m → ℝ)
    (q : Fin (k + 1) → Fin n → ℝ) :
    simplexMatrix (fun i => affine C c (q i)) = fun j l => ∑ i, C j i * simplexMatrix q i l := by
  funext j l
  simp only [simplexMatrix, affine_apply, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Affine maps commute with the parametrization: `F_{G ∘ q} = G ∘ F_q`. -/
theorem simplexMap_comp_affine (C : Fin m → Fin n → ℝ) (c : Fin m → ℝ)
    (q : Fin (k + 1) → Fin n → ℝ) (x : Fin k → ℝ) :
    simplexMap (fun i => affine C c (q i)) x = affine C c (simplexMap q x) := by
  rw [simplexMap, simplexMap, affine_comp, simplexMatrix_comp_affine]

/-- **The integral of a `k`-form over an oriented affine `k`-simplex** `p = (p₀, …, p_k)` in
`ℝⁿ`: `∫_p ω = ∫_{T̂_k} (F_p^* ω)_{univ}`, the coefficient of `dx̂₀ ∧ ⋯ ∧ dx̂_{k-1}` of the pullback
by the parametrization `F_p`. For a Mathlib simplex `σ : Affine.Simplex ℝ (Fin n → ℝ) k` the
integral over `σ` is `simplexIntegral σ.points ω`. -/
def simplexIntegral (p : Fin (k + 1) → Fin n → ℝ) (ω : FormField n) : ℝ :=
  ∫ x in refSimplex k, affinePullback (simplexMatrix p) (p 0) ω x univ

theorem simplexIntegral_def (p : Fin (k + 1) → Fin n → ℝ) (ω : FormField n) :
    simplexIntegral p ω = ∫ x in refSimplex k,
      ∑ s, ω (simplexMap p x) s * wedgeProd (simplexMatrix p) s univ := by
  simp only [simplexIntegral, affinePullback_apply, pullback_apply]
  rfl

/-- **Affine invariance**: `∫_{G ∘ q} ω = ∫_q G^* ω` for every affine map `G(y) = C y + c`. -/
theorem simplexIntegral_comp_affine (C : Fin m → Fin n → ℝ) (c : Fin m → ℝ)
    (q : Fin (k + 1) → Fin n → ℝ) (ω : FormField m) :
    simplexIntegral (fun i => affine C c (q i)) ω = simplexIntegral q (affinePullback C c ω) := by
  simp only [simplexIntegral, affinePullback_affinePullback, simplexMatrix_comp_affine]

theorem simplexMatrix_refVertex :
    simplexMatrix (refVertex k) = fun i j => if i = j then 1 else 0 := by
  funext i j
  simp [simplexMatrix, Pi.single_apply]

/-- On the reference simplex itself the integral is the Lebesgue integral of the top
coefficient. -/
theorem simplexIntegral_refVertex (η : FormField k) :
    simplexIntegral (refVertex k) η = ∫ x in refSimplex k, η x univ := by
  have ha : ∀ x, affine (fun i j : Fin k => if i = j then (1 : ℝ) else 0) 0 x = x := by
    intro x; funext i
    simp [affine_apply]
  simp only [simplexIntegral, affinePullback_apply, simplexMatrix_refVertex, refVertex_zero, ha,
    pullback_id]

/-- `∫_p ω` is the integral of the pullback `F_p^* ω` over the reference simplex. -/
theorem simplexIntegral_eq_refVertex (p : Fin (k + 1) → Fin n → ℝ) (ω : FormField n) :
    simplexIntegral p ω =
      simplexIntegral (refVertex k) (affinePullback (simplexMatrix p) (p 0) ω) := by
  rw [simplexIntegral_refVertex]; rfl

/-! ### Measure-preserving affine maps -/

/-- An affine self-map of `ℝᵏ` with `|det| = 1` preserves the Lebesgue measure. -/
theorem measurePreserving_affine {B : Fin k → Fin k → ℝ} (hB : |(Matrix.of B).det| = 1)
    (b : Fin k → ℝ) : MeasurePreserving (affine B b) := by
  have hdet : LinearMap.det (Matrix.toLin' (Matrix.of B)) ≠ 0 := by
    rw [LinearMap.det_toLin']; intro h; rw [h] at hB; simp at hB
  have hlin : MeasurePreserving (Matrix.toLin' (Matrix.of B)) := by
    refine ⟨(Matrix.toLin' (Matrix.of B)).continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, LinearMap.det_toLin', abs_inv, hB]
    simp
  have : affine B b = (fun y => y + b) ∘ Matrix.toLin' (Matrix.of B) := by
    funext y i
    simp [affine_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [this]
  exact (measurePreserving_add_right volume b).comp hlin

/-! ### Permutations of the vertices -/

/-- The affine self-map `x̂ ↦ F_{v̂ ∘ π}(x̂)` of `ℝᵏ` sending `v̂ᵢ` to `v̂_{π i}`. -/
def permMap (π : Equiv.Perm (Fin (k + 1))) : (Fin k → ℝ) → Fin k → ℝ :=
  simplexMap (refVertex k ∘ π)

/-- `permMap π` permutes the barycentric coordinates: `λ̂(A_π x̂) = λ̂(x̂) ∘ π⁻¹`. -/
theorem refBary_permMap (π : Equiv.Perm (Fin (k + 1))) (x : Fin k → ℝ) :
    refBary (permMap π x) = refBary x ∘ π.symm := by
  rw [permMap, simplexMap_eq_sum]
  have : ∑ i, refBary x i • (refVertex k ∘ π) i = ∑ j, refBary x (π.symm j) • refVertex k j := by
    rw [← Equiv.sum_comp π (fun j => refBary x (π.symm j) • refVertex k j)]
    simp
  rw [this, refBary_sum_smul_refVertex]
  · rfl
  · rw [Equiv.sum_comp π.symm (refBary x), sum_refBary]

theorem permMap_preimage_refSimplex (π : Equiv.Perm (Fin (k + 1))) :
    permMap π ⁻¹' refSimplex k = refSimplex k := by
  ext x
  change (∀ i, 0 ≤ refBary (permMap π x) i) ↔ ∀ i, 0 ≤ refBary x i
  simp only [refBary_permMap, Function.comp_apply]
  exact (π.forall_congr_left (p := fun i => 0 ≤ refBary x i)).symm

theorem permMap_mul (π ρ : Equiv.Perm (Fin (k + 1))) (x : Fin k → ℝ) :
    permMap (π * ρ) x = permMap π (permMap ρ x) := by
  have : (refVertex k ∘ (π * ρ)) = fun i => affine (simplexMatrix (refVertex k ∘ π))
      ((refVertex k ∘ π) 0) ((refVertex k ∘ ρ) i) := by
    funext i
    exact (simplexMap_refVertex (refVertex k ∘ π) (ρ i)).symm
  rw [permMap, this, simplexMap_comp_affine]
  rfl

theorem permMap_one (x : Fin k → ℝ) : permMap 1 x = x := by
  rw [permMap, simplexMap_eq_sum]
  have : refVertex k ∘ (1 : Equiv.Perm (Fin (k + 1))) = refVertex k := rfl
  rw [this]
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ, refVertex_zero,
    Pi.zero_apply, mul_zero, refVertex_succ, refBary_succ, zero_add]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

/-- The determinant of the linear part of `permMap π`. -/
def permDet (π : Equiv.Perm (Fin (k + 1))) : ℝ :=
  (Matrix.of (simplexMatrix (refVertex k ∘ π))).det

theorem simplexMatrix_perm_mul (π ρ : Equiv.Perm (Fin (k + 1))) :
    simplexMatrix (refVertex k ∘ (π * ρ)) = fun j l =>
      ∑ i, simplexMatrix (refVertex k ∘ π) j i * simplexMatrix (refVertex k ∘ ρ) i l := by
  have : (refVertex k ∘ (π * ρ)) = fun i => affine (simplexMatrix (refVertex k ∘ π))
      ((refVertex k ∘ π) 0) ((refVertex k ∘ ρ) i) := by
    funext i
    exact (simplexMap_refVertex (refVertex k ∘ π) (ρ i)).symm
  rw [this, simplexMatrix_comp_affine]

theorem permDet_mul (π ρ : Equiv.Perm (Fin (k + 1))) :
    permDet (π * ρ) = permDet π * permDet ρ := by
  rw [permDet, permDet, permDet, ← Matrix.det_mul, simplexMatrix_perm_mul]
  rfl

theorem permDet_one : permDet (1 : Equiv.Perm (Fin (k + 1))) = 1 := by
  rw [permDet, show refVertex k ∘ (1 : Equiv.Perm (Fin (k + 1))) = refVertex k from rfl,
    simplexMatrix_refVertex]
  rw [show (Matrix.of fun i j : Fin k => if i = j then (1 : ℝ) else 0) = 1 from by
    ext i j; simp [Matrix.one_apply]]
  exact Matrix.det_one

/-- `permDet` as a monoid homomorphism. -/
def permDetHom : Equiv.Perm (Fin (k + 1)) →* ℝ where
  toFun := permDet
  map_one' := permDet_one
  map_mul' := permDet_mul

theorem abs_permDet (π : Equiv.Perm (Fin (k + 1))) : |permDet π| = 1 := by
  have hpos := orderOf_pos π
  have h : permDet π ^ orderOf π = 1 := by
    change permDetHom π ^ orderOf π = 1
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have h' : |permDet π| ^ orderOf π = 1 := by rw [pow_abs, h, abs_one]
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) hpos.ne').1 h'

theorem permDet_swap_zero_one (m : ℕ) :
    permDet (k := m + 1) (Equiv.swap 0 1) = -1 := by
  set L := Matrix.of (simplexMatrix (refVertex (m + 1) ∘ Equiv.swap (0 : Fin (m + 2)) 1))
  have hL : ∀ j l : Fin (m + 1), L j l =
      (if j = l ∧ j ≠ 0 then 1 else 0) - if j = 0 then 1 else 0 := by
    intro j l
    simp only [L, Matrix.of_apply, simplexMatrix, Function.comp_apply]
    have h0 : Equiv.swap (0 : Fin (m + 2)) 1 0 = (0 : Fin (m + 1)).succ := by simp
    rw [h0, refVertex_succ]
    refine Fin.cases ?_ (fun l => ?_) l
    · have : Equiv.swap (0 : Fin (m + 2)) 1 (0 : Fin (m + 1)).succ = 0 := by simp
      rw [this, refVertex_zero]
      by_cases hj : j = 0 <;> simp [hj]
    · have : Equiv.swap (0 : Fin (m + 2)) 1 l.succ.succ = l.succ.succ := by
        refine Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) ?_
        intro h
        exact Fin.succ_ne_zero l (Fin.succ_injective _ h)
      rw [this, refVertex_succ]
      by_cases hj : j = 0
      · subst hj; simp [(Fin.succ_ne_zero l).symm]
      · simp [Pi.single_apply, hj]
  have hut : L.IsUpperTriangular := by
    intro j l hlj
    rw [hL]
    have hj : j ≠ 0 := fun h => by subst h; exact absurd hlj (Fin.not_lt_zero _)
    have hjl : ¬(j = l ∧ j ≠ 0) := fun h => (ne_of_gt hlj) h.1
    simp only [hjl, hj, ite_false, sub_zero]
  rw [permDet, Matrix.det_of_isUpperTriangular hut, Fin.prod_univ_succ]
  simp only [hL]
  simp [Fin.succ_ne_zero]

/-- `permDet π` is the sign of the permutation `π`. -/
theorem permDet_eq_sign (π : Equiv.Perm (Fin (k + 1))) :
    permDet π = ((Equiv.Perm.sign π : ℤ) : ℝ) := by
  induction π using Equiv.Perm.swap_induction_on with
  | one => simp [permDet_one]
  | swap_mul f x y hxy ih =>
    rw [permDet_mul, ih, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy]
    push_cast
    congr 1
    -- `swap x y` is conjugate to `swap 0 1`
    cases k with
    | zero => exact absurd (Fin.ext (by have := x.isLt; have := y.isLt; omega)) hxy
    | succ m =>
      set z := Equiv.swap (0 : Fin (m + 2)) x y
      have hz : z ≠ 0 := by
        intro h
        apply hxy
        have := congrArg (Equiv.swap (0 : Fin (m + 2)) x) h
        simp only [z, Equiv.swap_apply_self, Equiv.swap_apply_left] at this
        exact this.symm
      set ρ := Equiv.swap (0 : Fin (m + 2)) x * Equiv.swap 1 z
      have hρ0 : ρ 0 = x := by
        simp only [ρ, Equiv.Perm.mul_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (by simp) hz.symm, Equiv.swap_apply_left]
      have hρ1 : ρ 1 = y := by
        simp only [ρ, Equiv.Perm.mul_apply, Equiv.swap_apply_left, z, Equiv.swap_apply_self]
      have hs : Equiv.swap x y = ρ * Equiv.swap 0 1 * ρ⁻¹ := by
        rw [← Equiv.swap_apply_apply, hρ0, hρ1]
      rw [hs, permDet_mul, permDet_mul, permDet_swap_zero_one]
      have := permDet_mul ρ ρ⁻¹
      rw [mul_inv_cancel, permDet_one] at this
      linarith

theorem measurePreserving_permMap (π : Equiv.Perm (Fin (k + 1))) :
    MeasurePreserving (permMap π) :=
  measurePreserving_affine (abs_permDet π) _

/-- `permMap π` as a measurable equivalence. -/
def permMapEquiv (π : Equiv.Perm (Fin (k + 1))) : (Fin k → ℝ) ≃ᵐ (Fin k → ℝ) where
  toFun := permMap π
  invFun := permMap π⁻¹
  left_inv x := by rw [← permMap_mul, inv_mul_cancel, permMap_one]
  right_inv x := by rw [← permMap_mul, mul_inv_cancel, permMap_one]
  measurable_toFun := (continuous_simplexMap _).measurable
  measurable_invFun := (continuous_simplexMap _).measurable

/-- Vertex permutations of `T̂_k` preserve integrals over `T̂_k`. -/
theorem setIntegral_refSimplex_comp_permMap (π : Equiv.Perm (Fin (k + 1)))
    (g : (Fin k → ℝ) → ℝ) :
    ∫ x in refSimplex k, g (permMap π x) = ∫ x in refSimplex k, g x := by
  have h := (measurePreserving_permMap π).setIntegral_preimage_emb
    (permMapEquiv π).measurableEmbedding g (refSimplex k)
  rwa [permMap_preimage_refSimplex] at h

/-- **Independence of the parametrization**: permuting the vertices multiplies the integral by
the sign of the permutation (the change of orientation). -/
theorem simplexIntegral_comp_perm (p : Fin (k + 1) → Fin n → ℝ) (π : Equiv.Perm (Fin (k + 1)))
    (ω : FormField n) :
    simplexIntegral (p ∘ π) ω = ((Equiv.Perm.sign π : ℤ) : ℝ) * simplexIntegral p ω := by
  have hp : p ∘ π = fun i => affine (simplexMatrix p) (p 0) ((refVertex k ∘ π) i) := by
    funext i; exact (simplexMap_refVertex p (π i)).symm
  rw [hp, simplexIntegral_comp_affine, simplexIntegral_eq_refVertex p, simplexIntegral_refVertex]
  set η := affinePullback (simplexMatrix p) (p 0) ω
  simp only [simplexIntegral, affinePullback_apply, pullback_apply_univ]
  rw [integral_const_mul]
  change permDet π * ∫ x in refSimplex k, η (permMap π x) univ = _
  rw [permDet_eq_sign, setIntegral_refSimplex_comp_permMap π (fun x => η x univ)]

/-- The same statement for Mathlib simplices: reindexing reverses the orientation by the sign. -/
theorem simplexIntegral_reindex (σ : Affine.Simplex ℝ (Fin n → ℝ) k)
    (π : Equiv.Perm (Fin (k + 1))) (ω : FormField n) :
    simplexIntegral (σ.reindex π).points ω =
      ((Equiv.Perm.sign π : ℤ) : ℝ) * simplexIntegral σ.points ω := by
  change simplexIntegral (σ.points ∘ π.symm) ω = _
  rw [simplexIntegral_comp_perm, Equiv.Perm.sign_symm]

/-! ### Linearity and bounds -/

theorem continuousOn_pullback_univ {p : Fin (k + 1) → Fin n → ℝ} {ω : FormField n}
    (hω : ContinuousOn ω (simplexMap p '' refSimplex k)) :
    ContinuousOn (fun x => affinePullback (simplexMatrix p) (p 0) ω x univ) (refSimplex k) := by
  simp only [affinePullback_apply, pullback_apply]
  refine continuousOn_finsetSum _ fun s _ => ?_
  refine ContinuousOn.mul ?_ continuousOn_const
  exact (continuous_apply s).comp_continuousOn
    (hω.comp (continuous_simplexMap p).continuousOn (Set.mapsTo_image _ _))

theorem integrableOn_pullback_univ {p : Fin (k + 1) → Fin n → ℝ} {ω : FormField n}
    (hω : ContinuousOn ω (simplexMap p '' refSimplex k)) :
    IntegrableOn (fun x => affinePullback (simplexMatrix p) (p 0) ω x univ) (refSimplex k) :=
  (continuousOn_pullback_univ hω).integrableOn_compact (isCompact_refSimplex k)

/-- `ω` is integrable over the oriented simplex `p`: the top coefficient of `F_p^* ω` is
integrable on `T̂_k`. -/
def SimplexIntegrable (p : Fin (k + 1) → Fin n → ℝ) (ω : FormField n) : Prop :=
  IntegrableOn (fun x => affinePullback (simplexMatrix p) (p 0) ω x univ) (refSimplex k)

theorem SimplexIntegrable.of_continuousOn {p : Fin (k + 1) → Fin n → ℝ} {ω : FormField n}
    (hω : ContinuousOn ω (simplexMap p '' refSimplex k)) : SimplexIntegrable p ω :=
  integrableOn_pullback_univ hω

/-- Additivity of the integral for integrable forms. -/
theorem simplexIntegral_add_of_simplexIntegrable {p : Fin (k + 1) → Fin n → ℝ}
    {ω η : FormField n} (hω : SimplexIntegrable p ω) (hη : SimplexIntegrable p η) :
    simplexIntegral p (ω + η) = simplexIntegral p ω + simplexIntegral p η := by
  simp only [simplexIntegral, affinePullback_add, Pi.add_apply]
  exact integral_add hω hη

theorem simplexIntegral_add {p : Fin (k + 1) → Fin n → ℝ} {ω η : FormField n}
    (hω : ContinuousOn ω (simplexMap p '' refSimplex k))
    (hη : ContinuousOn η (simplexMap p '' refSimplex k)) :
    simplexIntegral p (ω + η) = simplexIntegral p ω + simplexIntegral p η :=
  simplexIntegral_add_of_simplexIntegrable (.of_continuousOn hω) (.of_continuousOn hη)

theorem simplexIntegral_smul (p : Fin (k + 1) → Fin n → ℝ) (c : ℝ) (ω : FormField n) :
    simplexIntegral p (c • ω) = c * simplexIntegral p ω := by
  simp only [simplexIntegral, affinePullback_smul, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

theorem simplexIntegral_neg (p : Fin (k + 1) → Fin n → ℝ) (ω : FormField n) :
    simplexIntegral p (-ω) = -simplexIntegral p ω := by
  rw [show -ω = (-1 : ℝ) • ω by simp, simplexIntegral_smul]; ring

theorem simplexIntegral_sub {p : Fin (k + 1) → Fin n → ℝ} {ω η : FormField n}
    (hω : ContinuousOn ω (simplexMap p '' refSimplex k))
    (hη : ContinuousOn η (simplexMap p '' refSimplex k)) :
    simplexIntegral p (ω - η) = simplexIntegral p ω - simplexIntegral p η := by
  rw [sub_eq_add_neg, simplexIntegral_add hω hη.neg, simplexIntegral_neg, sub_eq_add_neg]

theorem simplexIntegral_sum {β : Type*} (p : Fin (k + 1) → Fin n → ℝ) (u : Finset β)
    {ω : β → FormField n} (hω : ∀ b ∈ u, ContinuousOn (ω b) (simplexMap p '' refSimplex k)) :
    simplexIntegral p (∑ b ∈ u, ω b) = ∑ b ∈ u, simplexIntegral p (ω b) := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    rw [show (0 : FormField n) = (0 : ℝ) • (0 : FormField n) by simp, simplexIntegral_smul]
    simp
  | insert a u ha ih =>
    rw [sum_insert ha, sum_insert ha, simplexIntegral_add (hω a (mem_insert_self a u)),
      ih fun b hb => hω b (mem_insert_of_mem hb)]
    have : ∀ b ∈ u, ContinuousOn (ω b) (simplexMap p '' refSimplex k) :=
      fun b hb => hω b (mem_insert_of_mem hb)
    have hs : ContinuousOn (∑ b ∈ u, ω b) (simplexMap p '' refSimplex k) := by
      have := continuousOn_finsetSum u this
      convert this using 1
      funext x; simp [Finset.sum_apply]
    exact hs

/-- **Bound**: if `|ω_s| ≤ M` on the simplex, then
`|∫_p ω| ≤ (Σ_s |minor_s(F_p)|) · M / k!`, where `minor_s(F_p)` are the `k × k` minors of the
edge matrix (the coefficients of `F_p^* dx_s`). -/
theorem abs_simplexIntegral_le {p : Fin (k + 1) → Fin n → ℝ} {ω : FormField n} {M : ℝ}
    (hM : ∀ x ∈ refSimplex k, ∀ s, |ω (simplexMap p x) s| ≤ M) :
    |simplexIntegral p ω| ≤
      (∑ s, |wedgeProd (simplexMatrix p) s univ|) * M / k.factorial := by
  rw [simplexIntegral_def, ← Real.norm_eq_abs, div_eq_mul_one_div, ← volume_real_refSimplex]
  refine norm_setIntegral_le_of_norm_le_const (volume_refSimplex_lt_top k) fun x hx => ?_
  rw [Real.norm_eq_abs, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (hM x hx s) (abs_nonneg _)

/-! ### Top-dimensional simplices: `|∫_T ω| ≤ |T| · sup |ω|` -/

/-- For an `n`-simplex in `ℝⁿ`: `|∫_p ω| ≤ |det B_p| / n! · sup_T |ω_univ|`. -/
theorem abs_simplexIntegral_le_of_top {p : Fin (n + 1) → Fin n → ℝ} {ω : FormField n} {M : ℝ}
    (hM : ∀ x ∈ refSimplex n, |ω (simplexMap p x) univ| ≤ M) :
    |simplexIntegral p ω| ≤ |(Matrix.of (simplexMatrix p)).det| / n.factorial * M := by
  have h : ‖∫ x in refSimplex n, (affinePullback (simplexMatrix p) (p 0) ω x univ : ℝ)‖ ≤
      |(Matrix.of (simplexMatrix p)).det| * M * volume.real (refSimplex n) := by
    refine norm_setIntegral_le_of_norm_le_const (volume_refSimplex_lt_top n) fun x hx => ?_
    rw [affinePullback_apply, pullback_apply_univ, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg _)
  rw [volume_real_refSimplex, Real.norm_eq_abs] at h
  rw [simplexIntegral]
  convert h using 1
  ring

/-- The parametrization of a non-degenerate simplex is injective. -/
theorem injective_simplexMap {p : Fin (n + 1) → Fin n → ℝ}
    (hp : (Matrix.of (simplexMatrix p)).det ≠ 0) : Function.Injective (simplexMap p) := by
  intro x y hxy
  have h1 : Matrix.mulVec (Matrix.of (simplexMatrix p)) x =
      Matrix.mulVec (Matrix.of (simplexMatrix p)) y := by
    funext i
    have hi := congrFun hxy i
    simp only [simplexMap, affine_apply, add_left_inj] at hi
    simpa [Matrix.mulVec, dotProduct] using hi
  exact Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hp.isUnit) h1

/-- The volume of a non-degenerate `n`-simplex in `ℝⁿ`: `|F_p(T̂)| = |det B_p| / n!`. -/
theorem volume_real_image_simplexMap {p : Fin (n + 1) → Fin n → ℝ}
    (hp : (Matrix.of (simplexMatrix p)).det ≠ 0) :
    volume.real (simplexMap p '' refSimplex n) = |(Matrix.of (simplexMatrix p)).det| /
      n.factorial := by
  set L := (Matrix.toLin' (Matrix.of (simplexMatrix p))).toContinuousLinearMap
  have hderiv : ∀ x ∈ refSimplex n, HasFDerivWithinAt (simplexMap p) L (refSimplex n) x :=
    fun x _ => (hasFDerivAt_affine _ (p 0) x).hasFDerivWithinAt
  have hdetL : L.det = (Matrix.of (simplexMatrix p)).det := by
    rw [ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin']
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_refSimplex n) hderiv (injective_simplexMap hp).injOn (fun _ => (1 : ℝ))
  simp only [hdetL, smul_eq_mul, mul_one, setIntegral_const] at hcov
  rw [hcov, volume_real_refSimplex]
  ring

/-- **`|∫_T ω| ≤ |T| · sup_T |ω|`** for a non-degenerate `n`-simplex `T = F_p(T̂)` in `ℝⁿ`, where
`|ω_univ|` is the pointwise norm of a top-degree form. -/
theorem abs_simplexIntegral_le_volume_mul {p : Fin (n + 1) → Fin n → ℝ}
    (hp : (Matrix.of (simplexMatrix p)).det ≠ 0) {ω : FormField n} {M : ℝ}
    (hM : ∀ x ∈ simplexMap p '' refSimplex n, |ω x univ| ≤ M) :
    |simplexIntegral p ω| ≤ volume.real (simplexMap p '' refSimplex n) * M := by
  rw [volume_real_image_simplexMap hp]
  exact abs_simplexIntegral_le_of_top fun x hx => hM _ ⟨x, hx, rfl⟩

end Feec.FiniteElement
