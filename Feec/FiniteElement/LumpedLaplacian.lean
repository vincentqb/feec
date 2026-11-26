module

public import Feec.FiniteElement.LumpedMass
public import Feec.ForMathlib.Analysis.SubMarkov

/-!
# The lumped-mass `P₁` Laplacian on a set of nodes

On a non-obtuse mesh, the lumped-mass `P₁` Laplacian on any set of nodes is a sub-Markov generator
(`isSubMarkovGenerator_lumpedLaplacianOn`), conservative when every vertex is a node.

## References

* [P. G. Ciarlet, P.-A. Raviart, *Maximum principle and uniform convergence for the finite element method*][CiarletRaviart1973]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset

@[expose] public noncomputable section

namespace Feec.FiniteElement

open Feec.Mesh

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-! ### `P₁` gradients -/

theorem p1Grad_eq_vecMul (p : Fin (n + 1) → Fin n → ℝ) (u : (Fin n → ℝ) → ℝ) :
    p1Grad p u = Matrix.vecMul (fun l => u (p l.succ) - u (p 0)) (edgeMatrix p)⁻¹ := by
  funext i
  simp only [p1Grad_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ,
    baryGrad, Fin.cons_zero, Fin.cons_succ, Matrix.vecMul, dotProduct, sub_mul, sum_sub_distrib,
    mul_neg, mul_sum]
  ring

theorem p1Grad_nodalIndicator {p : Fin (n + 1) → Fin n → ℝ} (hp : Function.Injective p)
    (j : Fin (n + 1)) : p1Grad p (nodalIndicator (p j)) = baryGrad p j := by
  rw [p1Grad_apply, Finset.sum_eq_single j (fun i _ hij => by simp [nodalIndicator, hp.ne hij])
    (by simp)]
  simp [nodalIndicator]

/-! ### The lumped-mass Laplacian -/

variable (M : SimplicialMesh n) (x : ι → Fin n → ℝ)

/-- The entries `-a(φ_{x p}, φ_{x q}) / m(x p)` of the lumped-mass Laplacian. -/
def lumpedEntry (p q : ι) : ℝ :=
  -p1Stiffness M (nodalIndicator (x p)) (nodalIndicator (x q)) / lumpedMass M (x p)

/-- The lumped-mass `P₁` Laplacian `(Lₕ U)(p) = -a(φ_{x p}, U_h) / m(x p)` on the nodes `x`. -/
def lumpedLaplacianOn : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (Matrix.of (lumpedEntry M x)).mulVecLin.toContinuousLinearMap

theorem lumpedLaplacianOn_apply_eq_sum (U : ι → ℝ) (p : ι) :
    lumpedLaplacianOn M x U p = ∑ q, lumpedEntry M x p q * U q := rfl

theorem lumpedLaplacianOn_apply (U : ι → ℝ) (p : ι) :
    lumpedLaplacianOn M x U p =
      -p1Stiffness M (nodalIndicator (x p)) (nodalFun x U) / lumpedMass M (x p) := by
  rw [lumpedLaplacianOn_apply_eq_sum, nodalFun_eq_sum, p1Stiffness_sum_smul_right,
    ← sum_neg_distrib, sum_div]
  exact sum_congr rfl fun q _ => by rw [lumpedEntry]; ring

variable {M x}

omit [Fintype ι] in
theorem lumpedEntry_nonneg (hM : IsNonobtuse M) (hx : Function.Injective x) {p q : ι}
    (hpq : p ≠ q) : 0 ≤ lumpedEntry M x p q :=
  div_nonneg (neg_nonneg.2 (p1Stiffness_indicator_nonpos M hM fun h => hpq (hx h)))
    (lumpedMass_nonneg _ _)

theorem p1Stiffness_nodalFun_one (hx : Function.Injective x) (y : Fin n → ℝ) :
    p1Stiffness M (nodalIndicator y) (nodalFun x fun _ => 1) =
      -∑ z ∈ (M.simplices.biUnion vertexSet).filter (fun z => z ∉ Set.range x),
        p1Stiffness M (nodalIndicator y) (nodalIndicator z) := by
  classical
  set out := (M.simplices.biUnion vertexSet).filter (fun z => z ∉ Set.range x)
  have h1 : p1Stiffness M (nodalIndicator y)
      (nodalFun x (fun _ => 1) + ∑ z ∈ out, (1 : ℝ) • nodalIndicator z) = 0 := by
    rw [p1Stiffness_congr_right _ _ (w' := fun _ => 1) fun T hT j => ?_,
      p1Stiffness_const_right]
    have hv : T.points j ∈ M.simplices.biUnion vertexSet :=
      mem_biUnion.2 ⟨T, hT, mem_vertexSet.2 ⟨j, rfl⟩⟩
    simp only [Pi.add_apply, one_smul, Finset.sum_apply, nodalIndicator]
    by_cases hr : T.points j ∈ Set.range x
    · obtain ⟨q, hq⟩ := hr
      rw [← hq, nodalFun_apply hx, Finset.sum_eq_zero fun z hz => ?_, add_zero]
      rw [ite_eq_right_iff]
      exact fun h => absurd ⟨q, h⟩ (mem_filter.1 hz).2
    · rw [Finset.sum_eq_single (T.points j) (fun z _ hz => by simp [Ne.symm hz])
        (fun h => absurd (mem_filter.2 ⟨hv, hr⟩) h)]
      have : nodalFun x (fun _ => (1 : ℝ)) (T.points j) = 0 :=
        sum_eq_zero fun q _ => by rw [ite_eq_right_iff]; exact fun h => absurd ⟨q, h⟩ hr
      simp [this]
  rw [p1Stiffness_add_right, p1Stiffness_sum_smul_right] at h1
  simp only [one_mul] at h1
  linarith

/-- The discrete maximum principle on a non-obtuse mesh: the lumped-mass `P₁` Laplacian on any set
of nodes is a sub-Markov generator ([CiarletRaviart1973]). -/
theorem isSubMarkovGenerator_lumpedLaplacianOn (hM : IsNonobtuse M) (hx : Function.Injective x) :
    IsSubMarkovGenerator (lumpedLaplacianOn M x) where
  exists_shift := by
    classical
    refine ⟨∑ p, |lumpedEntry M x p p|, sum_nonneg fun _ _ => abs_nonneg _, fun U hU p => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [lumpedLaplacianOn_apply_eq_sum, ← Finset.add_sum_erase _ _ (mem_univ p)]
    have h1 : 0 ≤ ∑ q ∈ univ.erase p, lumpedEntry M x p q * U q := sum_nonneg fun q hq =>
      mul_nonneg (lumpedEntry_nonneg hM hx (Finset.ne_of_mem_erase hq).symm) (hU q)
    have h2 : 0 ≤ lumpedEntry M x p p + ∑ p, |lumpedEntry M x p p| := by
      have := single_le_sum (f := fun p => |lumpedEntry M x p p|) (fun _ _ => abs_nonneg _)
        (mem_univ p)
      linarith [neg_abs_le (lumpedEntry M x p p)]
    nlinarith [mul_nonneg h2 (hU p)]
  apply_one_nonpos p := by
    classical
    rw [lumpedLaplacianOn_apply, p1Stiffness_nodalFun_one hx, neg_neg]
    refine div_nonpos_of_nonpos_of_nonneg (sum_nonpos fun z hz => ?_) (lumpedMass_nonneg _ _)
    exact p1Stiffness_indicator_nonpos M hM fun h => (mem_filter.1 hz).2 ⟨p, h⟩

/-- `Lₕ 𝟙 = 0` when every vertex of the mesh is a node. -/
theorem lumpedLaplacianOn_apply_one (hx : Function.Injective x)
    (hV : ∀ T ∈ M.simplices, ∀ j, T.points j ∈ Set.range x) :
    lumpedLaplacianOn M x (fun _ => 1) = 0 := by
  classical
  funext p
  rw [lumpedLaplacianOn_apply, p1Stiffness_nodalFun_one hx, Finset.filter_false_of_mem, sum_empty,
    neg_zero, neg_zero, zero_div, Pi.zero_apply]
  intro z hz
  obtain ⟨T, hT, hzT⟩ := mem_biUnion.1 hz
  obtain ⟨j, rfl⟩ := mem_vertexSet.1 hzT
  exact not_not.2 (hV T hT j)

end Feec.FiniteElement
