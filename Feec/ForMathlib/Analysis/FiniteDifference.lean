module

public import Feec.ForMathlib.Analysis.SubMarkov
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The finite difference Laplacian on a lattice domain

The `(2|ι| + 1)`-point finite difference Laplacian with homogeneous Dirichlet data on a finite set
`G` of lattice points of `ℤ^ι` is a sub-Markov generator on `ℝ^G` with the maximum norm, the
discrete maximum principle ([Thomee2006], Ch. 15).

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Finset

@[expose] public noncomputable section

namespace FiniteDifference

variable {ι : Type*} [Fintype ι] {G : Finset (ι → ℤ)}

/-- The extension of a grid function on `G` by `0` to the lattice (homogeneous Dirichlet data). -/
def zeroExt (U : G → ℝ) (q : ι → ℤ) : ℝ := if h : q ∈ G then U ⟨q, h⟩ else 0

@[simp] theorem zeroExt_coe (U : G → ℝ) (p : G) : zeroExt U p = U p := by simp [zeroExt]

theorem zeroExt_nonneg {U : G → ℝ} (hU : 0 ≤ U) (q : ι → ℤ) : 0 ≤ zeroExt U q := by
  unfold zeroExt; split_ifs; exacts [hU _, le_rfl]

theorem zeroExt_one_le (q : ι → ℤ) : zeroExt (fun _ : G => (1 : ℝ)) q ≤ 1 := by
  unfold zeroExt; split_ifs <;> norm_num

theorem zeroExt_sub (U V : G → ℝ) (q : ι → ℤ) :
    zeroExt (U - V) q = zeroExt U q - zeroExt V q := by
  unfold zeroExt; split_ifs <;> simp

theorem abs_zeroExt_le (U : G → ℝ) (q : ι → ℤ) : |zeroExt U q| ≤ ‖U‖ := by
  unfold zeroExt
  split_ifs with h
  · exact (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm U ⟨q, h⟩)
  · simp

variable [DecidableEq ι]

variable (G) in
/-- The finite difference Laplacian `Σᵢ (U(p + eᵢ) - 2 U(p) + U(p - eᵢ)) / h²`, `U = 0` off `G`. -/
def laplacian (h : ℝ) : (G → ℝ) →L[ℝ] (G → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun U p => ∑ i, (zeroExt U ((p : ι → ℤ) + Pi.single i 1) - 2 * U p +
        zeroExt U ((p : ι → ℤ) - Pi.single i 1)) / h ^ 2
      map_add' := fun U V => funext fun p => by
        simp only [Pi.add_apply, zeroExt, ← sum_add_distrib]
        refine sum_congr rfl fun i _ => ?_
        split_ifs <;> ring
      map_smul' := fun c U => funext fun p => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, zeroExt, mul_sum]
        refine sum_congr rfl fun i _ => ?_
        split_ifs <;> ring }

theorem laplacian_apply (h : ℝ) (U : G → ℝ) (p : G) :
    laplacian G h U p = ∑ i, (zeroExt U ((p : ι → ℤ) + Pi.single i 1) - 2 * U p +
      zeroExt U ((p : ι → ℤ) - Pi.single i 1)) / h ^ 2 := rfl

/-- **The discrete maximum principle**: the difference Laplacian is a sub-Markov generator. -/
theorem isSubMarkovGenerator_laplacian (G : Finset (ι → ℤ)) (h : ℝ) :
    IsSubMarkovGenerator (laplacian G h) where
  exists_shift := ⟨2 * Fintype.card ι / h ^ 2, by positivity, fun v hv p => by
    have e : 2 * (Fintype.card ι : ℝ) / h ^ 2 * v p = ∑ _i : ι, 2 * v p / h ^ 2 := by
      simp only [sum_const, card_univ, nsmul_eq_mul]; ring
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, laplacian_apply, e,
      ← sum_add_distrib]
    refine sum_nonneg fun i _ => ?_
    rw [← add_div]
    have := zeroExt_nonneg hv ((p : ι → ℤ) + Pi.single i 1)
    have := zeroExt_nonneg hv ((p : ι → ℤ) - Pi.single i 1)
    exact div_nonneg (by linarith) (sq_nonneg h)⟩
  apply_one_nonpos p := by
    rw [laplacian_apply]
    refine sum_nonpos fun i _ => div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg h)
    linarith [zeroExt_one_le (G := G) ((p : ι → ℤ) + Pi.single i 1),
      zeroExt_one_le (G := G) ((p : ι → ℤ) - Pi.single i 1)]

end FiniteDifference
