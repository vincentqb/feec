module

public import Feec.ForMathlib.Analysis.Complexification
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# The complexification of an inner product space

For an inner product space `V` over `𝕜 = ℝ` or `ℂ`, the complexification `V_ℂ = V × V`
(`Complexification .hilbert 𝕜 V`, the pair `(x, y)` read as `x + i y`) is a complex inner product
space for `⟪(x, y), (x', y')⟫ = re ⟪x, x'⟫ + re ⟪y, y'⟫ + i (re ⟪x, y'⟫ - re ⟪y, x'⟫)`, whose
norm is the `L²` norm of the pair, `‖(x, y)‖² = ‖x‖² + ‖y‖²` (`Complexification.norm_sq`). It is a
`Complexification.NormCore`, so it is complete when `V` is, and a bounded operator `T` has
`‖T_ℂ‖ = ‖T‖`, `p(T)_ℂ = p(T_ℂ)` for real polynomials `p`, and is invertible when `T_ℂ` is
(`Feec.ForMathlib.Analysis.Complexification`). Moreover
`re ⟪T_ℂ (x, y), (x, y)⟫ = re ⟪T x, x⟫ + re ⟪T y, y⟫` (`Complexification.re_inner_map`), so `T_ℂ`
is dissipative when `T` is.

This is how statements about complex Hilbert spaces (von Neumann's inequality,
`ContinuousLinearMap.norm_aeval_le_of_norm_le_one`) reach real ones.

## References

* [P. R. Halmos, *Finite-Dimensional Vector Spaces*][Halmos1974], §77 (complexification)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace Complexification

variable {𝕜 V : Type*} [NormedAddCommGroup V]

/-- The Hilbert norm `‖x + i y‖ = (‖x‖² + ‖y‖²)^{1/2}`, the `L²` norm of the pair. -/
instance : Norm (Complexification .hilbert 𝕜 V) := ⟨fun p => ‖WithLp.toLp 2 (p.re, p.im)‖⟩

/-- `‖x + i y‖² = ‖x‖² + ‖y‖²`. -/
theorem norm_sq (p : Complexification .hilbert 𝕜 V) : ‖p‖ ^ 2 = ‖p.re‖ ^ 2 + ‖p.im‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

variable [RCLike 𝕜] [InnerProductSpace 𝕜 V]

instance : NormCore .hilbert 𝕜 V where
  norm_add_le p q := norm_add_le (WithLp.toLp 2 (p.re, p.im)) (WithLp.toLp 2 (q.re, q.im))
  norm_smul_le z p := by
    have h0 (q : Complexification .hilbert 𝕜 V) : 0 ≤ ‖q‖ :=
      norm_nonneg (WithLp.toLp 2 (q.re, q.im))
    refine ((sq_eq_sq₀ (h0 _) (mul_nonneg (norm_nonneg z) (h0 p))).1 ?_).le
    rw [mul_pow, norm_sq, norm_sq, re_smul, im_smul, norm_sub_sq (𝕜 := 𝕜), norm_add_sq (𝕜 := 𝕜)]
    simp only [norm_smul, RCLike.norm_ofReal, inner_smul_real_left, inner_smul_real_right,
      RCLike.smul_re, mul_pow, sq_abs, Complex.sq_norm, Complex.normSq_apply]
    ring
  norm_re_le p := WithLp.norm_fst_le V (WithLp.toLp 2 (p.re, p.im))
  norm_mk_zero x := WithLp.norm_toLp_fst 2 V V x
  norm_mk_map_le T p := by
    have h0 (q : Complexification .hilbert 𝕜 V) : 0 ≤ ‖q‖ :=
      norm_nonneg (WithLp.toLp 2 (q.re, q.im))
    exact (sq_le_sq₀ (h0 _) (mul_nonneg (norm_nonneg T) (h0 p))).1 (by
      rw [norm_sq, mul_pow, norm_sq, re_mk, im_mk]
      nlinarith [T.le_opNorm p.re, T.le_opNorm p.im, norm_nonneg (T p.re),
        norm_nonneg (T p.im), mul_nonneg (norm_nonneg T) (norm_nonneg p.re),
        mul_nonneg (norm_nonneg T) (norm_nonneg p.im)])

instance : InnerProductSpace ℂ (Complexification .hilbert 𝕜 V) where
  inner p q := ⟨RCLike.re ⟪p.re, q.re⟫_𝕜 + RCLike.re ⟪p.im, q.im⟫_𝕜,
    RCLike.re ⟪p.re, q.im⟫_𝕜 - RCLike.re ⟪p.im, q.re⟫_𝕜⟩
  norm_sq_eq_re_inner p := (norm_sq p).trans <| by
    rw [@norm_sq_eq_re_inner 𝕜, @norm_sq_eq_re_inner 𝕜]
    rfl
  conj_inner_symm p q := by
    apply Complex.ext
    · simp only [Complex.conj_re]
      rw [inner_re_symm (𝕜 := 𝕜) q.re, inner_re_symm (𝕜 := 𝕜) q.im]
    · simp only [Complex.conj_im]
      rw [inner_re_symm (𝕜 := 𝕜) q.re, inner_re_symm (𝕜 := 𝕜) q.im]
      ring
  add_left p q r := by
    apply Complex.ext <;> simp only [re_add, im_add, inner_add_left, map_add, Complex.add_re,
      Complex.add_im] <;> ring
  smul_left p q z := by
    apply Complex.ext <;>
      simp only [re_smul, im_smul, inner_sub_left, inner_add_left, inner_smul_real_left, map_sub,
        map_add, RCLike.smul_re, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im] <;> ring

theorem re_inner (p q : Complexification .hilbert 𝕜 V) :
    RCLike.re ⟪p, q⟫_ℂ = RCLike.re ⟪p.re, q.re⟫_𝕜 + RCLike.re ⟪p.im, q.im⟫_𝕜 := rfl

/-- `re ⟪T_ℂ (x + i y), x + i y⟫ = re ⟪T x, x⟫ + re ⟪T y, y⟫`. -/
theorem re_inner_map (T : V →L[𝕜] V) (p : Complexification .hilbert 𝕜 V) :
    (⟪map T p, p⟫_ℂ).re = RCLike.re ⟪T p.re, p.re⟫_𝕜 + RCLike.re ⟪T p.im, p.im⟫_𝕜 :=
  rfl

end Complexification
