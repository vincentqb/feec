module

public import Feec.ForMathlib.Calculus.SecondDifference

/-!
# The second difference along a direction

* `abs_secondDiff_sub_iteratedFDeriv_le`: for `u ∈ C⁴` on a real normed space,
  `|u(x + d) - 2 u(x) + u(x - d) - D²u(x)(d, d)| ≤ B / 12` when `|D⁴u(x + t d)(d, d, d, d)| ≤ B`
  for `t ∈ [-1, 1]`, the truncation error of the centred second difference along `d`
  (`abs_secondDiff_sub_le` along the line `t ↦ x + t d`);

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15
  (difference approximations of the Laplacian)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set

@[expose] public noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The truncation error of the second difference along a direction**: for `u ∈ C⁴` with
`|D⁴u(x + t d)(d, d, d, d)| ≤ B` for `t ∈ [-1, 1]`,
`|u(x + d) - 2 u(x) + u(x - d) - D²u(x)(d, d)| ≤ B / 12`. -/
theorem abs_secondDiff_sub_iteratedFDeriv_le {u : E → ℝ} (hu : ContDiff ℝ 4 u) (x d : E) {B : ℝ}
    (hB : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |iteratedFDeriv ℝ 4 u (x + t • d) (fun _ => d)| ≤ B) :
    |u (x + d) - 2 * u x + u (x - d) - iteratedFDeriv ℝ 2 u x (fun _ => d)| ≤ B / 12 := by
  set g : ℕ → ℝ → ℝ := fun k t => iteratedFDeriv ℝ k u (x + t • d) (fun _ => d) with hg
  have hd : ∀ k < 4, ∀ t, HasDerivAt (g k) (g (k + 1) t) t := by
    intro k hk t
    have hk' : ((k : ℕ) : WithTop ℕ∞) < 4 := by exact_mod_cast hk
    have hF : DifferentiableAt ℝ (iteratedFDeriv ℝ k u) (x + t • d) :=
      hu.differentiable_iteratedFDeriv hk' _
    have hl : HasDerivAt (fun t : ℝ => x + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have := (hF.hasFDerivAt.continuousMultilinear_apply_const (fun _ => d)).comp_hasDerivAt t hl
    convert this using 1
    · rfl
    · simp only [g, ContinuousLinearMap.flipMultilinear_apply_apply]
      rw [iteratedFDeriv_succ_apply_left]
      rfl
  have key := abs_secondDiff_sub_le (g := g 0) (g₁ := g 1) (g₂ := g 2) (g₃ := g 3) (g₄ := g 4)
    (h := 1) (B := B) zero_le_one (fun t _ => hd 0 (by norm_num) t)
    (fun t _ => hd 1 (by norm_num) t) (fun t _ => hd 2 (by norm_num) t)
    (fun t _ => hd 3 (by norm_num) t) hB
  simp only [g, iteratedFDeriv_zero_apply, one_smul, zero_smul, add_zero, neg_smul, one_pow,
    one_mul, mul_one] at key
  rwa [← sub_eq_add_neg] at key

end
