module

public import Feec.ForMathlib.Calculus.SecondDifference

/-!
# The difference Laplacian of a function on `ℝⁿ`

The `(2n + 1)`-point **difference Laplacian** of `f : ℝⁿ → ℝ` with step `h`,
`(Dₕ f)(x) = Σₗ (f(x + h eₗ) - 2 f(x) + f(x - h eₗ)) / h²` (`FiniteDifference.diffLaplacian`),
is the function whose values at the nodes of a grid are those of the finite difference Laplacian
`FiniteDifference.laplacian` of the nodal values. Its iterates are bounded by the pure second
derivatives:

* `Dₕ` commutes with the partial derivatives of a differentiable function
  (`FiniteDifference.partialDeriv_diffLaplacian`), hence with the words
  `∂²_{i₁} ⋯ ∂²_{i_k}` of pure second partial derivatives (`FiniteDifference.secondPartials`,
  `FiniteDifference.secondPartials_diffLaplacian`);
* `|Dₕ g| ≤ n B` for `|∂ᵢ² g| ≤ B` (`FiniteDifference.abs_diffLaplacian_le`, the second
  difference `Feec.abs_axis_secondDiff_le`), so `|Dₕᵏ f| ≤ nᵏ B` for `f ∈ C^{2k}` with
  `|∂²_{i₁} ⋯ ∂²_{i_k} f| ≤ B` (`FiniteDifference.abs_iterate_diffLaplacian_le`).

A function odd about the hyperplane `xᵢ = c` (`FiniteDifference.IsOddAbout`) vanishes on it
(`FiniteDifference.IsOddAbout.eq_zero`), and `Dₕ` keeps it odd
(`FiniteDifference.IsOddAbout.diffLaplacian`): this is how odd extensions turn the difference
Laplacian with homogeneous Dirichlet data into `Dₕ`.

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set Finset

@[expose] public noncomputable section

namespace FiniteDifference

variable {n : ℕ}

/-- **The difference Laplacian** `(Dₕ f)(x) = Σₗ (f(x + h eₗ) - 2 f(x) + f(x - h eₗ)) / h²` of a
function on `ℝⁿ`. -/
def diffLaplacian (h : ℝ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ l, (f (x + h • Pi.single l 1) - 2 * f x + f (x + (-h) • Pi.single l 1)) / h ^ 2

/-- The word `∂²_{i₁} ⋯ ∂²_{i_k} f` of pure second partial derivatives, `w = [i₁, …, i_k]`. -/
def secondPartials (w : List (Fin n)) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  w.foldr (fun i g => partialDeriv i (partialDeriv i g)) f

/-! ### Smoothness and derivatives -/

theorem contDiff_secondPartials {f : (Fin n → ℝ) → ℝ} (w : List (Fin n)) {m : ℕ}
    (hf : ContDiff ℝ (m + 2 * w.length : ℕ) f) : ContDiff ℝ m (secondPartials w f) := by
  induction w generalizing m with
  | nil => simpa [secondPartials] using hf
  | cons i w ih =>
    have h := ih (m := m + 2) (by
      convert hf using 2; simp only [List.length_cons]; ring)
    have h1 : ContDiff ℝ (m + 1 : ℕ) (partialDeriv i (secondPartials w f)) :=
      h.partialDeriv (by exact_mod_cast le_refl (m + 1 + 1)) i
    exact h1.partialDeriv (by exact_mod_cast le_refl (m + 1)) i

theorem _root_.ContDiff.diffLaplacian (h : ℝ) {f : (Fin n → ℝ) → ℝ} {k : WithTop ℕ∞}
    (hf : ContDiff ℝ k f) : ContDiff ℝ k (FiniteDifference.diffLaplacian h f) := by
  unfold FiniteDifference.diffLaplacian
  refine ContDiff.sum fun l _ => ?_
  refine ContDiff.div_const (((hf.comp (contDiff_id.add contDiff_const)).sub
    (contDiff_const.mul hf)).add (hf.comp (contDiff_id.add contDiff_const))) _

/-- `Dₕ` commutes with the partial derivatives of a differentiable function. -/
theorem partialDeriv_diffLaplacian (h : ℝ) {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (i : Fin n) : partialDeriv i (diffLaplacian h f) = diffLaplacian h (partialDeriv i f) := by
  funext x
  have ht : ∀ a : Fin n → ℝ, HasFDerivAt (fun y => f (y + a)) (fderiv ℝ f (x + a)) x :=
    fun a => (hf (x + a)).hasFDerivAt.comp x ((hasFDerivAt_id (𝕜 := ℝ) x).add_const a)
  have hd : HasFDerivAt (diffLaplacian h f) (∑ l, (h ^ 2)⁻¹ •
      (fderiv ℝ f (x + h • Pi.single l 1) - (2 : ℝ) • fderiv ℝ f x +
        fderiv ℝ f (x + (-h) • Pi.single l 1))) x := by
    have hl : ∀ l ∈ (Finset.univ : Finset (Fin n)), HasFDerivAt
        (fun y => (f (y + h • Pi.single l 1) - 2 * f y + f (y + (-h) • Pi.single l 1)) / h ^ 2)
        ((h ^ 2)⁻¹ • (fderiv ℝ f (x + h • Pi.single l 1) - (2 : ℝ) • fderiv ℝ f x +
          fderiv ℝ f (x + (-h) • Pi.single l 1))) x := fun l _ => by
      have := (((ht (h • Pi.single l 1)).sub ((hf x).hasFDerivAt.const_mul (2 : ℝ))).add
        (ht ((-h) • Pi.single l 1))).const_mul (h ^ 2)⁻¹
      convert this using 1
      funext y
      simp only [Pi.add_apply, Pi.sub_apply, div_eq_inv_mul]
    convert HasFDerivAt.sum hl using 1
    funext y
    simp only [diffLaplacian, Finset.sum_apply]
  rw [partialDeriv, hd.fderiv]
  simp only [diffLaplacian, partialDeriv, div_eq_inv_mul]
  simp
  exact Finset.sum_congr rfl fun l _ => by ring

/-- `Dₕ` commutes with the words of pure second partial derivatives of a `C^{2|w|+1}`
function. -/
theorem secondPartials_diffLaplacian (h : ℝ) {f : (Fin n → ℝ) → ℝ} (w : List (Fin n))
    (hf : ContDiff ℝ (2 * w.length + 1 : ℕ) f) :
    secondPartials w (diffLaplacian h f) = diffLaplacian h (secondPartials w f) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hw := ih (hf.of_le (by simp only [List.length_cons]; norm_cast; omega))
    have hc : ContDiff ℝ (1 + 2 : ℕ) (secondPartials w f) :=
      contDiff_secondPartials w (hf.of_le (by simp only [List.length_cons]; norm_cast; omega))
    show partialDeriv i (partialDeriv i (secondPartials w (diffLaplacian h f))) =
      diffLaplacian h (partialDeriv i (partialDeriv i (secondPartials w f)))
    rw [hw, partialDeriv_diffLaplacian h (hc.differentiable (by norm_num)),
      partialDeriv_diffLaplacian h (f := partialDeriv i (secondPartials w f))
        ((hc.partialDeriv (m := (1 + 1 : ℕ)) (by norm_num) i).differentiable (by norm_num))]

/-! ### The bound -/

/-- **The difference Laplacian is bounded by the second derivatives**:
`|Dₕ g(x)| ≤ n B` for `|∂ᵢ² g| ≤ B`, `h ≠ 0`. -/
theorem abs_diffLaplacian_le {h B : ℝ} (hh : h ≠ 0) {g : (Fin n → ℝ) → ℝ} (hg : ContDiff ℝ 2 g)
    (hB : ∀ i y, |partialDeriv i (partialDeriv i g) y| ≤ B) (x : Fin n → ℝ) :
    |diffLaplacian h g x| ≤ n * B := by
  unfold diffLaplacian
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have h2 : 0 < h ^ 2 := by positivity
  calc ∑ l, |(g (x + h • Pi.single l 1) - 2 * g x + g (x + (-h) • Pi.single l 1)) / h ^ 2|
      ≤ ∑ _l : Fin n, B := Finset.sum_le_sum fun l _ => by
        rw [abs_div, abs_of_pos h2, div_le_iff₀ h2]
        exact Feec.abs_axis_secondDiff_le hg x l fun τ _ => hB l _
    _ = n * B := by simp

/-- **`|Dₕᵏ f| ≤ nᵏ B`** for `f ∈ C^{2k}` with `|∂²_{i₁} ⋯ ∂²_{i_k} f| ≤ B`, `h ≠ 0`. -/
theorem abs_iterate_diffLaplacian_le {h : ℝ} (hh : h ≠ 0) (k : ℕ) {f : (Fin n → ℝ) → ℝ} {B : ℝ}
    (hf : ContDiff ℝ (2 * k : ℕ) f)
    (hB : ∀ (l : Fin k → Fin n) x, |secondPartials (List.ofFn l) f x| ≤ B) (x : Fin n → ℝ) :
    |(diffLaplacian h)^[k] f x| ≤ n ^ k * B := by
  induction k generalizing f B with
  | zero => simpa [secondPartials] using hB Fin.elim0 x
  | succ k ih =>
    rw [Function.iterate_succ_apply, pow_succ, mul_assoc]
    refine ih ((hf.of_le (by norm_cast; omega)).diffLaplacian h) (fun l y => ?_)
    have hw : ContDiff ℝ (2 * (List.ofFn l).length + 1 : ℕ) f :=
      hf.of_le (by simp only [List.length_ofFn]; norm_cast; omega)
    rw [secondPartials_diffLaplacian h _ hw]
    refine abs_diffLaplacian_le hh (contDiff_secondPartials (m := 2) _
      (hf.of_le (by simp only [List.length_ofFn]; norm_cast; omega))) (fun i z => ?_) y
    have := hB (Fin.cons i l) z
    rwa [List.ofFn_succ, Fin.cons_zero] at this

/-! ### Odd functions -/

/-- `f` is **odd about the hyperplane** `xᵢ = c`: odd under the reflection `xᵢ ↦ 2c - xᵢ`. -/
def IsOddAbout (i : Fin n) (c : ℝ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x, f (Function.update x i (2 * c - x i)) = -f x

/-- An odd function vanishes on the hyperplane of the reflection. -/
theorem IsOddAbout.eq_zero {i : Fin n} {c : ℝ} {f : (Fin n → ℝ) → ℝ} (hf : IsOddAbout i c f)
    {x : Fin n → ℝ} (hx : x i = c) : f x = 0 := by
  have h := hf x
  rw [hx, show 2 * c - c = c by ring, Function.update_eq_self_iff.2 hx.symm] at h
  linarith

private theorem update_reflect_add (i l : Fin n) (c t : ℝ) (x : Fin n → ℝ) :
    Function.update x i (2 * c - x i) + t • Pi.single l 1 =
      Function.update (x + (if l = i then -t else t) • Pi.single l 1) i
        (2 * c - (x + (if l = i then -t else t) • Pi.single l 1 : Fin n → ℝ) i) := by
  funext j
  by_cases hj : j = i
  · subst hj
    by_cases hl : l = j
    · subst hl; simp; ring
    · simp [hl, Ne.symm hl]
  · by_cases hl : l = i
    · subst hl; simp [hj]
    · simp [hj, hl]

/-- `Dₕ` keeps odd functions odd. -/
theorem IsOddAbout.diffLaplacian {i : Fin n} {c : ℝ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsOddAbout i c f) (h : ℝ) : IsOddAbout i c (diffLaplacian h f) := by
  intro x
  unfold FiniteDifference.diffLaplacian
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [update_reflect_add, update_reflect_add, hf, hf, hf]
  by_cases hl : l = i
  · simp only [hl, ↓reduceIte, neg_neg]; ring
  · simp only [hl, ↓reduceIte]; ring

end FiniteDifference
