module

public import Solution.Bridge

/-!
# Compatible initial data for the finite difference heat equation

The error bound of `Feec.Models.Cube.FiniteDifferenceHeat.finiteDifferenceHeat` for a rational
scheme of order `m` carries the factor `‖Δₕ^{m+1} v‖_∞` of the discrete datum `v`. For the nodal
interpolant `v = Iₕ f` of a function `f` that is odd under the reflections in the faces of the
cube `b + (0, s)ⁿ` and of class `C^{2m+2}`, it is at most `n^{m+1} B'`, `B'` a bound of the words
`∂²_{i₁} ⋯ ∂²_{i_{m+1}} f` (`norm_fdLaplacian_pow_gridInterp_le`):

* `Δₕ Iₕ f = Iₕ Dₕ f` for the difference Laplacian `Dₕ` on `ℝⁿ` (`diffLap`) of every `f`
  vanishing on the faces (`fdLaplacian_gridInterp`); odd functions vanish on the faces
  (`IsOddAt.eq_zero`) and `Dₕ` keeps them odd (`IsOddAt.diffLap`), so
  `Δₕᵏ Iₕ f = Iₕ Dₕᵏ f` (`fdLaplacian_pow_gridInterp`);
* `Dₕ` commutes with partial derivatives (`partialDeriv_diffLap`) and
  `|Dₕ g| ≤ n sup_i |∂ᵢ² g|` (`abs_diffLap_le`, the second difference), so
  `|Dₕᵏ f| ≤ nᵏ B'` (`abs_iterate_diffLap_le`).
-/

open Set Finset

@[expose] public noncomputable section

namespace TimeStepping

variable {n : ℕ}

/-- The difference Laplacian `(Dₕ f)(x) = Σₗ (f(x + h eₗ) - 2 f(x) + f(x - h eₗ)) / h²` of a
function on `ℝⁿ`. -/
def diffLap (h : ℝ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ l, (f (x + h • Pi.single l 1) - 2 * f x + f (x + (-h) • Pi.single l 1)) / h ^ 2

/-- The word `∂²_{i₁} ⋯ ∂²_{i_k}` of pure second partial derivatives. -/
def secondWord (w : List (Fin n)) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  w.foldr (fun i g => partialDeriv i (partialDeriv i g)) f

/-! ### Smoothness and derivatives -/

theorem contDiff_secondWord {f : (Fin n → ℝ) → ℝ} (w : List (Fin n)) {m : ℕ}
    (hf : ContDiff ℝ (m + 2 * w.length : ℕ) f) : ContDiff ℝ m (secondWord w f) := by
  induction w generalizing m with
  | nil => simpa [secondWord] using hf
  | cons i w ih =>
    have h := ih (m := m + 2) (by
      convert hf using 2; simp only [List.length_cons]; ring)
    have h1 : ContDiff ℝ (m + 1 : ℕ) (partialDeriv i (secondWord w f)) :=
      h.partialDeriv (by exact_mod_cast le_refl (m + 1 + 1)) i
    exact h1.partialDeriv (by exact_mod_cast le_refl (m + 1)) i

theorem contDiff_diffLap (h : ℝ) {f : (Fin n → ℝ) → ℝ} {k : WithTop ℕ∞} (hf : ContDiff ℝ k f) :
    ContDiff ℝ k (diffLap h f) := by
  unfold diffLap
  refine ContDiff.sum fun l _ => ?_
  refine ContDiff.div_const (((hf.comp (contDiff_id.add contDiff_const)).sub
    (contDiff_const.mul hf)).add (hf.comp (contDiff_id.add contDiff_const))) _

/-- `Dₕ` commutes with the partial derivatives of a differentiable function. -/
theorem partialDeriv_diffLap (h : ℝ) {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (i : Fin n) : partialDeriv i (diffLap h f) = diffLap h (partialDeriv i f) := by
  funext x
  have ht : ∀ a : Fin n → ℝ, HasFDerivAt (fun y => f (y + a)) (fderiv ℝ f (x + a)) x :=
    fun a => (hf (x + a)).hasFDerivAt.comp x ((hasFDerivAt_id (𝕜 := ℝ) x).add_const a)
  have hd : HasFDerivAt (diffLap h f) (∑ l, (h ^ 2)⁻¹ • (fderiv ℝ f (x + h • Pi.single l 1) -
      (2 : ℝ) • fderiv ℝ f x + fderiv ℝ f (x + (-h) • Pi.single l 1))) x := by
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
    simp only [diffLap, Finset.sum_apply]
  rw [partialDeriv, hd.fderiv]
  simp only [diffLap, partialDeriv, div_eq_inv_mul]
  simp
  exact Finset.sum_congr rfl fun l _ => by ring

/-- `Dₕ` commutes with the words of second partial derivatives of a `C^{2|w|+1}` function. -/
theorem secondWord_diffLap (h : ℝ) {f : (Fin n → ℝ) → ℝ} (w : List (Fin n))
    (hf : ContDiff ℝ (2 * w.length + 1 : ℕ) f) :
    secondWord w (diffLap h f) = diffLap h (secondWord w f) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hw := ih (hf.of_le (by simp only [List.length_cons]; norm_cast; omega))
    have hc : ContDiff ℝ (1 + 2 : ℕ) (secondWord w f) :=
      contDiff_secondWord w (hf.of_le (by simp only [List.length_cons]; norm_cast; omega))
    show partialDeriv i (partialDeriv i (secondWord w (diffLap h f))) =
      diffLap h (partialDeriv i (partialDeriv i (secondWord w f)))
    rw [hw, partialDeriv_diffLap h (hc.differentiable (by norm_num)),
      partialDeriv_diffLap h (f := partialDeriv i (secondWord w f))
        ((hc.partialDeriv (m := (1 + 1 : ℕ)) (by norm_num) i).differentiable (by norm_num))]

/-! ### The bound -/

/-- **The difference Laplacian is bounded by the second derivatives**:
`|Dₕ g(x)| ≤ n B` for `|∂ᵢ² g| ≤ B`, `h ≠ 0` (`abs_axis_secondDiff_le`). -/
theorem abs_diffLap_le {h B : ℝ} (hh : h ≠ 0) {g : (Fin n → ℝ) → ℝ} (hg : ContDiff ℝ 2 g)
    (hB : ∀ i y, |partialDeriv i (partialDeriv i g) y| ≤ B) (x : Fin n → ℝ) :
    |diffLap h g x| ≤ n * B := by
  unfold diffLap
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have h2 : 0 < h ^ 2 := by positivity
  calc ∑ l, |(g (x + h • Pi.single l 1) - 2 * g x + g (x + (-h) • Pi.single l 1)) / h ^ 2|
      ≤ ∑ _l : Fin n, B := Finset.sum_le_sum fun l _ => by
        rw [abs_div, abs_of_pos h2, div_le_iff₀ h2]
        exact Feec.abs_axis_secondDiff_le hg x l fun τ _ => hB l _
    _ = n * B := by simp

/-- **`|Dₕᵏ f| ≤ nᵏ B'`** for `f ∈ C^{2k}` with `|∂²_{i₁} ⋯ ∂²_{i_k} f| ≤ B'`. -/
theorem abs_iterate_diffLap_le {h : ℝ} (hh : h ≠ 0) (k : ℕ) {f : (Fin n → ℝ) → ℝ} {B : ℝ}
    (hf : ContDiff ℝ (2 * k : ℕ) f)
    (hB : ∀ (l : Fin k → Fin n) x, |secondWord (List.ofFn l) f x| ≤ B) (x : Fin n → ℝ) :
    |(diffLap h)^[k] f x| ≤ n ^ k * B := by
  induction k generalizing f B with
  | zero => simpa [secondWord] using hB Fin.elim0 x
  | succ k ih =>
    rw [Function.iterate_succ_apply, pow_succ, mul_assoc]
    refine ih (contDiff_diffLap h (hf.of_le (by norm_cast; omega))) (fun l y => ?_)
    have hw : ContDiff ℝ (2 * (List.ofFn l).length + 1 : ℕ) f :=
      hf.of_le (by simp only [List.length_ofFn]; norm_cast; omega)
    rw [secondWord_diffLap h _ hw]
    refine abs_diffLap_le hh (contDiff_secondWord (m := 2) _
      (hf.of_le (by simp only [List.length_ofFn]; norm_cast; omega))) (fun i z => ?_) y
    have := hB (Fin.cons i l) z
    rwa [List.ofFn_succ, Fin.cons_zero] at this

/-! ### Odd functions and the grid -/

/-- `f` is **odd under the reflection** `xᵢ ↦ 2c - xᵢ`. -/
def IsOddAt (i : Fin n) (c : ℝ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x, f (Function.update x i (2 * c - x i)) = -f x

theorem IsOddAt.eq_zero {i : Fin n} {c : ℝ} {f : (Fin n → ℝ) → ℝ} (hf : IsOddAt i c f)
    {x : Fin n → ℝ} (hx : x i = c) : f x = 0 := by
  have h := hf x
  rw [hx, show 2 * c - c = c by ring, Function.update_eq_self_iff.2 hx.symm] at h
  linarith

theorem update_reflect_add (i l : Fin n) (c t : ℝ) (x : Fin n → ℝ) :
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
theorem IsOddAt.diffLap {i : Fin n} {c : ℝ} {f : (Fin n → ℝ) → ℝ} (hf : IsOddAt i c f)
    (h : ℝ) : IsOddAt i c (diffLap h f) := by
  intro x
  unfold TimeStepping.diffLap
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [update_reflect_add, update_reflect_add, hf, hf, hf]
  by_cases hl : l = i
  · simp only [hl, ↓reduceIte, neg_neg]; ring
  · simp only [hl, ↓reduceIte]; ring

/-- `f` is odd under the reflections in the faces of the cube `b + (0, s)ⁿ`. -/
def IsOddCube (b : Fin n → ℝ) (s : ℝ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ i, IsOddAt i (b i) f ∧ IsOddAt i (b i + s) f

theorem IsOddCube.diffLap {b : Fin n → ℝ} {s : ℝ} {f : (Fin n → ℝ) → ℝ} (hf : IsOddCube b s f)
    (h : ℝ) : IsOddCube b s (diffLap h f) :=
  fun i => ⟨(hf i).1.diffLap h, (hf i).2.diffLap h⟩

theorem gridNode_add_single (b : Fin n → ℝ) (h : ℝ) (p : Fin n → ℤ) (l : Fin n) (e : ℤ) :
    (b + h • fun j => ((p + e • Pi.single l 1 : Fin n → ℤ) j : ℝ)) =
      (b + h • fun j => (p j : ℝ)) + (h * e) • Pi.single l 1 := by
  funext j
  by_cases hj : j = l
  · subst hj; simp; ring
  · simp [hj]

/-- **`Δₕ Iₕ f = Iₕ Dₕ f`** for `f` vanishing at the boundary nodes of the grid. -/
theorem fdLaplacian_gridInterp (b : Fin n → ℝ) (h : ℝ) (N : ℕ) {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ (q : Fin n → ℤ) j, (q j = 0 ∨ q j = N + 1) → f (b + h • fun j => (q j : ℝ)) = 0) :
    fdLaplacian (gridNodes n N) h (gridInterp b h N f) = gridInterp b h N (diffLap h f) := by
  rw [fdLaplacian_eq]
  funext p
  have hp : ∀ j, 0 < (p : Fin n → ℤ) j ∧ (p : Fin n → ℤ) j < N + 1 := fun j => by
    have := Fintype.mem_piFinset.1 p.2 j
    simpa using this
  rw [FiniteDifference.laplacian_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  have key : ∀ e : ℤ, (e = 1 ∨ e = -1) →
      FiniteDifference.zeroExt (gridInterp b h N f) ((p : Fin n → ℤ) + e • Pi.single l 1) =
        f ((b + h • fun j => ((p : Fin n → ℤ) j : ℝ)) + (h * e) • Pi.single l 1) := by
    intro e he
    rw [← gridNode_add_single]
    unfold FiniteDifference.zeroExt
    split_ifs with hq
    · rfl
    · symm
      refine hf _ l ?_
      have hl := hp l
      have : ¬ (0 < ((p : Fin n → ℤ) + e • Pi.single l 1 : Fin n → ℤ) l ∧
          ((p : Fin n → ℤ) + e • Pi.single l 1 : Fin n → ℤ) l < N + 1) := by
        intro hcon
        refine hq (Fintype.mem_piFinset.2 fun j => ?_)
        by_cases hj : j = l
        · subst hj; simpa using hcon
        · simpa [hj] using hp j
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at this ⊢
      omega
  have h1 := key 1 (Or.inl rfl)
  rw [one_smul, Int.cast_one, mul_one] at h1
  have h2 := key (-1) (Or.inr rfl)
  rw [neg_smul, one_smul, ← sub_eq_add_neg, Int.cast_neg, Int.cast_one, mul_neg, mul_one] at h2
  rw [h1, h2]
  rfl

theorem fdLaplacian_pow_gridInterp (b : Fin n → ℝ) {s : ℝ} (N : ℕ) {f : (Fin n → ℝ) → ℝ}
    (hf : IsOddCube b s f) (k : ℕ) :
    (fdLaplacian (gridNodes n N) (s / (N + 1 : ℕ)) ^ k) (gridInterp b (s / (N + 1 : ℕ)) N f) =
      gridInterp b (s / (N + 1 : ℕ)) N ((diffLap (s / (N + 1 : ℕ)))^[k] f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Function.iterate_succ_apply, ← ih (hf.diffLap _)]
    show (fdLaplacian (gridNodes n N) (s / (N + 1 : ℕ)) ^ k)
      (fdLaplacian (gridNodes n N) (s / (N + 1 : ℕ)) (gridInterp b (s / (N + 1 : ℕ)) N f)) = _
    congr 1
    refine fdLaplacian_gridInterp b _ N fun q j hq => ?_
    rcases hq with hq | hq
    · exact (hf j).1.eq_zero (by simp [hq])
    · refine (hf j).2.eq_zero ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hq]
      push_cast
      field_simp

/-- **The discrete datum of compatible initial data**: for `f ∈ C^{2m+2}` odd in the faces of
`b + (0, s)ⁿ` with `|∂²_{i₁} ⋯ ∂²_{i_{m+1}} f| ≤ B'`, `‖Δₕ^{m+1} Iₕ f‖_∞ ≤ n^{m+1} B'`. -/
theorem norm_fdLaplacian_pow_gridInterp_le (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N m : ℕ)
    {f : (Fin n → ℝ) → ℝ} {B : ℝ} (hf : ContDiff ℝ (2 * m + 2) f) (hodd : IsOddCube b s f)
    (hB : ∀ (l : Fin (m + 1) → Fin n) x, |secondWord (List.ofFn l) f x| ≤ B) :
    ‖(fdLaplacian (gridNodes n N) (s / (N + 1 : ℕ)) ^ (m + 1))
      (gridInterp b (s / (N + 1 : ℕ)) N f)‖ ≤ n ^ (m + 1) * B := by
  have hh : s / (N + 1 : ℕ) ≠ 0 := by positivity
  have h0 : 0 ≤ (n : ℝ) ^ (m + 1) * B := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact mul_nonneg (by positivity)
        ((abs_nonneg _).trans (hB (fun _ => ⟨0, hn⟩) 0))
  rw [fdLaplacian_pow_gridInterp b N hodd]
  refine (pi_norm_le_iff_of_nonneg h0).2 fun p => ?_
  rw [Real.norm_eq_abs]
  exact abs_iterate_diffLap_le hh (m + 1) (by exact_mod_cast hf) hB _

end TimeStepping
