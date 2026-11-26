module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Feec.Variational.InfSup

/-!
# Counterexamples on `ℓ²(ℕ, 𝕜)`

On `ℓ²(ℕ, 𝕜)`, a densely defined operator whose kernel is not closed (cf.
[QuennevilleBelair2015], §4.3), and a bounded form solvable for every right-hand side that
satisfies no inf-sup condition (cf. [QuennevilleBelair2015], Thm 4.9).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.3, Thm 4.9

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace

@[expose] public noncomputable section

namespace Feec.Counterexamples

namespace Ell2

variable (𝕜 : Type*) [RCLike 𝕜]

/-- `ℓ²(ℕ, 𝕜)`. -/
abbrev L2 := lp (fun _ : ℕ => 𝕜) 2

/-! ### Finitely supported sequences -/

/-- Finitely supported sequences: the span of the `lp.single` vectors. -/
def finSupp : Submodule 𝕜 (L2 𝕜) :=
  Submodule.span 𝕜 (Set.range fun p : ℕ × 𝕜 => lp.single 2 p.1 p.2)

variable {𝕜}

theorem finSupp_eventually_zero {f : L2 𝕜} (hf : f ∈ finSupp 𝕜) : ∃ N, ∀ n ≥ N, f n = 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨i, a⟩, rfl⟩ := hx
    exact ⟨i + 1, fun n hn => by
      simp only; exact lp.single_apply_ne (E := fun _ : ℕ => 𝕜) 2 i a (show n ≠ i by omega)⟩
  | zero => exact ⟨0, fun n _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hy
    refine ⟨max N M, fun n hn => ?_⟩
    rw [lp.coeFn_add, Pi.add_apply, hN n (le_of_max_le_left hn), hM n (le_of_max_le_right hn),
      add_zero]
  | smul a x _ hx =>
    obtain ⟨N, hN⟩ := hx
    exact ⟨N, fun n hn => by rw [lp.coeFn_smul, Pi.smul_apply, hN n hn, smul_zero]⟩

theorem dense_finSupp : Dense (finSupp 𝕜 : Set (L2 𝕜)) := by
  intro f
  refine mem_closure_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top f) ?_
  refine Filter.Eventually.of_forall fun s => ?_
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨(i, f i), rfl⟩

variable (𝕜) in
/-- The geometric sequence `(1/2)ⁿ` in `ℓ²`. -/
def geom : L2 𝕜 :=
  ⟨fun n => ((1 / 2 : ℝ) ^ n : ℝ), memℓp_gen <| by
    have h : ∀ n : ℕ, ‖(((1 / 2 : ℝ) ^ n : ℝ) : 𝕜)‖ ^ (2 : ENNReal).toReal = (1 / 4 : ℝ) ^ n := by
      intro n
      rw [RCLike.norm_ofReal, ENNReal.toReal_ofNat, abs_of_nonneg (by positivity), Real.rpow_two,
        ← pow_mul, mul_comm, pow_mul]
      norm_num
    simp_rw [h]
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)⟩

theorem not_isClosed_finSupp : ¬ IsClosed (finSupp 𝕜 : Set (L2 𝕜)) := by
  intro h
  have hg : geom 𝕜 ∈ finSupp 𝕜 := by
    have := (dense_finSupp (𝕜 := 𝕜)).closure_eq ▸ (Set.mem_univ (geom 𝕜))
    rwa [h.closure_eq] at this
  obtain ⟨N, hN⟩ := finSupp_eventually_zero hg
  have := hN N le_rfl
  change ((((1 / 2 : ℝ) ^ N : ℝ)) : 𝕜) = 0 at this
  exact pow_ne_zero N (by norm_num : (1 / 2 : ℝ) ≠ 0) (RCLike.ofReal_eq_zero.1 this)

/-! ### The backward shift -/

private lemma two_toReal_pos : 0 < (2 : ENNReal).toReal := by norm_num

theorem memℓp_shift (x : L2 𝕜) : Memℓp (fun n => x (n + 1)) 2 := by
  have hx := (memℓp_gen_iff two_toReal_pos).1 (lp.memℓp x)
  exact (memℓp_gen_iff two_toReal_pos).2 ((summable_nat_add_iff 1).2 hx)

variable (𝕜) in
/-- The backward shift `(S x)ₙ = xₙ₊₁` as a linear map on `ℓ²`. -/
def shiftₗ : L2 𝕜 →ₗ[𝕜] L2 𝕜 where
  toFun x := ⟨fun n => x (n + 1), memℓp_shift x⟩
  map_add' x y := by ext n; rfl
  map_smul' c x := by ext n; rfl

@[simp] theorem shiftₗ_apply (x : L2 𝕜) (n : ℕ) : shiftₗ 𝕜 x n = x (n + 1) := rfl

theorem norm_shiftₗ_le (x : L2 𝕜) : ‖shiftₗ 𝕜 x‖ ≤ ‖x‖ := by
  refine lp.norm_le_of_forall_sum_le two_toReal_pos (norm_nonneg _) fun s => ?_
  have hs := ((lp.memℓp x).summable two_toReal_pos)
  calc ∑ i ∈ s, ‖shiftₗ 𝕜 x i‖ ^ (2 : ENNReal).toReal
      = ∑ j ∈ s.map ⟨Nat.succ, Nat.succ_injective⟩, ‖x j‖ ^ (2 : ENNReal).toReal := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑' j, ‖x j‖ ^ (2 : ENNReal).toReal :=
        hs.sum_le_tsum _ fun i _ => by positivity
    _ = ‖x‖ ^ (2 : ENNReal).toReal := (lp.norm_rpow_eq_tsum two_toReal_pos x).symm

variable (𝕜) in
/-- The backward shift on `ℓ²` as a bounded operator. -/
def shift : L2 𝕜 →L[𝕜] L2 𝕜 := (shiftₗ 𝕜).mkContinuous 1 fun x => by simpa using norm_shiftₗ_le x

@[simp] theorem shift_apply (x : L2 𝕜) (n : ℕ) : shift 𝕜 x n = x (n + 1) := rfl

private theorem memℓp_unshift (f : L2 𝕜) :
    Memℓp (fun n => Nat.casesOn (motive := fun _ => 𝕜) n 0 fun m => f m) 2 := by
  have hf := (memℓp_gen_iff two_toReal_pos).1 (lp.memℓp f)
  exact (memℓp_gen_iff two_toReal_pos).2 ((summable_nat_add_iff 1).1 hf)

theorem shift_surjective : Function.Surjective (shift 𝕜) := fun f =>
  ⟨⟨_, memℓp_unshift f⟩, by ext n; rfl⟩

theorem shift_single : shift 𝕜 (lp.single 2 0 (1 : 𝕜)) = 0 := by
  ext n
  simp

theorem not_injective_shift : ¬ Function.Injective (shift 𝕜) := fun h => by
  have h1 := h (shift_single.trans (map_zero _).symm)
  have := congrArg (fun x : L2 𝕜 => x 0) h1
  simp at this

end Ell2

open Ell2

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Some densely defined operator on `ℓ²(ℕ, 𝕜)` vanishing on its domain has a non-closed kernel. -/
theorem exists_dense_not_isClosed_ker :
    ∃ T : L2 𝕜 →ₗ.[𝕜] L2 𝕜, Dense (T.domain : Set (L2 𝕜)) ∧ (∀ x : T.domain, T x = 0) ∧
      ¬ IsClosed (T.ker : Set (L2 𝕜)) := by
  refine ⟨⟨finSupp 𝕜, 0⟩, dense_finSupp, fun _ => rfl, ?_⟩
  have hker : (⟨finSupp 𝕜, 0⟩ : L2 𝕜 →ₗ.[𝕜] L2 𝕜).ker = finSupp 𝕜 := by
    ext x
    rw [LinearPMap.mem_ker_iff]
    exact ⟨fun ⟨y, hy, _⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl, rfl⟩⟩
  rw [hker]
  exact not_isClosed_finSupp

theorem not_forall_isClosed_ker :
    ¬ ∀ T : L2 𝕜 →ₗ.[𝕜] L2 𝕜, Dense (T.domain : Set (L2 𝕜)) → IsClosed (T.ker : Set (L2 𝕜)) :=
  fun h => by
    obtain ⟨T, hd, -, hc⟩ := exists_dense_not_isClosed_ker (𝕜 := 𝕜)
    exact hc (h T hd)

namespace Ell2

variable (𝕜) in
/-- The sesquilinear form `B u v = ⟪v, S u⟫` of the backward shift `S`. -/
def shiftForm : L2 𝕜 →L[𝕜] L2 𝕜 →L⋆[𝕜] 𝕜 := (innerSLFlip 𝕜).comp (shift 𝕜)

@[simp] theorem shiftForm_apply (u v : L2 𝕜) : shiftForm 𝕜 u v = ⟪v, shift 𝕜 u⟫_𝕜 := rfl

theorem exists_shiftForm_eq (f : L2 𝕜) : ∃ u, ∀ v, shiftForm 𝕜 u v = ⟪v, f⟫_𝕜 := by
  obtain ⟨u, hu⟩ := shift_surjective (𝕜 := 𝕜) f
  exact ⟨u, fun v => by simp [hu]⟩

theorem separatingRight_shiftForm : Variational.SeparatingRight (shiftForm 𝕜) := fun v hv => by
  obtain ⟨u, hu⟩ := shift_surjective (𝕜 := 𝕜) v
  have := hv u
  rw [shiftForm_apply, hu] at this
  exact inner_self_eq_zero.mp this

theorem not_infSup_shiftForm (γ : ℝ) : ¬ Variational.InfSup (shiftForm 𝕜) γ := fun hγ => by
  have := hγ.le (lp.single 2 0 (1 : 𝕜))
  rw [shiftForm, ContinuousLinearMap.comp_apply, shift_single, map_zero, norm_zero,
    lp.norm_single (by norm_num), norm_one, mul_one] at this
  linarith [hγ.pos]

theorem not_injective_shiftForm : ¬ Function.Injective (shiftForm 𝕜) := fun h =>
  not_injective_shift (𝕜 := 𝕜) fun x y hxy => h (by
    rw [shiftForm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hxy])

end Ell2

/-- Some bounded form on `ℓ²(ℕ, 𝕜)` is solvable for every right-hand side and separating in the
second slot, but satisfies no inf-sup condition and is not injective. -/
theorem surjective_not_infSup :
    ∃ B : L2 𝕜 →L[𝕜] L2 𝕜 →L⋆[𝕜] 𝕜, (∀ f : L2 𝕜, ∃ u, ∀ v, B u v = ⟪v, f⟫_𝕜) ∧
      Variational.SeparatingRight B ∧ (∀ γ, ¬ Variational.InfSup B γ) ∧
      ¬ Function.Injective B :=
  ⟨shiftForm 𝕜, exists_shiftForm_eq, separatingRight_shiftForm, not_infSup_shiftForm,
    not_injective_shiftForm⟩

end Feec.Counterexamples
