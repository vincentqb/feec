module

public import Feec.TimeStepping.Convergence

/-!
# Forced one-step schemes and discrete liftings

Forced iterates `Wₙ₊₁ = P Wₙ + gₙ`, and the Crank–Nicolson step with prescribed boundary DOFs of
[QuennevilleBelair2015], Ch. 7, as a lifting plus forced iterates of the compressed operator.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset

@[expose] public noncomputable section

namespace Feec.TimeStepping

/-! ### Forced iterates -/

section Forced

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {P : X →L[𝕜] X} {v : X} {g : ℕ → X}

/-- The forced iterates `W₀ = v`, `Wₙ₊₁ = P Wₙ + gₙ` of the one-step scheme `P` with load `g`. -/
def forcedIter (P : X →L[𝕜] X) (v : X) (g : ℕ → X) : ℕ → X
  | 0 => v
  | n + 1 => P (forcedIter P v g n) + g n

@[simp] theorem forcedIter_zero : forcedIter P v g 0 = v := rfl

theorem forcedIter_succ (n : ℕ) : forcedIter P v g (n + 1) = P (forcedIter P v g n) + g n := rfl

/-- **The discrete Duhamel formula**: `Wₙ = Pⁿ v + Σ_{j<n} Pʲ g_{n−1−j}`. -/
theorem forcedIter_eq (n : ℕ) :
    forcedIter P v g n = (P ^ n) v + ∑ j ∈ range n, (P ^ j) (g (n - 1 - j)) := by
  simpa using sub_eq_sum_of_step (w := 0) (fun k => forcedIter_succ (P := P) (v := v) (g := g) k) n

@[simp] theorem forcedIter_zero_load (n : ℕ) : forcedIter P v 0 n = (P ^ n) v := by
  simp [forcedIter_eq]

/-- **Stability plus consistency for forced iterates**: if `‖Pᵏ‖ ≤ M` for `k ≤ n`, then for every
comparison sequence `wₖ`, `‖Wₙ - wₙ‖ ≤ M (‖v - w₀‖ + Σ_{k<n} ‖wₖ₊₁ - P wₖ - gₖ‖)`. -/
theorem norm_forcedIter_sub_le {M : ℝ} {n : ℕ} (hP : ∀ k ≤ n, ‖P ^ k‖ ≤ M) (w : ℕ → X) :
    ‖forcedIter P v g n - w n‖ ≤
      M * (‖v - w 0‖ + ∑ k ∈ range n, ‖w (k + 1) - P (w k) - g k‖) :=
  norm_sub_le_of_step hP fun _ => rfl

end Forced

/-! ### Prescribed boundary degrees of freedom as a discrete lifting -/

section DirichletLifting

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (V₀ : Submodule ℝ V) (A : V →ₗ[ℝ] V)

/-- The compression `A₀ = P_{V₀} A|_{V₀}` of `A` to the fields with vanishing boundary DOFs. -/
def compress : V₀ →L[ℝ] V₀ :=
  LinearMap.toContinuousLinearMap (V₀.orthogonalProjectionOnto.toLinearMap ∘ₗ A ∘ₗ V₀.subtype)

variable {V₀ A}

@[simp] theorem inner_compress (w v : V₀) : ⟪(compress V₀ A w : V), v⟫ = ⟪A w, v⟫ := by
  have e := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (K := V₀) v (A w)
  rw [Submodule.coe_inner] at e
  exact e

variable (V₀ A) in
/-- The **Crank–Nicolson step of the compression**, `cayley(A₀, s)`. -/
def compressCN (s : ℝ) : V₀ →L[ℝ] V₀ := cayley ((compress V₀ A : V₀ →ₗ[ℝ] V₀).toPMap ⊤) s

theorem re_inner_compress_self_nonpos (hA : ∀ w ∈ V₀, ⟪A w, w⟫ ≤ 0) (w : V₀) :
    RCLike.re ⟪compress V₀ A w, w⟫ ≤ 0 := by
  simpa [inner_compress] using hA w w.2

theorem IsDirichletCNStep.sub_eq_cayley_add (hA : ∀ w ∈ V₀, ⟪A w, w⟫ ≤ 0) {s : ℝ} (hs : 0 < s)
    {f g g' u u' : V} {b : V₀} (h : IsDirichletCNStep V₀ A s f g' u u') (hu : u - g ∈ V₀)
    (hb : IsDirichletCNStep V₀ A s f g' g (g' + b)) :
    u' - g' = (compressCN V₀ A s ⟨u - g, hu⟩ : V) + b := by
  have hm := (compress V₀ A).isMDissipative_toPMap_top (re_inner_compress_self_nonpos hA)
  have hR := hm.isResolvent (inv_pos.2 hs)
  rw [RCLike.ofReal_real_eq_id, id] at hR
  have hstep := isCNStep_cayley hR hs.ne' ⟨u - g, hu⟩
  have hw₁ : u' - g' - b ∈ V₀ := V₀.sub_mem h.1 b.2
  have hcn : IsCNStep ((compress V₀ A : V₀ →ₗ[ℝ] V₀).toPMap ⊤) s ⟨u - g, hu⟩ ⟨_, hw₁⟩ := by
    refine ⟨trivial, ext_inner_right ℝ fun v => ?_⟩
    have e1 := h.2 v v.2
    have e2 := hb.2 v v.2
    change ⟪((⟨_, hw₁⟩ - ⟨u - g, hu⟩ : V₀) : V), v⟫ =
      ⟪(((s : ℝ) • compress V₀ A (⟨_, hw₁⟩ + ⟨u - g, hu⟩) : V₀) : V), v⟫
    rw [Submodule.coe_smul, real_inner_smul_left, inner_compress]
    simp only [Submodule.coe_sub, Submodule.coe_add]
    have i1 : u' - g' - b - (u - g) = (u' - u) - (g' + ↑b - g) := by abel
    have i2 : u' - g' - b + (u - g) = (u' + u) - (g' + ↑b + g) := by abel
    rw [i1, i2, inner_sub_left, e1, e2, map_sub, inner_sub_left]
    ring
  have := hcn.unique hm.dissipative hs.le hstep
  rw [compressCN, ← this]
  simp

/-- **The Dirichlet CN iterates are lifted forced Crank–Nicolson iterates** (`A` dissipative on
`V₀`, `s > 0`): `uₙ = gₙ + Wₙ`, `Wₙ` the forced iterates of `cayley(A₀, s)` from `u₀ − g₀` with
the interior loads of the lifting. -/
theorem eq_add_forcedIter_of_isDirichletCNStep (hA : ∀ w ∈ V₀, ⟪A w, w⟫ ≤ 0) {s : ℝ}
    (hs : 0 < s) {N : ℕ} {f g u : ℕ → V} {b : ℕ → V₀}
    (h : ∀ n < N, IsDirichletCNStep V₀ A s (f n) (g (n + 1)) (u n) (u (n + 1)))
    (hb : ∀ n < N, IsDirichletCNStep V₀ A s (f n) (g (n + 1)) (g n) (g (n + 1) + b n))
    (h0 : u 0 - g 0 ∈ V₀) :
    ∀ n ≤ N, u n = g n + ((forcedIter (compressCN V₀ A s)
      ⟨u 0 - g 0, h0⟩ b n : V₀) : V) := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have ih := ih (Nat.le_of_succ_le hn)
    have hu : u n - g n ∈ V₀ := by rw [ih, add_sub_cancel_left]; exact Submodule.coe_mem _
    have e := (h n hn).sub_eq_cayley_add hA hs hu (hb n hn)
    have hw : (⟨u n - g n, hu⟩ : V₀) = forcedIter _ ⟨u 0 - g 0, h0⟩ b n :=
      Subtype.ext (show u n - g n = _ by rw [ih, add_sub_cancel_left])
    rw [hw] at e
    rw [forcedIter_succ, Submodule.coe_add, ← e]
    abel

theorem exists_eq_add_forcedIter_of_isDirichletCNStep (hA : ∀ w ∈ V₀, ⟪A w, w⟫ ≤ 0) {s : ℝ}
    (hs : 0 < s) {N : ℕ} {f g u : ℕ → V}
    (h : ∀ n < N, IsDirichletCNStep V₀ A s (f n) (g (n + 1)) (u n) (u (n + 1)))
    (h0 : u 0 - g 0 ∈ V₀) :
    ∃ b : ℕ → V₀, (∀ n, IsDirichletCNStep V₀ A s (f n) (g (n + 1)) (g n) (g (n + 1) + b n)) ∧
      ∀ n ≤ N, u n = g n + ((forcedIter (compressCN V₀ A s)
        ⟨u 0 - g 0, h0⟩ b n : V₀) : V) := by
  have hA' : ∀ w ∈ V₀, s * ⟪A w, w⟫ ≤ 0 := fun w hw =>
    mul_nonpos_of_nonneg_of_nonpos hs.le (hA w hw)
  have c := fun n => (existsUnique_isDirichletCNStep hA' (f n) (g (n + 1)) (g n)).exists
  refine ⟨fun n => ⟨(c n).choose - g (n + 1), (c n).choose_spec.1⟩, fun n => ?_,
    eq_add_forcedIter_of_isDirichletCNStep hA hs h (fun n _ => ?_) h0⟩ <;>
  · simpa using (c n).choose_spec

end DirichletLifting

end Feec.TimeStepping
