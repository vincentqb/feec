module

public import Feec.TimeStepping.Convergence

/-!
# Forced one-step schemes and discrete liftings

A one-step scheme `P` with a load `gₙ` produces the **forced iterates** `W₀ = v`,
`Wₙ₊₁ = P Wₙ + gₙ` (`forcedIter`). By the discrete Duhamel formula they are the unforced
iterates plus the propagated loads, `Wₙ = Pⁿ v + Σ_{j<n} Pʲ g_{n−1−j}` (`forcedIter_eq`), and
stability plus consistency bounds their error against every comparison sequence
(`norm_forcedIter_sub_le`, from `norm_sub_le_of_step`).

## Prescribed boundary degrees of freedom are a discrete lifting

The Crank–Nicolson step with prescribed boundary DOFs (`IsDirichletCNStep V₀ A s f g' u u'`, the
scheme of `fem4gr` and of [QuennevilleBelair2015], Ch. 7) is the discrete counterpart of the
reduction of inhomogeneous boundary data to a forcing (`Feec.Evolution.isBoundarySolution_iff`):
write `uₙ = gₙ + Wₙ` with `gₙ` any field with the prescribed boundary DOFs (a **discrete lifting**,
e.g. the interpolant of the exact solution) and `Wₙ ∈ V₀`. Then
(`IsDirichletCNStep.sub_eq_cayley_add`, `eq_add_forcedIter_of_isDirichletCNStep`,
`exists_eq_add_forcedIter_of_isDirichletCNStep`)

`Wₙ₊₁ = cayley(A₀, s) Wₙ + bₙ`,

the forced iterates of the Crank–Nicolson step `cayley(A₀, s)` (`compressCN`) of the
**compression** `A₀ = P_{V₀} A|_{V₀}` (`compress`), the operator of the scheme on the fields with
vanishing boundary DOFs, with the load `bₙ ∈ V₀` the interior part of the Dirichlet step taken from
the lifting itself (`gₙ ↦ gₙ₊₁ + bₙ`; it exists by `existsUnique_isDirichletCNStep`). This has
the form of the step `cayley(Lₕ, τ/2)` of `Feec.HilbertComplex.DissipFEEC.crankNicolson` with
`A₀` in place of the discrete generator `Lₕ`; for the Whitney spaces of the thesis `A₀` should be
`𝐝ₕ − 𝐝ₕ*` on the subcomplex `V̊ₕ`, but its identification with the generator of a conforming
window is open.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7 (Crank–Nicolson with the boundary data of the exact solution)
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 8
  (single step methods for the inhomogeneous equation: stability and consistency)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset

@[expose] public noncomputable section

namespace Feec.TimeStepping

/-! ### Forced iterates -/

section Forced

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {P : X →L[𝕜] X} {v : X} {g : ℕ → X}

/-- The **forced iterates** of the one-step scheme `P` with load `g`: `W₀ = v`,
`Wₙ₊₁ = P Wₙ + gₙ`. -/
def forcedIter (P : X →L[𝕜] X) (v : X) (g : ℕ → X) : ℕ → X
  | 0 => v
  | n + 1 => P (forcedIter P v g n) + g n

@[simp] theorem forcedIter_zero : forcedIter P v g 0 = v := rfl

theorem forcedIter_succ (n : ℕ) : forcedIter P v g (n + 1) = P (forcedIter P v g n) + g n := rfl

/-- **The discrete Duhamel formula**: `Wₙ = Pⁿ v + Σ_{j<n} Pʲ g_{n−1−j}`. -/
theorem forcedIter_eq (n : ℕ) :
    forcedIter P v g n = (P ^ n) v + ∑ j ∈ range n, (P ^ j) (g (n - 1 - j)) := by
  simpa using sub_eq_sum_of_step (w := 0) (fun k => forcedIter_succ (P := P) (v := v) (g := g) k) n

/-- Without load, the forced iterates are the iterates `Pⁿ v`. -/
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

/-- The **compression** `A₀ = P_{V₀} A|_{V₀}` of `A` to `V₀`: the operator of the scheme on the
fields with vanishing boundary degrees of freedom. -/
def compress : V₀ →L[ℝ] V₀ :=
  LinearMap.toContinuousLinearMap (V₀.orthogonalProjectionOnto.toLinearMap ∘ₗ A ∘ₗ V₀.subtype)

variable {V₀ A}

@[simp] theorem inner_compress (w v : V₀) : ⟪(compress V₀ A w : V), v⟫ = ⟪A w, v⟫ := by
  have e := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (K := V₀) v (A w)
  rw [Submodule.coe_inner] at e
  exact e

variable (V₀ A) in
/-- The **Crank–Nicolson step of the compression**, `cayley(A₀, s)` (`Feec.TimeStepping.cayley`):
the step of the interior part of the Dirichlet CN scheme. -/
def compressCN (s : ℝ) : V₀ →L[ℝ] V₀ := cayley ((compress V₀ A : V₀ →ₗ[ℝ] V₀).toPMap ⊤) s

/-- A dissipative form on `V₀` has a dissipative compression. -/
theorem re_inner_compress_self_nonpos (hA : ∀ w ∈ V₀, ⟪A w, w⟫ ≤ 0) (w : V₀) :
    RCLike.re ⟪compress V₀ A w, w⟫ ≤ 0 := by
  simpa [inner_compress] using hA w w.2

/-- **Prescribed boundary degrees of freedom are a discrete lifting**: let `u'` be a Dirichlet CN
step from `u` (`A` dissipative on `V₀`, `s > 0`), `g` a field with the boundary DOFs of `u`
(`u − g ∈ V₀`), and `g' + b`, `b ∈ V₀`, the Dirichlet CN step from `g` with the same data. Then
`u' − g' = cayley(A₀, s)(u − g) + b`: the interior part is advanced by the Crank–Nicolson step of
the compression `A₀`, with the load `b`. -/
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

/-- **The Dirichlet CN iterates are lifted forced Crank–Nicolson iterates**: for Dirichlet CN
iterates `uₙ` with boundary data `gₙ₊₁` and loads `fₙ` for `n < N`, `u₀ − g₀ ∈ V₀`, and the
interior parts `bₙ ∈ V₀` of the Dirichlet steps from the lifting `gₙ ↦ gₙ₊₁ + bₙ`,
`uₙ = gₙ + Wₙ` for `n ≤ N`, `Wₙ` the forced iterates of `cayley(A₀, s)` with load `b` from
`u₀ − g₀`. -/
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

/-- **The loads of the discrete lifting exist**: for Dirichlet CN iterates with `u₀ − g₀ ∈ V₀`
(`A` dissipative on `V₀`, `s > 0`) there are loads `bₙ ∈ V₀` (the interior parts of the Dirichlet
steps from the lifting, `existsUnique_isDirichletCNStep`) with `uₙ = gₙ + Wₙ`, `Wₙ` the forced
Crank–Nicolson iterates of the compression from `u₀ − g₀`. -/
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
