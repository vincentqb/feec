module

public import Feec.Evolution.Energy

/-!
# Error bound skeleton for Galerkin approximations of evolution problems

The energy-method error estimate for a semi-discrete Galerkin scheme splits the error
`u − uₕ = (u − p) + (p − uₕ)` with `p` a projection of the exact solution `u` (elliptic,
orthogonal, …) onto the discrete space. The first term is a pure approximation error; the
second, the *projected error* `ε = p − uₕ`, lies in the discrete space, and testing the error
equation with `ε` (the spatial form being accretive, or skew, on the discrete space) gives
`re ⟪ε', ε⟫ ≤ -λ ‖ε‖² + g ‖ε‖`, where `g` collects the consistency errors (typically
`‖(p − u)'‖`, plus `‖p − u‖` for an elliptic projection with a zero-order term).

* `norm_sub_le_of_projected_error_decay`: the resulting bound with decay rate `λ`;
* `norm_sub_le_of_projected_error`: the case `λ = 0`,
  `‖u t − uₕ t‖ ≤ ‖u t − p t‖ + ‖p a − uₕ a‖ + ∫ₐᵗ g`.

Thesis: Thm 4.14.
-/

open Set

@[expose] public noncomputable section

namespace Feec.Variational

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- **Galerkin error bound with decay rate `λ`.** Let `u` be the exact solution, `uₕ` the
discrete one and `p` a projection of `u`. If the projected error `ε = p − uₕ` is continuous on
`[a,b]` with right derivative `ε'` on `[a,b)`, and the error equation tested with `ε` gives
`re ⟪ε', ε⟫ ≤ -λ ‖ε‖² + g ‖ε‖` for a continuous `g ≥ 0`, then on `[a,b]`
`‖u t − uₕ t‖ ≤ ‖u t − p t‖ + e^{-λ(t-a)} ‖p a − uₕ a‖ + ∫ₐᵗ e^{-λ(t-s)} g s`.
Thesis: Thm 4.14. -/
theorem norm_sub_le_of_projected_error_decay {u p uh ε' : ℝ → E} {g : ℝ → ℝ} {a b lam : ℝ}
    (hεc : ContinuousOn (fun t => p t - uh t) (Icc a b))
    (hε : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => p t - uh t) (ε' t) (Ici t) t)
    (hgc : ContinuousOn g (Icc a b)) (hg0 : ∀ t ∈ Ico a b, 0 ≤ g t)
    (herr : ∀ t ∈ Ico a b,
      RCLike.re ⟪ε' t, p t - uh t⟫ ≤ -lam * ‖p t - uh t‖ ^ 2 + g t * ‖p t - uh t‖) :
    ∀ t ∈ Icc a b, ‖u t - uh t‖ ≤ ‖u t - p t‖ + Real.exp (-lam * (t - a)) * ‖p a - uh a‖ +
      ∫ s in a..t, Real.exp (-lam * (t - s)) * g s := by
  intro t ht
  have h := Evolution.Energy.norm_le_of_re_inner_deriv_le (𝕜 := 𝕜) hεc hε hgc hg0 herr t ht
  calc ‖u t - uh t‖ = ‖(u t - p t) + (p t - uh t)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖u t - p t‖ + ‖p t - uh t‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- **Galerkin error bound.** With the notation of `norm_sub_le_of_projected_error_decay`, if
`re ⟪ε', ε⟫ ≤ g ‖ε‖` (the spatial form is accretive on the discrete space) then
`‖u t − uₕ t‖ ≤ ‖u t − p t‖ + ‖p a − uₕ a‖ + ∫ₐᵗ g` on `[a,b]`.
Thesis: Thm 4.14. -/
theorem norm_sub_le_of_projected_error {u p uh ε' : ℝ → E} {g : ℝ → ℝ} {a b : ℝ}
    (hεc : ContinuousOn (fun t => p t - uh t) (Icc a b))
    (hε : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => p t - uh t) (ε' t) (Ici t) t)
    (hgc : ContinuousOn g (Icc a b)) (hg0 : ∀ t ∈ Ico a b, 0 ≤ g t)
    (herr : ∀ t ∈ Ico a b, RCLike.re ⟪ε' t, p t - uh t⟫ ≤ g t * ‖p t - uh t‖) :
    ∀ t ∈ Icc a b, ‖u t - uh t‖ ≤ ‖u t - p t‖ + ‖p a - uh a‖ + ∫ s in a..t, g s := by
  intro t ht
  have h := norm_sub_le_of_projected_error_decay (𝕜 := 𝕜) (u := u) (lam := 0) hεc hε hgc hg0
    (fun s hs => by simpa using herr s hs) t ht
  simpa using h

end Feec.Variational
