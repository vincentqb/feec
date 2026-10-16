module

public import Feec.ForMathlib.Analysis.Gronwall

/-!
# Energy estimates

The energy estimates for curves in inner product spaces over `𝕜 = ℝ` or `ℂ` live in
`Feec.ForMathlib.Analysis.Gronwall` (root namespace):

* `HasDerivWithinAt.norm_sq_re_inner`: `d/dt ‖e‖² = 2 re ⟪e', e⟫`;
* `norm_le_add_integral_of_re_inner_deriv_le`: `re ⟪e', e⟫ ≤ g ‖e‖` gives
  `‖e t‖ ≤ ‖e a‖ + ∫ₐᵗ g`;
* `norm_le_of_re_inner_deriv_le`: the decay-rate form
  `‖e t‖ ≤ e^{-λ(t-a)} ‖e a‖ + ∫ₐᵗ e^{-λ(t-s)} g s`;
* `norm_le_add_integral_norm_deriv`: `‖e t‖ ≤ ‖e a‖ + ∫ₐᵗ ‖e'‖`.

This module re-exports them under `Feec.Evolution.Energy` for the evolution layer.
-/

open Set

@[expose] public noncomputable section

namespace Feec.Evolution.Energy

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

omit [IsScalarTower ℝ 𝕜 E] in
/-- Right derivative of `‖e‖²` over `𝕜`: `d/dt ‖e‖² = 2 re ⟪e', e⟫`
(`HasDerivWithinAt.norm_sq_re_inner`). -/
theorem hasDerivWithinAt_norm_sq {e : ℝ → E} {e' : E} {s : Set ℝ} {t : ℝ}
    (he : HasDerivWithinAt e e' s t) :
    HasDerivWithinAt (fun r => ‖e r‖ ^ 2) (2 * RCLike.re ⟪e', e t⟫) s t :=
  he.norm_sq_re_inner

omit [IsScalarTower ℝ 𝕜 E] in
/-- **Energy estimate** (`_root_.norm_le_add_integral_of_re_inner_deriv_le`).
Thesis: Lemma 4.12 (corrected). -/
theorem norm_le_add_integral_of_re_inner_deriv_le {e e' : ℝ → E} {g : ℝ → ℝ} {a b : ℝ}
    (hec : ContinuousOn e (Icc a b)) (he : ∀ t ∈ Ico a b, HasDerivWithinAt e (e' t) (Ici t) t)
    (hgc : ContinuousOn g (Icc a b)) (hg0 : ∀ t ∈ Ico a b, 0 ≤ g t)
    (hle : ∀ t ∈ Ico a b, RCLike.re ⟪e' t, e t⟫ ≤ g t * ‖e t‖) :
    ∀ t ∈ Icc a b, ‖e t‖ ≤ ‖e a‖ + ∫ s in a..t, g s :=
  _root_.norm_le_add_integral_of_re_inner_deriv_le (𝕜 := 𝕜) hec he hgc hg0 hle

/-- **Energy estimate with decay rate `λ`** (`_root_.norm_le_of_re_inner_deriv_le`).
Thesis: Lemma 4.12 (corrected). -/
theorem norm_le_of_re_inner_deriv_le {e e' : ℝ → E} {g : ℝ → ℝ} {a b lam : ℝ}
    (hec : ContinuousOn e (Icc a b)) (he : ∀ t ∈ Ico a b, HasDerivWithinAt e (e' t) (Ici t) t)
    (hgc : ContinuousOn g (Icc a b)) (hg0 : ∀ t ∈ Ico a b, 0 ≤ g t)
    (hle : ∀ t ∈ Ico a b, RCLike.re ⟪e' t, e t⟫ ≤ -lam * ‖e t‖ ^ 2 + g t * ‖e t‖) :
    ∀ t ∈ Icc a b, ‖e t‖ ≤ Real.exp (-lam * (t - a)) * ‖e a‖ +
      ∫ s in a..t, Real.exp (-lam * (t - s)) * g s :=
  _root_.norm_le_of_re_inner_deriv_le (𝕜 := 𝕜) hec he hgc hg0 hle

/-- `‖e t‖ ≤ ‖e a‖ + ∫ₐᵗ ‖e'‖` on `[a,b]` (`_root_.norm_le_add_integral_norm_deriv`). -/
theorem norm_le_add_integral_norm_deriv {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {e e' : ℝ → F} {a b : ℝ}
    (hec : ContinuousOn e (Icc a b)) (he : ∀ t ∈ Ico a b, HasDerivWithinAt e (e' t) (Ici t) t)
    (he'c : ContinuousOn e' (Icc a b)) :
    ∀ t ∈ Icc a b, ‖e t‖ ≤ ‖e a‖ + ∫ s in a..t, ‖e' s‖ :=
  _root_.norm_le_add_integral_norm_deriv hec he he'c

end Feec.Evolution.Energy
