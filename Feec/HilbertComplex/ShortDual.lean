module

public import Feec.HilbertComplex.ReducedSystem

/-!
# The dual of a short Hilbert complex, and the weak form of its wave equation

For a short complex `W₀ --d₀--> W₁ --d₁--> W₂` of closed densely defined operators, the adjoints
form the short complex `W₂ --d₁†--> W₁ --d₀†--> W₀` (`ShortHilbertComplex.dual`), the window
form of `Feec.HilbertComplex.dual` read backwards. By von Neumann's `T†† = T` its adjoints are
the original operators (`adjoint_dual_d₀`, `adjoint_dual_d₁`), so dualizing twice gives the
complex back (`dual_dual`): the wave operator of the dual has domain
`D(d₁†) × (D(d₀†) ∩ D(d₁)) × D(d₀)`, the boundary conditions moved to the other end.

The Hodge wave equation `U' = L U` of a short complex, with `U = (σ, u, ρ)`, is equivalent to the
weak equations `(σ̇, τ) = -(u, d₀ τ)`, `(u̇, v) - (d₀ σ, v) + (ρ, d₁ v) = 0`, `ρ̇ = d₁ u` with
`σ ∈ D(d₀)`, `u ∈ D(d₁)` (`weakEqs_of_isStrongSolution`, `isStrongSolution_of_weakEqs`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.2 (dual complex), §6.1 ((6.1), the weak form)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1.2

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open LinearPMap Set

universe u

namespace Feec.ShortHilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ W₂ : Type u}
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]
  (S : ShortHilbertComplex 𝕜 W₀ W₁ W₂)

/-! ## The dual complex -/

/-- **The dual short complex** `W₂ --d₁†--> W₁ --d₀†--> W₀`. [QuennevilleBelair2015], §4.2 -/
def dual : ShortHilbertComplex 𝕜 W₂ W₁ W₀ where
  d₀ := S.d₁†
  d₁ := S.d₀†
  dense₀ := LinearPMap.dense_adjoint_domain _ S.dense₁ S.closed₁
  dense₁ := LinearPMap.dense_adjoint_domain _ S.dense₀ S.closed₀
  closed₀ := LinearPMap.adjoint_isClosed S.dense₁
  closed₁ := LinearPMap.adjoint_isClosed S.dense₀
  mapsTo := Feec.Operator.adjoint_mapsTo S.dense₁ S.mapsTo S.comp
  comp := Feec.Operator.adjoint_comp_eq_zero S.dense₀ S.dense₁ S.mapsTo S.comp

@[simp] theorem dual_d₀ : S.dual.d₀ = S.d₁† := rfl

@[simp] theorem dual_d₁ : S.dual.d₁ = S.d₀† := rfl

/-- `(d₁†)† = d₁` (von Neumann). -/
theorem adjoint_dual_d₀ : S.dual.d₀† = S.d₁ :=
  LinearPMap.adjoint_adjoint _ S.dense₁ S.closed₁

/-- `(d₀†)† = d₀` (von Neumann). -/
theorem adjoint_dual_d₁ : S.dual.d₁† = S.d₀ :=
  LinearPMap.adjoint_adjoint _ S.dense₀ S.closed₀

/-- `S** = S`. -/
theorem dual_dual : S.dual.dual = S := by
  cases S with
  | mk d₀ d₁ dense₀ dense₁ closed₀ closed₁ mapsTo comp =>
    have h₀ : d₀†† = d₀ := LinearPMap.adjoint_adjoint _ dense₀ closed₀
    have h₁ : d₁†† = d₁ := LinearPMap.adjoint_adjoint _ dense₁ closed₁
    change ShortHilbertComplex.mk (d₀††) (d₁††) _ _ _ _ _ _ = _
    congr

/-! ## The weak form of the Hodge wave equation -/

section Weak

attribute [-instance] instNormedSpaceRealW3 instIsScalarTowerRealW3

variable [NormedSpace ℝ (PiLp 2 (W3 W₀ W₁ W₂))]

/-- **The weak equations of a strong solution** of `U' = L U`: writing `U(t) = (σ, u, ρ)`, at
each `t ∈ I` we have `σ ∈ D(d₀)`, `u ∈ D(d₁)`, and `U̇(t) = (σ̇, u̇, ρ̇)` with
`(σ̇, τ) = -(u, d₀ τ)` for `τ ∈ D(d₀)`, `(u̇, v) - (d₀ σ, v) + (ρ, d₁ v) = 0` for `v ∈ D(d₁)`, and
`ρ̇ = d₁ u`. [QuennevilleBelair2015], (6.1) -/
theorem weakEqs_of_isStrongSolution {I : Set ℝ} {U : ℝ → PiLp 2 (W3 W₀ W₁ W₂)}
    (hU : Evolution.IsStrongSolution S.wave I 0 U) {t : ℝ} (ht : t ∈ I) :
    ∃ (hσ : ((U t : PiLp 2 (W3 W₀ W₁ W₂)) 0 : W₀) ∈ S.d₀.domain) (hu : ((U t : PiLp 2 (W3 W₀ W₁
        W₂)) 1 : W₁) ∈ S.d₁.domain) (σ' : W₀) (u' : W₁)
      (ρ' : W₂), HasDerivWithinAt U (mk3 σ' u' ρ') I t ∧
      (∀ τ : S.d₀.domain, ⟪σ', (τ : W₀)⟫_𝕜 = -⟪((U t : PiLp 2 (W3 W₀ W₁ W₂)) 1 : W₁), S.d₀ τ⟫_𝕜) ∧
      (∀ v : S.d₁.domain, ⟪u', (v : W₁)⟫_𝕜 - ⟪S.d₀ ⟨_, hσ⟩, (v : W₁)⟫_𝕜 +
        ⟪((U t : PiLp 2 (W3 W₀ W₁ W₂)) 2 : W₂), S.d₁ v⟫_𝕜 = 0) ∧
      ρ' = S.d₁ ⟨_, hu⟩ := by
  have hD := hU.mem_domain ht
  obtain ⟨h0, h1, h1', h2⟩ := (S.mem_wave_domain).1 hD
  have hd := hU.hasDerivWithinAt ht
  rw [Pi.zero_apply, add_zero] at hd
  set x : S.wave.domain := ⟨U t, hD⟩
  refine ⟨h0, h1, -(S.d₀† ⟨_, h1'⟩), S.d₀ ⟨_, h0⟩ - S.d₁† ⟨_, h2⟩, S.d₁ ⟨_, h1⟩, ?_, ?_, ?_, rfl⟩
  · refine hd.congr_deriv ?_
    rw [← mk3_eta (S.wave x)]
    congr 1
    · exact S.wave_apply_zero x
    · exact S.wave_apply_one x
    · exact S.wave_apply_two x
  · intro τ
    rw [inner_neg_left, LinearPMap.adjoint_isFormalAdjoint S.dense₀]
    rfl
  · intro v
    rw [inner_sub_left, LinearPMap.adjoint_isFormalAdjoint S.dense₁]
    change _ - ⟪((U t : PiLp 2 (W3 W₀ W₁ W₂)) 2 : W₂), _⟫_𝕜 - _ + _ = 0
    ring

/-- **Converse**: a path `U = (σ, u, ρ)` with `σ(t) ∈ D(d₀)`, `u(t) ∈ D(d₁)` whose derivative
satisfies the weak equations at every `t ∈ I` is a strong solution of `U' = L U` (the first
equation gives `u ∈ D(d₀†)`, `d₀† u = -σ̇`; the second `ρ ∈ D(d₁†)`, `d₁† ρ = d₀ σ - u̇`). -/
theorem isStrongSolution_of_weakEqs {I : Set ℝ} {U : ℝ → PiLp 2 (W3 W₀ W₁ W₂)}
    (hw : ∀ t ∈ I, ∃ (hσ : ((U t : PiLp 2 (W3 W₀ W₁ W₂)) 0 : W₀) ∈ S.d₀.domain) (hu : ((U t : PiLp
        2 (W3 W₀ W₁ W₂)) 1 : W₁) ∈ S.d₁.domain)
      (σ' : W₀) (u' : W₁) (ρ' : W₂), HasDerivWithinAt U (mk3 σ' u' ρ') I t ∧
      (∀ τ : S.d₀.domain, ⟪σ', (τ : W₀)⟫_𝕜 = -⟪((U t : PiLp 2 (W3 W₀ W₁ W₂)) 1 : W₁), S.d₀ τ⟫_𝕜) ∧
      (∀ v : S.d₁.domain, ⟪u', (v : W₁)⟫_𝕜 - ⟪S.d₀ ⟨_, hσ⟩, (v : W₁)⟫_𝕜 +
        ⟪((U t : PiLp 2 (W3 W₀ W₁ W₂)) 2 : W₂), S.d₁ v⟫_𝕜 = 0) ∧
      ρ' = S.d₁ ⟨_, hu⟩) :
    Evolution.IsStrongSolution S.wave I 0 U := by
  refine Evolution.IsStrongSolution.of_deriv fun t ht => ?_
  obtain ⟨hσ, hu, σ', u', ρ', hd, ha, hb, hc⟩ := hw t ht
  set u₁ : W₁ := (U t : PiLp 2 (W3 W₀ W₁ W₂)) 1 with hu₁
  set ρ₂ : W₂ := (U t : PiLp 2 (W3 W₀ W₁ W₂)) 2 with hρ₂
  have ka : ∀ τ : S.d₀.domain, ⟪-σ', (τ : W₀)⟫_𝕜 = ⟪u₁, S.d₀ τ⟫_𝕜 := fun τ => by
    rw [inner_neg_left, ha τ, neg_neg]
    rfl
  have kb : ∀ v : S.d₁.domain, ⟪S.d₀ ⟨_, hσ⟩ - u', (v : W₁)⟫_𝕜 = ⟪ρ₂, S.d₁ v⟫_𝕜 :=
    fun v => by
      have h := hb v
      change ⟪u', (v : W₁)⟫_𝕜 - ⟪S.d₀ ⟨_, hσ⟩, (v : W₁)⟫_𝕜 + ⟪ρ₂, S.d₁ v⟫_𝕜 = 0 at h
      rw [inner_sub_left]
      linear_combination (-1 : 𝕜) * h
  have h1' : u₁ ∈ S.d₀†.domain := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, ka⟩
  have h2 : ρ₂ ∈ S.d₁†.domain := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, kb⟩
  have hD : U t ∈ S.wave.domain := (S.mem_wave_domain).2 ⟨hσ, hu, h1', h2⟩
  refine ⟨mk3 σ' u' ρ', ?_, by rw [Pi.zero_apply, add_zero]; exact hd⟩
  have e : S.wave ⟨U t, hD⟩ = mk3 σ' u' ρ' := by
    rw [← mk3_eta (S.wave ⟨U t, hD⟩)]
    congr 1
    · rw [S.wave_apply_zero, LinearPMap.adjoint_apply_eq S.dense₀ _ ka, neg_neg]
    · rw [S.wave_apply_one, LinearPMap.adjoint_apply_eq S.dense₁ _ kb]
      exact sub_sub_cancel _ _
    · rw [S.wave_apply_two, hc]
  rw [← e]
  exact S.wave.mem_graph ⟨U t, hD⟩

end Weak

end Feec.ShortHilbertComplex
