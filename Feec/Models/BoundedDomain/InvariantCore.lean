module

public import Feec.Models.BoundedDomain.SymCurl
public import Feec.HilbertComplex.InvariantCoreSpectral

/-!
# Bounded domains: when does `K*` contain a moving datum?

For the grad–curl complex on a bounded open `Ω ⊆ ℝ³` and `K = {0} × L²(TSD) × L²(TSD)`, under a
complete set of eigenvectors, `K*` contains a moving datum iff some nonzero `u ∈ L²(TSD)` solves
`curl† curl u = ω² u`, `ω > 0`.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace LinearPMap
open Set Feec.Domain

namespace Feec.Models.BoundedDomain

-- Over `ℝ` the generic real structure on the window spaces duplicates the inner-product one.
attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

variable {Ω : Set R3}

theorem tsd_le_ker_gradCurl (hΩ : IsOpen Ω) : tsd Ω ≤ (gradCurl ℝ hΩ).d₀†.ker := fun _ hB =>
  ((mem_tsd_iff_ker hΩ).1 hB).2.2

/-- Under a complete set of eigenvectors, `K*` for `K = {0} × L²(TSD) × L²(TSD)` is not stationary
iff some nonzero `u ∈ L²(TSD)` is a curl–curl eigenfield; such `u` lie in `L²(TSD₀)` and move. -/
theorem gradCurl_coreSub_spectral (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hD : (gradCurl ℝ hΩ).EigenDense) :
    (∀ x, (∀ t, 0 ≤ t → (gradCurl ℝ hΩ).toHilbertComplex.waveGroup.S t x ∈
        HilbertComplex.totalSub (ShortHilbertComplex.family3 ⊥ (tsd Ω) (tsd Ω))) ↔
          x ∈ (gradCurl ℝ hΩ).coreSub (tsd Ω) (tsd Ω)) ∧
    ((gradCurl ℝ hΩ).coreSub (tsd Ω) (tsd Ω) ≤
        (gradCurl ℝ hΩ).stationary ↔
      ∀ v ∈ (gradCurl ℝ hΩ).invariantCore₁ (tsd Ω) (tsd Ω),
        ∃ h1 : v ∈ (gradCurl ℝ hΩ).d₁.domain, (gradCurl ℝ hΩ).d₁ ⟨v, h1⟩ = 0) ∧
    (¬ (gradCurl ℝ hΩ).coreSub (tsd Ω) (tsd Ω) ≤
        (gradCurl ℝ hΩ).stationary ↔
      ∃ ω : ℝ, 0 < ω ∧ ∃ v : L2F ℝ Ω Ix, v ≠ 0 ∧ v ∈ tsd Ω ∧ (gradCurl ℝ hΩ).IsEigenfield ω v) ∧
    (∀ ω : ℝ, 0 < ω → ∀ v : L2F ℝ Ω Ix, v ∈ tsd Ω → (gradCurl ℝ hΩ).IsEigenfield ω v →
          v ∈ (gradCurl ℝ hΩ).invariantCore₁ (tsd Ω) (tsd Ω) ∧ v ∈ tsd₀ Ω hΩ hb ∧
            (v ≠ 0 → ShortHilbertComplex.inj₁ (𝕜 := ℝ) (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix)
              (L2F ℝ Ω Ix) v ∉ (gradCurl ℝ hΩ).stationary)) := by
  have H :=
    ShortHilbertComplex.coreSub_spectral (S := gradCurl ℝ hΩ) (S₂ := tsd Ω)
      (tsd_le_ker_gradCurl hΩ) hD
  refine ⟨H.1, H.2.1, ?_, fun ω hω v hv hE => ?_⟩
  · rw [H.2.2]
    refine exists_congr fun ω => and_congr_right fun _ => exists_congr fun v =>
        and_congr_right fun _ => and_congr_right fun hv => ?_
    unfold ShortHilbertComplex.IsEigenfield
    exact exists_congr fun h1 => exists_congr fun _ =>
      ⟨And.right, And.intro (minimal_curl_mem_tsd hΩ ⟨v, h1⟩ hv)⟩
  obtain ⟨hv1, hv3, e⟩ := hE
  obtain ⟨h2, e2⟩ := LinearPMap.exists_apply_eq_zero_of_mem_ker (tsd_le_ker_gradCurl hΩ hv)
  obtain ⟨-, hm, hns⟩ := ShortHilbertComplex.eigenfield_mem_invariantCore₁
    (S := gradCurl ℝ hΩ) (S₂ := tsd Ω) hω hv hv1 h2 e2 hv3
    (minimal_curl_mem_tsd hΩ ⟨v, hv1⟩ hv) e
  exact ⟨hm, invariantCore₁_le_tsd₀ hΩ hb (gradCurl ℝ hΩ) le_rfl (tsd Ω) hm, hns⟩

end Feec.Models.BoundedDomain
