module

public import Feec.Models.BoundedDomain.SymCurl
public import Feec.HilbertComplex.InvariantCoreSpectral

/-!
# Bounded domains: when does `K*` contain a moving datum?

For the thesis' complex `H̊¹(Ω; ℝ³) --grad--> H̊(curl, Ω; ℝ³ˣ³) --curl--> L²(Ω; ℝ³ˣ³)`
(`Feec.Models.BoundedDomain.gradCurl`) on a bounded open `Ω ⊆ ℝ³` and
`K = {0} × L²(TSD) × L²(TSD)`, the invariant core `K* = {0} × S₁* × S₂*` of `K` under the wave
group is the largest propagating constraint space (`Feec.ShortHilbertComplex.coreSub`). This file
specializes `Feec.ShortHilbertComplex.coreSub_spectral` to it: `K*` is stationary iff its electric
fields are curl-free, and, under a complete set of eigenvectors of `L²`, it contains a moving
datum iff the curl–curl eigenproblem `curl† curl u = ω² u`, `ω > 0`, has a nonzero solution
`u ∈ L²(TSD) ∩ H̊(curl)`; every such `u` lies in `S₁* ⊆ L²(TSD₀)` and moves.

The eigenvector hypothesis (`Feec.C0Group.EigenDense`) stands for the spectral consequence of
the compactness of the complex (Rellich for `H̊¹`, a Weber–Weck selection theorem for
`H̊(curl) ∩ H(div)`, known under boundary regularity such as Lipschitz `Ω`); it is not proved here
for any `Ω`. Whether such eigenfields exist is not decided here.

## Main results

* `tsd_le_ker_gradCurl`: `L²(TSD) ⊆ N(d₀†)`.
* **`gradCurl_coreSub_spectral`**.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Lemma 3.5, §4.10 (Prop 4.17)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace LinearPMap
open Set Feec.Domain

namespace Feec.Models.BoundedDomain

-- Over `ℝ` the generic real structure on the window spaces duplicates the inner-product one.
attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

variable {Ω : Set R3}

/-- `L²(TSD) ⊆ N(d₀†)` for the grad–curl complex (the divergence condition). -/
theorem tsd_le_ker_gradCurl (hΩ : IsOpen Ω) : tsd Ω ≤ (gradCurl ℝ hΩ).d₀†.ker := fun _ hB =>
  ((mem_tsd_iff_ker hΩ).1 hB).2.2

/-- **`K*` on a bounded domain for the thesis' complex** `H̊¹(V) → H̊(curl, M) → L²(M)` and
`K = {0} × L²(TSD) × L²(TSD)`, under a complete set of eigenvectors of `L²` (`hD`):
1. a datum whose forward orbit (`t ≥ 0`) stays in `K` lies in `K*`;
2. `K*` is stationary iff every `E ∈ S₁*` lies in `H̊(curl)` with `curl E = 0` (no hypothesis);
3. `K*` contains a non-stationary datum iff there are `ω > 0` and a nonzero
   `u ∈ L²(TSD) ∩ H̊(curl)` with `curl u ∈ D(curl†)` and `curl† curl u = ω² u` (then
   `curl u ∈ L²(TSD)` automatically, `minimal_curl_mem_tsd`);
4. every such `u` lies in `S₁* ⊆ L²(TSD₀)`, and `(0, u, 0)` moves: its orbit is
   `(0, cos(ωt) u, (sin(ωt)/ω) curl u)` (`Feec.C0Group.IsIsometric.S_eq_of_isEigenSq`). -/
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
