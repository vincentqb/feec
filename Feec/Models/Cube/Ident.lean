module

public import Feec.Models.Cube.Static
public import Feec.Legacy.Box.Ident

/-!
# The cube complexes and the bounded-domain realizations

The parity model of `Feec.Models.Cube.Parity` (thesis boundary conditions) is identified, through
the reflection extensions, with the bounded-domain complex `H̊¹(Q) → H̊(curl, Q) → L²(Q)` of
`Feec.Legacy.BoundedDomain.thesisComplex` (the **minimal** realizations of `grad` and `curl`,
`Feec.Legacy.BoxIdent.bijOn_resB_HcurlZero`, `Feec.Legacy.BoxIdent.iota_waveOp`), and transported to every open
cube `∏ (bᵢ, bᵢ + s)` by `x ↦ a x + b` (`Feec.Legacy.BoxIdent.pullX_waveOp`). This file states the
results on the bounded-domain complexes in the language of window complexes:

* on every open cube, for every closed `S₁`, `S₂` inside `L²(TSD)`, forward invariance of
  `{0} × S₁ × S₂` under the wave group forces stationarity (`Ident.forward_iff`), the largest
  invariant subspace consists of the stationary data (`Ident.mem_invariantCore_iff`), and for the
  thesis' constraint these are the data `(0, 0, B₀)` with `B₀ ∈ L²(TSD)` and `curl B₀ = 0`
  (`Ident.mem_invariantCore_tsd_iff`). The forward statement goes through the spectral argument of
  `Feec.Models.Cube.Static` (pure point spectrum on the torus); no Cesàro means are used.
The comparison of the mirror complex on `Q` with the minimal and maximal realizations is in
`Feec.Models.Cube.MirrorDirichlet`.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17)
* [Brezis2011], §9.2 (extension by reflection)
-/

open Feec.Legacy

open scoped RealInnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

namespace Feec.Models.Cube

open Feec.Legacy.HilbertComplex2 Feec.ShortHilbertComplex Feec.Legacy.Constraints Feec.Legacy.Torus Feec.Legacy.Box
open Feec.HilbertComplex (totalSub)
open Feec.Legacy.BoxIdent (openCube mem_Qr_iff_openCube cxCube cxQ Qr)
open Feec.Legacy.BoundedDomain (R3)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

namespace Ident

variable {b : R3} {s : ℝ}

/-- **The thesis' complex on the open cube** `∏ (bᵢ, bᵢ + s)`: `H̊¹ → H̊(curl) → L²`, the minimal
realizations of `grad` and `curl` (`Feec.Legacy.BoundedDomain.thesisComplex`), as a window complex. -/
abbrev complexCube (b : R3) (s : ℝ) := (cxCube b s).toShort.toHilbertComplex

/-- The spaces of `complexCube`. -/
abbrev V (b : R3) (s : ℝ) := Feec.Legacy.BoundedDomain.L2V (openCube b s)
/-- The spaces of `complexCube`. -/
abbrev M (b : R3) (s : ℝ) := Feec.Legacy.BoundedDomain.L2M (openCube b s)

/-- **On every open cube with the thesis' boundary conditions, forward invariance forces
stationarity**: for closed `S₁, S₂ ⊆ L²(TSD)`, the forward orbit of `y` under the wave group stays
in `{0} × S₁ × S₂` iff `y` lies there and is stationary.
Thesis: Prop 4.17 (corrected) -/
theorem forward_iff (hs : 0 < s) {S1 S2 : Submodule ℝ (M b s)}
    (h1 : S1 ≤ Feec.Legacy.BoundedDomain.TSD (openCube b s))
    (h2 : S2 ≤ Feec.Legacy.BoundedDomain.TSD (openCube b s))
    (y : PiLp 2 (W3 (V b s) (M b s) (M b s))) :
    (∀ t, 0 ≤ t → (complexCube b s).waveGroup.S t y ∈
        totalSub (sub3 (⊥ : Submodule ℝ (V b s)) S1 S2)) ↔
      y ∈ totalSub (sub3 (⊥ : Submodule ℝ (V b s)) S1 S2) ∧
        y ∈ (complexCube b s).waveGroup.stationary := by
  obtain ⟨x, rfl⟩ := totEquiv.surjective y
  set G := (cxCube b s).waveGroup
  have h : (∀ t, 0 ≤ t → G.S t x ∈ Kc (V b s) S1 S2) ↔ x ∈ Kc (V b s) S1 S2 ∧ ∀ t, G.S t x = x := by
    constructor
    · intro h
      have hx : x ∈ Kc (V b s) S1 S2 := by simpa [G.map_zero] using h 0 le_rfl
      refine ⟨hx, ((Feec.Legacy.BoxIdent.openCube_forward_iff hs G x).1 fun t ht => ?_).2⟩
      have := h t ht
      rw [mem_Kc] at this ⊢
      exact ⟨this.1, h1 this.2.1, h2 this.2.2⟩
    · rintro ⟨hx, hst⟩ t _
      rw [hst]; exact hx
  simp only [mem_Kc_iff, totEquiv_S (cxCube b s) G] at h
  rw [mem_stationary_iff (cxCube b s) G] at h
  exact h

/-- **`K*` on every open cube with the thesis' boundary conditions consists of the stationary data
in `K`**, for every closed `S₁, S₂ ⊆ L²(TSD)`.
Thesis: Prop 4.17 (corrected) -/
theorem mem_invariantCore_iff (hs : 0 < s) {S1 S2 : Submodule ℝ (M b s)}
    (h1 : S1 ≤ Feec.Legacy.BoundedDomain.TSD (openCube b s))
    (h2 : S2 ≤ Feec.Legacy.BoundedDomain.TSD (openCube b s))
    (y : PiLp 2 (W3 (V b s) (M b s) (M b s))) :
    y ∈ (complexCube b s).waveGroup.invariantCore
        (totalSub (sub3 (⊥ : Submodule ℝ (V b s)) S1 S2)) ↔
      y ∈ totalSub (sub3 (⊥ : Submodule ℝ (V b s)) S1 S2) ∧
        y ∈ (complexCube b s).waveGroup.stationary := by
  refine ⟨fun hy => (forward_iff hs h1 h2 y).1 fun t _ => C0Group.mem_invariantCore.1 hy t,
    fun ⟨hK, hst⟩ => C0Group.mem_invariantCore.2 fun t => ?_⟩
  rw [C0Group.mem_stationary.1 hst t]; exact hK

/-- **`K*` on every open cube for the thesis' constraint, explicitly**: `y ∈ K*` iff
`y = (0, 0, B₀)` with `B₀ ∈ L²(TSD)` and `d₁* B₀ = curl B₀ = 0` (no boundary condition on `B₀`).
Thesis: Prop 4.17 (corrected) -/
theorem mem_invariantCore_tsd_iff (hs : 0 < s) (y : PiLp 2 (W3 (V b s) (M b s) (M b s))) :
    y ∈ (complexCube b s).waveGroup.invariantCore (totalSub (sub3 (⊥ : Submodule ℝ (V b s))
        (Feec.Legacy.BoundedDomain.TSD (openCube b s)) (Feec.Legacy.BoundedDomain.TSD (openCube b s)))) ↔
      ∃ B ∈ Feec.Legacy.BoundedDomain.TSD (openCube b s), ∃ h : B ∈ (cxCube b s).d1†.domain,
        (cxCube b s).d1† ⟨B, h⟩ = 0 ∧ y = totEquiv (ini (V b s) 0 B) := by
  obtain ⟨x, rfl⟩ := totEquiv.surjective y
  rw [← map_Kc, ← mem_Kmax_iff (cxCube b s) (cxCube b s).waveGroup,
    Feec.Legacy.BoxIdent.openCube_mem_Kmax_iff' hs]
  simp only [totEquiv.injective.eq_iff]

end Ident

end Feec.Models.Cube
