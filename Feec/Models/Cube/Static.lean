module

public import Feec.Models.Cube.Parity
public import Feec.Ch4.BoundedKstar

/-!
# Only static data propagate on the cube with the thesis' boundary conditions

For the cube complex with the thesis' boundary conditions (`Feec.Models.Cube.Parity.complex`)
the largest invariant subspace of `K = {0} × S₁ × S₂` consists of the stationary data in `K`
(`Feec.Models.Cube.Parity.mem_invariantCore_iff`). This file shows:

* **forward invariance already forces stationarity** (`Parity.forward_iff`): if the forward
  orbit (`t ≥ 0`) of a datum stays in `K`, the datum is stationary. Forward invariance of a
  closed subspace gives invariance for all `t` as soon as the group has pure point spectrum
  (`Feec.C0Group.IsIsometric.mem_invariantCore_of_forward_invariant`, von Neumann's mean ergodic
  theorem), and the torus wave group has pure point spectrum (`isPurePoint_torus`: the single
  Fourier modes span `L²` and each splits into eigenvectors of `L²`). The resolvent is not
  compact here (the harmonic space `ker L ⊇ {0} × {0} × ker curl` is infinite-dimensional), so
  `Feec.C0Group.eigenDense_of_compactResolvent` does not apply; the Fourier eigenbasis replaces
  it.
* **the stationary data are not zero** (`Parity.exists_linearIndependent_invariantCore`): the
  constant fields `diag(1, -1, 0)` and `e₀e₁ᵀ + e₁e₀ᵀ` (Hessians of the harmonic polynomials
  `(x₀² − x₁²)/2` and `x₀x₁`), placed in the magnetic slot, are linearly independent elements of
  `K*` for `K = {0} × L²(TSD) × L²(TSD)`.

## Main results

* `isPurePoint_torus`.
* **`Parity.forward_torus_iff`**, **`Parity.forward_iff`**, **`Parity.forward_tsd_iff`**.
* `Parity.staticB_mem_invariantCore`, `Parity.offB_mem_invariantCore`,
  **`Parity.exists_linearIndependent_invariantCore`**, `Parity.invariantCore_ne_bot`.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17)
* [ReedSimon1980], §VII.3 (mean ergodic theorem)
-/

open scoped RealInnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

namespace Feec.Models.Cube

open Feec.HilbertComplex2 Feec.ShortHilbertComplex Feec.Constraints Feec.Torus Feec.Box

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

/-- **The torus wave group has pure point spectrum**: the periodic vectors span a dense subspace
of `L²(𝕋³; ℂ³) × L²(𝕋³; ℂ³ˣ³) × L²(𝕋³; ℂ³ˣ³)` (each Fourier mode splits into a stationary part
and a part of frequency `|ξ_k|`). -/
theorem isPurePoint_torus : torus.waveGroup.IsPurePoint := by
  have h := purePoint_of_eigenDense eigenDense_periodicGroup
  have e : ∀ τ, (Per periodicGroup τ).map
      (totEquiv (W0 := L2V) (W1 := L2M) (W2 := L2M) : Tot L2V L2M L2M →ₗ[ℝ] _) =
      torus.waveGroup.periodic τ := fun τ => by
    ext y
    rw [Submodule.mem_map_equiv, C0Group.mem_periodic, mem_Per]
    change periodicGroup.S τ (totEquiv.symm y) = totEquiv.symm y ↔ _
    rw [← totEquiv_symm_waveGroup periodicComplex periodicGroup, totEquiv.symm.injective.eq_iff]
  unfold C0Group.IsPurePoint
  simp_rw [← e, ← Submodule.map_iSup, Submodule.map_coe]
  exact (totEquiv (W0 := L2V) (W1 := L2M) (W2 := L2M)).toHomeomorph.isDenseEmbedding.dense_image.2 h

namespace Parity

theorem isClosed_constraint (S1 S2 : Submodule ℝ L2M) [S1.HasOrthogonalProjection]
    [S2.HasOrthogonalProjection] :
    IsClosed (HilbertComplex.totalSub (constraint S1 S2) : Set (PiLp 2 (W3 L2V L2M L2M))) :=
  HilbertComplex.isClosed_totalSub

/-- **Forward invariance forces stationarity on the torus side**: for `S₁`, `S₂` as in
`mem_invariantCore_torus_iff`, the forward orbit of `y` stays in `K = {0} × S₁ × S₂` iff `y ∈ K`
is stationary.
Thesis: Prop 4.17 (corrected) -/
theorem forward_torus_iff {S1 S2 : Submodule ℝ L2M} [S1.HasOrthogonalProjection]
    [S2.HasOrthogonalProjection] (hS1 : S1 ≤ ParRow 1 ⊓ boxSym ⊓ boxTr)
    (hS2 : S2 ≤ ParRow (-1) ⊓ boxSym ⊓ boxTr) (y : PiLp 2 (W3 L2V L2M L2M)) :
    (∀ t, 0 ≤ t → torus.waveGroup.S t y ∈ HilbertComplex.totalSub (constraint S1 S2)) ↔
      y ∈ HilbertComplex.totalSub (constraint S1 S2) ∧ y ∈ torus.waveGroup.stationary := by
  refine ⟨fun h => (mem_invariantCore_torus_iff hS1 hS2 y).1
    (torus.isIsometric_waveGroup.mem_invariantCore_of_forward_invariant isPurePoint_torus
      (isClosed_constraint S1 S2) h), fun ⟨hK, hs⟩ t _ => ?_⟩
  rw [C0Group.mem_stationary.1 hs t]; exact hK

/-- **On the cube with the thesis' boundary conditions, forward invariance forces stationarity**:
for the cube complex and `S₁`, `S₂` closed, symmetric and trace-free on the cube in the electric
and magnetic parity classes, the forward orbit (`t ≥ 0`) of `y` stays in `K = {0} × S₁ × S₂` iff
`y ∈ K` and `y` is stationary.
Thesis: Prop 4.17 (corrected) -/
theorem forward_iff {S1 S2 : Submodule ℝ L2M} [S1.HasOrthogonalProjection]
    [S2.HasOrthogonalProjection] (hS1 : S1 ≤ ParRow 1 ⊓ boxSym ⊓ boxTr)
    (hS2 : S2 ≤ ParRow (-1) ⊓ boxSym ⊓ boxTr) (y : PiLp 2 fun i => rowAction.fixed i) :
    (∀ t, 0 ≤ t → complex.waveGroup.S t y ∈
        HilbertComplex.totalSub (compSub rowAction.fixed (constraint S1 S2))) ↔
      y ∈ HilbertComplex.totalSub (compSub rowAction.fixed (constraint S1 S2)) ∧
        y ∈ complex.waveGroup.stationary := by
  rw [forward_compSub_iff, forward_torus_iff hS1 hS2, mem_stationary_compSub_iff]
  rfl

/-- **Forward invariance of the thesis' constraint on the cube**: the forward orbit of `y` stays
in `{0} × L²(TSD) × L²(TSD)` iff `y = (0, 0, B₀)` with `B₀ ∈ L²(TSD)` curl-free.
Thesis: Prop 4.17 (corrected) -/
theorem forward_tsd_iff (y : PiLp 2 (W3 L2V L2M L2M)) :
    (∀ t, 0 ≤ t → torus.waveGroup.S t y ∈
        HilbertComplex.totalSub (constraint (boxTSD 1) (boxTSD (-1)))) ↔
      (y 0 : L2V) = 0 ∧ (y 1 : L2M) = 0 ∧ (y 2 : L2M) ∈ boxTSD (-1) ∧
        ∀ k, curlSym (freq k) (slot2 y k) = 0 := by
  have : (boxTSD 1).HasOrthogonalProjection := by
    have := (isClosed_boxTSD 1).completeSpace_coe; infer_instance
  have : (boxTSD (-1)).HasOrthogonalProjection := by
    have := (isClosed_boxTSD (-1)).completeSpace_coe; infer_instance
  rw [← mem_invariantCore_tsd_iff]
  exact ⟨torus.isIsometric_waveGroup.mem_invariantCore_of_forward_invariant isPurePoint_torus
    (isClosed_constraint _ _), fun h t _ => C0Group.mem_invariantCore.1 h t⟩

/-- The datum `(0, 0, B₀)`. -/
def magState (B : L2M) : PiLp 2 (W3 L2V L2M L2M) := totEquiv (ini L2V (0 : L2M) B)

theorem magState_mem_invariantCore {B : L2M} (hB : B ∈ boxTSD (-1))
    (hc : ∀ k, curlSym (freq k) (B k) = 0) :
    magState B ∈ torus.waveGroup.invariantCore
      (HilbertComplex.totalSub (constraint (boxTSD 1) (boxTSD (-1)))) := by
  rw [mem_invariantCore_tsd_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change -(tot L2V L2M L2M (ini L2V (0 : L2M) B)).1 = 0
    rw [tot_ini, neg_zero]
  · change (tot L2V L2M L2M (ini L2V (0 : L2M) B)).2.1 = 0
    rw [tot_ini]
  · change (tot L2V L2M L2M (ini L2V (0 : L2M) B)).2.2 ∈ _
    rw [tot_ini]; exact hB
  · intro k
    change curlSym (freq k) ((tot L2V L2M L2M (ini L2V (0 : L2M) B)).2.2 k) = 0
    rw [tot_ini]; exact hc k

/-- The constant field `diag(1, -1, 0)` in the magnetic slot lies in `K*`. -/
theorem staticB_mem_invariantCore :
    magState staticB ∈ torus.waveGroup.invariantCore
      (HilbertComplex.totalSub (constraint (boxTSD 1) (boxTSD (-1)))) :=
  magState_mem_invariantCore staticB_mem_boxTSD curlSym_staticB

/-- The constant field `e₀e₁ᵀ + e₁e₀ᵀ` in the magnetic slot lies in `K*`. -/
theorem offB_mem_invariantCore :
    magState offB ∈ torus.waveGroup.invariantCore
      (HilbertComplex.totalSub (constraint (boxTSD 1) (boxTSD (-1)))) :=
  magState_mem_invariantCore offB_mem_boxTSD curlSym_offB

/-- **`K*` contains two linearly independent stationary data** for the thesis' constraint on the
cube: `(0, 0, diag(1, -1, 0))` and `(0, 0, e₀e₁ᵀ + e₁e₀ᵀ)`.
Thesis: Prop 4.17 (corrected) -/
theorem exists_linearIndependent_invariantCore :
    ∃ v : Fin 2 → PiLp 2 (W3 L2V L2M L2M), LinearIndependent ℝ v ∧
      ∀ i, v i ∈ torus.waveGroup.invariantCore
        (HilbertComplex.totalSub (constraint (boxTSD 1) (boxTSD (-1)))) := by
  refine ⟨![magState staticB, magState offB], ?_, fun i => ?_⟩
  · have h := offB_mem_Kmax.2
    have e : ![magState staticB, magState offB] =
        (totEquiv (W0 := L2V) (W1 := L2M) (W2 := L2M) : Tot L2V L2M L2M →ₗ[ℝ] _) ∘
          ![ini L2V (0 : L2M) staticB, ini L2V (0 : L2M) offB] := by
      ext i : 1; fin_cases i <;> rfl
    rw [e]
    exact h.map' _ (LinearEquiv.ker _)
  · fin_cases i
    exacts [staticB_mem_invariantCore, offB_mem_invariantCore]

/-- `K* ≠ 0` for the thesis' constraint on the cube complex.
Thesis: Prop 4.17 (corrected) -/
theorem invariantCore_ne_bot :
    complex.waveGroup.invariantCore
        (HilbertComplex.totalSub (compSub rowAction.fixed (constraint (boxTSD 1) (boxTSD (-1))))) ≠
      ⊥ := by
  have : (boxTSD 1).HasOrthogonalProjection := by
    have := (isClosed_boxTSD 1).completeSpace_coe; infer_instance
  have : (boxTSD (-1)).HasOrthogonalProjection := by
    have := (isClosed_boxTSD (-1)).completeSpace_coe; infer_instance
  have hfix : ∀ i, magState staticB i ∈ rowAction.fixed i := by
    intro i
    fin_cases i
    · change -(tot L2V L2M L2M (ini L2V (0 : L2M) staticB)).1 ∈ rowAction.fixed 0
      rw [tot_ini, neg_zero]; exact Submodule.zero_mem _
    · change (tot L2V L2M L2M (ini L2V (0 : L2M) staticB)).2.1 ∈ rowAction.fixed 1
      rw [tot_ini]; exact Submodule.zero_mem _
    · change (tot L2V L2M L2M (ini L2V (0 : L2M) staticB)).2.2 ∈ rowAction.fixed 2
      rw [tot_ini]
      exact (mem_fixed_reflAction_two _ _ _).2 (mem_rowB_fix.2 staticB_mem_ParRow)
  set y : PiLp 2 fun i => rowAction.fixed i := WithLp.toLp 2 fun i => ⟨_, hfix i⟩
  intro hbot
  have hy : y ∈ complex.waveGroup.invariantCore
      (HilbertComplex.totalSub (compSub rowAction.fixed (constraint (boxTSD 1) (boxTSD (-1))))) :=
    (mem_invariantCore_compSub_iff _ _ y).2 staticB_mem_invariantCore
  rw [hbot, Submodule.mem_bot] at hy
  have h2 := congrArg
    (fun z : PiLp 2 fun i => rowAction.fixed i => ((z 2 : W3 L2V L2M L2M 2) : L2M)) hy
  change (tot L2V L2M L2M (ini L2V (0 : L2M) staticB)).2.2 = 0 at h2
  rw [tot_ini] at h2
  exact staticB_ne_zero h2

end Parity

end Feec.Models.Cube
