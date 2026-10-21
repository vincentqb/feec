module

public import Feec.Models.Box.RowWise
public import Feec.Models.BoundedDomain.InvariantCore
public import Feec.HilbertComplex.CompressCompact

/-!
# A complete set of eigenvectors, and `K*`, on every box

On a box `B = ∏ (aᵢ, aᵢ + ℓᵢ)` with arbitrary sides `ℓᵢ > 0`, the thesis' complex
`H̊¹(B) → H̊(curl, B) → L²(B)` is the compression of the anisotropic torus grad–curl complex
(frequencies `ξ_d(n) = d * 2πn`, `dᵢ = 1/(2ℓᵢ)`) along the parity extension of the pulled-back
fields (`Feec.Models.Box.complexBox_eq_compress`). Hence:

* **the wave group has a complete set of eigenvectors** (`Box.eigenDense_gradCurl_box`), the
  Fourier modes of the anisotropic torus, compressed (`Feec.HilbertComplex.eigenDense_compress`);
  so `Feec.Models.BoundedDomain.gradCurl_coreSub_spectral` holds unconditionally on every box
  (`Box.gradCurl_coreSub_spectral_box`);
* **only stationary data propagate** (`Box.forward_iff`, `Box.mem_invariantCore_iff`): for
  `S₁, S₂ ⊆ L²(TSD)` (closed or not), the forward orbit of a datum stays in `{0} × S₁ × S₂` iff
  the datum lies there and is stationary; the eigenvectors of `L²` with eigenvalue `-ω²`, `ω > 0`,
  are trigonometric polynomials (`|ξ_d(n)| = ω` is a finite set), and a trigonometric polynomial
  of a row-wise parity class that is symmetric and trace-free on `Q` vanishes;
* **`K*` for the thesis' constraint** `K = {0} × L²(TSD) × L²(TSD)` consists of the data
  `(0, 0, B₀)` with `B₀ ∈ L²(TSD)` and `curl B₀ = 0` (`Box.mem_invariantCore_tsd_iff`): the
  electric harmonic fields vanish (`ξ_d(n) ≠ 0` for `n ≠ 0`, and the constant mode has odd
  parity).

This extends `Feec.Models.Cube.EigenDense` and `Feec.Models.Cube.Ident` from cubes to boxes with
unequal sides. On general bounded `Ω` (balls, Lipschitz domains) the question is **still open**:
`Feec.Models.BoundedDomain.not_coreSub_le_stationary_iff` reduces it, under `EigenDense`,
to the existence of a TSD eigenfield `u` with `curl u ∉ H̊(curl)`, and `EigenDense` is proved here
and in `Feec.Models.Cube.EigenDense` on cubes and boxes only.

## Main results

* **`Box.eigenDense_complexBox`**, **`Box.eigenDense_gradCurl_box`**,
  **`Box.gradCurl_coreSub_spectral_box`**.
* `Box.waveGroup_JB`, `Box.mem_stationary_iff_JB`, **`Box.forward_iff`**,
  **`Box.mem_invariantCore_iff`**, **`Box.mem_invariantCore_tsd_iff`**.
* `Box.coreSub_le_stationary_box`, `Box.not_exists_tsd_eigenfield_box`: no nonzero TSD eigenfield
  on a box.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6 (the eigenvalue problem
  of the Hodge Laplacian)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set LinearPMap MeasureTheory

@[expose] public noncomputable section

namespace Feec.Models.Box

open Feec.Models.Torus.GradCurl (Space)
open Models.BoundedDomain (R3 Ix tsd tsd₀ gradCurl)
open Domain (L2F)
open HilbertComplex (totalSub totalJ)
open ShortHilbertComplex (W3 family3 inj₂ mem_totalSub_family3)
open Models.Cube (rowAction)
open Models.Cube.RowWise (J Jr WQ)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

attribute [local instance] Models.Cube.RealTorus.isScalarTower

variable {a ℓ : R3}

/-! ### A complete set of eigenvectors -/

/-- **The wave group of the thesis' complex on every box has a dense set of eigenvectors.** -/
theorem eigenDense_complexBox (hℓ : ∀ i, 0 < ℓ i) : (complexBox a ℓ).waveGroup.EigenDense := by
  rw [complexBox_eq_compress hℓ]
  exact HilbertComplex.eigenDense_compress _ _ _ (eigenDense_torusD (dB_pos hℓ))

/-- **The eigenvector hypothesis of `gradCurl_coreSub_spectral` holds on every box**
`∏ (aᵢ, aᵢ + ℓᵢ)`, `ℓᵢ > 0`. -/
theorem eigenDense_gradCurl_box (hℓ : ∀ i, 0 < ℓ i) :
    (gradCurl ℝ (isOpen_openBox a ℓ)).EigenDense :=
  eigenDense_complexBox hℓ

/-- **`K*` on every box for the thesis' complex**, unconditionally
(`Feec.Models.BoundedDomain.gradCurl_coreSub_spectral` with its eigenvector hypothesis
discharged by `eigenDense_gradCurl_box`). -/
theorem gradCurl_coreSub_spectral_box (hℓ : ∀ i, 0 < ℓ i) :
    (∀ x, (∀ t, 0 ≤ t →
        (gradCurl ℝ (isOpen_openBox a ℓ)).toHilbertComplex.waveGroup.S t x ∈
          HilbertComplex.totalSub
            (ShortHilbertComplex.family3 ⊥ (tsd (openBox a ℓ)) (tsd (openBox a ℓ)))) ↔
          x ∈ (gradCurl ℝ (isOpen_openBox a ℓ)).coreSub (tsd (openBox a ℓ))
            (tsd (openBox a ℓ))) ∧
    ((gradCurl ℝ (isOpen_openBox a ℓ)).coreSub (tsd (openBox a ℓ))
        (tsd (openBox a ℓ)) ≤ (gradCurl ℝ (isOpen_openBox a ℓ)).stationary ↔
      ∀ v ∈ (gradCurl ℝ (isOpen_openBox a ℓ)).invariantCore₁ (tsd (openBox a ℓ))
          (tsd (openBox a ℓ)),
        ∃ h1 : v ∈ (gradCurl ℝ (isOpen_openBox a ℓ)).d₁.domain,
          (gradCurl ℝ (isOpen_openBox a ℓ)).d₁ ⟨v, h1⟩ = 0) ∧
    (¬ (gradCurl ℝ (isOpen_openBox a ℓ)).coreSub (tsd (openBox a ℓ))
        (tsd (openBox a ℓ)) ≤ (gradCurl ℝ (isOpen_openBox a ℓ)).stationary ↔
      ∃ ω : ℝ, 0 < ω ∧ ∃ v : L2F ℝ (openBox a ℓ) Ix, v ≠ 0 ∧ v ∈ tsd (openBox a ℓ) ∧
        (gradCurl ℝ (isOpen_openBox a ℓ)).IsEigenfield ω v) ∧
    (∀ ω : ℝ, 0 < ω → ∀ v : L2F ℝ (openBox a ℓ) Ix, v ∈ tsd (openBox a ℓ) →
      (gradCurl ℝ (isOpen_openBox a ℓ)).IsEigenfield ω v →
        v ∈ (gradCurl ℝ (isOpen_openBox a ℓ)).invariantCore₁ (tsd (openBox a ℓ))
            (tsd (openBox a ℓ)) ∧
          v ∈ tsd₀ (openBox a ℓ) (isOpen_openBox a ℓ) (isBounded_openBox a ℓ) ∧
            (v ≠ 0 → ShortHilbertComplex.inj₁ (𝕜 := ℝ) (L2F ℝ (openBox a ℓ) (Fin 3))
              (L2F ℝ (openBox a ℓ) Ix) (L2F ℝ (openBox a ℓ) Ix) v ∉
                (gradCurl ℝ (isOpen_openBox a ℓ)).stationary)) :=
  Models.BoundedDomain.gradCurl_coreSub_spectral (isOpen_openBox a ℓ)
    (isBounded_openBox a ℓ) (eigenDense_gradCurl_box hℓ)

/-! ### Only stationary data propagate on a box -/

theorem JB_injective (hℓ : ∀ i, 0 < ℓ i) (i : Fin 3) : Function.Injective (JB (a := a) hℓ i) :=
  fun _ _ h => (pullB hℓ i).symm.injective (Models.Cube.RowWise.scaledEmbedding.J_injective i h)

theorem totalJB_injective (hℓ : ∀ i, 0 < ℓ i) :
    Function.Injective (totalJ (JB (a := a) hℓ) : PiLp 2 (WB a ℓ) →L[ℝ] PiLp 2 Space) :=
  fun _ _ h => PiLp.ext fun i => JB_injective hℓ i (congrArg (fun z => z i) h)

/-- **The extension intertwines the wave groups**: `J P⁻¹ e^{tL_B} = e^{tL_d} J P⁻¹`. -/
theorem waveGroup_JB (hℓ : ∀ i, 0 < ℓ i) (t : ℝ) (y : PiLp 2 (WB a ℓ)) :
    totalJ (JB hℓ) ((complexBox a ℓ).waveGroup.S t y) =
      (torusD (dB_pos hℓ)).waveGroup.S t (totalJ (JB hℓ) y) := by
  rw [complexBox_eq_compress hℓ]
  exact HilbertComplex.waveGroup_compress _ _ _ t y

theorem mem_stationary_iff_JB (hℓ : ∀ i, 0 < ℓ i) (y : PiLp 2 (WB a ℓ)) :
    y ∈ (complexBox a ℓ).waveGroup.stationary ↔
      totalJ (JB hℓ) y ∈ (torusD (dB_pos hℓ)).waveGroup.stationary := by
  simp only [C0Group.mem_stationary, ← waveGroup_JB hℓ]
  exact forall_congr' fun t => (totalJB_injective hℓ).eq_iff.symm

/-- The restriction of torus fields to the box: `P ∘ Jr`. -/
def JrB (hℓ : ∀ i, 0 < ℓ i) (i : Fin 3) : Space i →L[ℝ] WB a ℓ i :=
  ((pullB (a := a) hℓ i : WQ i ≃L[ℝ] WB a ℓ i) : WQ i →L[ℝ] WB a ℓ i) ∘L Jr i

theorem JrB_JB (hℓ : ∀ i, 0 < ℓ i) (i : Fin 3) (u : WB a ℓ i) : JrB hℓ i (JB hℓ i u) = u := by
  change pullB hℓ i (Jr i (J i ((pullB hℓ i).symm u))) = u
  rw [Models.Cube.RowWise.Jr_J, ContinuousLinearEquiv.apply_symm_apply]

theorem JB_JrB (hℓ : ∀ i, 0 < ℓ i) (i : Fin 3) {x : Space i}
    (hx : x ∈ Models.Cube.Parity.realAction.fixed i) : JB (a := a) hℓ i (JrB hℓ i x) = x := by
  change J i ((pullB hℓ i).symm (pullB hℓ i (Jr i x))) = x
  rw [ContinuousLinearEquiv.symm_apply_apply, Models.Cube.RowWise.J_Jr i hx]

/-- The pull-back to `Q` of a symmetric trace-free field on the box is symmetric and
trace-free. -/
theorem pullDiagF_symm_symTr (hℓ : ∀ i, 0 < ℓ i) {u : L2F ℝ (openBox a ℓ) Ix}
    (hs : ∀ i j, u (i, j) = u (j, i)) (ht : ∑ i, u (i, i) = 0) :
    (∀ i j, (Domain.pullDiagF (dB_ne_zero hℓ) (bB a ℓ) Models.Cube.Geometry.measurableSet_Q
        (preimage_Q hℓ) Ix).symm u (i, j) =
      (Domain.pullDiagF (dB_ne_zero hℓ) (bB a ℓ) Models.Cube.Geometry.measurableSet_Q
        (preimage_Q hℓ) Ix).symm u (j, i)) ∧
      ∑ i, (Domain.pullDiagF (dB_ne_zero hℓ) (bB a ℓ) Models.Cube.Geometry.measurableSet_Q
        (preimage_Q hℓ) Ix).symm u (i, i) = 0 := by
  simp only [Domain.pullDiagF_symm_apply, Domain.pullDiagF_apply]
  refine ⟨fun i j => by rw [hs i j], ?_⟩
  rw [← map_sum, ht, _root_.map_zero]

theorem JB_one_mem_of_tsd (hℓ : ∀ i, 0 < ℓ i) {u : WB a ℓ 1} (hu : u ∈ tsd (openBox a ℓ)) :
    JB hℓ 1 u ∈ rowAction.fixed 1 ⊓ Models.Cube.Parity.boxSym ⊓ Models.Cube.Parity.boxTr := by
  obtain ⟨hs, ht⟩ := pullDiagF_symm_symTr hℓ hu.1 hu.2.1
  exact ⟨⟨(Models.Cube.Parity.mem_realFixed_iff.1 (Models.Cube.RowWise.J_mem 1 _)).2,
    Models.Cube.RowWise.JR_mem_boxSym hs⟩, Models.Cube.RowWise.JR_mem_boxTr ht⟩

theorem JB_two_mem_of_tsd (hℓ : ∀ i, 0 < ℓ i) {u : WB a ℓ 2} (hu : u ∈ tsd (openBox a ℓ)) :
    JB hℓ 2 u ∈ rowAction.fixed 2 ⊓ Models.Cube.Parity.boxSym ⊓ Models.Cube.Parity.boxTr := by
  obtain ⟨hs, ht⟩ := pullDiagF_symm_symTr hℓ hu.1 hu.2.1
  exact ⟨⟨(Models.Cube.Parity.mem_realFixed_iff.1 (Models.Cube.RowWise.J_mem 2 _)).2,
    Models.Cube.RowWise.JR_mem_boxSym hs⟩, Models.Cube.RowWise.JR_mem_boxTr ht⟩

/-- The torus counterpart of a constraint `S` on the box: the real parity fields whose
restriction to the box lies in the closure of `S`. -/
def torusSubB (hℓ : ∀ i, 0 < ℓ i) (i : Fin 3) (S : Submodule ℝ (WB a ℓ i)) :
    Submodule ℝ (Space i) :=
  Models.Cube.Parity.realAction.fixed i ⊓
    S.topologicalClosure.comap (JrB (a := a) hℓ i : Space i →ₗ[ℝ] WB a ℓ i)

theorem isClosed_torusSubB (hℓ : ∀ i, 0 < ℓ i) (i : Fin 3) (S : Submodule ℝ (WB a ℓ i)) :
    IsClosed (torusSubB hℓ i S : Set (Space i)) :=
  (Models.Cube.Parity.realAction.isClosed_fixed i).inter
    (S.isClosed_topologicalClosure.preimage (JrB hℓ i).continuous)

instance instHasOrthogonalProjectionTorusSubB (hℓ : ∀ i, 0 < ℓ i) (i : Fin 3)
    (S : Submodule ℝ (WB a ℓ i)) : (torusSubB hℓ i S).HasOrthogonalProjection := by
  have : CompleteSpace (torusSubB hℓ i S) := (isClosed_torusSubB hℓ i S).completeSpace_coe
  infer_instance

theorem JB_mem_torusSubB (hℓ : ∀ i, 0 < ℓ i) {i : Fin 3} {S : Submodule ℝ (WB a ℓ i)}
    {u : WB a ℓ i} (hu : u ∈ S) : JB hℓ i u ∈ torusSubB hℓ i S :=
  ⟨Models.Cube.RowWise.J_mem i _, by
    change JrB hℓ i (JB hℓ i u) ∈ S.topologicalClosure
    rw [JrB_JB]; exact S.le_topologicalClosure hu⟩

theorem torusSubB_one_le (hℓ : ∀ i, 0 < ℓ i) {S : Submodule ℝ (L2F ℝ (openBox a ℓ) Ix)}
    (h : S ≤ tsd (openBox a ℓ)) :
    torusSubB hℓ 1 S ≤ rowAction.fixed 1 ⊓ Models.Cube.Parity.boxSym ⊓
      Models.Cube.Parity.boxTr := by
  intro x hx
  rw [← JB_JrB hℓ 1 hx.1]
  exact JB_one_mem_of_tsd hℓ
    (S.topologicalClosure_minimal h Models.BoundedDomain.isClosed_tsd hx.2)

theorem torusSubB_two_le (hℓ : ∀ i, 0 < ℓ i) {S : Submodule ℝ (L2F ℝ (openBox a ℓ) Ix)}
    (h : S ≤ tsd (openBox a ℓ)) :
    torusSubB hℓ 2 S ≤ rowAction.fixed 2 ⊓ Models.Cube.Parity.boxSym ⊓
      Models.Cube.Parity.boxTr := by
  intro x hx
  rw [← JB_JrB hℓ 2 hx.1]
  exact JB_two_mem_of_tsd hℓ
    (S.topologicalClosure_minimal h Models.BoundedDomain.isClosed_tsd hx.2)

/-- **On every box with the thesis' boundary conditions, forward invariance forces
stationarity**: for `S₁, S₂ ⊆ L²(TSD)` (closed or not), the forward orbit (`t ≥ 0`) of `y` under
the wave group of `H̊¹(B) → H̊(curl, B) → L²(B)` stays in `{0} × S₁ × S₂` iff `y` lies there
and is stationary. See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem forward_iff (hℓ : ∀ i, 0 < ℓ i) {S1 S2 : Submodule ℝ (L2F ℝ (openBox a ℓ) Ix)}
    (h1 : S1 ≤ tsd (openBox a ℓ)) (h2 : S2 ≤ tsd (openBox a ℓ)) (y : PiLp 2 (WB a ℓ)) :
    (∀ t, 0 ≤ t → (complexBox a ℓ).waveGroup.S t y ∈
        totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openBox a ℓ) (Fin 3))) S1 S2)) ↔
      y ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openBox a ℓ) (Fin 3))) S1 S2) ∧
        y ∈ (complexBox a ℓ).waveGroup.stationary := by
  have := instHasOrthogonalProjectionTorusSubB hℓ 1 S1
  have := instHasOrthogonalProjectionTorusSubB hℓ 2 S2
  constructor
  · intro h
    have hy := h 0 le_rfl
    rw [C0Group.S_zero_apply] at hy
    refine ⟨hy, ?_⟩
    have hK : ∀ t, 0 ≤ t → (torusD (dB_pos hℓ)).waveGroup.S t (totalJ (JB hℓ) y) ∈
        totalSub (Models.Cube.Parity.constraint (torusSubB hℓ 1 S1) (torusSubB hℓ 2 S2)) := by
      intro t ht
      rw [← waveGroup_JB]
      obtain ⟨e0, m1, m2⟩ := mem_totalSub_family3.1 (h t ht)
      refine Models.Cube.Parity.mem_totalSub_constraint.2
        ⟨?_, JB_mem_torusSubB hℓ m1, JB_mem_torusSubB hℓ m2⟩
      have e0' : ((complexBox a ℓ).waveGroup.S t y 0 : L2F ℝ (openBox a ℓ) (Fin 3)) = 0 := e0
      show JB hℓ 0 ((complexBox a ℓ).waveGroup.S t y 0) = 0
      rw [e0', _root_.map_zero]
    have hc := (torusD (dB_pos hℓ)).isIsometric_waveGroup.mem_invariantCore_of_forward_invariant
      (isPurePoint_torusD (dB_pos hℓ)) HilbertComplex.isClosed_totalSub hK
    exact (mem_stationary_iff_JB hℓ y).2 ((mem_invariantCore_torusD_iff (dB_pos hℓ)
      (torusSubB_one_le hℓ h1) (torusSubB_two_le hℓ h2) _).1 hc).2
  · rintro ⟨hK, hst⟩ t _
    rw [C0Group.mem_stationary.1 hst t]; exact hK

/-- **`K*` on every box with the thesis' boundary conditions consists of the stationary data in
`K`**, for every `S₁, S₂ ⊆ L²(TSD)`. See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem mem_invariantCore_iff (hℓ : ∀ i, 0 < ℓ i) {S1 S2 : Submodule ℝ (L2F ℝ (openBox a ℓ) Ix)}
    (h1 : S1 ≤ tsd (openBox a ℓ)) (h2 : S2 ≤ tsd (openBox a ℓ)) (y : PiLp 2 (WB a ℓ)) :
    y ∈ (complexBox a ℓ).waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openBox a ℓ) (Fin 3))) S1 S2)) ↔
      y ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openBox a ℓ) (Fin 3))) S1 S2) ∧
        y ∈ (complexBox a ℓ).waveGroup.stationary := by
  refine ⟨fun hy => (forward_iff hℓ h1 h2 y).1 fun t _ => C0Group.mem_invariantCore.1 hy t,
    fun ⟨hK, hst⟩ => C0Group.mem_invariantCore.2 fun t => ?_⟩
  rw [C0Group.mem_stationary.1 hst t]; exact hK

/-- **`K*` on every box for the thesis' constraint, explicitly**: `y ∈ K*` iff `y = (0, 0, B₀)`
with `B₀ ∈ L²(TSD)` and `d₁† B₀ = curl B₀ = 0` (no boundary condition on `B₀`).
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem mem_invariantCore_tsd_iff (hℓ : ∀ i, 0 < ℓ i) (y : PiLp 2 (WB a ℓ)) :
    y ∈ (complexBox a ℓ).waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openBox a ℓ) (Fin 3)))
          (tsd (openBox a ℓ)) (tsd (openBox a ℓ)))) ↔
      ∃ B ∈ tsd (openBox a ℓ),
        ∃ h : B ∈ ((gradCurl ℝ (isOpen_openBox a ℓ)).d₁†).domain,
          (gradCurl ℝ (isOpen_openBox a ℓ)).d₁† ⟨B, h⟩ = 0 ∧
            y = inj₂ (𝕜 := ℝ) (L2F ℝ (openBox a ℓ) (Fin 3)) (L2F ℝ (openBox a ℓ) Ix)
              (L2F ℝ (openBox a ℓ) Ix) B := by
  rw [mem_invariantCore_iff hℓ le_rfl le_rfl, mem_totalSub_family3]
  constructor
  · rintro ⟨⟨h0, h1, h2⟩, hst⟩
    have h0' : (y 0 : WB a ℓ 0) = 0 := h0
    have hf : ((totalJ (JB hℓ) y) 1 : Space 1) ∈ rowAction.fixed 1 :=
      (Models.Cube.Parity.mem_realFixed_iff.1 (Models.Cube.RowWise.J_mem 1 _)).2
    have e1 := mem_stationary_torusD_of (dB_pos hℓ) hf ((mem_stationary_iff_JB hℓ y).1 hst)
    have hy1 : (y 1 : WB a ℓ 1) = 0 :=
      JB_injective hℓ 1 (e1.trans (_root_.map_zero (JB hℓ 1)).symm)
    have hy : y = inj₂ (𝕜 := ℝ) (L2F ℝ (openBox a ℓ) (Fin 3)) (L2F ℝ (openBox a ℓ) Ix)
        (L2F ℝ (openBox a ℓ) Ix) (y 2 : WB a ℓ 2) := PiLp.ext fun i => by
      fin_cases i
      exacts [h0', hy1, rfl]
    rw [hy] at hst
    obtain ⟨hB, hB0⟩ := (Models.Cube.RowWise.inj₂_mem_stationary_iff _ _).1 hst
    exact ⟨y 2, h2, hB, hB0, hy⟩
  · rintro ⟨B, hB, hd, hd0, rfl⟩
    exact ⟨⟨rfl, Submodule.zero_mem _, hB⟩,
      (Models.Cube.RowWise.inj₂_mem_stationary_iff _ _).2 ⟨hd, hd0⟩⟩

/-- **`K*` is stationary on every box.** -/
theorem coreSub_le_stationary_box (hℓ : ∀ i, 0 < ℓ i) :
    (gradCurl ℝ (isOpen_openBox a ℓ)).coreSub (tsd (openBox a ℓ)) (tsd (openBox a ℓ)) ≤
      (gradCurl ℝ (isOpen_openBox a ℓ)).stationary := by
  intro y hy
  exact ((forward_iff hℓ le_rfl le_rfl y).1 (((gradCurl_coreSub_spectral_box hℓ).1 y).2 hy)).2

/-- **No TSD eigenfield on a box**: there are no `ω > 0` and nonzero `u ∈ L²(TSD) ∩ H̊(curl)` with
`curl u ∈ D(curl†)` and `curl† curl u = ω² u`. -/
theorem not_exists_tsd_eigenfield_box (hℓ : ∀ i, 0 < ℓ i) :
    ¬ ∃ ω : ℝ, 0 < ω ∧ ∃ v : L2F ℝ (openBox a ℓ) Ix, v ≠ 0 ∧ v ∈ tsd (openBox a ℓ) ∧
      (gradCurl ℝ (isOpen_openBox a ℓ)).IsEigenfield ω v :=
  fun h => ((gradCurl_coreSub_spectral_box hℓ).2.2.1.2 h) (coreSub_le_stationary_box hℓ)

end Feec.Models.Box
