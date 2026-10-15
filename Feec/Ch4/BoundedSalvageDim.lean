module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Feec.Ch4.BoundedSalvageMax

/-!
# The bounded-domain obstruction is infinite-dimensional

On a nonempty bounded open `Ω ⊆ ℝ³`, `Feec.Ch4.BoundedSalvage` shows that the Hessian `∇²h` of
every smooth harmonic `h` lies in the obstruction space `obstr = L²(TSD) ⊓ L²(TSD₀)ᗮ` (the part of
`L²(TSD)` that `L²(TSD) ∩ H̊(curl, M)` cannot approximate), and `Feec.Ch4.BoundedSalvageMax`
shows that it is a stationary magnetic datum of the thesis' (4.14), i.e. lies in the slot `S2*`
of the maximal propagating constraint space. This file proves that these Hessians span an
infinite-dimensional space: the obstruction is not just the five constant directions.

## The mathematics

Take `h_t(x) = e^{-t x₁} cos(t x₂)` (`expCos t`), harmonic, for `t = 1, 2, 3, …`. Then
`∂₁ ∇²h_t = -t ∇²h_t` (Schwarz), so the Hessians are eigenvectors of `∂₁` with distinct
eigenvalues. To transport this to `L²(Ω)`, let `M` be the smooth matrix fields on `ℝ³` and
`F : M → L²(Ω; ℝ³ˣ³)` the restriction (`restrictL2`). Since `Ω` is open, `F Ψ = 0` iff `Ψ = 0` on
`Ω` (`eqOn_zero_of_smoothField_eq_zero`), so `∂₁` preserves `ker F` and descends to
`M ⧸ ker F ≅ range F`; there the classes of `∇²h_t` are eigenvectors with distinct eigenvalues,
nonzero because the entries `t² e^{-t x₁} cos(t x₂)` and `t² e^{-t x₁} sin(t x₂)` never vanish
together. Eigenvectors for distinct eigenvalues are linearly independent
(`Module.End.eigenvectors_linearIndependent'`).

## Main results

* `linearIndependent_hessL2_expCos`: the `L²(Ω)` classes of `∇²h_{n+1}`, `n ∈ ℕ`, are linearly
  independent.
* `not_finiteDimensional_obstr`: `obstr` is infinite-dimensional.
* `thesisComplex_not_finiteDimensional_S2max`: the magnetic slot `S2*` of the maximal
  propagating constraint space of the thesis' complex is infinite-dimensional (it contains the
  harmonic Hessians as stationary data).

Correction: the defect of the density claimed in [QuennevilleBelair2015, §4.10, proof of
Prop 4.17] is infinite-dimensional: `L²(TSD) ∩ H̊(curl, M)` misses an infinite-dimensional
subspace of `L²(TSD)`.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17)
* [Brezis2011] (Sobolev spaces)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ContDiff
open MeasureTheory Set Filter Topology

namespace Feec.BoundedDomain

variable {Ω : Set R3}

/-! ## Restriction of smooth fields to `L²(Ω)` -/

/-- Smooth matrix fields on `ℝ³`. -/
def smoothFields : Submodule ℝ (Ix → R3 → ℝ) where
  carrier := {Ψ | ∀ ij, ContDiff ℝ ∞ (Ψ ij)}
  zero_mem' := fun _ => contDiff_const
  add_mem' := fun hΨ hΦ ij => (hΨ ij).add (hΦ ij)
  smul_mem' := fun c _ hΨ ij => (hΨ ij).const_smul c

/-- The restriction `F : Ψ ↦ [Ψ|_Ω] ∈ L²(Ω; ℝ³ˣ³)`. -/
def restrictL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    smoothFields →ₗ[ℝ] L2M Ω where
  toFun Ψ := smoothField hΩ hb Ψ fun ij => (Ψ.2 ij).continuous
  map_add' Ψ Φ := by
    refine (WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_)
    filter_upwards [coeFn_smoothField hΩ hb (Ψ + Φ : smoothFields)
        (fun ij => ((Ψ + Φ).2 ij).continuous) ij,
      coeFn_smoothField hΩ hb Ψ (fun ij => (Ψ.2 ij).continuous) ij,
      coeFn_smoothField hΩ hb Φ (fun ij => (Φ.2 ij).continuous) ij,
      Lp.coeFn_add (smoothField hΩ hb Ψ (fun ij => (Ψ.2 ij).continuous) ij)
        (smoothField hΩ hb Φ (fun ij => (Φ.2 ij).continuous) ij)] with x h1 h2 h3 h4
    simp only [PiLp.add_apply] at h4 ⊢
    rw [h1, h4, Pi.add_apply, h2, h3]
    rfl
  map_smul' c Ψ := by
    refine (WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_)
    filter_upwards [coeFn_smoothField hΩ hb (c • Ψ : smoothFields)
        (fun ij => ((c • Ψ).2 ij).continuous) ij,
      coeFn_smoothField hΩ hb Ψ (fun ij => (Ψ.2 ij).continuous) ij,
      Lp.coeFn_smul c (smoothField hΩ hb Ψ (fun ij => (Ψ.2 ij).continuous) ij)] with x h1 h2 h3
    simp only [PiLp.smul_apply, RingHom.id_apply] at h3 ⊢
    rw [h1, h3, Pi.smul_apply, h2]
    rfl

theorem restrictL2_apply (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (Ψ : smoothFields) :
    restrictL2 hΩ hb Ψ = smoothField hΩ hb Ψ fun ij => (Ψ.2 ij).continuous := rfl

/-- A continuous field whose `L²(Ω)` class vanishes vanishes on `Ω` (`Ω` open). -/
theorem eqOn_zero_of_smoothField_eq_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, Continuous (Ψ ij)) (h0 : smoothField hΩ hb Ψ hΨ = 0)
    (ij : Ix) : ∀ x ∈ Ω, Ψ ij x = 0 := by
  have hae : Ψ ij =ᵐ[volume.restrict Ω] fun _ => (0 : ℝ) := by
    filter_upwards [coeFn_smoothField hΩ hb Ψ hΨ ij, Lp.coeFn_zero ℝ 2 (volume.restrict Ω)]
      with x h1 h2
    rw [← h1, h0]
    exact h2
  exact fun x hx => Measure.eqOn_open_of_ae_eq hae hΩ (hΨ ij).continuousOn continuousOn_const hx

/-- A continuous field vanishing on `Ω` is `0` in `L²(Ω)`. -/
theorem smoothField_eq_zero_of_eqOn (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, Continuous (Ψ ij)) (h0 : ∀ ij, ∀ x ∈ Ω, Ψ ij x = 0) :
    smoothField hΩ hb Ψ hΨ = 0 := by
  refine (WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_)
  filter_upwards [coeFn_smoothField hΩ hb Ψ hΨ ij, Lp.coeFn_zero ℝ 2 (volume.restrict Ω),
    ae_restrict_mem hΩ.measurableSet] with x h1 h2 hx
  rw [h1, h0 ij x hx]
  exact h2.symm

/-! ## The operator `∂₁` on smooth fields -/

/-- `∂₁` acting entrywise on smooth matrix fields. -/
def pd0L : smoothFields →ₗ[ℝ] smoothFields where
  toFun Ψ := ⟨fun ij => pd 0 (Ψ.1 ij), fun ij => contDiff_pd_top (Ψ.2 ij) 0⟩
  map_add' Ψ Φ := by
    refine Subtype.ext (funext fun ij => funext fun x => ?_)
    exact pd_add ((Ψ.2 ij).differentiable (by simp)) ((Φ.2 ij).differentiable (by simp)) 0 x
  map_smul' c Ψ := by
    refine Subtype.ext (funext fun ij => funext fun x => ?_)
    exact pd_const_mul ((Ψ.2 ij).differentiable (by simp)) c 0 x

/-- `∂₁` preserves `ker F` (fields vanishing on the open set `Ω`). -/
theorem pd0L_mem_ker (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (Ψ : smoothFields)
    (hΨ : Ψ ∈ LinearMap.ker (restrictL2 hΩ hb)) :
    pd0L Ψ ∈ LinearMap.ker (restrictL2 hΩ hb) := by
  rw [LinearMap.mem_ker, restrictL2_apply] at hΨ ⊢
  refine smoothField_eq_zero_of_eqOn hΩ hb _ fun ij x hx => ?_
  have h0 := eqOn_zero_of_smoothField_eq_zero hΩ hb _ hΨ ij
  have hev : Ψ.1 ij =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hΩ.mem_nhds hx) fun y hy => h0 y hy
  change pd 0 (Ψ.1 ij) x = 0
  rw [pd, hev.fderiv_eq]
  simp

/-! ## The harmonic functions `e^{-t x₁} cos(t x₂)` -/

theorem pd_expCos_fun (t : ℝ) (k : Fin 3) :
    pd k (expCos t) = fun x =>
      if k = 0 then -t * expCos t x else if k = 1 then -t * expSin t x else 0 :=
  funext (pd_expCos t k)

theorem pd_expSin_fun (t : ℝ) (k : Fin 3) :
    pd k (expSin t) = fun x =>
      if k = 0 then -t * expSin t x else if k = 1 then t * expCos t x else 0 :=
  funext (pd_expSin t k)

theorem pd_const_mul_fun {f : R3 → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (k : Fin 3) :
    pd k (fun x => c * f x) = fun x => c * pd k f x :=
  funext (pd_const_mul hf c k)

/-- `∂₁ h_t = -t h_t`. -/
theorem pd0_expCos (t : ℝ) : pd 0 (expCos t) = fun x => -t * expCos t x := by
  rw [pd_expCos_fun]; simp

/-- `h_t` is harmonic. -/
theorem lap_expCos (t : ℝ) (x : R3) : lap (expCos t) x = 0 := by
  simp only [lap, Fin.sum_univ_three, pd_expCos_fun]
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq]
  rw [pd_const_mul_fun (differentiable_expCos t), pd_const_mul_fun (differentiable_expSin t),
    pd_expCos_fun, pd_expSin_fun]
  simp [pd]

/-- `∂₁ ∇²h = ∇²(∂₁ h)` for smooth `h` (Schwarz). -/
theorem pd0_hessField {h : R3 → ℝ} (hh : ContDiff ℝ ∞ h) (ij : Ix) :
    pd 0 (hessField h ij) = hessField (pd 0 h) ij := by
  simp only [hessField]
  funext x
  have e1 : pd 0 (pd ij.1 h) = pd ij.1 (pd 0 h) :=
    funext fun y => pd_pd_comm (hh.of_le (by simp)) 0 ij.1 y
  rw [pd_pd_comm ((contDiff_pd_top hh _).of_le (by simp)) 0 ij.2 x, e1]

/-- `∇²(c h) = c ∇²h`. -/
theorem hessField_const_mul {h : R3 → ℝ} (hh : ContDiff ℝ ∞ h) (c : ℝ) (ij : Ix) :
    hessField (fun x => c * h x) ij = fun x => c * hessField h ij x := by
  simp only [hessField]
  rw [pd_const_mul_fun (hh.differentiable (by simp)),
    pd_const_mul_fun ((contDiff_pd_top hh _).differentiable (by simp))]

/-- The Hessian `∇²h_t` as a smooth field. -/
def hessExp (t : ℝ) : smoothFields := ⟨hessField (expCos t), contDiff_hessField (contDiff_expCos t)⟩

/-- `∂₁ ∇²h_t = -t ∇²h_t`. -/
theorem pd0L_hessExp (t : ℝ) : pd0L (hessExp t) = (-t) • hessExp t := by
  refine Subtype.ext (funext fun ij => ?_)
  change pd 0 (hessField (expCos t) ij) = fun x => -t * hessField (expCos t) ij x
  rw [pd0_hessField (contDiff_expCos t), pd0_expCos, hessField_const_mul (contDiff_expCos t)]

/-- Two entries of `∇²h_t`: `(∇²h_t)_{11} = t² h_t`, `(∇²h_t)_{12} = t² e^{-t x₁} sin(t x₂)`. -/
theorem hessField_expCos_00 (t : ℝ) (x : R3) :
    hessField (expCos t) (0, 0) x = t ^ 2 * expCos t x := by
  simp only [hessField, pd0_expCos]
  rw [pd_const_mul_fun (differentiable_expCos t), pd0_expCos]
  ring

theorem hessField_expCos_01 (t : ℝ) (x : R3) :
    hessField (expCos t) (0, 1) x = t ^ 2 * expSin t x := by
  simp only [hessField, pd0_expCos]
  rw [pd_const_mul_fun (differentiable_expCos t), pd_expCos_fun]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
  ring

/-- `∇²h_t ≠ 0` in `L²(Ω)` for `t ≠ 0` and nonempty `Ω`. -/
theorem restrictL2_hessExp_ne_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) {t : ℝ} (ht : t ≠ 0) : restrictL2 hΩ hb (hessExp t) ≠ 0 := by
  intro h0
  obtain ⟨x, hx⟩ := hne
  rw [restrictL2_apply] at h0
  have a := eqOn_zero_of_smoothField_eq_zero hΩ hb _ h0 (0, 0) x hx
  have b := eqOn_zero_of_smoothField_eq_zero hΩ hb _ h0 (0, 1) x hx
  change hessField (expCos t) (0, 0) x = 0 at a
  change hessField (expCos t) (0, 1) x = 0 at b
  rw [hessField_expCos_00] at a
  rw [hessField_expCos_01] at b
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hex : Real.exp (-t * x 0) ≠ 0 := (Real.exp_pos _).ne'
  simp only [mul_eq_zero, ht2, false_or, expCos, expSin, hex] at a b
  have := Real.sin_sq_add_cos_sq (t * x 1)
  rw [a, b] at this
  norm_num at this

/-! ## Linear independence and infinite dimension -/

/-- **The Hessians `∇²h_{n+1}` are linearly independent in `L²(Ω; ℝ³ˣ³)`** for every nonempty
bounded open `Ω`. -/
theorem linearIndependent_hessL2_expCos (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    LinearIndependent ℝ (fun n : ℕ => hessL2 hΩ hb (contDiff_expCos ((n : ℝ) + 1))) := by
  set F := restrictL2 hΩ hb
  set N := LinearMap.ker F
  let D : Module.End ℝ (smoothFields ⧸ N) := N.mapQ N (pd0L) fun Ψ hΨ => pd0L_mem_ker hΩ hb Ψ hΨ
  have hli : LinearIndependent ℝ (fun n : ℕ => N.mkQ (hessExp ((n : ℝ) + 1))) := by
    refine Module.End.eigenvectors_linearIndependent' D (fun n : ℕ => -((n : ℝ) + 1))
      (fun m n h => by simpa using h) _ fun n => ?_
    refine Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 ?_, ?_⟩
    · change N.mkQ (pd0L (hessExp ((n : ℝ) + 1))) = _
      rw [pd0L_hessExp, LinearMap.map_smul]
    · rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker]
      exact restrictL2_hessExp_ne_zero hΩ hb hne (by positivity)
  have hinj : LinearMap.ker (N.liftQ F le_rfl) = ⊥ := Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have := hli.map' (N.liftQ F le_rfl) hinj
  exact this

/-- **The obstruction space is infinite-dimensional** on every nonempty bounded open `Ω ⊆ ℝ³`:
`L²(TSD) ⊓ L²(TSD₀)ᗮ`, which `L²(TSD) ∩ H̊(curl, M)` cannot approximate, contains the
independent Hessians `∇²(e^{-n x₁} cos(n x₂))`.

Correction: [QuennevilleBelair2015, §4.10, proof of Prop 4.17]. -/
theorem not_finiteDimensional_obstr (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : ¬ FiniteDimensional ℝ (obstr Ω hΩ hb) := by
  intro hfin
  let v : ℕ → obstr Ω hΩ hb := fun n => ⟨_, hessL2_mem_obstr hΩ hb
    (contDiff_expCos ((n : ℝ) + 1)) (lap_expCos _)⟩
  have hli : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (obstr Ω hΩ hb).subtype (linearIndependent_hessL2_expCos hΩ hb hne)
  exact Module.Finite.not_linearIndependent_of_infinite v hli

open Feec.Constraints in
/-- **The stationary part of the maximal propagating constraint space is infinite-dimensional**:
for the thesis' complex on a nonempty bounded open `Ω` and any orthogonal group `G` generated by
`-L`, the magnetic slot `S2*` contains the independent harmonic Hessians. -/
theorem thesisComplex_not_finiteDimensional_S2max (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (G : UnitaryGroupGenerator (-(thesisComplex hΩ hb).waveOp)) :
    ¬ FiniteDimensional ℝ (S2max G (TSD Ω) (TSD Ω)) := by
  intro hfin
  let v : ℕ → S2max G (TSD Ω) (TSD Ω) := fun n => ⟨_, thesisComplex_hessL2_mem_S2max hΩ hb G
    (contDiff_expCos ((n : ℝ) + 1)) (lap_expCos _)⟩
  have hli : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (S2max G (TSD Ω) (TSD Ω)).subtype
      (linearIndependent_hessL2_expCos hΩ hb hne)
  exact Module.Finite.not_linearIndependent_of_infinite v hli

end Feec.BoundedDomain
