module

public import Feec.ForMathlib.LinearAlgebra.MatrixDeterminantLemma
public import Feec.TimeStepping.RungeKutta

/-!
# Runge–Kutta methods of bounded operators

For bounded `L` with `d(τL)` invertible, the Runge–Kutta stages exist and are unique, and the step
is the rational scheme `n(τL) d(τL)⁻¹` of the stability function.

## References

* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996],
  §IV.3

Bibliography: [references.bib](../../docs/references.bib)
-/

open Polynomial Matrix

@[expose] public noncomputable section

namespace Feec.TimeStepping.ButcherTableau

variable {s : ℕ} (T : ButcherTableau s)

/-- The matrix `1 - X A` over `ℝ[X]`; its determinant is the stability denominator. -/
def stageMatrix : Matrix (Fin s) (Fin s) ℝ[X] := 1 - (X : ℝ[X]) • T.A.map C

theorem det_stageMatrix : T.stageMatrix.det = T.stabilityDen := rfl

theorem stabilityNum_eq_stabilityDen_add : T.stabilityNum = T.stabilityDen +
    X * ((fun i => C (T.b i)) ⬝ᵥ (T.stageMatrix.adjugate *ᵥ fun _ => 1)) := by
  have e : (1 : Matrix (Fin s) (Fin s) ℝ[X]) -
      (X : ℝ[X]) • (T.A - vecMulVec (fun _ => 1) T.b).map C =
      T.stageMatrix + replicateCol Unit (fun _ => (X : ℝ[X])) *
        replicateRow Unit (fun j => C (T.b j)) := by
    refine Matrix.ext fun i j => ?_
    simp [stageMatrix, vecMulVec_apply, Matrix.mul_apply, replicateCol_apply, replicateRow_apply]
    ring
  rw [stabilityNum, e, det_add_replicateCol_mul_replicateRow_eq_det_add, det_stageMatrix,
    show (fun _ => (X : ℝ[X])) = (X : ℝ[X]) • fun _ : Fin s => (1 : ℝ[X]) from
      funext fun _ => by rw [Pi.smul_apply, smul_eq_mul, mul_one],
    mulVec_smul, dotProduct_smul, smul_eq_mul]

/-! ### The stages of a bounded operator -/

section Stages

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The stages `kᵢ = L (u + τ ∑ⱼ aᵢⱼ kⱼ)` of the method for `u' = L u` with step `τ` from `u`. -/
def IsStage (L : E →L[𝕜] E) (τ : ℝ) (u : E) (k : Fin s → E) : Prop :=
  ∀ i, k i = L (u + (τ : 𝕜) • ∑ j, (T.A i j : 𝕜) • k j)

/-- A square matrix of operators acting on `Eˢ`. -/
private def act (N : Matrix (Fin s) (Fin s) (E →L[𝕜] E)) (k : Fin s → E) : Fin s → E :=
  fun i => ∑ j, N i j (k j)

private theorem act_mul (N N' : Matrix (Fin s) (Fin s) (E →L[𝕜] E)) (k : Fin s → E) :
    act (N * N') k = act N (act N' k) := by
  funext i
  simp only [act, Matrix.mul_apply, _root_.sum_apply, mul_apply_eq_comp, map_sum]
  exact Finset.sum_comm

variable (L : E →L[𝕜] E) (τ : ℝ)

/-- Real polynomials evaluated at `τ L`. -/
private def ev : ℝ[X] →+* (E →L[𝕜] E) :=
  (aeval ((τ : 𝕜) • L)).toRingHom.comp (mapRingHom (algebraMap ℝ 𝕜))

private theorem ev_apply (f : ℝ[X]) :
    ev L τ f = aeval ((τ : 𝕜) • L) (f.map (algebraMap ℝ 𝕜)) :=
  rfl

private theorem commute_ev (f g : ℝ[X]) : Commute (ev L τ f) (ev L τ g) :=
  commute_aeval (commute_aeval (Commute.refl _) _).symm _

private theorem ev_C (a : ℝ) (x : E) : ev L τ (C a) x = (a : 𝕜) • x := by
  simp [ev_apply, Algebra.algebraMap_eq_smul_one]

private theorem ev_X (x : E) : ev L τ X x = (τ : 𝕜) • L x := by
  simp [ev_apply]

private theorem act_smul_one (c : ℝ[X]) (k : Fin s → E) :
    act ((c • (1 : Matrix (Fin s) (Fin s) ℝ[X])).map (ev L τ)) k = fun i => ev L τ c (k i) := by
  funext i
  simp only [act, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

private theorem act_stageMatrix (k : Fin s → E) (i : Fin s) :
    act (T.stageMatrix.map (ev L τ)) k i = k i - L ((τ : 𝕜) • ∑ j, (T.A i j : 𝕜) • k j) := by
  simp only [act, stageMatrix, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, map_sub, map_mul, _root_.sub_apply, mul_apply_eq_comp,
    Finset.sum_sub_distrib, ev_C, ev_X, map_sum, map_smul, Finset.smul_sum]
  congr 1
  · rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simp
  · exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

private theorem isStage_iff_act (u : E) (k : Fin s → E) :
    T.IsStage L τ u k ↔ act (T.stageMatrix.map (ev L τ)) k = fun _ => L u := by
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  rw [act_stageMatrix, map_add, sub_eq_iff_eq_add, add_comm]

private theorem ev_apply_apply (f : ℝ[X]) (x : E) : ev L τ f (L x) = L (ev L τ f x) :=
  DFunLike.congr_fun (commute_aeval ((Commute.refl L).smul_left (τ : 𝕜)) _).eq x

variable {L τ}

private theorem ev_den_apply_of_isStage {u : E} {k : Fin s → E} (hk : T.IsStage L τ u k)
    (i : Fin s) :
    ev L τ T.stabilityDen (k i) = ∑ j, ev L τ (T.stageMatrix.adjugate i j) (L u) := by
  have h := congrFun (act_mul (T.stageMatrix.adjugate.map (ev L τ))
    (T.stageMatrix.map (ev L τ)) k) i
  rw [← Matrix.map_mul, adjugate_mul, act_smul_one, (T.isStage_iff_act L τ u k).1 hk] at h
  exact h

/-- **The stages exist and are unique** when `d(τL)` is invertible, `d = det(1 - X A)`.
[HairerWanner1996], §IV.3 -/
theorem existsUnique_isStage
    (h : IsUnit (aeval ((τ : 𝕜) • L) (T.stabilityDen.map (algebraMap ℝ 𝕜)))) (u : E) :
    ∃! k, T.IsStage L τ u k := by
  obtain ⟨Q, hQ⟩ := h
  rw [← ev_apply] at hQ
  set N := T.stageMatrix.adjugate.map (ev L τ)
  set M := T.stageMatrix.map (ev L τ)
  have hc : ∀ i j, Commute (M i j) (↑Q⁻¹ : E →L[𝕜] E) := fun i j =>
    Commute.units_inv_right (hQ ▸ commute_ev L τ _ _)
  refine ⟨fun i => (↑Q⁻¹ : E →L[𝕜] E) (act N (fun _ => L u) i), ?_, fun k hk => ?_⟩
  · refine (T.isStage_iff_act L τ u _).2 (funext fun i => ?_)
    have e : act M (fun i => (↑Q⁻¹ : E →L[𝕜] E) (act N (fun _ => L u) i)) i =
        (↑Q⁻¹ : E →L[𝕜] E) (act (M * N) (fun _ => L u) i) := by
      rw [act_mul]
      simp only [act, map_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ =>
        DFunLike.congr_fun (hc i j).eq _
    rw [e, show M * N = (T.stabilityDen • (1 : Matrix (Fin s) (Fin s) ℝ[X])).map (ev L τ) by
      rw [← Matrix.map_mul, mul_adjugate, det_stageMatrix], act_smul_one, ← hQ,
      ← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]
  · funext i
    have h := T.ev_den_apply_of_isStage hk i
    rw [← hQ] at h
    rw [show act N (fun _ => L u) i = ∑ j, ev L τ (T.stageMatrix.adjugate i j) (L u) from rfl,
      ← h, ← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]

variable {T} in
/-- **The Runge–Kutta step is the rational scheme of its stability function**: if `d(τL)` is
invertible, `u + τ ∑ᵢ bᵢ kᵢ = n(τL) d(τL)⁻¹ u` for the stages `k`. [HairerWanner1996], §IV.3 -/
theorem IsStage.add_smul_sum_eq {u : E} {k : Fin s → E} (hk : T.IsStage L τ u k)
    (h : IsUnit (aeval ((τ : 𝕜) • L) (T.stabilityDen.map (algebraMap ℝ 𝕜)))) :
    u + (τ : 𝕜) • ∑ i, (T.b i : 𝕜) • k i =
      (aeval ((τ : 𝕜) • L) (T.stabilityNum.map (algebraMap ℝ 𝕜)) *
        Ring.inverse (aeval ((τ : 𝕜) • L) (T.stabilityDen.map (algebraMap ℝ 𝕜)))) u := by
  rw [← ev_apply, ← ev_apply]
  rw [← ev_apply] at h
  -- `d(τL)` applied to the update is `n(τL) u`
  have key : ev L τ T.stabilityDen (u + (τ : 𝕜) • ∑ i, (T.b i : 𝕜) • k i) =
      ev L τ T.stabilityNum u := by
    rw [T.stabilityNum_eq_stabilityDen_add, (ev L τ).map_add, _root_.add_apply,
      map_add (ev L τ T.stabilityDen), (ev L τ).map_mul, mul_apply_eq_comp, ev_X]
    congr 1
    simp only [map_smul, map_sum, T.ev_den_apply_of_isStage hk, ev_apply_apply]
    simp only [dotProduct, mulVec, map_sum, map_mul, mul_one, _root_.sum_apply, mul_apply_eq_comp,
      ev_C]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    simp only [map_smul]
  obtain ⟨Q, hQ⟩ := h
  have hc : Commute (ev L τ T.stabilityNum) (↑Q⁻¹ : E →L[𝕜] E) :=
    Commute.units_inv_right (hQ ▸ commute_ev L τ _ _)
  rw [← hQ, Ring.inverse_unit]
  calc u + (τ : 𝕜) • ∑ i, (T.b i : 𝕜) • k i =
        ((↑Q⁻¹ : E →L[𝕜] E) * ↑Q) (u + (τ : 𝕜) • ∑ i, (T.b i : 𝕜) • k i) := by
          rw [Units.inv_mul, one_apply_eq_self]
    _ = (↑Q⁻¹ : E →L[𝕜] E) (ev L τ T.stabilityNum u) := by rw [mul_apply_eq_comp, hQ, key]
    _ = (ev L τ T.stabilityNum * ↑Q⁻¹) u := (DFunLike.congr_fun hc.eq u).symm

end Stages

end Feec.TimeStepping.ButcherTableau
