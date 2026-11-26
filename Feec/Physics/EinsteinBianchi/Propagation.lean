module

public import Feec.Physics.EinsteinBianchi.Fields
public import Feec.ForMathlib.Calculus.TimeSlice
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Constraint propagation for the linearized Einstein–Bianchi system on `ℝ³`

For `C²` solutions of `Ė = -curl B`, `Ḃ = curl E` on `ℝ³` with compact spatial support, locally
uniformly in time, TSD data stay TSD for all `t ≥ 0` ([QuennevilleBelair2015], Prop 3.6 (adapted)).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Matrix Feec.MatrixSymbol Feec.DoubleForm
open MeasureTheory Filter Topology Set

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi

section Calculus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {M N P Q : X → Matrix (Fin 3) (Fin 3) ℝ}

theorem flux_apply (E B : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3) :
    flux E B c = 2 * E.trace * vskw B c - 2 * B.trace * vskw E c +
      4 * (vskw E ⨯₃ vskw B) c := by
  simp [flux]

theorem fluxD_apply (E B dE dB : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3) :
    fluxD E B dE dB c = 2 * dE.trace * vskw B c + 2 * E.trace * vskw dB c -
      2 * dB.trace * vskw E c - 2 * B.trace * vskw dE c +
      4 * ((vskw dE ⨯₃ vskw B) c + (vskw E ⨯₃ vskw dB) c) := by
  simp [fluxD]; ring

theorem cd_trace (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j) :
    ContDiff ℝ 1 fun y => (M y).trace := by
  simp only [Matrix.trace, Matrix.diag]
  exact ContDiff.sum fun i _ => hM i i

theorem cd_vskw (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j) (a : Fin 3) :
    ContDiff ℝ 1 fun y => vskw (M y) a := by
  simp only [vskw_apply, invOf_eq_inv]
  exact contDiff_const.mul
    (ContDiff.sum fun b _ => ContDiff.sum fun c _ => contDiff_const.mul (hM b c))

theorem cd_dot {u v : X → Fin 3 → ℝ} (hu : ∀ a, ContDiff ℝ 1 fun y => u y a)
    (hv : ∀ a, ContDiff ℝ 1 fun y => v y a) : ContDiff ℝ 1 fun y => u y ⬝ᵥ v y := by
  simp only [dotProduct]
  exact ContDiff.sum fun a _ => (hu a).mul (hv a)

theorem cd_cross {u v : X → Fin 3 → ℝ} (hu : ∀ a, ContDiff ℝ 1 fun y => u y a)
    (hv : ∀ a, ContDiff ℝ 1 fun y => v y a) (a : Fin 3) :
    ContDiff ℝ 1 fun y => (u y ⨯₃ v y) a := by
  fin_cases a <;> simp only [cross_apply] <;> simp
  · exact ((hu 1).mul (hv 2)).sub ((hu 2).mul (hv 1))
  · exact ((hu 2).mul (hv 0)).sub ((hu 0).mul (hv 2))
  · exact ((hu 0).mul (hv 1)).sub ((hu 1).mul (hv 0))

theorem cd_energyD (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j)
    (hN : ∀ i j, ContDiff ℝ 1 fun y => N y i j) (hP : ∀ i j, ContDiff ℝ 1 fun y => P y i j)
    (hQ : ∀ i j, ContDiff ℝ 1 fun y => Q y i j) :
    ContDiff ℝ 1 fun y => energyD (M y) (N y) (P y) (Q y) := by
  unfold energyD
  exact ((((contDiff_const.mul (cd_trace hM)).mul (cd_trace hP)).add
    (contDiff_const.mul (cd_dot (cd_vskw hM) (cd_vskw hP)))).add
    ((contDiff_const.mul (cd_trace hN)).mul (cd_trace hQ))).add
    (contDiff_const.mul (cd_dot (cd_vskw hN) (cd_vskw hQ)))

theorem cd_energy (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j)
    (hN : ∀ i j, ContDiff ℝ 1 fun y => N y i j) :
    ContDiff ℝ 1 fun y => energy (M y) (N y) := by
  unfold energy
  exact ((((cd_trace hM).pow 2).add (contDiff_const.mul (cd_dot (cd_vskw hM) (cd_vskw hM)))).add
    ((cd_trace hN).pow 2)).add (contDiff_const.mul (cd_dot (cd_vskw hN) (cd_vskw hN)))

theorem cd_flux (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j)
    (hN : ∀ i j, ContDiff ℝ 1 fun y => N y i j) (c : Fin 3) :
    ContDiff ℝ 1 fun y => flux (M y) (N y) c := by
  simp only [flux_apply]
  exact (((contDiff_const.mul (cd_trace hM)).mul (cd_vskw hN c)).sub
    ((contDiff_const.mul (cd_trace hN)).mul (cd_vskw hM c))).add
    (contDiff_const.mul (cd_cross (cd_vskw hM) (cd_vskw hN) c))

theorem cd_fluxD (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j)
    (hN : ∀ i j, ContDiff ℝ 1 fun y => N y i j) (hP : ∀ i j, ContDiff ℝ 1 fun y => P y i j)
    (hQ : ∀ i j, ContDiff ℝ 1 fun y => Q y i j) (c : Fin 3) :
    ContDiff ℝ 1 fun y => fluxD (M y) (N y) (P y) (Q y) c := by
  simp only [fluxD_apply]
  exact (((((contDiff_const.mul (cd_trace hP)).mul (cd_vskw hN c)).add
    ((contDiff_const.mul (cd_trace hM)).mul (cd_vskw hQ c))).sub
    ((contDiff_const.mul (cd_trace hQ)).mul (cd_vskw hM c))).sub
    ((contDiff_const.mul (cd_trace hN)).mul (cd_vskw hP c))).add
    (contDiff_const.mul ((cd_cross (cd_vskw hP) (cd_vskw hN) c).add
      (cd_cross (cd_vskw hM) (cd_vskw hQ) c)))

variable {m n : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {m' n' : Matrix (Fin 3) (Fin 3) ℝ} {s : ℝ}

theorem hd_trace (hm : ∀ i j, HasDerivAt (fun r => m r i j) (m' i j) s) :
    HasDerivAt (fun r => (m r).trace) m'.trace s := by
  simp only [Matrix.trace, Matrix.diag]
  exact HasDerivAt.fun_sum fun i _ => hm i i

theorem hd_vskw (hm : ∀ i j, HasDerivAt (fun r => m r i j) (m' i j) s) (a : Fin 3) :
    HasDerivAt (fun r => vskw (m r) a) (vskw m' a) s := by
  simp only [vskw_apply, invOf_eq_inv]
  exact (HasDerivAt.fun_sum fun b _ => HasDerivAt.fun_sum fun c _ =>
    (hm b c).const_mul _).const_mul _

theorem hd_dot {u v : ℝ → Fin 3 → ℝ} {u' v' : Fin 3 → ℝ}
    (hu : ∀ a, HasDerivAt (fun r => u r a) (u' a) s)
    (hv : ∀ a, HasDerivAt (fun r => v r a) (v' a) s) :
    HasDerivAt (fun r => u r ⬝ᵥ v r) (u' ⬝ᵥ v s + u s ⬝ᵥ v') s := by
  simp only [dotProduct]
  have := HasDerivAt.fun_sum (u := Finset.univ) fun a _ => (hu a).mul (hv a)
  convert this using 1
  rw [← Finset.sum_add_distrib]

theorem hd_cross {u v : ℝ → Fin 3 → ℝ} {u' v' : Fin 3 → ℝ}
    (hu : ∀ a, HasDerivAt (fun r => u r a) (u' a) s)
    (hv : ∀ a, HasDerivAt (fun r => v r a) (v' a) s) (a : Fin 3) :
    HasDerivAt (fun r => (u r ⨯₃ v r) a) ((u' ⨯₃ v s + u s ⨯₃ v') a) s := by
  fin_cases a
  · convert ((hu 1).mul (hv 2)).sub ((hu 2).mul (hv 1)) using 1
    · funext r; simp [cross_apply]
    · simp [cross_apply]; ring
  · convert ((hu 2).mul (hv 0)).sub ((hu 0).mul (hv 2)) using 1
    · funext r; simp [cross_apply]
    · simp [cross_apply]; ring
  · convert ((hu 0).mul (hv 1)).sub ((hu 1).mul (hv 0)) using 1
    · funext r; simp [cross_apply]
    · simp [cross_apply]; ring

theorem hd_energy (hm : ∀ i j, HasDerivAt (fun r => m r i j) (m' i j) s)
    (hn : ∀ i j, HasDerivAt (fun r => n r i j) (n' i j) s) :
    HasDerivAt (fun r => energy (m r) (n r)) (energyD (m s) (n s) m' n') s := by
  have h := ((((hd_trace hm).pow 2).add ((hd_dot (hd_vskw hm) (hd_vskw hm)).const_mul 4)).add
    ((hd_trace hn).pow 2)).add ((hd_dot (hd_vskw hn) (hd_vskw hn)).const_mul 4)
  refine h.congr_deriv ?_
  simp only [energyD, dotProduct_comm (vskw m') (vskw (m s)),
    dotProduct_comm (vskw n') (vskw (n s))]
  push_cast; ring

theorem hd_flux (hm : ∀ i j, HasDerivAt (fun r => m r i j) (m' i j) s)
    (hn : ∀ i j, HasDerivAt (fun r => n r i j) (n' i j) s) (c : Fin 3) :
    HasDerivAt (fun r => flux (m r) (n r) c) (fluxD (m s) (n s) m' n' c) s := by
  have h := ((((hd_trace hm).const_mul 2).mul (hd_vskw hn c)).sub
    (((hd_trace hn).const_mul 2).mul (hd_vskw hm c))).add
    ((hd_cross (hd_vskw hm) (hd_vskw hn) c).const_mul 4)
  convert h using 1
  · funext r; exact flux_apply _ _ c
  · rw [fluxD_apply]; simp only [Pi.add_apply]; ring

end Calculus

section FiniteSpeed


/-- The point `(t, x) ∈ ℝ⁴`. -/
abbrev ev (t : ℝ) (x : Fin 3 → ℝ) : Fin 4 → ℝ := Fin.cons t x

theorem const_of_deriv_pos {f f' : ℝ → ℝ} (hd : ∀ t, HasDerivAt f (f' t) t)
    (h0 : ∀ t, 0 < t → f' t = 0) (t : ℝ) (ht : 0 ≤ t) : f t = f 0 := by
  rcases ht.eq_or_lt with h | h
  · rw [← h]
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope f f' h
    (fun y _ => (hd y).continuousAt.continuousWithinAt) (fun y _ => hd y)
  rw [h0 c hc.1, sub_zero, eq_comm, div_eq_zero_iff] at hc'
  rcases hc' with hc' | hc'
  · linarith
  · linarith

theorem partialDeriv_congr_pos {f g : (Fin 4 → ℝ) → ℝ} (h : ∀ Z : (Fin 4 → ℝ), 0 < Z 0 → f Z = g Z) {Y : (Fin 4 → ℝ)}
    (hY : 0 < Y 0) (μ : Fin 4) : partialDeriv μ f Y = partialDeriv μ g Y := by
  have ho : IsOpen {Z : (Fin 4 → ℝ) | 0 < Z 0} := isOpen_lt continuous_const (continuous_apply 0)
  have he : f =ᶠ[𝓝 Y] g := Filter.eventuallyEq_of_mem (ho.mem_nhds hY) fun Z hZ => h Z hZ
  simp only [partialDeriv, he.fderiv_eq]

/-- Second spacetime jet `∂_μ ∂_ν M` of a matrix field. -/
def jet42 (M : (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (Y : (Fin 4 → ℝ)) : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℝ :=
  fun μ ν => Matrix.of fun i j => partialDeriv μ (partialDeriv ν fun Z => M Z i j) Y

/-- Pointwise TSD: symmetric, trace-free and (row-wise) divergence-free in space. -/
def TSDAt (M : (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (Y : (Fin 4 → ℝ)) : Prop :=
  (M Y)ᵀ = M Y ∧ (M Y).trace = 0 ∧ div (sp (jet4 M Y)) = 0

variable {E B : (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}

theorem partialDeriv_curl (hB : ∀ i j, ContDiff ℝ 2 fun Y => B Y i j) (Y : (Fin 4 → ℝ)) (μ : Fin 4) (i j : Fin 3) :
    partialDeriv μ (fun Z => curl (sp (jet4 B Z)) i j) Y = curl (sp (jet42 B Y μ)) i j := by
  have hd : ∀ c a d, Differentiable ℝ (partialDeriv c fun Z => B Z a d) := fun c a d =>
    differentiable_partialDeriv' (hB a d) c
  simp only [curl, sp, jet4, jet42, Matrix.of_apply]
  rw [partialDeriv_fintype_sum (fun c => (Differentiable.fun_sum fun d _ =>
    ((hd c.succ i d).const_mul (leviCivita3 ℝ j c d))) Y)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [partialDeriv_fintype_sum (fun d => ((hd c.succ i d).const_mul _) Y)]
  exact Finset.sum_congr rfl fun d _ => partialDeriv_const_mul ((hd c.succ i d) Y) _ _

/-- For `C²` solutions of `Ė = -curl B`, `Ḃ = curl E` on `t > 0`, the divergences of `E` and `B`
are constant in time for `t ≥ 0`. -/
theorem div_const_field (hEc : ∀ i j, ContDiff ℝ 2 fun Y => E Y i j)
    (hBc : ∀ i j, ContDiff ℝ 2 fun Y => B Y i j)
    (hEeq : ∀ Y : (Fin 4 → ℝ), 0 < Y 0 → jet4 E Y 0 = -curl (sp (jet4 B Y)))
    (hBeq : ∀ Y : (Fin 4 → ℝ), 0 < Y 0 → jet4 B Y 0 = curl (sp (jet4 E Y)))
    (x : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    div (sp (jet4 E (ev t x))) = div (sp (jet4 E (ev 0 x))) ∧
      div (sp (jet4 B (ev t x))) = div (sp (jet4 B (ev 0 x))) := by
  -- the second jets at `Y` with `Y 0 > 0` satisfy the hypotheses of `div_propagation`
  have prop : ∀ Y : (Fin 4 → ℝ), 0 < Y 0 → div (fun c : Fin 3 => jet42 E Y 0 c.succ) = 0 ∧
      div (fun c : Fin 3 => jet42 B Y 0 c.succ) = 0 := by
    intro Y hY
    refine div_propagation (jet42 E Y) (jet42 B Y) ?_ ?_ ?_ ?_
    · intro μ ν; ext i j; exact partialDeriv_comm (hEc i j) μ ν Y
    · intro μ ν; ext i j; exact partialDeriv_comm (hBc i j) μ ν Y
    · intro c; ext i j
      have h := partialDeriv_congr_pos (f := partialDeriv 0 fun Z => E Z i j)
        (g := fun Z => -curl (sp (jet4 B Z)) i j)
        (fun Z hZ => by
          rw [show partialDeriv 0 (fun Z => E Z i j) Z = jet4 E Z 0 i j from rfl, hEeq Z hZ]; rfl)
        hY c.succ
      simp only [jet42, Matrix.of_apply, Matrix.neg_apply] at h ⊢
      rw [h, partialDeriv_neg, partialDeriv_curl hBc]
    · intro c; ext i j
      have h := partialDeriv_congr_pos (f := partialDeriv 0 fun Z => B Z i j)
        (g := fun Z => curl (sp (jet4 E Z)) i j)
        (fun Z hZ => by rw [show partialDeriv 0 (fun Z => B Z i j) Z = jet4 B Z 0 i j from rfl, hBeq Z hZ])
        hY c.succ
      simp only [jet42, Matrix.of_apply] at h ⊢
      rw [h, partialDeriv_curl hEc]
  have key : ∀ (M : (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ), (∀ i j, ContDiff ℝ 2 fun Y => M Y i j) →
      (∀ Y : (Fin 4 → ℝ), 0 < Y 0 → div (fun c : Fin 3 => jet42 M Y 0 c.succ) = 0) →
      div (sp (jet4 M (ev t x))) = div (sp (jet4 M (ev 0 x))) := by
    intro M hM hP
    ext a
    have hd : ∀ b : Fin 3, Differentiable ℝ (partialDeriv b.succ fun Z => M Z a b) := fun b =>
      differentiable_partialDeriv' (hM a b) _
    have hψ : Differentiable ℝ fun Y => ∑ b : Fin 3, partialDeriv b.succ (fun Z => M Z a b) Y :=
      Differentiable.fun_sum fun b _ => hd b
    have hzero : ∀ s, 0 < s →
        partialDeriv 0 (fun Y => ∑ b : Fin 3, partialDeriv b.succ (fun Z => M Z a b) Y) (ev s x) = 0 := by
      intro s hs
      have := congrFun (hP (ev s x) hs) a
      simp only [div, jet42, Matrix.of_apply, Pi.zero_apply] at this
      rw [partialDeriv_fintype_sum (fun b => hd b _)]
      exact this
    have := const_of_deriv_pos ((fun t => (hψ (ev t x)).hasDerivAt_finCons_left)) hzero t ht
    simpa [div, sp, jet4] using this
  exact ⟨key E hEc fun Y hY => (prop Y hY).1, key B hBc fun Y hY => (prop Y hY).2⟩

theorem partialDeriv_flux (hE1 : ∀ i j, ContDiff ℝ 1 fun Y => E Y i j)
    (hB1 : ∀ i j, ContDiff ℝ 1 fun Y => B Y i j) (Y : (Fin 4 → ℝ)) (μ : Fin 4) (c : Fin 3) :
    partialDeriv μ (fun Y => flux (E Y) (B Y) c) Y =
      fluxD (E Y) (B Y) (jet4 E Y μ) (jet4 B Y μ) c := by
  have h1 := ((cd_flux hE1 hB1 c).differentiable (by norm_num) Y).hasDerivAt_partialDeriv μ
  have h2 := hd_flux (m := fun r => E (Y + r • Pi.single μ 1))
    (n := fun r => B (Y + r • Pi.single μ 1))
    (fun i j => ((hE1 i j).differentiable (by norm_num) Y).hasDerivAt_partialDeriv μ)
    (fun i j => ((hB1 i j).differentiable (by norm_num) Y).hasDerivAt_partialDeriv μ) c
  simp only [zero_smul, add_zero] at h2
  exact h1.unique h2

@[simp] theorem vskw_zero : vskw (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  ext a; simp [vskw_apply, invOf_eq_inv]

theorem energyD_zero_left (dE dB : Matrix (Fin 3) (Fin 3) ℝ) : energyD 0 0 dE dB = 0 := by
  simp [energyD]

theorem fluxD_zero_left (dE dB : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3) :
    fluxD 0 0 dE dB c = 0 := by
  simp [fluxD]

/-- `C²` solutions of `Ė = -curl B`, `Ḃ = curl E` (`t > 0`) with compact spatial support, locally
uniformly in time, and TSD data stay TSD for `t ≥ 0`. [QuennevilleBelair2015], Prop 3.6 (adapted) -/
theorem tsd_propagates (hEc : ∀ i j, ContDiff ℝ 2 fun Y => E Y i j)
    (hBc : ∀ i j, ContDiff ℝ 2 fun Y => B Y i j)
    (hsupp : ∀ s : ℝ, ∃ K : Set (Fin 3 → ℝ), IsCompact K ∧
      ∀ r ∈ Metric.closedBall s 1, ∀ x ∉ K, E (ev r x) = 0 ∧ B (ev r x) = 0)
    (hEeq : ∀ Y : (Fin 4 → ℝ), 0 < Y 0 → jet4 E Y 0 = -curl (sp (jet4 B Y)))
    (hBeq : ∀ Y : (Fin 4 → ℝ), 0 < Y 0 → jet4 B Y 0 = curl (sp (jet4 E Y)))
    (h0 : ∀ x, TSDAt E (ev 0 x) ∧ TSDAt B (ev 0 x)) (t : ℝ) (ht : 0 ≤ t) (x : Fin 3 → ℝ) :
    TSDAt E (ev t x) ∧ TSDAt B (ev t x) := by
  -- compact support of each time slice
  have hsl : ∀ s, ∃ K : Set (Fin 3 → ℝ), IsCompact K ∧
      ∀ y ∉ K, E (ev s y) = 0 ∧ B (ev s y) = 0 := fun s => by
    obtain ⟨K, hK, hsK⟩ := hsupp s
    exact ⟨K, hK, hsK s (Metric.mem_closedBall_self zero_le_one)⟩
  -- regularity
  have hE1 : ∀ i j, ContDiff ℝ 1 fun Y => E Y i j := fun i j => (hEc i j).of_le (by norm_num)
  have hB1 : ∀ i j, ContDiff ℝ 1 fun Y => B Y i j := fun i j => (hBc i j).of_le (by norm_num)
  have hEd : ∀ i j, Differentiable ℝ fun Y => E Y i j := fun i j =>
    (hE1 i j).differentiable (by norm_num)
  have hBd : ∀ i j, Differentiable ℝ fun Y => B Y i j := fun i j =>
    (hB1 i j).differentiable (by norm_num)
  have hEp : ∀ μ i j, ContDiff ℝ 1 fun Y => jet4 E Y μ i j := fun μ i j =>
    (hEc i j).partialDeriv (by norm_num) μ
  have hBp : ∀ μ i j, ContDiff ℝ 1 fun Y => jet4 B Y μ i j := fun μ i j =>
    (hBc i j).partialDeriv (by norm_num) μ
  -- step 1: the divergence constraints
  have hdiv : ∀ s, 0 ≤ s → ∀ y, div (sp (jet4 E (ev s y))) = 0 ∧
      div (sp (jet4 B (ev s y))) = 0 := by
    intro s hs y
    obtain ⟨h1, h2⟩ := div_const_field hEc hBc hEeq hBeq y s hs
    exact ⟨h1.trans (h0 y).1.2.2, h2.trans (h0 y).2.2.2⟩
  -- step 2: the violation energy
  have hΦe : ContDiff ℝ 1 fun Y => energy (E Y) (B Y) := cd_energy hE1 hB1
  have hΦe' : ContDiff ℝ 1 fun Y => energyD (E Y) (B Y) (jet4 E Y 0) (jet4 B Y 0) :=
    cd_energyD hE1 hB1 (hEp 0) (hBp 0)
  have he_cont : ∀ s, Continuous fun y => energy (E (ev s y)) (B (ev s y)) := fun s =>
    hΦe.continuous.comp (contDiff_finCons_right (k := 1) s).continuous
  have he'_cont : ∀ s, Continuous fun y =>
      energyD (E (ev s y)) (B (ev s y)) (jet4 E (ev s y) 0) (jet4 B (ev s y) 0) := fun s =>
    hΦe'.continuous.comp (contDiff_finCons_right (k := 1) s).continuous
  have he_int : ∀ s, Integrable fun y => energy (E (ev s y)) (B (ev s y)) := fun s => by
    obtain ⟨K, hK, hsK⟩ := hsl s
    exact (he_cont s).integrable_of_hasCompactSupport (HasCompactSupport.intro hK fun y hy => by
      simp [(hsK y hy).1, (hsK y hy).2, energy])
  have hfluxD_int : ∀ s c, Integrable fun y => fluxD (E (ev s y)) (B (ev s y))
      (jet4 E (ev s y) c.succ) (jet4 B (ev s y) c.succ) c := fun s c => by
    obtain ⟨K, hK, hsK⟩ := hsl s
    exact ((cd_fluxD hE1 hB1 (hEp c.succ) (hBp c.succ) c).continuous.comp
      (contDiff_finCons_right (k := 1) s).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK fun y hy => by
        simp only [Function.comp_apply]
        rw [(hsK y hy).1, (hsK y hy).2, fluxD_zero_left])
  -- the spatial integrals of the flux divergence vanish
  have hflux : ∀ s c, ∫ y, fluxD (E (ev s y)) (B (ev s y)) (jet4 E (ev s y) c.succ)
      (jet4 B (ev s y) c.succ) c = 0 := by
    intro s c
    obtain ⟨K, hK, hsK⟩ := hsl s
    have hΦ : Differentiable ℝ fun Y => flux (E Y) (B Y) c :=
      (cd_flux hE1 hB1 c).differentiable (by norm_num)
    have hg : Differentiable ℝ fun y => flux (E (ev s y)) (B (ev s y)) c :=
      hΦ.comp ((contDiff_finCons_right (k := 1) s).differentiable (by norm_num))
    have hg' : (fun y => fderiv ℝ (fun y => flux (E (ev s y)) (B (ev s y)) c) y
        (Pi.single c 1)) = fun y => fluxD (E (ev s y)) (B (ev s y)) (jet4 E (ev s y) c.succ)
          (jet4 B (ev s y) c.succ) c := by
      funext y
      show partialDeriv c (fun y => flux (E (ev s y)) (B (ev s y)) c) y = _
      rw [partialDeriv_comp_finCons (hΦ _) c, partialDeriv_flux hE1 hB1]
    have hgint : Integrable fun y => flux (E (ev s y)) (B (ev s y)) c :=
      ((cd_flux hE1 hB1 c).continuous.comp
        (contDiff_finCons_right (k := 1) s).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hK fun y hy => by
          simp only [Function.comp_apply]
          simp [(hsK y hy).1, (hsK y hy).2, flux])
    have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun _ : Fin 3 → ℝ => (1 : ℝ)) (g := fun y => flux (E (ev s y)) (B (ev s y)) c)
      (v := Pi.single c 1) (by simp) (by simpa [hg'] using hfluxD_int s c) (by simpa using hgint)
      (fun _ _ => differentiableAt_const _) (fun y _ => hg y)
    simpa [hg'] using ibp
  -- differentiation under the integral sign
  have hI : ∀ s, HasDerivAt (fun r => ∫ y, energy (E (ev r y)) (B (ev r y)))
      (∫ y, energyD (E (ev s y)) (B (ev s y)) (jet4 E (ev s y) 0) (jet4 B (ev s y) 0)) s := by
    intro s
    obtain ⟨K, hK, hsK⟩ := hsupp s
    have hzero' : ∀ r ∈ Metric.ball s 1, ∀ y ∉ K,
        energyD (E (ev r y)) (B (ev r y)) (jet4 E (ev r y) 0) (jet4 B (ev r y) 0) = 0 := by
      intro r hr y hy
      have h := hsK r (Metric.ball_subset_closedBall hr) y hy
      rw [h.1, h.2, energyD_zero_left]
    set S := (fun p : ℝ × (Fin 3 → ℝ) => ev p.1 p.2) '' (Metric.closedBall s 1 ×ˢ K)
    have hS : IsCompact S := ((isCompact_closedBall s 1).prod hK).image continuous_finCons
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hΦe'.continuous.continuousOn
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := K.indicator fun _ => C)
      (F := fun r y => energy (E (ev r y)) (B (ev r y)))
      (F' := fun r y => energyD (E (ev r y)) (B (ev r y)) (jet4 E (ev r y) 0) (jet4 B (ev r y) 0))
      (Metric.ball_mem_nhds s one_pos)
      (Eventually.of_forall fun r => (he_cont r).aestronglyMeasurable) (he_int s)
      (he'_cont s).aestronglyMeasurable ?_ ?_ ?_).2
    · refine Eventually.of_forall fun y r hr => ?_
      by_cases hy : y ∈ K
      · rw [indicator_of_mem hy]
        exact hC (ev r y) ⟨(r, y), ⟨Metric.ball_subset_closedBall hr, hy⟩, rfl⟩
      · rw [hzero' r hr y hy, indicator_of_notMem hy, norm_zero]
    · exact (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
    · exact Eventually.of_forall fun y r _ =>
        hd_energy (m := fun r => E (ev r y)) (n := fun r => B (ev r y))
          (fun i j => ((hEd i j) (ev r y)).hasDerivAt_finCons_left)
          (fun i j => ((hBd i j) (ev r y)).hasDerivAt_finCons_left)
  -- the energy integral is constant for `t ≥ 0`
  have hI0 : ∀ s, 0 < s → ∫ y, energyD (E (ev s y)) (B (ev s y)) (jet4 E (ev s y) 0)
      (jet4 B (ev s y) 0) = 0 := by
    intro s hs
    have pw : ∀ y, energyD (E (ev s y)) (B (ev s y)) (jet4 E (ev s y) 0) (jet4 B (ev s y) 0) =
        2 * ∑ c, fluxD (E (ev s y)) (B (ev s y)) (jet4 E (ev s y) c.succ)
          (jet4 B (ev s y) c.succ) c := by
      intro y
      have := energy_flux (E (ev s y)) (B (ev s y)) (jet4 E (ev s y)) (jet4 B (ev s y))
        (hEeq _ hs) (hBeq _ hs) (hdiv s hs.le y).1 (hdiv s hs.le y).2
      linarith
    simp only [pw]
    rw [integral_const_mul, integral_finsetSum _ fun c _ => hfluxD_int s c]
    simp [hflux]
  have hconst := const_of_deriv_pos hI hI0 t ht
  have hinit : ∫ y, energy (E (ev 0 y)) (B (ev 0 y)) = 0 := by
    have : (fun y => energy (E (ev 0 y)) (B (ev 0 y))) = fun _ => 0 := by
      funext y
      exact (energy_eq_zero_iff _ _).2 ⟨⟨(h0 y).1.1, (h0 y).1.2.1⟩, ⟨(h0 y).2.1, (h0 y).2.2.1⟩⟩
    simp [this]
  rw [hinit] at hconst
  have hae := (integral_eq_zero_iff_of_nonneg (fun y => energy_nonneg _ _) (he_int t)).1 hconst
  have heq := (Continuous.ae_eq_iff_eq volume (he_cont t) continuous_const).1 hae
  have hx := (energy_eq_zero_iff _ _).1 (congrFun heq x)
  exact ⟨⟨hx.1.1, hx.1.2, (hdiv t ht x).1⟩, ⟨hx.2.1, hx.2.2, (hdiv t ht x).2⟩⟩

/-! ### Non-vacuity of the hypotheses of Prop 3.6 -/

open scoped ContDiff

/-- A fixed smooth bump function on `ℝ³` (equal to `1` near `0`). -/
noncomputable def bump3 : ContDiffBump (0 : Fin 3 → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The static field `E(t, x) = ∇²φ(x)` built from `φ = bump3`. -/
noncomputable def hessField (Y : (Fin 4 → ℝ)) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b => partialDeriv a (partialDeriv b bump3) (spatialProj ℝ 3 Y)

theorem contDiff_hess (a b : Fin 3) : ContDiff ℝ ∞ (partialDeriv a (partialDeriv b bump3)) :=
  ((((bump3.contDiff (n := ⊤))).partialDeriv (m := ∞) (by simp) b).partialDeriv (m := ∞)
    (by simp) a)

/-- Some nonzero `C²` fields with compact spatial support solve `Ė = -curl B`, `Ḃ = curl E`. -/
theorem propagation_hyps_nonvacuous :
    ∃ E B : (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, ContDiff ℝ 2 fun Y => E Y i j) ∧ (∀ i j, ContDiff ℝ 2 fun Y => B Y i j) ∧
      (∀ s : ℝ, ∃ K : Set (Fin 3 → ℝ), IsCompact K ∧
        ∀ r ∈ Metric.closedBall s 1, ∀ x ∉ K, E (ev r x) = 0 ∧ B (ev r x) = 0) ∧
      (∀ Y : (Fin 4 → ℝ), 0 < Y 0 → jet4 E Y 0 = -curl (sp (jet4 B Y))) ∧
      (∀ Y : (Fin 4 → ℝ), 0 < Y 0 → jet4 B Y 0 = curl (sp (jet4 E Y))) ∧
      ∃ x, E (ev 0 x) ≠ 0 := by
  have hd : ∀ a b, Differentiable ℝ (partialDeriv a (partialDeriv b bump3)) := fun a b =>
    (contDiff_hess a b).differentiable (by simp)
  have hB : ∀ Y, jet4 (fun _ : (Fin 4 → ℝ) => (0 : Matrix (Fin 3) (Fin 3) ℝ)) Y = 0 := by
    intro Y; funext μ; ext i j; simp [jet4, partialDeriv]
  refine ⟨hessField, fun _ => 0, fun i j => ?_, fun _ _ => contDiff_const, fun s => ?_,
    fun Y _ => ?_, fun Y _ => ?_, ?_⟩
  · exact ((contDiff_hess i j).of_le (by simp)).comp (spatialProj ℝ 3).contDiff
  · refine ⟨tsupport bump3, bump3.hasCompactSupport.isCompact, fun r _ x hx => ⟨?_, rfl⟩⟩
    ext a b
    simp only [hessField, spatialProj_finCons, Matrix.of_apply, Matrix.zero_apply]
    exact image_eq_zero_of_notMem_tsupport fun h =>
      hx (tsupport_partialDeriv_subset _ b (tsupport_partialDeriv_subset _ a h))
  · rw [hB]; ext a b
    have := partialDeriv_zero_comp_spatialProj (f := partialDeriv a (partialDeriv b bump3))
      ((hd a b) (spatialProj ℝ 3 Y))
    simp only [jet4, hessField, Matrix.of_apply]
    rw [this]; simp [sp, curl]
  · rw [hB]; ext a b
    simp only [Pi.zero_apply, Matrix.zero_apply, curl, sp, jet4, hessField, Matrix.of_apply]
    have hsucc : ∀ c d, partialDeriv c.succ
        (fun Y => partialDeriv a (partialDeriv d bump3) (spatialProj ℝ 3 Y)) Y =
        partialDeriv c (partialDeriv a (partialDeriv d bump3)) (spatialProj ℝ 3 Y) := fun c d =>
      partialDeriv_succ_comp_spatialProj ((hd _ _) _) c
    simp only [hsucc]
    set x := spatialProj ℝ 3 Y
    have hc : ∀ c d, partialDeriv c (partialDeriv a (partialDeriv d bump3)) x = partialDeriv a (partialDeriv c (partialDeriv d bump3)) x := fun c d =>
      partialDeriv_comm ((((bump3.contDiff (n := ⊤)).partialDeriv (m := ∞) (by simp) d)).of_le (by simp)) c a x
    have hs : ∀ c d, partialDeriv c (partialDeriv d bump3) = partialDeriv d (partialDeriv c bump3) := fun c d =>
      funext (partialDeriv_comm (bump3.contDiff (n := 2)) c d)
    simp only [hc]
    fin_cases b <;>
      simp [leviCivita3_apply, Fin.sum_univ_three, hs 1 0, hs 2 0, hs 2 1]
  · by_contra! h
    have hφ : ∀ b x, partialDeriv b bump3 x = 0 := by
      intro b
      refine eq_zero_of_partialDeriv_eq_zero ((((bump3.contDiff (n := ⊤)).partialDeriv (m := ∞) (by simp) b)).differentiable (by simp))
        ?_ fun a x => ?_
      · exact bump3.hasCompactSupport.mono'
          ((subset_tsupport _).trans (tsupport_partialDeriv_subset _ b))
      · simpa [hessField] using congrFun (congrFun (h x) a) b
    have := eq_zero_of_partialDeriv_eq_zero ((bump3.contDiff (n := 1)).differentiable one_ne_zero)
      bump3.hasCompactSupport hφ 0
    rw [bump3.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)] at this
    exact one_ne_zero this

end FiniteSpeed

end Feec.EinsteinBianchi
