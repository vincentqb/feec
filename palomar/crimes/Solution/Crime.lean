module

public import Solution.Dynamic

/-!
# The bridge for variational crimes

A family of discrete differential spaces of the challenge on the window `[a, a + m)`
(`HilbertComplex.CrimeFamily`) is a `Feec.HilbertComplex.ApproxComplexCrime.Family` of the window
`H.toFeec.window a m` (`CrimeFamily.toFeec`, the same fields, with the real structure of `Xₕ`
restricted from `𝕜`). The mixed problems of the challenge are those of `Feec`: the mixed Hodge
Laplacian of the window is the mixed problem of the total complex
(`isTotalMixedSolution_iff`), the discrete one that of `(Xₕ, 𝐝ₕ)` with the load `iₕ* f`
(`CrimeFamily.isMixedSolution_iff`), and the read errors agree (`CrimeFamily.readError_eq`). The
residual of the challenge bounds `Feec`'s residual functional (`CrimeFamily.norm_staticResidual_le`).
This module turns `Feec.HilbertComplex.ApproxComplexCrime.Family.staticFEEC`, the cochain case of
`Feec.HilbertComplex.Approximation.StaticCochain` and
`Feec.HilbertComplex.ApproxComplexCrime.HeatFamily.heatFEEC` into the verdict of the challenge
(`CrimeFamily.verdict`).

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012], §3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

universe u

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex

variable (H : HilbertComplex 𝕜 W) (a : ℤ) (m : ℕ)

/-- The window of `H` as a `Feec` Hilbert complex. -/
abbrev win : Feec.HilbertComplex 𝕜 (ComplexShape.window m) (fun i : Fin m => W (a + (i : ℕ))) :=
  H.toFeec.window a m

theorem totalD_apply_eq (y : (H.totalD a m).domain) : H.totalD a m y = (H.win a m).totalD y :=
  LinearPMap.apply_eq_of_eq (H.totalD_eq a m) _ _ rfl

theorem totalHarmonic_eq : H.totalHarmonic a m = (H.win a m).total.harmonic () := by
  rw [Feec.HilbertComplex.harmonic_eq_cycles_inf_dual]
  unfold totalHarmonic
  rw [H.totalD_eq a m]
  rfl

/-- A point of `D(𝐝)` as a point of the domain space of the total complex. -/
def toDomT (y : (H.totalD a m).domain) : (H.win a m).total.domainSpace () :=
  (H.win a m).totalD.toGraphSpace y

/-- The coordinate in `D(𝐝)` of a point of the domain space of the total complex. -/
def coordT (y : (H.win a m).total.domainSpace ()) : (H.totalD a m).domain :=
  (H.win a m).total.domainCoord () () y

@[simp] theorem coordT_toDomT (y : (H.totalD a m).domain) : H.coordT a m (H.toDomT a m y) = y :=
  rfl

theorem coe_coordT (y : (H.win a m).total.domainSpace ()) :
    (H.coordT a m y : Total W a m) = (H.win a m).total.domainIncl () y :=
  rfl

theorem totalD_coordT (y : (H.win a m).total.domainSpace ()) :
    H.totalD a m (H.coordT a m y) = (H.win a m).total.d () () ((H.win a m).total.domainCoord () () y) :=
  H.totalD_apply_eq a m _

theorem toDomT_coordT (y : (H.win a m).total.domainSpace ()) : H.toDomT a m (H.coordT a m y) = y :=
  (H.win a m).total.domainIncl_injective () rfl

/-- **The mixed Hodge Laplacian of the window is the mixed problem of the total complex.** -/
theorem isTotalMixedSolution_iff {f : Total W a m} {σ u : (H.win a m).total.domainSpace ()}
    {p : (H.win a m).total.harmonic ()} :
    H.IsTotalMixedSolution a m f (H.coordT a m σ) (H.coordT a m u) p ↔
      (H.win a m).total.IsMixedSolution () () () f σ u p := by
  constructor
  · intro hs
    refine ⟨fun τ => ?_, fun v => ?_, fun q hq => ?_⟩
    · have := hs.fst (H.coordT a m τ)
      simp only [totalD_coordT] at this
      exact this
    · have := hs.snd (H.coordT a m v)
      simp only [totalD_coordT] at this
      exact this
    · exact hs.harm q ((H.totalHarmonic_eq a m).symm ▸ hq)
  · intro hs
    refine ⟨(H.totalHarmonic_eq a m).symm ▸ p.2, fun τ => ?_, fun v => ?_, fun q hq => ?_⟩
    · have := hs.fst (H.toDomT a m τ)
      simp only [← totalD_coordT, coordT_toDomT] at this
      exact this
    · have := hs.snd (H.toDomT a m v)
      simp only [← totalD_coordT, coordT_toDomT] at this
      exact this
    · exact hs.harm q ((H.totalHarmonic_eq a m) ▸ hq)

/-- Closed ranges of `H` in the degrees `a + 1, …, a + m - 1` give closed ranges of the total
complex of the window. -/
theorem closedRangeAt_win
    (hcr : ∀ i : Fin m, 0 < (i : ℕ) → IsClosed (H.boundaries (a + (i : ℕ)) : Set (W (a + (i : ℕ)))))
    (i : Fin m) : (H.win a m).ClosedRangeAt i :=
  H.closedRangeAt_window a m hcr i

/-- The mixed solution of the window with data `f` (closed ranges). -/
abbrev totalSol (hcr : ∀ i, (H.win a m).ClosedRangeAt i) (f : Total W a m) :
    (H.win a m).total.MixedSpace () () :=
  (H.win a m).totalMixedSolution hcr f

theorem isTotalMixedSolution_totalSol (hcr : ∀ i, (H.win a m).ClosedRangeAt i)
    (f : Total W a m) :
    H.IsTotalMixedSolution a m f (H.coordT a m (H.totalSol a m hcr f).fst)
      (H.coordT a m (H.totalSol a m hcr f).snd.fst) (H.totalSol a m hcr f).snd.snd :=
  (H.isTotalMixedSolution_iff a m).2 ((H.win a m).isMixedSolution_totalMixedSolution hcr f)

/-- **Uniqueness for the mixed Hodge Laplacian of the window**: every solution is `Feec`'s. -/
theorem eq_totalSol (hcr : ∀ i, (H.win a m).ClosedRangeAt i) {f : Total W a m}
    {σ u : (H.totalD a m).domain} {p : Total W a m} (hs : H.IsTotalMixedSolution a m f σ u p) :
    σ = H.coordT a m (H.totalSol a m hcr f).fst ∧
      u = H.coordT a m (H.totalSol a m hcr f).snd.fst ∧ p = (H.totalSol a m hcr f).snd.snd := by
  have hp : p ∈ (H.win a m).total.harmonic () := (H.totalHarmonic_eq a m) ▸ hs.mem
  have hs' : (H.win a m).total.IsMixedSolution () () () f (H.toDomT a m σ) (H.toDomT a m u)
      ⟨p, hp⟩ := (H.isTotalMixedSolution_iff a m).1 hs
  have e := (H.win a m).total.mixedSolution_eq (Feec.HilbertComplex.loop_rel () ())
    (Feec.HilbertComplex.loop_rel () ()) ((H.win a m).closedRangeAt_total hcr ())
    ((H.win a m).closedRangeAt_total hcr ()) hs'
  rw [show H.totalSol a m hcr f = _ from e]
  exact ⟨rfl, rfl, rfl⟩

namespace CrimeFamily

variable {H a m} {κ : Type*} (S : HilbertComplex.CrimeFamily.{u} H a m κ)

/-- The real structure of `Xₕ`, restricted from `𝕜`. -/
abbrev normedSpaceReal (h : κ) : NormedSpace ℝ (S.X h) := NormedSpace.restrictScalars ℝ 𝕜 (S.X h)

theorem isScalarTower (h : κ) :
    letI := S.normedSpaceReal h
    IsScalarTower ℝ 𝕜 (S.X h) := by
  let := S.normedSpaceReal h
  exact ⟨fun r c x => by
    change (r • c) • x = (algebraMap ℝ 𝕜 r) • (c • x)
    rw [Algebra.smul_def, mul_smul]⟩

/-- **The family as a `Feec` family of discrete differential spaces** of the window (the same
fields). -/
def toFeec : Feec.HilbertComplex.ApproxComplexCrime.Family.{u} (H.win a m) κ where
  X := S.X
  normedSpaceReal := S.normedSpaceReal
  isScalarTower := S.isScalarTower
  D := S.D
  D_D := S.D_D
  incl := S.incl
  proj := S.proj
  proj_incl := S.proj_incl
  bound := S.bound

/-- `v ∈ Xₕ` in the domain space of `(Xₕ, 𝐝ₕ)`. -/
abbrev toD (h : κ) (v : S.X h) : (S.toFeec.cpx h).domainSpace () :=
  Feec.HilbertComplex.toDom (S.D h) (S.D_D h) v

/-- The point of `Xₕ` of a point of the domain space of `(Xₕ, 𝐝ₕ)`. -/
abbrev inclD (h : κ) (v : (S.toFeec.cpx h).domainSpace ()) : S.X h :=
  (S.toFeec.cpx h).domainIncl () v

theorem toD_inclD (h : κ) (v : (S.toFeec.cpx h).domainSpace ()) : S.toD h (S.inclD h v) = v :=
  (S.toFeec.cpx h).domainIncl_injective () rfl

theorem mem_harmonic_iff (h : κ) {q : S.toFeec.X h} :
    q ∈ S.harmonic h ↔ q ∈ (S.toFeec.cpx h).harmonic () :=
  (Feec.HilbertComplex.mem_diffComplex_harmonic (S.D h) (S.D_D h)).symm

/-- **The discrete mixed problem is that of `Feec`** with the load `iₕ* f`. -/
theorem isMixedSolution_iff (h : κ) {f : Total W a m} {σ u p : S.X h}
    (hp : p ∈ (S.toFeec.cpx h).harmonic ()) :
    S.IsMixedSolution h f σ u p ↔ (S.toFeec.cpx h).IsMixedSolution () () ()
      ((S.incl h).adjoint f) (S.toD h σ) (S.toD h u) ⟨p, hp⟩ := by
  constructor
  · rintro ⟨-, hr⟩
    refine ⟨fun τ => ?_, fun v => ?_, fun q hq => ?_⟩
    · have := hr (S.inclD h τ) 0 0 (Submodule.zero_mem _)
      simp only [residual₀, _root_.map_zero, inner_zero_left, add_zero, sub_zero] at this
      exact this
    · have := hr 0 (S.inclD h v) 0 (Submodule.zero_mem _)
      simp only [residual₀, _root_.map_zero, inner_zero_left, zero_add, sub_zero] at this
      change _ = ⟪S.inclD h v, (S.incl h).adjoint f⟫_𝕜
      rw [ContinuousLinearMap.adjoint_inner_right]
      exact sub_eq_zero.1 this
    · have := hr 0 0 q ((S.mem_harmonic_iff h).2 hq)
      simp only [residual₀, _root_.map_zero, inner_zero_left, add_zero,
        zero_sub, sub_zero, neg_eq_zero] at this
      exact this
  · intro hs
    refine ⟨(S.mem_harmonic_iff h).2 hp, fun τ v q hq => ?_⟩
    have h1 := hs.fst (S.toD h τ)
    have h2 := hs.snd (S.toD h v)
    have h3 := hs.harm q ((S.mem_harmonic_iff h).1 hq)
    change ⟪τ, σ⟫_𝕜 - ⟪S.D h τ, u⟫_𝕜 = 0 at h1
    change ⟪v, S.D h σ⟫_𝕜 + ⟪S.D h v, S.D h u⟫_𝕜 + ⟪v, p⟫_𝕜 = ⟪v, (S.incl h).adjoint f⟫_𝕜 at h2
    change ⟪q, u⟫_𝕜 = 0 at h3
    rw [ContinuousLinearMap.adjoint_inner_right] at h2
    unfold residual₀
    linear_combination h1 + h2 - h3

/-- **Uniqueness for the discrete mixed problem**: every solution is `Feec`'s. -/
theorem eq_mixedSol {h : κ} {f : Total W a m} {σ u p : S.X h}
    (hs : S.IsMixedSolution h f σ u p) :
    σ = S.inclD h (S.toFeec.mixedSol h f).fst ∧ u = S.inclD h (S.toFeec.mixedSol h f).snd.fst ∧
      p = ((S.toFeec.mixedSol h f).snd.snd : S.toFeec.X h) := by
  have hp := (S.mem_harmonic_iff h).1 hs.1
  have e := (S.toFeec.cpx h).mixedSolution_eq (Feec.HilbertComplex.loop_rel () ())
    (Feec.HilbertComplex.loop_rel () ()) (Feec.HilbertComplex.closedRangeAt_diffComplex _ _ ())
    (Feec.HilbertComplex.closedRangeAt_diffComplex _ _ ()) ((S.isMixedSolution_iff h hp).1 hs)
  change S.toFeec.mixedSol h f = _ at e
  rw [e]
  exact ⟨rfl, rfl, rfl⟩

theorem isMixedSolution_mixedSol (h : κ) (f : Total W a m) :
    S.IsMixedSolution h f (S.inclD h (S.toFeec.mixedSol h f).fst)
      (S.inclD h (S.toFeec.mixedSol h f).snd.fst)
      ((S.toFeec.mixedSol h f).snd.snd : S.toFeec.X h) := by
  have hs := S.toFeec.isMixedSolution_mixedSol h f
  refine (S.isMixedSolution_iff h (S.toFeec.mixedSol h f).snd.snd.2).2 ?_
  rwa [S.toD_inclD, S.toD_inclD]

/-- **The read errors are `Feec`'s.** -/
theorem readError_eq (h : κ) (X : (H.win a m).total.MixedSpace () ())
    (x : (S.toFeec.cpx h).MixedSpace () ()) :
    S.toFeec.readError h X x = S.readError₀ h (H.coordT a m X.fst) (H.coordT a m X.snd.fst)
      X.snd.snd (S.inclD h x.fst) (S.inclD h x.snd.fst) (x.snd.snd : S.toFeec.X h) := by
  unfold Feec.HilbertComplex.ApproxComplexCrime.Family.readError readError₀
  rw [H.totalD_coordT a m, H.totalD_coordT a m]
  rfl

/-- **The read error of the solutions is `Feec`'s static error.** -/
theorem readError_sol_eq (hcr : ∀ i, (H.win a m).ClosedRangeAt i) {h : κ} {f : Total W a m}
    {σ u : (H.totalD a m).domain} {p : Total W a m} (hs : H.IsTotalMixedSolution a m f σ u p)
    {σh uh ph : S.X h} (hsh : S.IsMixedSolution h f σh uh ph) :
    S.readError₀ h σ u p σh uh ph = S.toFeec.staticError hcr h f := by
  obtain ⟨rfl, rfl, rfl⟩ := H.eq_totalSol a m hcr hs
  obtain ⟨rfl, rfl, rfl⟩ := S.eq_mixedSol hsh
  exact (S.readError_eq h _ _).symm

/-- **The residual functional of `Feec`** at a test point is the residual of the challenge. -/
theorem staticResidual_apply (h : κ) (f : Total W a m) (x y : (S.toFeec.cpx h).MixedSpace () ()) :
    S.toFeec.staticResidual h f x y = S.residual₀ h f (S.inclD h x.fst) (S.inclD h x.snd.fst)
      (x.snd.snd : S.toFeec.X h) (S.inclD h y.fst) (S.inclD h y.snd.fst)
      (y.snd.snd : S.toFeec.X h) := by
  rw [Feec.HilbertComplex.ApproxComplexCrime.Family.staticResidual, _root_.sub_apply,
    Feec.HilbertComplex.mixedForm_apply, Feec.HilbertComplex.mixedRHS_apply,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- The five component norms of a point of the discrete mixed space sum to at most `3 ‖y‖`. -/
theorem sum_norm_le (h : κ) (y : (S.toFeec.cpx h).MixedSpace () ()) :
    ‖S.inclD h y.fst‖ + ‖S.D h (S.inclD h y.fst)‖ + ‖S.inclD h y.snd.fst‖ +
      ‖S.D h (S.inclD h y.snd.fst)‖ + ‖(y.snd.snd : S.toFeec.X h)‖ ≤ 3 * ‖y‖ := by
  have e := Feec.HilbertComplex.MixedSpace.norm_sq y
  have e1 := (S.toFeec.cpx h).norm_sq_domainSpace () y.fst
  have e2 := (S.toFeec.cpx h).norm_sq_domainSpace () y.snd.fst
  change ‖y.fst‖ ^ 2 = ‖S.inclD h y.fst‖ ^ 2 + ‖S.D h (S.inclD h y.fst)‖ ^ 2 at e1
  change ‖y.snd.fst‖ ^ 2 = ‖S.inclD h y.snd.fst‖ ^ 2 + ‖S.D h (S.inclD h y.snd.fst)‖ ^ 2 at e2
  set A := ‖S.inclD h y.fst‖
  set B := ‖S.D h (S.inclD h y.fst)‖
  set C := ‖S.inclD h y.snd.fst‖
  set D := ‖S.D h (S.inclD h y.snd.fst)‖
  set E := ‖(y.snd.snd : S.toFeec.X h)‖
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have hC : 0 ≤ C := norm_nonneg _
  have hD : 0 ≤ D := norm_nonneg _
  have hE : 0 ≤ E := norm_nonneg _
  have hy := norm_nonneg y
  have key : (A + B + C + D + E) ^ 2 ≤ (3 * ‖y‖) ^ 2 := by
    nlinarith [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (A - D), sq_nonneg (A - E),
      sq_nonneg (B - C), sq_nonneg (B - D), sq_nonneg (B - E), sq_nonneg (C - D),
      sq_nonneg (C - E), sq_nonneg (D - E)]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 key

/-- **The residual of the challenge bounds `Feec`'s residual functional**: `‖B x - F‖ ≤ 3 ε`. -/
theorem norm_staticResidual_le (h : κ) (f : Total W a m) (x : (S.toFeec.cpx h).MixedSpace () ())
    {ε : ℝ} (hε : 0 ≤ ε) (hres : ∀ τ v q, q ∈ S.harmonic h →
      ‖S.residual₀ h f (S.inclD h x.fst) (S.inclD h x.snd.fst) (x.snd.snd : S.toFeec.X h) τ v q‖ ≤
        ε * (‖τ‖ + ‖S.D h τ‖ + ‖v‖ + ‖S.D h v‖ + ‖q‖)) :
    ‖S.toFeec.staticResidual h f x‖ ≤ 3 * ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  rw [S.staticResidual_apply]
  refine (hres _ _ _ ((S.mem_harmonic_iff h).2 y.snd.snd.2)).trans ?_
  exact (mul_le_mul_of_nonneg_left (S.sum_norm_le h y) hε).trans_eq (by ring)

/-- **The static verdict with crimes**, constant `240 C c_P²` (`c_P ≥ 1`, `C` the bound of the
reading maps), from `Feec.HilbertComplex.ApproxComplexCrime.Family.staticFEEC`. -/
theorem staticVerdict
    (hcr : ∀ i : Fin m, 0 < (i : ℕ) → IsClosed (H.boundaries (a + (i : ℕ)) : Set (W (a + (i : ℕ)))))
    {cP : ℝ} (hP : S.IsPoincare cP) : ∃ C, S.StaticVerdict₀ C := by
  have hcr' := H.closedRangeAt_win a m hcr
  have hcP : 1 ≤ max cP 1 := le_max_right _ _
  have hP' : S.toFeec.IsPoincare (max cP 1) := fun h v hv =>
    (hP h v hv).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have V := S.toFeec.staticFEEC hcr' S.l hcP hP'
  have hC₀ := S.toFeec.boundConst_nonneg
  refine ⟨240 * S.toFeec.boundConst * max cP 1 ^ 2,
    { existsUnique := fun f => ⟨(H.coordT a m (H.totalSol a m hcr' f).fst,
        H.coordT a m (H.totalSol a m hcr' f).snd.fst, (H.totalSol a m hcr' f).snd.snd),
        H.isTotalMixedSolution_totalSol a m hcr' f, fun x hx => ?_⟩
      existsUnique_discrete := fun h f => ⟨(S.inclD h (S.toFeec.mixedSol h f).fst,
        S.inclD h (S.toFeec.mixedSol h f).snd.fst,
        ((S.toFeec.mixedSol h f).snd.snd : S.toFeec.X h)), S.isMixedSolution_mixedSol h f,
        fun x hx => ?_⟩
      stable := fun h {f σ u p} hs => ?_
      strang := fun h {f σ u p} hs {σh uh ph} hsh σ' u' p' hp' {ε} hε hres => ?_
      converges := fun {D} hD hc {f σ u p} hs {σh uh ph} hsh => ?_ }⟩
  · obtain ⟨h1, h2, h3⟩ := H.eq_totalSol a m hcr' hx
    exact Prod.ext h1 (Prod.ext h2 h3)
  · obtain ⟨h1, h2, h3⟩ := S.eq_mixedSol hx
    exact Prod.ext h1 (Prod.ext h2 h3)
  · obtain ⟨rfl, rfl, rfl⟩ := S.eq_mixedSol hs
    have h1 := V.stable h f
    have hf := norm_nonneg f
    have hcP2 : 0 ≤ max cP 1 ^ 2 := sq_nonneg _
    refine (S.sum_norm_le h (S.toFeec.mixedSol h f)).trans ?_
    nlinarith [mul_nonneg (mul_nonneg hC₀ hcP2) hf]
  · rw [S.readError_sol_eq hcr' hs hsh]
    obtain ⟨rfl, rfl, rfl⟩ := H.eq_totalSol a m hcr' hs
    set x := Feec.HilbertComplex.MixedSpace.mk (S.toD h σ') (S.toD h u')
      ⟨p', (S.mem_harmonic_iff h).1 hp'⟩
    have h1 := V.strang h f x
    have h2 := S.norm_staticResidual_le h f x hε hres
    have e : S.toFeec.readError h (H.totalSol a m hcr' f) x = S.readError₀ h
        (H.coordT a m (H.totalSol a m hcr' f).fst) (H.coordT a m (H.totalSol a m hcr' f).snd.fst)
        (H.totalSol a m hcr' f).snd.snd σ' u' p' := S.readError_eq h _ x
    rw [e] at h1
    have hcP2 : 0 ≤ max cP 1 ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hC₀ hcP2]
  · have hc' : ∀ g ∈ D, S.toFeec.StaticConsistent hcr' S.l g := fun g hg ε hε => by
      have hev := hc g hg (H.coordT a m (H.totalSol a m hcr' g).fst)
        (H.coordT a m (H.totalSol a m hcr' g).snd.fst) (H.totalSol a m hcr' g).snd.snd
        (H.isTotalMixedSolution_totalSol a m hcr' g) (ε / 3) (by positivity)
      filter_upwards [hev] with h hh
      obtain ⟨σ', u', p', hp', h1, h2⟩ := hh
      set x : (S.toFeec.cpx h).MixedSpace () () := Feec.HilbertComplex.MixedSpace.mk
        (S.toD h σ') (S.toD h u') ⟨p', (S.mem_harmonic_iff h).1 hp'⟩
      refine ⟨x, ?_, ?_⟩
      · have e : S.toFeec.readError h (H.totalSol a m hcr' g) x = S.readError₀ h
            (H.coordT a m (H.totalSol a m hcr' g).fst)
            (H.coordT a m (H.totalSol a m hcr' g).snd.fst) (H.totalSol a m hcr' g).snd.snd
            σ' u' p' := S.readError_eq h _ x
        rw [e]
        linarith
      · have := S.norm_staticResidual_le h g x (by positivity) h2
        linarith
    exact (V.converges hD hc' f).congr fun h => (S.readError_sol_eq hcr' hs (hsh h)).symm

theorem J_eq (h : κ) : S.toFeec.J h = (S.incl h).adjoint ∘L S.incl h := rfl

/-- The cochain property is `Feec`'s. -/
theorem IsCochain.toFeec {S : HilbertComplex.CrimeFamily.{u} H a m κ} (hi : S.IsCochain) :
    S.toFeec.IsCochain :=
  ⟨hi.incl_mem, fun h v => (H.totalD_apply_eq a m _).symm.trans (hi.totalD_incl h v)⟩

/-- The cochain projections as `Feec`'s, bounded by `max C_π 0`. -/
def CochainProj.toFeec {S : HilbertComplex.CrimeFamily.{u} H a m κ} {Cπ : ℝ}
    (P : S.CochainProj Cπ) : S.toFeec.CochainProj (max Cπ 0) where
  π := P.π
  π_incl := P.π_incl
  nonneg := le_max_right _ _
  norm_π_le h x hx := (P.norm_π_le h ⟨x, hx⟩).trans (by
    rw [H.totalD_apply_eq a m]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  π_totalD h z := (congrArg (P.π h) (H.totalD_apply_eq a m z).symm).trans (P.π_totalD h z)

/-- A uniform discrete Poincaré constant `≥ 1` for cochain reading maps (closed range). -/
theorem IsCochain.exists_isPoincare {S : HilbertComplex.CrimeFamily.{u} H a m κ}
    (hi : S.IsCochain) (hcr : ∀ i, (H.win a m).ClosedRangeAt i) {Cπ : ℝ} (P : S.CochainProj Cπ) :
    ∃ cP, 1 ≤ cP ∧ S.toFeec.IsPoincare cP := by
  obtain ⟨c₀, hc₀⟩ := (H.win a m).exists_poincare_totalD hcr
  exact ⟨_, le_max_right _ 1, (hi.toFeec.isPoincare P.toFeec hc₀).mono (le_max_left _ _)⟩

set_option maxHeartbeats 1000000 in
/-- **The cochain verdict** from the cochain case of `Feec`
(`Feec.HilbertComplex.Approximation.StaticCochain`). -/
theorem cochainVerdict
    (hcr : ∀ i : Fin m, 0 < (i : ℕ) → IsClosed (H.boundaries (a + (i : ℕ)) : Set (W (a + (i : ℕ)))))
    (hi : S.IsCochain) {Cπ : ℝ} (P : S.CochainProj Cπ) : S.CochainVerdict₀ P := by
  have hcr' := H.closedRangeAt_win a m hcr
  obtain ⟨cP, hcP, hP⟩ := hi.exists_isPoincare hcr' P
  refine
    { poincare := ⟨cP, hP⟩
      converges := fun hJ hπ {f σ u p} hs {σh uh ph} hsh => ?_
      cohomology := fun hπ => ?_
      rate := ⟨S.toFeec.cochainRateConst (max Cπ 0) cP, fun h {f σ u p} hs {σh uh ph} hsh {ε}
        hσ hu hp hb hJ => ?_⟩ }
  · exact (hi.toFeec.tendsto_staticError hcr' P.toFeec hP hcP hJ (fun x hx => hπ ⟨x, hx⟩)
      f).congr fun h => (S.readError_sol_eq hcr' hs (hsh h)).symm
  · have : FiniteDimensional 𝕜 ((H.win a m).total.harmonic ()) := (H.totalHarmonic_eq a m) ▸ ‹_›
    have happ : ∀ q ∈ (H.win a m).total.harmonic (), Tendsto (fun h =>
        ‖q - S.toFeec.incl h (P.toFeec.π h q)‖) S.l (𝓝 0) := fun q hq =>
      hπ q ((H.totalHarmonic_eq a m).symm ▸ hq)
    filter_upwards [P.toFeec.eventually_norm_sub_incl_π_lt happ] with h hgap
    refine ⟨fun w hw => ⟨⟨S.incl h w, hi.incl_mem h w⟩, by rw [hi.totalD_incl, hw, _root_.map_zero],
      0, by rw [_root_.map_zero, P.π_incl, sub_self]⟩, fun z hz ⟨y, hy⟩ => ?_⟩
    have hinj := hi.toFeec.cohomologyMap_injective P.toFeec hcr' h hgap
    have hzc : (z : Total W a m) ∈ (H.win a m).total.cycles () :=
      LinearPMap.mem_ker_iff.2 ⟨⟨(z : Total W a m), z.2⟩, rfl,
        (H.totalD_apply_eq a m z).symm.trans hz⟩
    have h0 : P.toFeec.cohomologyMap h (Submodule.Quotient.mk ⟨z, hzc⟩) = 0 := by
      rw [Feec.HilbertComplex.ApproxComplexCrime.Family.CochainProj.cohomologyMap,
        Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨⟨y, Submodule.mem_top⟩, hy.symm⟩
    have h1 := hinj (h0.trans (_root_.map_zero _).symm)
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨y', hy'⟩ := h1
    exact ⟨⟨(y' : Total W a m), y'.2⟩, hy'.symm.trans (H.totalD_apply_eq a m ⟨_, y'.2⟩).symm⟩
  · rw [S.readError_sol_eq hcr' hs hsh]
    obtain ⟨rfl, rfl, rfl⟩ := H.eq_totalSol a m hcr' hs
    set X := H.totalSol a m hcr' f
    have hb' : ((H.win a m).total.cycles ()).starProjection ((H.win a m).greenOp hcr' f) =
        (LinearMap.range (H.totalD a m).toFun).topologicalClosure.starProjection
          (H.coordT a m X.snd.fst : Total W a m) := by
      rw [Feec.HilbertComplex.starProjection_cycles_eq_of_mem_orthogonal _ ()
        ((H.win a m).greenOp_mem_orthogonal_harmonic hcr' f)]
      exact starProjection_congr (by rw [H.totalD_eq a m]; rfl) _
    have hXn : ‖X‖ ≤ ‖(H.coordT a m X.fst : Total W a m)‖ + ‖H.totalD a m (H.coordT a m X.fst)‖ +
        ‖(H.coordT a m X.snd.fst : Total W a m)‖ + ‖H.totalD a m (H.coordT a m X.snd.fst)‖ +
        ‖(X.snd.snd : Total W a m)‖ := by
      have e := Feec.HilbertComplex.MixedSpace.norm_sq X
      have e1 := (H.win a m).total.norm_sq_domainSpace () X.fst
      have e2 := (H.win a m).total.norm_sq_domainSpace () X.snd.fst
      rw [← H.totalD_coordT a m] at e1 e2
      change _ = ‖(H.coordT a m X.fst : Total W a m)‖ ^ 2 + _ at e1
      change _ = ‖(H.coordT a m X.snd.fst : Total W a m)‖ ^ 2 + _ at e2
      have := norm_nonneg X
      refine (pow_le_pow_iff_left₀ (norm_nonneg X) (by positivity) two_ne_zero).1 ?_
      nlinarith [norm_nonneg (H.coordT a m X.fst : Total W a m),
        norm_nonneg (H.totalD a m (H.coordT a m X.fst)),
        norm_nonneg (H.coordT a m X.snd.fst : Total W a m),
        norm_nonneg (H.totalD a m (H.coordT a m X.snd.fst)), norm_nonneg (X.snd.snd : Total W a m)]
    refine hi.toFeec.staticError_le_of_approx hcr' P.toFeec hP hcP h f ?_ ?_ ?_ ?_ ?_
    · obtain ⟨v, hv⟩ := hσ
      exact ⟨v, by
        rw [Feec.HilbertComplex.mixedI0_apply, Feec.HilbertComplex.mixedD0_apply,
          ← H.totalD_coordT a m]
        exact hv⟩
    · obtain ⟨v, hv⟩ := hu
      exact ⟨v, by
        rw [Feec.HilbertComplex.mixedI1_apply, Feec.HilbertComplex.mixedD1_apply,
          ← H.totalD_coordT a m]
        exact hv⟩
    · exact hp
    · rw [hb']; exact hb
    · have key : ‖1 - (S.incl h).adjoint ∘L S.incl h‖ * ‖X‖ ≤ ε :=
        (mul_le_mul_of_nonneg_left hXn (norm_nonneg _)).trans hJ
      exact key

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **The heat verdict with crimes** from `Feec.HilbertComplex.ApproxComplexCrime.HeatFamily.heatFEEC`
(no constraint, `K = W`) and the fully discrete FEEC theorem on its heat core. -/
theorem heatVerdict
    (hcr : ∀ i : Fin m, 0 < (i : ℕ) → IsClosed (H.boundaries (a + (i : ℕ)) : Set (W (a + (i : ℕ)))))
    {cP : ℝ} (hP : S.IsPoincare cP) (hJ : Tendsto S.defect S.l (𝓝 0))
    (hconv : ∀ f, S.ConvergesAt f) :
    ∃ U, EvolutionVerdict (sq (H.wave a m)) S.l S.X S.incl
      (fun h => (S.D h - (S.D h).adjoint) ^ 2) U := by
  have hcr' := H.closedRangeAt_win a m hcr
  have hcP : 1 ≤ max cP 1 := le_max_right _ _
  have hP' : S.toFeec.IsPoincare (max cP 1) := fun h v hv =>
    (hP h v hv).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  let F : Feec.HilbertComplex.ApproxComplexCrime.HeatFamily.{u} (H.win a m) κ :=
    { toFamily := S.toFeec
      K := ⊤
      isClosed_K := by rw [Submodule.top_coe]; exact isClosed_univ
      l := S.l
      tendsto_innerDefect := hJ }
  have hconv' : ∀ f, Tendsto (fun h => S.toFeec.staticError hcr' h f) S.l (𝓝 0) := fun f =>
    ((S.convergesAt_iff.1 (hconv f)) _ _ _ (H.isTotalMixedSolution_totalSol a m hcr' f)
      (fun h => S.inclD h (S.toFeec.mixedSol h f).fst)
      (fun h => S.inclD h (S.toFeec.mixedSol h f).snd.fst)
      (fun h => ((S.toFeec.mixedSol h f).snd.snd : S.toFeec.X h))
      (fun h => S.isMixedSolution_mixedSol h f)).congr fun h =>
        S.readError_sol_eq hcr' (H.isTotalMixedSolution_totalSol a m hcr' f)
          (S.isMixedSolution_mixedSol h f)
  have V := F.heatFEEC hcr' hcP hP' hconv'
  have hZ : ∀ x, x ∈ (F.heatCore hcr' hcP hP' hconv').Data.topologicalClosure := fun x => by
    rw [F.dense_heatCore_data hcr' hcP hP' hconv']; exact Submodule.mem_top
  have hL : (fun h => (S.D h - (S.D h).adjoint) ^ 2) = fun h => F.toHeat.L h :=
    funext fun h =>
      (ContinuousLinearMap.sub_adjoint_sq (ContinuousLinearMap.ext (S.D_D h))).trans rfl
  let _ : ∀ h, NormedSpace ℝ (S.X h) := S.normedSpaceReal
  have _ : ∀ h, IsScalarTower ℝ 𝕜 (S.X h) := S.isScalarTower
  refine ⟨F.toHeat.S, ?_⟩
  rw [H.heat_eq a m, hL]
  exact evolutionVerdict_of (S' := F.toHeat.S) (fun _ _ => rfl) F.toHeat.isMDissipative
    F.toHeat.dissipative V.isClassicalSolution V.unique V.antitone
    (fun x => by rw [Feec.HilbertComplex.DissipFEEC.S_def, Feec.C0Semigroup.S_zero_apply])
    (fun x v hv T => V.converges (hZ x) hv T)
    (fun r hr _ hp hp0 τ hτ hτ0 x v hv T ε hε =>
      (Feec.HilbertComplex.dissipFEEC_fullyDiscrete (F.heatCore hcr' hcP hP' hconv')
        (F.toHeat.rationalScheme r hr hp hp0 τ hτ)).converges_iterates
        (hZ x) hv hτ0 T hε)

end CrimeFamily

end HilbertComplex

end FEEC
