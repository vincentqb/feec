module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Feec.Variational.SaddlePoint

/-!
# Galerkin theory: Lax–Milgram, Babuška–Nečas, quasi-optimality, Brezzi (thesis §4.5)

Abstract well-posedness and approximation results for bounded bilinear forms on real Hilbert
spaces, used later for the elliptic projection (§4.6) and the BGG saddle point (Ch 5).

* Thm 4.8 (Lax–Milgram): `lax_milgram`, with the stability bound `lax_milgram_bound`.
* §4.5 definitions: `InfSupCond` (Riesz form), `DenseRangeCond` (quantifier on the second slot,
  correcting the thesis' "equivalently"), and `infSupCond_iff_attained` (the thesis' attained
  form, strengthened to the same constant).
* Thm 4.9 (Babuška–Nečas): `existsUnique_solution`, `existsUnique_solution_dual`,
  `norm_le_of_solution`, `infSup_const_iff` (best constant `‖L⁻¹‖⁻¹`), and the corrected
  equivalence `babuska_necas_iff` / `babuska_necas_iff_dual` ("exists" ↦ "exists unique"),
  with the counterexample `surjective_not_infSup` (backward shift on `ℓ²`) to the thesis' converse.
* Thm 4.10 (quasi-optimality): `quasi_opt`, `quasi_opt_infDist`, `thm_4_10`, with `a` bounded on
  all of `X` (correction), and discrete well-posedness `discrete_existsUnique`.
* Thm 4.11 (Brezzi), corrected (`B : X → Y*`, inf-sup of `b` with the inf over `q`) and proved:
  `brezzi`, `brezzi_unique`, `brezzi_stability`, `brezzi_wellPosed`, and the bilinear-form
  statement `thm_4_11`; `not_infSup_first_of_ker_ne_bot` shows the thesis-literal inf-sup on `b`
  fails whenever `Z ≠ 0`.

Saddle point data are given in Riesz form: `b(v,q) = ⟪B v, q⟫` with `B : X →L[ℝ] Y`, and the
right-hand sides by their representatives; `thm_4_11` states the functional form.

## References

* [QuennevilleBelair2015], §4.5 (Thm 4.8 Lax–Milgram, the inf-sup and dense range conditions,
  Thm 4.9, Thm 4.10 quasi-optimality, Thm 4.11 Brezzi); used in §4.6 and Ch. 5
* [Babuska1971] (inf-sup condition, generalized Lax–Milgram, quasi-optimality of Galerkin
  approximations)
* [Brezzi1974] (existence, uniqueness and stability for saddle point problems; Thm 4.11)
* [BoffiBrezziFortin2013], Ch. 4 (saddle point problems in Hilbert spaces)
* [Arnold2018] (abstract well-posedness and Galerkin stability framework of FEEC)
* [AFW2010] (stability of Galerkin and mixed methods via inf-sup conditions in FEEC)
-/

open scoped RealInnerProductSpace
open InnerProductSpace

@[expose] public noncomputable section

namespace Feec.Galerkin

/-! ## Inf-sup and dense range conditions -/

section InfSup

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- The Riesz operator of a bilinear form: `⟪B♯ u, v⟫ = B u v`. -/
local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

/-- The inf-sup condition (thesis §4.5), Riesz form: `γ ‖u‖ ≤ ‖B u ·‖_{V*}`.

See [QuennevilleBelair2015, §4.5]; cf. [Babuska1971]. -/
def InfSupCond (B : V →L[ℝ] V →L[ℝ] ℝ) : Prop := ∃ γ, 0 < γ ∧ ∀ u, γ * ‖u‖ ≤ ‖B u‖

/-- The dense range condition (thesis §4.5), with the quantifier on the *second* slot.

See [QuennevilleBelair2015, §4.5]; cf. [Babuska1971]. -/
def DenseRangeCond (B : V →L[ℝ] V →L[ℝ] ℝ) : Prop := ∀ v, (∀ u, B u v = 0) → v = 0

/-- Riesz isometry: `‖B♯ u‖ = ‖B u ·‖_{V*}`. -/
theorem norm_sharp (u : V) : ‖B♯ u‖ = ‖B u‖ := by
  simp [continuousLinearMapOfBilin]

/-- Thesis §4.5, the "equivalently" form of the inf-sup condition: on a Hilbert space the
Riesz form `γ ‖u‖ ≤ ‖B u‖` is equivalent, with the *same* constant, to the attained form
`∀ u, ∃ v, ‖v‖ ≤ 1 ∧ γ ‖u‖ ≤ B u v` (the thesis' `a(u,v) ≥ γ ‖u‖ ‖v‖`, normalized).

The thesis' equivalence (with `γ` existentially quantified on both sides) is correct and holds
in any normed space: from `sup ≥ γ ‖u‖` pick `v` reaching `γ/2`. This lemma proves the stronger
same-constant version, which uses that the supremum is attained at the Riesz representative.

See [QuennevilleBelair2015, §4.5]. -/
theorem infSupCond_iff_attained :
    InfSupCond B ↔ ∃ γ, 0 < γ ∧ ∀ u, ∃ v, ‖v‖ ≤ 1 ∧ γ * ‖u‖ ≤ B u v := by
  constructor
  · rintro ⟨γ, hγ, h⟩
    refine ⟨γ, hγ, fun u => ?_⟩
    by_cases h0 : B♯ u = 0
    · refine ⟨0, by simp, ?_⟩
      have := h u
      rw [← norm_sharp, h0, norm_zero] at this
      simpa using this
    · refine ⟨‖B♯ u‖⁻¹ • B♯ u, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)]
      · rw [map_smul, ← continuousLinearMapOfBilin_apply, smul_eq_mul, real_inner_self_eq_norm_sq,
          norm_sharp, sq, ← mul_assoc, inv_mul_cancel₀ (by rwa [← norm_sharp, norm_ne_zero_iff]),
          one_mul]
        exact h u
  · rintro ⟨γ, hγ, h⟩
    refine ⟨γ, hγ, fun u => ?_⟩
    obtain ⟨v, hv, hγv⟩ := h u
    calc γ * ‖u‖ ≤ B u v := hγv
      _ ≤ ‖B u v‖ := Real.le_norm_self _
      _ ≤ ‖B u‖ * ‖v‖ := (B u).le_opNorm v
      _ ≤ ‖B u‖ * 1 := by gcongr
      _ = ‖B u‖ := mul_one _

/-! ## Babuška–Nečas (Thm 4.9) -/

/-- Thm 4.9, step 1: inf-sup makes `B♯` injective. -/
theorem ker_eq_bot (h : InfSupCond B) : (B♯).ker = ⊥ := by
  obtain ⟨γ, hγ, hb⟩ := h
  rw [LinearMap.ker_eq_bot']
  intro u hu
  have := hb u
  rw [← norm_sharp, show (B♯) u = 0 from hu, norm_zero] at this
  have : ‖u‖ ≤ 0 := by nlinarith [norm_nonneg u]
  exact norm_le_zero_iff.mp this

/-- Thm 4.9, step 2: inf-sup makes `B♯` bounded below, hence of closed range. -/
theorem isClosed_range (h : InfSupCond B) : IsClosed ((B♯).range : Set V) := by
  obtain ⟨γ, hγ, hb⟩ := h
  have : AntilipschitzWith (γ⁻¹).toNNReal (B♯) := by
    refine ContinuousLinearMap.antilipschitz_of_bound (B♯) ?_
    intro u
    rw [Real.coe_toNNReal _ (inv_pos.mpr hγ).le, norm_sharp]
    rw [← div_eq_inv_mul, le_div_iff₀ hγ, mul_comm]
    exact hb u
  exact this.isClosed_range (B♯).uniformContinuous

/-- Thm 4.9, step 3: closed range plus dense range give `B♯` onto. -/
theorem range_eq_top (h : InfSupCond B) (hd : DenseRangeCond B) : (B♯).range = ⊤ := by
  have := (isClosed_range h).completeSpace_coe
  rw [← (B♯).range.orthogonal_orthogonal, Submodule.eq_top_iff']
  intro v w hw
  have : w = 0 := hd w fun u => by
    rw [← continuousLinearMapOfBilin_apply]
    exact hw _ ⟨u, rfl⟩
  subst this
  exact inner_zero_left _

/-- Under inf-sup and dense range, `u ↦ B u ·` (through Riesz) is an isomorphism `V ≃L V`. -/
def equivOfInfSup (h : InfSupCond B) (hd : DenseRangeCond B) : V ≃L[ℝ] V :=
  ContinuousLinearEquiv.ofBijective (B♯) (ker_eq_bot h) (range_eq_top h hd)

/-- Defining property of `equivOfInfSup`. -/
@[simp]
theorem equivOfInfSup_apply (h : InfSupCond B) (hd : DenseRangeCond B) (u v : V) :
    ⟪equivOfInfSup h hd u, v⟫ = B u v :=
  continuousLinearMapOfBilin_apply B u v

omit [CompleteSpace V] in
/-- `InfSupCond` is the inf-sup condition (`Feec.Variational.InfSup`) of `B` seen as a
sesquilinear form. -/
theorem infSupCond_iff_exists_infSup :
    InfSupCond B ↔ ∃ γ, Variational.InfSup (Variational.toSesq B) γ :=
  ⟨fun ⟨γ, hγ, h⟩ => ⟨γ, ⟨hγ, fun u => by rw [Variational.norm_toSesq_apply]; exact h u⟩⟩,
    fun ⟨γ, h⟩ => ⟨γ, h.pos, fun u => by rw [← Variational.norm_toSesq_apply]; exact h.le u⟩⟩

omit [CompleteSpace V] in
/-- `DenseRangeCond` is `Feec.Variational.SeparatingRight`. -/
theorem denseRangeCond_iff_separatingRight :
    DenseRangeCond B ↔ Variational.SeparatingRight (Variational.toSesq B) := Iff.rfl

/-- **Thesis Thm 4.9** (Babuška–Nečas), forward direction, Riesz-representative form.

Thesis gap: the thesis gives no proof and writes "there exists"; the conclusion is existence
*and uniqueness*.

See [QuennevilleBelair2015, Thm 4.9]; cf. [Babuska1971]. -/
theorem existsUnique_solution (h : InfSupCond B) (hd : DenseRangeCond B) (f : V) :
    ∃! u, ∀ v, B u v = ⟪f, v⟫ := by
  obtain ⟨γ, hγ⟩ := infSupCond_iff_exists_infSup.1 h
  exact (existsUnique_congr fun u => forall_congr' fun v => by
    rw [Variational.toSesq_apply, real_inner_comm]).1 (Variational.existsUnique_inner hγ hd f)

/-- **Thesis Thm 4.9**, forward direction, for a functional `f ∈ V*`. -/
theorem existsUnique_solution_dual (h : InfSupCond B) (hd : DenseRangeCond B)
    (f : StrongDual ℝ V) : ∃! u, ∀ v, B u v = f v := by
  simpa only [toDual_symm_apply] using existsUnique_solution h hd ((toDual ℝ V).symm f)

omit [CompleteSpace V] in
/-- **Thesis Thm 4.9**, stability: a solution of `B u · = f` satisfies `‖u‖ ≤ γ⁻¹ ‖f‖`. -/
theorem norm_le_of_solution {γ : ℝ} (hγ : 0 < γ) (h : ∀ u, γ * ‖u‖ ≤ ‖B u‖)
    {f : StrongDual ℝ V} {u : V} (hu : ∀ v, B u v = f v) : ‖u‖ ≤ γ⁻¹ * ‖f‖ := by
  have : B u = f := ContinuousLinearMap.ext hu
  rw [le_inv_mul_iff₀ hγ, ← this]
  exact h u

/-- **Thesis Thm 4.9**, the constant: under inf-sup and dense range, a constant `γ ≥ 0`
is admissible in the inf-sup condition iff `γ ‖L⁻¹‖ ≤ 1`; i.e. the best inf-sup constant is
`‖L⁻¹‖⁻¹`.

See [QuennevilleBelair2015, Thm 4.9] (the identity following its statement). -/
theorem infSup_const_iff (h : InfSupCond B) (hd : DenseRangeCond B) {γ : ℝ} (hγ : 0 ≤ γ) :
    (∀ u, γ * ‖u‖ ≤ ‖B u‖) ↔
      γ * ‖((equivOfInfSup h hd).symm : V →L[ℝ] V)‖ ≤ 1 := by
  set e := equivOfInfSup h hd
  have he : ∀ u, ‖e u‖ = ‖B u‖ := fun u => norm_sharp u
  constructor
  · intro hb
    rcases hγ.lt_or_eq with hγ | rfl
    · rw [← le_div_iff₀' hγ]
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
      have := hb (e.symm f)
      rw [← he, ContinuousLinearEquiv.apply_symm_apply] at this
      rw [ContinuousLinearEquiv.coe_coe, div_mul_eq_mul_div, one_mul, le_div_iff₀' hγ]
      exact this
    · simp
  · intro hb u
    calc γ * ‖u‖ = γ * ‖(e.symm : V →L[ℝ] V) (e u)‖ := by simp
      _ ≤ γ * (‖(e.symm : V →L[ℝ] V)‖ * ‖e u‖) := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ = (γ * ‖(e.symm : V →L[ℝ] V)‖) * ‖e u‖ := by ring
      _ ≤ 1 * ‖e u‖ := by gcongr
      _ = ‖B u‖ := by rw [one_mul, he]

omit [CompleteSpace V] in
/-- Thesis Thm 4.9 converse, first half: solvability for every `f` gives dense range. -/
theorem denseRange_of_solvable (hs : ∀ f : V, ∃ u, ∀ v, B u v = ⟪f, v⟫) :
    DenseRangeCond B := by
  intro v hv
  obtain ⟨u, hu⟩ := hs v
  have := hu v
  rw [hv u] at this
  exact inner_self_eq_zero.mp this.symm

/-- Bounded inverse theorem: a bijective Riesz map gives the inf-sup condition. -/
theorem infSup_of_bijective (hinj : Function.Injective (B♯))
    (hs : Function.Surjective (B♯)) : InfSupCond B := by
  let e := ContinuousLinearEquiv.ofBijective (B♯) (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hs)
  have hpos : 0 < ‖(e.symm : V →L[ℝ] V)‖ + 1 := by positivity
  refine ⟨(‖(e.symm : V →L[ℝ] V)‖ + 1)⁻¹, inv_pos.mpr hpos, fun u => ?_⟩
  rw [inv_mul_le_iff₀ hpos, ← norm_sharp]
  have h1 : u = e.symm ((B♯) u) := (e.symm_apply_apply u).symm
  calc ‖u‖ = ‖e.symm ((B♯) u)‖ := by rw [← h1]
    _ ≤ ‖(e.symm : V →L[ℝ] V)‖ * ‖(B♯) u‖ := (e.symm : V →L[ℝ] V).le_opNorm _
    _ ≤ (‖(e.symm : V →L[ℝ] V)‖ + 1) * ‖(B♯) u‖ := by gcongr; linarith

/-- **Thesis Thm 4.9** (Babuška–Nečas), corrected: inf-sup and dense range hold iff for every
`f` there is a *unique* `u` with `B u v = ⟪f, v⟫` for all `v`.

Correction: the thesis states the converse with "there exists `u`"; that is false (see
`surjective_not_infSup`: the backward shift on `ℓ²`). Uniqueness is required, and the converse
uses the bounded inverse theorem.

See [QuennevilleBelair2015, Thm 4.9]; cf. [Babuska1971]. -/
theorem babuska_necas_iff :
    (InfSupCond B ∧ DenseRangeCond B) ↔ ∀ f : V, ∃! u, ∀ v, B u v = ⟪f, v⟫ := by
  rw [infSupCond_iff_exists_infSup, denseRangeCond_iff_separatingRight,
    Variational.babuskaNecas_iff_inner]
  exact forall_congr' fun f => existsUnique_congr fun u => forall_congr' fun v => by
    rw [Variational.toSesq_apply, real_inner_comm]

/-- **Thesis Thm 4.9** (Babuška–Nečas), corrected, with right-hand sides `f ∈ V*` as in the
thesis: inf-sup and dense range hold iff `B u v = f v` (all `v`) is uniquely solvable for every
`f ∈ V*`. See `babuska_necas_iff` for the correction ("exists" ↦ "exists unique"). -/
theorem babuska_necas_iff_dual :
    (InfSupCond B ∧ DenseRangeCond B) ↔ ∀ f : StrongDual ℝ V, ∃! u, ∀ v, B u v = f v := by
  rw [babuska_necas_iff]
  constructor
  · intro hs f
    simpa only [toDual_symm_apply] using hs ((toDual ℝ V).symm f)
  · intro hs f
    simpa only [toDual_apply_apply] using hs (toDual ℝ V f)

/-! ## Lax–Milgram (Thm 4.8) -/

omit [CompleteSpace V] in
/-- Coercivity implies the inf-sup and dense range conditions. -/
theorem infSupCond_of_isCoercive (h : IsCoercive B) : InfSupCond B ∧ DenseRangeCond B := by
  obtain ⟨α, hα, hc⟩ := h
  refine ⟨⟨α, hα, fun u => ?_⟩, fun v hv => ?_⟩
  · rcases (norm_nonneg u).lt_or_eq with hu | hu
    · have : α * ‖u‖ * ‖u‖ ≤ ‖B u‖ * ‖u‖ :=
        (hc u).trans ((Real.le_norm_self _).trans ((B u).le_opNorm u))
      exact le_of_mul_le_mul_right this hu
    · rw [← hu, mul_zero]; exact norm_nonneg _
  · have := hc v
    rw [hv v] at this
    have : ‖v‖ * ‖v‖ ≤ 0 := by nlinarith [norm_nonneg v]
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])

/-- **Thesis Thm 4.8** (Lax–Milgram): a bounded coercive bilinear form `B` on a Hilbert space
admits, for every `f ∈ V*`, a unique `u` with `B u v = f v` for all `v`. Obtained here as a
special case of Thm 4.9.

See [QuennevilleBelair2015, Thm 4.8]. -/
theorem lax_milgram (h : IsCoercive B) (f : StrongDual ℝ V) : ∃! u, ∀ v, B u v = f v := by
  obtain ⟨α, hα, hc⟩ := h
  have H := Variational.existsUnique_of_coercive (B := Variational.toSesq B) hα
    (fun x => by rw [Variational.toSesq_apply, RCLike.re_to_real, sq, ← mul_assoc]; exact hc x)
    (Variational.toAnti f)
  refine (existsUnique_congr fun u => ?_).1 H
  rw [Variational.toSesq_apply_eq]
  exact ⟨fun h v => by simpa using congrArg (fun F => F v) h,
    fun h => congrArg _ (ContinuousLinearMap.ext h)⟩

omit [CompleteSpace V] in
/-- **Thesis Thm 4.8**, stability bound `‖u‖ ≤ α⁻¹ ‖f‖`.

Thesis gap: the bound is the useful part of Lax–Milgram but is not stated.

See [QuennevilleBelair2015, Thm 4.8]. -/
theorem lax_milgram_bound {α : ℝ} (hα : 0 < α) (hc : ∀ u, α * ‖u‖ * ‖u‖ ≤ B u u)
    {f : StrongDual ℝ V} {u : V} (hu : ∀ v, B u v = f v) : ‖u‖ ≤ α⁻¹ * ‖f‖ := by
  rw [le_inv_mul_iff₀ hα]
  rcases (norm_nonneg u).lt_or_eq with hpos | h0
  · have : α * ‖u‖ * ‖u‖ ≤ ‖f‖ * ‖u‖ := by
      calc α * ‖u‖ * ‖u‖ ≤ B u u := hc u
        _ = f u := hu u
        _ ≤ ‖f u‖ := Real.le_norm_self _
        _ ≤ ‖f‖ * ‖u‖ := f.le_opNorm u
    exact le_of_mul_le_mul_right this hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _

end InfSup

/-! ## Counterexample to the converse of Thm 4.9 as stated -/

section BackwardShift

/-- The real sequence space `ℓ²(ℕ)`. -/
abbrev L2 := lp (fun _ : ℕ => ℝ) 2

private lemma two_toReal_pos : 0 < (2 : ENNReal).toReal := by norm_num

lemma memℓp_shift (x : L2) : Memℓp (fun n => x (n + 1)) 2 := by
  have hx := (memℓp_gen_iff two_toReal_pos).1 (lp.memℓp x)
  exact (memℓp_gen_iff two_toReal_pos).2 ((summable_nat_add_iff 1).2 hx)

/-- The backward shift `(Sx)ₙ = xₙ₊₁` as a linear map on `ℓ²`. -/
def shiftₗ : L2 →ₗ[ℝ] L2 where
  toFun x := ⟨fun n => x (n + 1), memℓp_shift x⟩
  map_add' x y := by ext n; rfl
  map_smul' c x := by ext n; rfl

/-- Componentwise formula for the backward shift. -/
@[simp] lemma shiftₗ_apply (x : L2) (n : ℕ) : shiftₗ x n = x (n + 1) := rfl

/-- The backward shift is a contraction on `ℓ²`. -/
lemma norm_shiftₗ_le (x : L2) : ‖shiftₗ x‖ ≤ ‖x‖ := by
  refine lp.norm_le_of_forall_sum_le two_toReal_pos (norm_nonneg _) fun s => ?_
  have hs := ((lp.memℓp x).summable two_toReal_pos)
  calc ∑ i ∈ s, ‖shiftₗ x i‖ ^ (2 : ENNReal).toReal
      = ∑ j ∈ s.map ⟨Nat.succ, Nat.succ_injective⟩, ‖x j‖ ^ (2 : ENNReal).toReal := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑' j, ‖x j‖ ^ (2 : ENNReal).toReal :=
        hs.sum_le_tsum _ fun i _ => by positivity
    _ = ‖x‖ ^ (2 : ENNReal).toReal := (lp.norm_rpow_eq_tsum two_toReal_pos x).symm

/-- The backward shift on `ℓ²` as a bounded operator. -/
def shift : L2 →L[ℝ] L2 := shiftₗ.mkContinuous 1 fun x => by simpa using norm_shiftₗ_le x

/-- Componentwise formula for the bounded backward shift. -/
@[simp] lemma shift_apply (x : L2) (n : ℕ) : shift x n = x (n + 1) := rfl

private lemma memℓp_unshift (f : L2) :
    Memℓp (fun n => Nat.casesOn (motive := fun _ => ℝ) n 0 fun m => f m) 2 := by
  have hf := (memℓp_gen_iff two_toReal_pos).1 (lp.memℓp f)
  exact (memℓp_gen_iff two_toReal_pos).2 ((summable_nat_add_iff 1).1 hf)

/-- The backward shift is onto (right inverse: the forward shift). -/
lemma shift_surjective : Function.Surjective shift := fun f =>
  ⟨⟨_, memℓp_unshift f⟩, by ext n; rfl⟩

/-- The backward shift kills `e₀`, so it is not injective. -/
lemma shift_single : shift (lp.single 2 0 (1 : ℝ)) = 0 := by
  ext n
  simp

/-- **Correction to Thesis Thm 4.9** (converse): the bounded bilinear form
`B u v = ⟪S u, v⟫` on `ℓ²`, with `S` the backward shift, satisfies the dense range condition
and is solvable for every right-hand side, yet violates the inf-sup condition (`S e₀ = 0`).
Hence "there exists `u`" in the thesis' converse must be "there exists a unique `u`".

Concerns [QuennevilleBelair2015, Thm 4.9]. -/
theorem surjective_not_infSup :
    ∃ B : L2 →L[ℝ] L2 →L[ℝ] ℝ, (∀ f, ∃ u, ∀ v, B u v = ⟪f, v⟫) ∧ DenseRangeCond B ∧
      ¬ InfSupCond B := by
  refine ⟨(innerSL ℝ).comp shift, fun f => ?_, fun v hv => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := shift_surjective f
    exact ⟨u, fun v => by simp [hu]⟩
  · obtain ⟨u, hu⟩ := shift_surjective v
    have := hv u
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, hu] at this
    exact inner_self_eq_zero.mp this
  · rintro ⟨γ, hγ, h⟩
    have := h (lp.single 2 0 (1 : ℝ))
    rw [ContinuousLinearMap.comp_apply, shift_single, map_zero, norm_zero,
      lp.norm_single (by norm_num), norm_one, mul_one] at this
    linarith

end BackwardShift

/-! ## Quasi-optimality (Thm 4.10) -/

section QuasiOpt

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The attained inf-sup condition on `K` is `Feec.Variational.InfSup` of the restriction. -/
theorem infSup_restrict_of_forall (B : X →L[ℝ] X →L[ℝ] ℝ) (K : Submodule ℝ X) {γ : ℝ}
    (hγ : 0 < γ) (hinf : ∀ w ∈ K, ∃ v ∈ K, ‖v‖ ≤ 1 ∧ γ * ‖w‖ ≤ B w v) :
    Variational.InfSup (Variational.restrict B K K) γ :=
  Variational.InfSup.of_forall_exists_norm_le_one hγ fun w => by
    obtain ⟨v, hv, hv1, h⟩ := hinf w w.2
    exact ⟨⟨v, hv⟩, hv1, h.trans (Real.le_norm_self _)⟩

/-- **Thesis Thm 4.10** (quasi-optimality, Céa/Babuška), abstract core: under a discrete inf-sup
condition on a subspace `K` and Galerkin orthogonality, `‖u - uₕ‖ ≤ (1 + ‖B‖/γ) ‖u - w‖` for
every `w ∈ K`.

Correction: the theorem statement restates boundedness of `a` only on `Xₕ × Xₕ`, while the
proof needs the standing hypothesis (thesis, paragraph before Thm 4.10) that `a` is bounded on
`X × X`; here `‖B‖` is the norm on all of `X`. Neither completeness, finite dimension nor the
orthogonal projection `rₕ` is needed.

See [QuennevilleBelair2015, Thm 4.10]; cf. [Babuska1971]. -/
theorem quasi_opt (B : X →L[ℝ] X →L[ℝ] ℝ) (K : Submodule ℝ X) {γ : ℝ} (hγ : 0 < γ)
    (hinf : ∀ w ∈ K, ∃ v ∈ K, ‖v‖ ≤ 1 ∧ γ * ‖w‖ ≤ B w v)
    {u uh : X} (huh : uh ∈ K) (horth : ∀ v ∈ K, B (u - uh) v = 0) :
    ∀ w ∈ K, ‖u - uh‖ ≤ (1 + ‖B‖ / γ) * ‖u - w‖ := fun _ hw =>
  (infSup_restrict_of_forall B K hγ hinf).norm_sub_le_of_orthogonal huh horth hw

/-- **Thesis Thm 4.10**, best-approximation form: `‖u - uₕ‖ ≤ (1 + ‖B‖/γ) dist(u, K)`. -/
theorem quasi_opt_infDist (B : X →L[ℝ] X →L[ℝ] ℝ) (K : Submodule ℝ X) {γ : ℝ} (hγ : 0 < γ)
    (hinf : ∀ w ∈ K, ∃ v ∈ K, ‖v‖ ≤ 1 ∧ γ * ‖w‖ ≤ B w v)
    {u uh : X} (huh : uh ∈ K) (horth : ∀ v ∈ K, B (u - uh) v = 0) :
    ‖u - uh‖ ≤ (1 + ‖B‖ / γ) * Metric.infDist u K :=
  (infSup_restrict_of_forall B K hγ hinf).norm_sub_le_infDist huh horth

/-- Thesis Thm 4.10, discrete well-posedness: on a finite-dimensional subspace `K` (the space
`Xₕ`), the discrete inf-sup condition alone gives a unique Galerkin solution `uₕ ∈ K`.

Thesis gap: existence and uniqueness of `uₕ` are used but not argued (Thm 4.9 on `Xₕ` would also
need dense range on `Xₕ`, which holds here by rank–nullity).

See [QuennevilleBelair2015, Thm 4.10]. -/
theorem discrete_existsUnique (B : X →L[ℝ] X →L[ℝ] ℝ) (K : Submodule ℝ X)
    [FiniteDimensional ℝ K] {γ : ℝ} (hγ : 0 < γ)
    (hinf : ∀ w ∈ K, ∃ v ∈ K, ‖v‖ ≤ 1 ∧ γ * ‖w‖ ≤ B w v) (F : StrongDual ℝ X) :
    ∃! uh, uh ∈ K ∧ ∀ v ∈ K, B uh v = F v :=
  Variational.existsUnique_galerkin rfl (infSup_restrict_of_forall B K hγ hinf) F

/-- **Thesis Thm 4.10** as stated, corrected: let `u` solve `B u v = F v` on `X`, and `uₕ ∈ K`
solve `B uₕ v = F v` for `v ∈ K`. Then `‖u - uₕ‖ ≤ (1 + ‖B‖/γ) inf_{w ∈ K} ‖u - w‖`, where the
constant `C = 1 + ‖B‖/γ` is independent of `u`, `uₕ` and (for uniform `γ`) of `h`.

See [QuennevilleBelair2015, Thm 4.10]; cf. [Babuska1971]. -/
theorem thm_4_10 (B : X →L[ℝ] X →L[ℝ] ℝ) (K : Submodule ℝ X) {γ : ℝ} (hγ : 0 < γ)
    (hinf : ∀ w ∈ K, ∃ v ∈ K, ‖v‖ ≤ 1 ∧ γ * ‖w‖ ≤ B w v) (F : StrongDual ℝ X)
    {u uh : X} (hu : ∀ v, B u v = F v) (huh : uh ∈ K) (huhF : ∀ v ∈ K, B uh v = F v) :
    ‖u - uh‖ ≤ (1 + ‖B‖ / γ) * Metric.infDist u K :=
  quasi_opt_infDist B K hγ hinf huh fun v hv => by
    rw [map_sub, sub_apply, hu, huhF v hv, sub_self]

end QuasiOpt

/-! ## Brezzi (Thm 4.11) -/

section Brezzi

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

local notation "adj" => ContinuousLinearMap.adjoint

private lemma norm_sq_adj (Bs : X →L[ℝ] Y) (q : Y) :
    ⟪Bs (adj Bs q), q⟫ = ‖adj Bs q‖ ^ 2 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

omit [InnerProductSpace ℝ X] [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y] in
/-- **Correction to Thesis Thm 4.11**: the thesis' inf-sup hypothesis on `b`, read with its own
convention (inf over the first argument `u ∈ X`), `β ‖u‖ ≤ sup_{‖q‖ ≤ 1} b(u,q)`, can only hold
when `Z = {u | b(u,·) = 0} = 0`. Hence in any genuine saddle point problem (`Z ≠ 0`) it fails,
and the inf must be taken over `q` (as in `brezzi`, `thm_4_11`). Only normed spaces are needed.

Concerns [QuennevilleBelair2015, Thm 4.11]; the correct condition is that of [Brezzi1974]. -/
theorem not_infSup_first_of_ker_ne_bot [NormedSpace ℝ X] [NormedSpace ℝ Y]
    (b : X →L[ℝ] Y →L[ℝ] ℝ) {z : X} (hz : ∀ q, b z q = 0) (hz0 : z ≠ 0) :
    ¬ ∃ β > 0, ∀ u, β * ‖u‖ ≤ ‖b u‖ := by
  rintro ⟨β, hβ, h⟩
  have hbz : b z = 0 := ContinuousLinearMap.ext hz
  have := h z
  rw [hbz, norm_zero] at this
  exact absurd this (not_le.mpr (mul_pos hβ (norm_pos_iff.mpr hz0)))

/-- The old saddle point equations are `Feec.Variational.IsSaddleSolution` for `a` seen as a
sesquilinear form and the Riesz functionals of `F`, `G`. -/
theorem isSaddleSolution_iff (a : X →L[ℝ] X →L[ℝ] ℝ) (Bs : X →L[ℝ] Y) (F : X) (G : Y) (u : X)
    (p : Y) :
    Variational.IsSaddleSolution (Variational.toSesq a) Bs (innerSLFlip ℝ F) (innerSLFlip ℝ G)
        u p ↔ (∀ v, a u v + ⟪Bs v, p⟫ = ⟪F, v⟫) ∧ ∀ q, ⟪Bs u, q⟫ = ⟪G, q⟫ := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => ?_, fun q => ?_⟩
    · have := h1 v
      rwa [Variational.toSesq_apply, ContinuousLinearMap.adjoint_inner_right,
        innerSLFlip_apply_apply, real_inner_comm F v] at this
    · have := h2 q
      rwa [innerSLFlip_apply_apply, real_inner_comm (Bs u) q, real_inner_comm G q] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => ?_, fun q => ?_⟩
    · rw [Variational.toSesq_apply, ContinuousLinearMap.adjoint_inner_right,
        innerSLFlip_apply_apply, real_inner_comm F v]; exact h1 v
    · rw [innerSLFlip_apply_apply, real_inner_comm (Bs u) q, real_inner_comm G q]; exact h2 q

omit [CompleteSpace X] [CompleteSpace Y] in
/-- The old inf-sup hypothesis on `Z = ker B` is `Feec.Variational.InfSup` of the restriction. -/
theorem infSup_ker_of_forall (a : X →L[ℝ] X →L[ℝ] ℝ) (Bs : X →L[ℝ] Y) {γ : ℝ} (hγ : 0 < γ)
    (hZ : ∀ z ∈ Bs.ker, ∃ z' ∈ Bs.ker, ‖z'‖ ≤ 1 ∧ γ * ‖z‖ ≤ a z z') :
    Variational.InfSup (Variational.restrict (Variational.toSesq a) Bs.ker Bs.ker) γ :=
  Variational.InfSup.of_forall_exists_norm_le_one hγ fun z => by
    obtain ⟨z', hz', h1, h2⟩ := hZ z z.2
    exact ⟨⟨z', hz'⟩, h1, h2.trans (Real.le_norm_self _)⟩

/-- Brezzi, lifting step: if `Bᵀ` is bounded below by `β`, then `B Bᵀ` is onto, so every
`G ∈ Y` is `B u_G` with `u_G = Bᵀ w` and `β ‖u_G‖ ≤ ‖G‖`. -/
theorem brezzi_lift (Bs : X →L[ℝ] Y) {β : ℝ} (hβ : 0 < β) (hb : ∀ q, β * ‖q‖ ≤ ‖adj Bs q‖)
    (G : Y) : ∃ w : Y, Bs (adj Bs w) = G ∧ β * ‖adj Bs w‖ ≤ ‖G‖ := by
  obtain ⟨w, hw, hβw⟩ := Variational.exists_lift hβ hb (innerSLFlip ℝ G)
  refine ⟨w, ext_inner_left ℝ fun q => by rw [hw, innerSLFlip_apply_apply], ?_⟩
  rwa [Variational.norm_innerSLFlip] at hβw

/-- **Thesis Thm 4.11** (Brezzi), uniqueness half: the discrete inf-sup on `Z = ker B` and the
inf-sup of `b` (inf over `q ∈ Y`) force uniqueness of the saddle point.

See [QuennevilleBelair2015, Thm 4.11]; cf. [Brezzi1974], [BoffiBrezziFortin2013, Ch. 4]. -/
theorem brezzi_unique (a : X →L[ℝ] X →L[ℝ] ℝ) (Bs : X →L[ℝ] Y) {γ : ℝ} (hγ : 0 < γ)
    (hZ : ∀ z ∈ Bs.ker, ∃ z' ∈ Bs.ker, ‖z'‖ ≤ 1 ∧ γ * ‖z‖ ≤ a z z') {β : ℝ} (hβ : 0 < β)
    (hb : ∀ q, β * ‖q‖ ≤ ‖adj Bs q‖) {F : X} {G : Y} {u u' : X} {p p' : Y}
    (h1 : ∀ v, a u v + ⟪Bs v, p⟫ = ⟪F, v⟫) (h2 : ∀ q, ⟪Bs u, q⟫ = ⟪G, q⟫)
    (h1' : ∀ v, a u' v + ⟪Bs v, p'⟫ = ⟪F, v⟫) (h2' : ∀ q, ⟪Bs u', q⟫ = ⟪G, q⟫) :
    u = u' ∧ p = p' :=
  Variational.IsSaddleSolution.unique (infSup_ker_of_forall a Bs hγ hZ) hβ hb
    ((isSaddleSolution_iff a Bs F G u p).2 ⟨h1, h2⟩)
    ((isSaddleSolution_iff a Bs F G u' p').2 ⟨h1', h2'⟩)

/-- **Thesis Thm 4.11** (Brezzi), corrected and proved: existence and uniqueness for the saddle
point problem `a(u,v) + b(v,p) = F(v)`, `b(u,q) = G(q)`, with `b(v,q) = ⟪B v, q⟫`.

Correction: the thesis writes `B : Y → X*` while defining `b(u,q) = Bu(q)`; here
`B : X → Y`. Its inf-sup hypothesis on `b`, read with the thesis' own convention (inf over the
first argument), fails whenever `Z ≠ 0` (`not_infSup_first_of_ker_ne_bot`); the correct
hypothesis is `inf_q sup_v`, i.e.
`β ‖q‖ ≤ ‖Bᵀ q‖`. `a` is bounded on all of `X`. Thesis gap: no proof is given; the proof here
lifts `G` through `B Bᵀ` (Lax–Milgram), solves on `Z` by Thm 4.9, and recovers `p` from
`Z ∩ Zᗮ = 0`.

See [QuennevilleBelair2015, Thm 4.11]; cf. [Brezzi1974], [BoffiBrezziFortin2013, Ch. 4]. -/
theorem brezzi (a : X →L[ℝ] X →L[ℝ] ℝ) (Bs : X →L[ℝ] Y)
    (hZ : ∃ γ > 0, ∀ z ∈ Bs.ker, ∃ z' ∈ Bs.ker, ‖z'‖ ≤ 1 ∧ γ * ‖z‖ ≤ a z z')
    (hZd : ∀ z' ∈ Bs.ker, (∀ z ∈ Bs.ker, a z z' = 0) → z' = 0)
    (hb : ∃ β > 0, ∀ q, β * ‖q‖ ≤ ‖adj Bs q‖) (F : X) (G : Y) :
    ∃! up : X × Y, (∀ v, a up.1 v + ⟪Bs v, up.2⟫ = ⟪F, v⟫) ∧ ∀ q, ⟪Bs up.1, q⟫ = ⟪G, q⟫ := by
  obtain ⟨γ, hγ, hZ⟩ := hZ
  obtain ⟨β, hβ, hb⟩ := hb
  have hs : Variational.SeparatingRight
      (Variational.restrict (Variational.toSesq a) Bs.ker Bs.ker) := fun z' hz' =>
    Subtype.ext (hZd z' z'.2 fun z hz => hz' ⟨z, hz⟩)
  exact (existsUnique_congr fun up : X × Y => isSaddleSolution_iff a Bs F G up.1 up.2).1
    (Variational.existsUnique_isSaddleSolution (infSup_ker_of_forall a Bs hγ hZ) hs hβ hb _ _)

/-- **Thesis Thm 4.11**, stability (the thesis' "well-posed" constant, made explicit): every
solution satisfies `‖u‖ ≤ γ⁻¹‖F‖ + β⁻¹(1 + ‖a‖/γ)‖G‖` and `‖p‖ ≤ β⁻¹(‖F‖ + ‖a‖‖u‖)`.

Thesis gap: no constant is given; it depends on `‖a‖`, `γ` and `β`.

See [QuennevilleBelair2015, Thm 4.11]; cf. [Brezzi1974], [BoffiBrezziFortin2013, Ch. 4]. -/
theorem brezzi_stability (a : X →L[ℝ] X →L[ℝ] ℝ) (Bs : X →L[ℝ] Y) {γ : ℝ} (hγ : 0 < γ)
    (hZ : ∀ z ∈ Bs.ker, ∃ z' ∈ Bs.ker, ‖z'‖ ≤ 1 ∧ γ * ‖z‖ ≤ a z z') {β : ℝ} (hβ : 0 < β)
    (hb : ∀ q, β * ‖q‖ ≤ ‖adj Bs q‖) {F : X} {G : Y} {u : X} {p : Y}
    (h1 : ∀ v, a u v + ⟪Bs v, p⟫ = ⟪F, v⟫) (h2 : ∀ q, ⟪Bs u, q⟫ = ⟪G, q⟫) :
    ‖u‖ ≤ γ⁻¹ * ‖F‖ + β⁻¹ * (1 + ‖a‖ / γ) * ‖G‖ ∧ ‖p‖ ≤ β⁻¹ * (‖F‖ + ‖a‖ * ‖u‖) := by
  have hs := (isSaddleSolution_iff a Bs F G u p).2 ⟨h1, h2⟩
  have hu := hs.norm_fst_le (infSup_ker_of_forall a Bs hγ hZ) hβ hb
  have hp := hs.norm_snd_le hβ hb
  rw [Variational.norm_innerSLFlip, Variational.norm_innerSLFlip] at hu
  rw [Variational.norm_innerSLFlip] at hp
  have ha := Variational.norm_toSesq_le a
  refine ⟨hu.trans ?_, hp.trans ?_⟩
  · gcongr
  · gcongr

/-- **Thesis Thm 4.11**, well-posedness in the thesis' sense: unique solvability and
`‖u‖ + ‖p‖ ≤ C (‖F‖ + ‖G‖)` with `C` depending only on `‖a‖`, `γ`, `β`.

See [QuennevilleBelair2015, §4.5, Thm 4.11]; cf. [Brezzi1974]. -/
theorem brezzi_wellPosed (a : X →L[ℝ] X →L[ℝ] ℝ) (Bs : X →L[ℝ] Y)
    (hZ : ∃ γ > 0, ∀ z ∈ Bs.ker, ∃ z' ∈ Bs.ker, ‖z'‖ ≤ 1 ∧ γ * ‖z‖ ≤ a z z')
    (hZd : ∀ z' ∈ Bs.ker, (∀ z ∈ Bs.ker, a z z' = 0) → z' = 0)
    (hb : ∃ β > 0, ∀ q, β * ‖q‖ ≤ ‖adj Bs q‖) :
    (∀ F G, ∃! up : X × Y,
      (∀ v, a up.1 v + ⟪Bs v, up.2⟫ = ⟪F, v⟫) ∧ ∀ q, ⟪Bs up.1, q⟫ = ⟪G, q⟫) ∧
    ∃ C, ∀ (F : X) (G : Y) (u : X) (p : Y),
      (∀ v, a u v + ⟪Bs v, p⟫ = ⟪F, v⟫) → (∀ q, ⟪Bs u, q⟫ = ⟪G, q⟫) →
        ‖u‖ + ‖p‖ ≤ C * (‖F‖ + ‖G‖) := by
  refine ⟨brezzi a Bs hZ hZd hb, ?_⟩
  obtain ⟨γ, hγ, hZ⟩ := hZ
  obtain ⟨β, hβ, hb⟩ := hb
  set Cu := γ⁻¹ + β⁻¹ * (1 + ‖a‖ / γ)
  have hCu : 0 ≤ Cu := by positivity
  refine ⟨Cu + β⁻¹ * (1 + ‖a‖ * Cu), fun F G u p h1 h2 => ?_⟩
  obtain ⟨hu, hp⟩ := brezzi_stability a Bs hγ hZ hβ hb h1 h2
  have hS : 0 ≤ ‖F‖ + ‖G‖ := by positivity
  have hu' : ‖u‖ ≤ Cu * (‖F‖ + ‖G‖) := by
    calc ‖u‖ ≤ γ⁻¹ * ‖F‖ + β⁻¹ * (1 + ‖a‖ / γ) * ‖G‖ := hu
      _ ≤ γ⁻¹ * (‖F‖ + ‖G‖) + β⁻¹ * (1 + ‖a‖ / γ) * (‖F‖ + ‖G‖) := by
          gcongr
          · linarith [norm_nonneg G]
          · linarith [norm_nonneg F]
      _ = Cu * (‖F‖ + ‖G‖) := by ring
  have hp' : ‖p‖ ≤ β⁻¹ * (1 + ‖a‖ * Cu) * (‖F‖ + ‖G‖) := by
    calc ‖p‖ ≤ β⁻¹ * (‖F‖ + ‖a‖ * ‖u‖) := hp
      _ ≤ β⁻¹ * ((‖F‖ + ‖G‖) + ‖a‖ * (Cu * (‖F‖ + ‖G‖))) := by
          gcongr
          linarith [norm_nonneg G]
      _ = _ := by ring
  calc ‖u‖ + ‖p‖ ≤ Cu * (‖F‖ + ‖G‖) + β⁻¹ * (1 + ‖a‖ * Cu) * (‖F‖ + ‖G‖) := add_le_add hu' hp'
    _ = _ := by ring

/-- The Riesz operator `B : X → Y` of a bounded bilinear form `b : X × Y → ℝ`,
`⟪B v, q⟫ = b v q`. -/
def rieszOp (b : X →L[ℝ] Y →L[ℝ] ℝ) : X →L[ℝ] Y :=
  LinearMap.mkContinuous
    { toFun := fun v => (toDual ℝ Y).symm (b v)
      map_add' := fun v w => by rw [map_add, map_add]
      map_smul' := fun c v => by
        rw [map_smul, LinearIsometryEquiv.map_smulₛₗ]
        simp }
    ‖b‖ fun v => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearIsometryEquiv.norm_map]
      exact b.le_opNorm v

omit [CompleteSpace X] in
/-- Defining property of `rieszOp`. -/
@[simp] lemma inner_rieszOp (b : X →L[ℝ] Y →L[ℝ] ℝ) (v : X) (q : Y) :
    ⟪rieszOp b v, q⟫ = b v q := by
  simp [rieszOp, toDual_symm_apply]

omit [CompleteSpace X] in
/-- `ker B = Z = {v | b(v, ·) = 0}` (thesis §4.5). -/
lemma mem_ker_rieszOp (b : X →L[ℝ] Y →L[ℝ] ℝ) (v : X) :
    v ∈ (rieszOp b).ker ↔ ∀ q, b v q = 0 := by
  constructor
  · intro h q
    rw [← inner_rieszOp, show rieszOp b v = 0 from h, inner_zero_left]
  · intro h
    show rieszOp b v = 0
    exact ext_inner_right ℝ fun q => by rw [inner_rieszOp, h, inner_zero_left]

/-- **Thesis Thm 4.11** (Brezzi) in the thesis' bilinear-form formulation, corrected.

Let `a : X × X → ℝ` and `b : X × Y → ℝ` be bounded, `Z = {u | b(u,q) = 0 ∀ q}`. Assume
* `a` satisfies inf-sup and dense range on `Z × Z`;
* `b` satisfies inf-sup with the **inf over `q ∈ Y`**: `β ‖q‖ ≤ sup_{‖v‖ ≤ 1} b(v,q)`.
Then for all `F ∈ X*`, `G ∈ Y*` the saddle point problem `a(u,v) + b(v,p) = F v`,
`b(u,q) = G q` has a unique solution, and `‖u‖ + ‖p‖ ≤ C (‖F‖ + ‖G‖)` (well-posedness).

Correction: the thesis' inf-sup convention (inf over the first argument) applied to `b` is
unsatisfiable when `Z ≠ 0` (`not_infSup_first_of_ker_ne_bot`), and its `B : Y → X*` should be
`B : X → Y*`; `a` is assumed bounded
on all of `X`. Thesis gap: no proof is given in the thesis.

See [QuennevilleBelair2015, Thm 4.11]; cf. [Brezzi1974], [BoffiBrezziFortin2013, Ch. 4]. -/
theorem thm_4_11 (a : X →L[ℝ] X →L[ℝ] ℝ) (b : X →L[ℝ] Y →L[ℝ] ℝ)
    (hZ : ∃ γ > 0, ∀ z, (∀ q, b z q = 0) →
      ∃ z', (∀ q, b z' q = 0) ∧ ‖z'‖ ≤ 1 ∧ γ * ‖z‖ ≤ a z z')
    (hZd : ∀ z', (∀ q, b z' q = 0) → (∀ z, (∀ q, b z q = 0) → a z z' = 0) → z' = 0)
    (hb : ∃ β > 0, ∀ q, ∃ v, ‖v‖ ≤ 1 ∧ β * ‖q‖ ≤ b v q) :
    (∀ (F : StrongDual ℝ X) (G : StrongDual ℝ Y), ∃! up : X × Y,
      (∀ v, a up.1 v + b v up.2 = F v) ∧ ∀ q, b up.1 q = G q) ∧
    ∃ C, ∀ (F : StrongDual ℝ X) (G : StrongDual ℝ Y) (u : X) (p : Y),
      (∀ v, a u v + b v p = F v) → (∀ q, b u q = G q) → ‖u‖ + ‖p‖ ≤ C * (‖F‖ + ‖G‖) := by
  set Bs := rieszOp b
  have hZ' : ∃ γ > 0, ∀ z ∈ Bs.ker, ∃ z' ∈ Bs.ker, ‖z'‖ ≤ 1 ∧ γ * ‖z‖ ≤ a z z' := by
    obtain ⟨γ, hγ, h⟩ := hZ
    refine ⟨γ, hγ, fun z hz => ?_⟩
    obtain ⟨z', hz', h1, h2⟩ := h z ((mem_ker_rieszOp b z).1 hz)
    exact ⟨z', (mem_ker_rieszOp b z').2 hz', h1, h2⟩
  have hZd' : ∀ z' ∈ Bs.ker, (∀ z ∈ Bs.ker, a z z' = 0) → z' = 0 := fun z' hz' h =>
    hZd z' ((mem_ker_rieszOp b z').1 hz') fun z hz => h z ((mem_ker_rieszOp b z).2 hz)
  have hb' : ∃ β > 0, ∀ q, β * ‖q‖ ≤ ‖adj Bs q‖ := by
    obtain ⟨β, hβ, h⟩ := hb
    refine ⟨β, hβ, fun q => ?_⟩
    obtain ⟨v, hv, hβv⟩ := h q
    calc β * ‖q‖ ≤ b v q := hβv
      _ = ⟪v, adj Bs q⟫ := by rw [ContinuousLinearMap.adjoint_inner_right, inner_rieszOp]
      _ ≤ ‖v‖ * ‖adj Bs q‖ := real_inner_le_norm _ _
      _ ≤ 1 * ‖adj Bs q‖ := by gcongr
      _ = _ := one_mul _
  obtain ⟨hex, C, hC⟩ := brezzi_wellPosed a Bs hZ' hZd' hb'
  have key : ∀ (F : StrongDual ℝ X) (G : StrongDual ℝ Y) (u : X) (p : Y),
      ((∀ v, a u v + b v p = F v) ∧ ∀ q, b u q = G q) ↔
      ((∀ v, a u v + ⟪Bs v, p⟫ = ⟪(toDual ℝ X).symm F, v⟫) ∧
        ∀ q, ⟪Bs u, q⟫ = ⟪(toDual ℝ Y).symm G, q⟫) := by
    intro F G u p
    simp only [Bs, inner_rieszOp, toDual_symm_apply]
  refine ⟨fun F G => ?_, C, fun F G u p h1 h2 => ?_⟩
  · obtain ⟨up, hup, huniq⟩ := hex ((toDual ℝ X).symm F) ((toDual ℝ Y).symm G)
    exact ⟨up, (key F G up.1 up.2).2 hup, fun up' h => huniq up' ((key F G up'.1 up'.2).1 h)⟩
  · have := (key F G u p).1 ⟨h1, h2⟩
    have hb := hC _ _ u p this.1 this.2
    simpa only [LinearIsometryEquiv.norm_map] using hb

end Brezzi

end Feec.Galerkin
