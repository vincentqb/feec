module

public import Feec.Algebra.MatrixSymbol
public import Feec.Geometry.WeylDecomposition
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Algebra.Order.Star.Real

/-!
# The linearized Einstein–Bianchi system: jets

The linearized Einstein–Bianchi (EB) system of thesis §3.4, in a fixed Minkowski frame
(`x⁰ = t`, spatial index `c : Fin 3` ↔ coordinate `c + 1`), at the level of jets. A Weyl field
is `C = [[E, B], [B, -E]]` in the bivector block form of `Feec.Geometry.WeylDecomposition`; the
matrix calculus (`curl`, `div`, `vskw`, Lemma 3.5) is `Feec.Algebra.MatrixSymbol`.

## Main results

* **Prop 3.4**: `linBianchi_iff` (the linearized second Bianchi identity for a Weyl field with
  symmetric `E, B` ⇔ `div E = div B = 0`, `Ė + curl B = 0`, `Ḃ - curl E = 0`);
  `linBianchi_iff_sym` (reduced form for trace-free `E, B`) and `EBJetSym_surjective` (exactly
  16 independent equations: 6 constraints and 10 evolution equations).
* **Prop 3.6, algebraic core**: `div_propagation` (`∂_t div E = ∂_t div B = 0`),
  `violation_evolution` (closed system for `(tr E, vskw E, tr B, vskw B)`), `energy_flux`
  (`½ ∂_t e = div F`), `energy_nonneg`, `energy_eq_zero_iff`.

## References

* [QuennevilleBelair2015], §3.3–3.4 (Prop 3.4, Lemma 3.5, Prop 3.6)
* [Bel1958], [Friedrich1996], [ACBY1997]
-/

open Matrix Feec.MatrixSymbol Feec.DoubleForm

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi

/-- A first jet `dA c = ∂_c A` of a spatial matrix field. -/
abbrev SpaceJet := Fin 3 → Matrix (Fin 3) (Fin 3) ℝ

/-- The jet of `vskw A`. -/
def vskwJ (dA : SpaceJet) : Fin 3 → Fin 3 → ℝ := fun c => vskw (dA c)

/-- The jet of `skw A = ½ (A - Aᵀ)`. -/
def skwJ (dA : SpaceJet) : SpaceJet := fun c => (1 / 2 : ℝ) • (dA c - (dA c)ᵀ)

/-- The symmetric part `sym A = ½ (A + Aᵀ)`. -/
def symPart (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (1 / 2 : ℝ) • (A + Aᵀ)

/-- Entrywise symmetry of a jet of symmetric matrices. -/
theorem jet_symm {dA : SpaceJet} (hsym : ∀ c, (dA c)ᵀ = dA c) (c i j : Fin 3) :
    dA c i j = dA c j i := by
  simpa [Matrix.transpose_apply] using congrFun (congrFun (hsym c) j) i

/-! ## Prop 3.4 on jets: the linearized second Bianchi identity

A first jet of a spacetime matrix field is `dX : Fin 4 → Matrix`, `dX μ = ∂_μ X`, with
`μ = 0` the time direction; `sp dX` is its spatial part. -/

/-- First jet of a spacetime matrix field. -/
abbrev Jet4 := Fin 4 → Matrix (Fin 3) (Fin 3) ℝ

/-- Spatial part `(∂_1, ∂_2, ∂_3)` of a spacetime jet. -/
def sp (dX : Jet4) : SpaceJet := fun c => dX c.succ

/-- The jet `∂_μ C` of the Weyl field `C = [[E, B], [B, -E]]` (block form of Prop 3.3).
See [QuennevilleBelair2015], Prop 3.3; the decomposition goes back to [Bel1958]. -/
def dWeyl (dE dB : Jet4) (μ : Fin 4) : DoubleForm.Tensor4 := ofBlocks (dE μ) (dB μ) (dB μ) (-dE μ)

/-- The linearized second Bianchi expression `∂_α C_{βγδθ} + ∂_β C_{γαδθ} + ∂_γ C_{αβδθ}`. -/
def bianchi2 (dE dB : Jet4) (α β γ δ θ : Fin 4) : ℝ :=
  dWeyl dE dB α β γ δ θ + dWeyl dE dB β γ α δ θ + dWeyl dE dB γ α β δ θ

/-- The linearized EB system (Thesis (3.3)–(3.4)) on jets:
`div E = 0`, `div B = 0`, `Ė + curl B = 0`, `Ḃ - curl E = 0`.
See [QuennevilleBelair2015], §3.4, Prop 3.4; cf. the nonlinear EB system of [Friedrich1996]
and [ACBY1997]. -/
def EBJet (dE dB : Jet4) : Prop :=
  div (sp dE) = 0 ∧ div (sp dB) = 0 ∧ dE 0 + curl (sp dB) = 0 ∧ dB 0 - curl (sp dE) = 0

/-- The reduced form (Thesis Prop 3.4, count refinement): constraints plus the symmetric parts
of the evolution equations. -/
def EBJetSym (dE dB : Jet4) : Prop :=
  div (sp dE) = 0 ∧ div (sp dB) = 0 ∧ dE 0 + symPart (curl (sp dB)) = 0 ∧
    dB 0 - symPart (curl (sp dE)) = 0

/-- The Bianchi expression in bivector components. -/
theorem bianchi2_eq (dE dB : Jet4) (α β γ δ θ : Fin 4) :
    bianchi2 dE dB α β γ δ θ = sgn δ θ *
      (sgn β γ * fromBlocks (dE α) (dB α) (dB α) (-dE α) (pidx β γ) (pidx δ θ)
      + sgn γ α * fromBlocks (dE β) (dB β) (dB β) (-dE β) (pidx γ α) (pidx δ θ)
      + sgn α β * fromBlocks (dE γ) (dB γ) (dB γ) (-dE γ) (pidx α β) (pidx δ θ)) := by
  simp only [bianchi2, dWeyl, ofBlocks, ofMat_apply]; ring

/-- The 24 scalar components of `EBJet`. -/
private theorem EBJet_iff_components (dE dB : Jet4) : EBJet dE dB ↔
    (∀ a, ∑ b, dE b.succ a b = 0) ∧ (∀ a, ∑ b, dB b.succ a b = 0) ∧
    (∀ a b, dE 0 a b + ∑ c, ∑ d, leviCivita3 ℝ b c d * dB c.succ a d = 0) ∧
    (∀ a b, dB 0 a b - ∑ c, ∑ d, leviCivita3 ℝ b c d * dE c.succ a d = 0) := by
  simp only [EBJet, funext_iff, div, sp, ← Matrix.ext_iff, curl, Matrix.add_apply,
    Matrix.sub_apply, Matrix.of_apply, Pi.zero_apply, Matrix.zero_apply]

/-- The cyclic sum in `bianchi2_eq` at a fixed second bivector `J`. -/
def cyc3 (dE dB : Jet4) (α β γ : Fin 4) (J : Ix) : ℝ :=
  sgn β γ * fromBlocks (dE α) (dB α) (dB α) (-dE α) (pidx β γ) J
    + sgn γ α * fromBlocks (dE β) (dB β) (dB β) (-dE β) (pidx γ α) J
    + sgn α β * fromBlocks (dE γ) (dB γ) (dB γ) (-dE γ) (pidx α β) J

/-- The cyclic sum vanishes for the second bivector `inl 0` (Thesis Prop 3.4, `⇐`). -/
private theorem cyc3_zero_inl0 (dE dB : Jet4) (hE : ∀ μ, (dE μ)ᵀ = dE μ)
    (hB : ∀ μ, (dB μ)ᵀ = dB μ) (hEB : EBJet dE dB) (α β γ : Fin 4) :
    cyc3 dE dB α β γ (.inl 0) = 0 := by
  have sE : ∀ μ i j, dE μ i j = dE μ j i := fun μ i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hE μ) j) i
  have sB : ∀ μ i j, dB μ i j = dB μ j i := fun μ i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hB μ) j) i
  have nrm : ∀ μ, (dE μ 0 1 = dE μ 1 0 ∧ dE μ 0 2 = dE μ 2 0 ∧ dE μ 1 2 = dE μ 2 1) ∧
      (dB μ 0 1 = dB μ 1 0 ∧ dB μ 0 2 = dB μ 2 0 ∧ dB μ 1 2 = dB μ 2 1) :=
    fun μ => ⟨⟨sE μ 0 1, sE μ 0 2, sE μ 1 2⟩, ⟨sB μ 0 1, sB μ 0 2, sB μ 1 2⟩⟩
  rw [EBJet_iff_components] at hEB
  simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, Fin.sum_univ_three,
    leviCivita3_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hEB
  norm_num [nrm] at hEB
  obtain ⟨⟨c0, c1, c2⟩, ⟨c3, c4, c5⟩, ⟨⟨c6, c7, c8⟩, ⟨c9, c10, c11⟩, ⟨c12, c13, c14⟩⟩,
    ⟨⟨c15, c16, c17⟩, ⟨c18, c19, c20⟩, ⟨c21, c22, c23⟩⟩⟩ := hEB
  fin_cases α <;> fin_cases β <;> fin_cases γ <;>
    simp [cyc3, sgn, pidx] <;> linarith

/-- The cyclic sum vanishes for the second bivector `inl 1` (Thesis Prop 3.4, `⇐`). -/
private theorem cyc3_zero_inl1 (dE dB : Jet4) (hE : ∀ μ, (dE μ)ᵀ = dE μ)
    (hB : ∀ μ, (dB μ)ᵀ = dB μ) (hEB : EBJet dE dB) (α β γ : Fin 4) :
    cyc3 dE dB α β γ (.inl 1) = 0 := by
  have sE : ∀ μ i j, dE μ i j = dE μ j i := fun μ i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hE μ) j) i
  have sB : ∀ μ i j, dB μ i j = dB μ j i := fun μ i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hB μ) j) i
  have nrm : ∀ μ, (dE μ 0 1 = dE μ 1 0 ∧ dE μ 0 2 = dE μ 2 0 ∧ dE μ 1 2 = dE μ 2 1) ∧
      (dB μ 0 1 = dB μ 1 0 ∧ dB μ 0 2 = dB μ 2 0 ∧ dB μ 1 2 = dB μ 2 1) :=
    fun μ => ⟨⟨sE μ 0 1, sE μ 0 2, sE μ 1 2⟩, ⟨sB μ 0 1, sB μ 0 2, sB μ 1 2⟩⟩
  rw [EBJet_iff_components] at hEB
  simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, Fin.sum_univ_three,
    leviCivita3_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hEB
  norm_num [nrm] at hEB
  obtain ⟨⟨c0, c1, c2⟩, ⟨c3, c4, c5⟩, ⟨⟨c6, c7, c8⟩, ⟨c9, c10, c11⟩, ⟨c12, c13, c14⟩⟩,
    ⟨⟨c15, c16, c17⟩, ⟨c18, c19, c20⟩, ⟨c21, c22, c23⟩⟩⟩ := hEB
  fin_cases α <;> fin_cases β <;> fin_cases γ <;>
    simp [cyc3, sgn, pidx, nrm] <;> linarith

/-- The cyclic sum vanishes for the second bivector `inl 2` (Thesis Prop 3.4, `⇐`). -/
private theorem cyc3_zero_inl2 (dE dB : Jet4) (hE : ∀ μ, (dE μ)ᵀ = dE μ)
    (hB : ∀ μ, (dB μ)ᵀ = dB μ) (hEB : EBJet dE dB) (α β γ : Fin 4) :
    cyc3 dE dB α β γ (.inl 2) = 0 := by
  have sE : ∀ μ i j, dE μ i j = dE μ j i := fun μ i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hE μ) j) i
  have sB : ∀ μ i j, dB μ i j = dB μ j i := fun μ i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hB μ) j) i
  have nrm : ∀ μ, (dE μ 0 1 = dE μ 1 0 ∧ dE μ 0 2 = dE μ 2 0 ∧ dE μ 1 2 = dE μ 2 1) ∧
      (dB μ 0 1 = dB μ 1 0 ∧ dB μ 0 2 = dB μ 2 0 ∧ dB μ 1 2 = dB μ 2 1) :=
    fun μ => ⟨⟨sE μ 0 1, sE μ 0 2, sE μ 1 2⟩, ⟨sB μ 0 1, sB μ 0 2, sB μ 1 2⟩⟩
  rw [EBJet_iff_components] at hEB
  simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, Fin.sum_univ_three,
    leviCivita3_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hEB
  norm_num [nrm] at hEB
  obtain ⟨⟨c0, c1, c2⟩, ⟨c3, c4, c5⟩, ⟨⟨c6, c7, c8⟩, ⟨c9, c10, c11⟩, ⟨c12, c13, c14⟩⟩,
    ⟨⟨c15, c16, c17⟩, ⟨c18, c19, c20⟩, ⟨c21, c22, c23⟩⟩⟩ := hEB
  fin_cases α <;> fin_cases β <;> fin_cases γ <;>
    simp [cyc3, sgn, pidx, nrm] <;> linarith

/-- The cyclic sum vanishes for the second bivector `inr 0` (Thesis Prop 3.4, `⇐`). -/
private theorem cyc3_zero_inr0 (dE dB : Jet4) (hE : ∀ μ, (dE μ)ᵀ = dE μ)
    (hB : ∀ μ, (dB μ)ᵀ = dB μ) (hEB : EBJet dE dB) (α β γ : Fin 4) :
    cyc3 dE dB α β γ (.inr 0) = 0 := by
  have sE : ∀ μ i j, dE μ i j = dE μ j i := fun μ i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hE μ) j) i
  have sB : ∀ μ i j, dB μ i j = dB μ j i := fun μ i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hB μ) j) i
  have nrm : ∀ μ, (dE μ 0 1 = dE μ 1 0 ∧ dE μ 0 2 = dE μ 2 0 ∧ dE μ 1 2 = dE μ 2 1) ∧
      (dB μ 0 1 = dB μ 1 0 ∧ dB μ 0 2 = dB μ 2 0 ∧ dB μ 1 2 = dB μ 2 1) :=
    fun μ => ⟨⟨sE μ 0 1, sE μ 0 2, sE μ 1 2⟩, ⟨sB μ 0 1, sB μ 0 2, sB μ 1 2⟩⟩
  rw [EBJet_iff_components] at hEB
  simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, Fin.sum_univ_three,
    leviCivita3_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hEB
  norm_num [nrm] at hEB
  obtain ⟨⟨c0, c1, c2⟩, ⟨c3, c4, c5⟩, ⟨⟨c6, c7, c8⟩, ⟨c9, c10, c11⟩, ⟨c12, c13, c14⟩⟩,
    ⟨⟨c15, c16, c17⟩, ⟨c18, c19, c20⟩, ⟨c21, c22, c23⟩⟩⟩ := hEB
  fin_cases α <;> fin_cases β <;> fin_cases γ <;>
    simp [cyc3, sgn, pidx] <;> linarith

/-- The cyclic sum vanishes for the second bivector `inr 1` (Thesis Prop 3.4, `⇐`). -/
private theorem cyc3_zero_inr1 (dE dB : Jet4) (hE : ∀ μ, (dE μ)ᵀ = dE μ)
    (hB : ∀ μ, (dB μ)ᵀ = dB μ) (hEB : EBJet dE dB) (α β γ : Fin 4) :
    cyc3 dE dB α β γ (.inr 1) = 0 := by
  have sE : ∀ μ i j, dE μ i j = dE μ j i := fun μ i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hE μ) j) i
  have sB : ∀ μ i j, dB μ i j = dB μ j i := fun μ i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hB μ) j) i
  have nrm : ∀ μ, (dE μ 0 1 = dE μ 1 0 ∧ dE μ 0 2 = dE μ 2 0 ∧ dE μ 1 2 = dE μ 2 1) ∧
      (dB μ 0 1 = dB μ 1 0 ∧ dB μ 0 2 = dB μ 2 0 ∧ dB μ 1 2 = dB μ 2 1) :=
    fun μ => ⟨⟨sE μ 0 1, sE μ 0 2, sE μ 1 2⟩, ⟨sB μ 0 1, sB μ 0 2, sB μ 1 2⟩⟩
  rw [EBJet_iff_components] at hEB
  simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, Fin.sum_univ_three,
    leviCivita3_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hEB
  norm_num [nrm] at hEB
  obtain ⟨⟨c0, c1, c2⟩, ⟨c3, c4, c5⟩, ⟨⟨c6, c7, c8⟩, ⟨c9, c10, c11⟩, ⟨c12, c13, c14⟩⟩,
    ⟨⟨c15, c16, c17⟩, ⟨c18, c19, c20⟩, ⟨c21, c22, c23⟩⟩⟩ := hEB
  fin_cases α <;> fin_cases β <;> fin_cases γ <;>
    simp [cyc3, sgn, pidx, nrm] <;> linarith

/-- The cyclic sum vanishes for the second bivector `inr 2` (Thesis Prop 3.4, `⇐`). -/
private theorem cyc3_zero_inr2 (dE dB : Jet4) (hE : ∀ μ, (dE μ)ᵀ = dE μ)
    (hB : ∀ μ, (dB μ)ᵀ = dB μ) (hEB : EBJet dE dB) (α β γ : Fin 4) :
    cyc3 dE dB α β γ (.inr 2) = 0 := by
  have sE : ∀ μ i j, dE μ i j = dE μ j i := fun μ i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hE μ) j) i
  have sB : ∀ μ i j, dB μ i j = dB μ j i := fun μ i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hB μ) j) i
  have nrm : ∀ μ, (dE μ 0 1 = dE μ 1 0 ∧ dE μ 0 2 = dE μ 2 0 ∧ dE μ 1 2 = dE μ 2 1) ∧
      (dB μ 0 1 = dB μ 1 0 ∧ dB μ 0 2 = dB μ 2 0 ∧ dB μ 1 2 = dB μ 2 1) :=
    fun μ => ⟨⟨sE μ 0 1, sE μ 0 2, sE μ 1 2⟩, ⟨sB μ 0 1, sB μ 0 2, sB μ 1 2⟩⟩
  rw [EBJet_iff_components] at hEB
  simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, Fin.sum_univ_three,
    leviCivita3_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hEB
  norm_num [nrm] at hEB
  obtain ⟨⟨c0, c1, c2⟩, ⟨c3, c4, c5⟩, ⟨⟨c6, c7, c8⟩, ⟨c9, c10, c11⟩, ⟨c12, c13, c14⟩⟩,
    ⟨⟨c15, c16, c17⟩, ⟨c18, c19, c20⟩, ⟨c21, c22, c23⟩⟩⟩ := hEB
  fin_cases α <;> fin_cases β <;> fin_cases γ <;>
    simp [cyc3, sgn, pidx, nrm] <;> linarith

/-- **Thesis Prop 3.4** (jet level): for jets of symmetric `E`, `B`, the linearized second
Bianchi identity `∂_[α C_βγ]δθ = 0` for `C = [[E, B], [B, -E]]` holds iff
`div E = div B = 0`, `Ė + curl B = 0`, `Ḃ - curl E = 0`.

Thesis gap: `div` and matrix `curl` are used before being defined (conventions fixed as in
Lemma 3.5; the signs depend on them); the equivalence is pointwise and needs only `C ∈ C¹`
(field version: `linBianchi_field_iff`); "using the symmetries in Proposition 3.2" should cite
Prop 3.3. Trace-freeness is not needed for this equivalence (the 24 equations are not reduced
by assuming trace-freeness here; their independence on general symmetric jets is not proved);
it is needed for the count of 16 (`linBianchi_iff_sym`,
`EBJetSym_surjective`). This module starts from the linearized identity
`∂_[α C_βγ]δθ = 0` (the thesis' `0 = ε∂_[α C_βγ]δθ + O(ε²)` at first order).

See [QuennevilleBelair2015], Prop 3.4; the nonlinear analogue is in [Friedrich1996]
(cf. [ACBY1997]). -/
theorem linBianchi_iff (dE dB : Jet4) (hE : ∀ μ, (dE μ)ᵀ = dE μ) (hB : ∀ μ, (dB μ)ᵀ = dB μ) :
    (∀ α β γ δ θ, bianchi2 dE dB α β γ δ θ = 0) ↔ EBJet dE dB := by
  have sE : ∀ μ i j, dE μ i j = dE μ j i := fun μ i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hE μ) j) i
  have sB : ∀ μ i j, dB μ i j = dB μ j i := fun μ i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hB μ) j) i
  have nrm : ∀ μ, (dE μ 0 1 = dE μ 1 0 ∧ dE μ 0 2 = dE μ 2 0 ∧ dE μ 1 2 = dE μ 2 1) ∧
      (dB μ 0 1 = dB μ 1 0 ∧ dB μ 0 2 = dB μ 2 0 ∧ dB μ 1 2 = dB μ 2 1) :=
    fun μ => ⟨⟨sE μ 0 1, sE μ 0 2, sE μ 1 2⟩, ⟨sB μ 0 1, sB μ 0 2, sB μ 1 2⟩⟩
  constructor
  · intro h
    rw [EBJet_iff_components]
    simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, Fin.sum_univ_three,
      leviCivita3_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    norm_num [nrm]
    have k : ∀ α β γ (J : Ix), bianchi2 dE dB α β γ (p J) (q J) = 0 := fun α β γ J => h _ _ _ _ _
    have k1 := fun J => k 1 2 3 J
    have k2 := fun J => k 0 2 3 J
    have k3 := fun J => k 0 3 1 J
    have k4 := fun J => k 0 1 2 J
    simp only [bianchi2_eq, Sum.forall, Fin.forall_fin_succ,
      IsEmpty.forall_iff] at k1 k2 k3 k4
    norm_num [sgn, pidx, p, q, nrm] at k1 k2 k3 k4
    obtain ⟨⟨a1, a2, a3⟩, ⟨a4, a5, a6⟩⟩ := k1
    obtain ⟨⟨b1, b2, b3⟩, ⟨b4, b5, b6⟩⟩ := k2
    obtain ⟨⟨c1, c2, c3⟩, ⟨c4, c5, c6⟩⟩ := k3
    obtain ⟨⟨d1, d2, d3⟩, ⟨d4, d5, d6⟩⟩ := k4
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩,
      ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩⟩ <;> linarith
  · intro hEB α β γ δ θ
    rw [bianchi2_eq]
    have H : cyc3 dE dB α β γ (pidx δ θ) = 0 := by
      rcases pidx δ θ with j | j <;> fin_cases j
      · exact cyc3_zero_inl0 dE dB hE hB hEB α β γ
      · exact cyc3_zero_inl1 dE dB hE hB hEB α β γ
      · exact cyc3_zero_inl2 dE dB hE hB hEB α β γ
      · exact cyc3_zero_inr0 dE dB hE hB hEB α β γ
      · exact cyc3_zero_inr1 dE dB hE hB hEB α β γ
      · exact cyc3_zero_inr2 dE dB hE hB hEB α β γ
    simp only [cyc3] at H
    rw [H, mul_zero]

/-- Jets of symmetric trace-free matrices (pointwise TSD up to the divergence condition). -/
def IsSymTF (dX : Jet4) : Prop := ∀ μ, (dX μ)ᵀ = dX μ ∧ (dX μ).trace = 0

/-- `sym A = A` for symmetric `A` (used in Thesis Prop 3.4, count refinement). -/
theorem symPart_of_transpose_eq {A : Matrix (Fin 3) (Fin 3) ℝ} (h : Aᵀ = A) : symPart A = A := by
  rw [symPart, h, ← two_smul ℝ A, smul_smul]; norm_num

/-- `sym A` is symmetric (used in Thesis Prop 3.4, count refinement). -/
theorem transpose_symPart (A : Matrix (Fin 3) (Fin 3) ℝ) : (symPart A)ᵀ = symPart A := by
  simp [symPart, Matrix.transpose_add, add_comm]

/-- `tr sym A = tr A` (used in Thesis Prop 3.4, count refinement). -/
theorem trace_symPart (A : Matrix (Fin 3) (Fin 3) ℝ) : (symPart A).trace = A.trace := by
  simp [symPart, Matrix.trace_add, Matrix.trace_transpose, Matrix.trace_smul]; ring

/-- **Thesis Prop 3.4**, corrected count: for jets of symmetric trace-free `E`, `B`, the linearized
Bianchi identity is equivalent to the 6 constraints `div E = div B = 0` and the symmetric parts
`Ė + sym curl B = 0`, `Ḃ - sym curl E = 0` of the evolution equations.

Refinement: the thesis counts "6 constraints + 18 evolution equations" (at most 24
conditions); only 16 of them are independent on symmetric trace-free jets. The trace parts of the
evolution equations are `0 = 0` (`trace_curl_of_transpose_eq`) and the skew parts repeat the constraints
(`transpose_curl_eq`), so the content is 6 constraints plus 10 evolution equations (each `sym curl`
equation is valued in symmetric trace-free matrices, a 5-dimensional space); see
`EBJetSym_surjective` for the independence of these 16 equations.

See [QuennevilleBelair2015], §3.4, Prop 3.4. -/
theorem linBianchi_iff_sym (dE dB : Jet4) (hE : IsSymTF dE) (hB : IsSymTF dB) :
    (∀ α β γ δ θ, bianchi2 dE dB α β γ δ θ = 0) ↔ EBJetSym dE dB := by
  rw [linBianchi_iff dE dB (fun μ => (hE μ).1) (fun μ => (hB μ).1)]
  have cE : ∀ (hd : div (sp dE) = 0), symPart (curl (sp dE)) = curl (sp dE) := fun hd =>
    symPart_of_transpose_eq (transpose_curl_eq (fun c => (hE c.succ).1) (funext fun c => (hE c.succ).2) hd)
  have cB : ∀ (hd : div (sp dB) = 0), symPart (curl (sp dB)) = curl (sp dB) := fun hd =>
    symPart_of_transpose_eq (transpose_curl_eq (fun c => (hB c.succ).1) (funext fun c => (hB c.succ).2) hd)
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, by rw [cB h2]; exact h3, by rw [cE h1]; exact h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, by rw [← cB h2]; exact h3, by rw [← cE h1]; exact h4⟩

/-- The spatial part of `Fin.cons X f` is `f`. -/
@[simp] theorem sp_cons (X : Matrix (Fin 3) (Fin 3) ℝ) (f : SpaceJet) :
    sp (Fin.cons X f : Jet4) = f := by
  funext c; simp [sp]

/-- A spatial jet of symmetric trace-free matrices with prescribed divergence `v`:
`∂_c A = (3/10)(v ⊗ e_c + e_c ⊗ v - (2/3) v_c I)`. -/
def divJet (v : Fin 3 → ℝ) : SpaceJet := fun c => (3 / 10 : ℝ) • Matrix.of fun a b =>
  v a * (if b = c then 1 else 0) + (if a = c then 1 else 0) * v b -
    2 / 3 * v c * (if a = b then 1 else 0)

/-- `divJet v` is a jet of symmetric matrices (Thesis Prop 3.4, count). -/
theorem divJet_symm (v : Fin 3 → ℝ) (c : Fin 3) : (divJet v c)ᵀ = divJet v c := by
  ext a b; fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [divJet, Matrix.transpose_apply]

/-- `divJet v` is a jet of trace-free matrices (Thesis Prop 3.4, count). -/
theorem divJet_trace (v : Fin 3 → ℝ) (c : Fin 3) : (divJet v c).trace = 0 := by
  fin_cases c <;> simp [divJet, Matrix.trace, Fin.sum_univ_three] <;> ring

/-- `div (divJet v) = v` (Thesis Prop 3.4, count). -/
theorem div_divJet (v : Fin 3 → ℝ) : div (divJet v) = v := by
  ext a; fin_cases a <;> simp [div, divJet, Fin.sum_univ_three] <;> ring

/-- **Thesis Prop 3.4**, independence of the 16 equations: on jets of symmetric trace-free
`E`, `B`, the map `(dE, dB) ↦ (div E, div B, Ė + sym curl B, Ḃ - sym curl E)` is onto
`ℝ³ × ℝ³ × Sym₀ × Sym₀` (dimension `3 + 3 + 5 + 5 = 16`). Together with `linBianchi_iff_sym`,
on such jets the Bianchi identity is equivalent to 16 independent equations: 6 constraints
plus 10 evolution equations.

Refinement: the thesis counts "6 constraints + 18 evolution equations" (at most 24
conditions) without determining how many are independent; the answer is 16.

See [QuennevilleBelair2015], §3.4, Prop 3.4. -/
theorem EBJetSym_surjective (v w : Fin 3 → ℝ) (P Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hP : Pᵀ = P ∧ P.trace = 0) (hQ : Qᵀ = Q ∧ Q.trace = 0) :
    ∃ dE dB : Jet4, IsSymTF dE ∧ IsSymTF dB ∧ div (sp dE) = v ∧ div (sp dB) = w ∧
      dE 0 + symPart (curl (sp dB)) = P ∧ dB 0 - symPart (curl (sp dE)) = Q := by
  refine ⟨Fin.cons (P - symPart (curl (divJet w))) (divJet v),
    Fin.cons (Q + symPart (curl (divJet v))) (divJet w), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro μ
    refine Fin.cases ?_ (fun c => ?_) μ
    · simp only [Fin.cons_zero]
      refine ⟨by rw [Matrix.transpose_sub, transpose_symPart, hP.1], ?_⟩
      rw [Matrix.trace_sub, trace_symPart, trace_curl_of_transpose_eq (divJet_symm w), hP.2, sub_zero]
    · simp only [Fin.cons_succ]; exact ⟨divJet_symm v c, divJet_trace v c⟩
  · intro μ
    refine Fin.cases ?_ (fun c => ?_) μ
    · simp only [Fin.cons_zero]
      refine ⟨by rw [Matrix.transpose_add, transpose_symPart, hQ.1], ?_⟩
      rw [Matrix.trace_add, trace_symPart, trace_curl_of_transpose_eq (divJet_symm v), hQ.2, add_zero]
    · simp only [Fin.cons_succ]; exact ⟨divJet_symm w c, divJet_trace w c⟩
  · exact div_divJet v
  · exact div_divJet w
  · simp
  · simp

/-! ## Prop 3.6: the algebraic core of constraint propagation -/

/-- **Thesis Prop 3.6, proof, step 1 (jet level)**: if `Ė = -curl B` and `Ḃ = curl E`, then
`∂_t div E = 0` and `∂_t div B = 0`. Here `d2E μ c = ∂_μ ∂_c E` are second jets, symmetric in
`(μ, c)`. The divergence constraints thus propagate without any uniqueness argument
(field version: `div_const_field`).

Thesis gap: the thesis proves Prop 3.6 only by a forward reference to Cor 4.5 (cited as
"Theorem 4.5"), whose hypotheses it never verifies; this step is missing.

See [QuennevilleBelair2015], Prop 3.6, Cor 4.5. -/
theorem div_propagation (d2E d2B : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℝ)
    (hsE : ∀ μ ν, d2E μ ν = d2E ν μ) (hsB : ∀ μ ν, d2B μ ν = d2B ν μ)
    (hE : ∀ c : Fin 3, d2E c.succ 0 = -curl (sp (d2B c.succ)))
    (hB : ∀ c : Fin 3, d2B c.succ 0 = curl (sp (d2E c.succ))) :
    div (fun c : Fin 3 => d2E 0 c.succ) = 0 ∧ div (fun c : Fin 3 => d2B 0 c.succ) = 0 := by
  have h1 : (fun c : Fin 3 => d2E 0 c.succ) =
      fun c : Fin 3 => -curl (fun b : Fin 3 => d2B c.succ b.succ) := by
    funext c; rw [hsE, hE]; rfl
  have h2 : (fun c : Fin 3 => d2B 0 c.succ) =
      fun c : Fin 3 => curl (fun b : Fin 3 => d2E c.succ b.succ) := by
    funext c; rw [hsB, hB]; rfl
  have dB0 := div_curl (fun c b : Fin 3 => d2B c.succ b.succ) (fun _ _ => hsB _ _)
  have dE0 := div_curl (fun c b : Fin 3 => d2E c.succ b.succ) (fun _ _ => hsE _ _)
  refine ⟨?_, ?_⟩
  · rw [h1]; ext a; have := congrFun dB0 a
    simp only [div, Pi.zero_apply, Matrix.neg_apply, Finset.sum_neg_distrib] at this ⊢
    rw [this, neg_zero]
  · rw [h2]; exact dE0

/-- **Thesis Prop 3.6, proof, step 2 (closed system for the violations)**: write `a = tr E`,
`α = vskw E`, `b = tr B`, `β = vskw B`. If `Ė = -curl B` and `Ḃ = curl E` (first jets), then
`ȧ = 2 div β`, `α̇ = -½ grad b - curl β + ½ div B`, `ḃ = -2 div α`,
`β̇ = ½ grad a + curl α - ½ div E`.
With `div E = div B = 0` (step 1), `(a, α, b, β)` solves a closed homogeneous first-order system.

Thesis gap: not in the thesis (it relies on Cor 4.5 instead).
Cf. [QuennevilleBelair2015], Prop 3.6, Cor 4.5. -/
theorem violation_evolution (dE dB : Jet4) (hE : dE 0 = -curl (sp dB))
    (hB : dB 0 = curl (sp dE)) :
    (dE 0).trace = 2 * vdiv (vskwJ (sp dB)) ∧
    vskw (dE 0) = -(1 / 2 : ℝ) • traceJet (sp dB) - vcurl (vskwJ (sp dB)) +
      (1 / 2 : ℝ) • div (sp dB) ∧
    (dB 0).trace = -2 * vdiv (vskwJ (sp dE)) ∧
    vskw (dB 0) = (1 / 2 : ℝ) • traceJet (sp dE) + vcurl (vskwJ (sp dE)) -
      (1 / 2 : ℝ) • div (sp dE) := by
  rw [hE, hB]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.trace_neg, trace_curl_eq_vskw]; unfold vskwJ; ring
  · ext a
    fin_cases a <;>
      simp [vskw_apply, invOf_eq_inv, curl, traceJet, vcurl, vskwJ, div, Matrix.trace, leviCivita3_apply,
        Fin.sum_univ_three] <;> ring
  · rw [trace_curl_eq_vskw]; rfl
  · ext a
    fin_cases a <;>
      simp [vskw_apply, invOf_eq_inv, curl, traceJet, vcurl, vskwJ, div, Matrix.trace, leviCivita3_apply,
        Fin.sum_univ_three] <;> ring

/-- The violation energy density `e = (tr E)² + 4|vskw E|² + (tr B)² + 4|vskw B|²`
(zero iff `E` and `B` are symmetric and trace-free). -/
def energy (E B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  E.trace ^ 2 + 4 * (vskw E ⬝ᵥ vskw E) + B.trace ^ 2 + 4 * (vskw B ⬝ᵥ vskw B)

/-- The violation flux `F = 2 (tr E) vskw B - 2 (tr B) vskw E + 4 vskw E × vskw B`. -/
def flux (E B : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  (2 * E.trace) • vskw B - (2 * B.trace) • vskw E + (4 : ℝ) • (vskw E ⨯₃ vskw B)

/-- Directional derivative of `energy` at `(E, B)` in the direction `(dE, dB)`. -/
def energyD (E B dE dB : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  2 * E.trace * dE.trace + 8 * (vskw E ⬝ᵥ vskw dE) + 2 * B.trace * dB.trace +
    8 * (vskw B ⬝ᵥ vskw dB)

/-- Directional derivative of `flux` at `(E, B)` in the direction `(dE, dB)`. -/
def fluxD (E B dE dB : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  (2 * dE.trace) • vskw B + (2 * E.trace) • vskw dB - (2 * dB.trace) • vskw E -
    (2 * B.trace) • vskw dE + (4 : ℝ) • (vskw dE ⨯₃ vskw B + vskw E ⨯₃ vskw dB)

/-- `e ≥ 0`. -/
theorem energy_nonneg (E B : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ energy E B := by
  unfold energy
  have h1 := dotProduct_self_star_nonneg (vskw E)
  have h2 := dotProduct_self_star_nonneg (vskw B)
  simp only [star_trivial] at h1 h2
  positivity

/-- `e = 0` iff `E` and `B` are symmetric and trace-free. -/
theorem energy_eq_zero_iff (E B : Matrix (Fin 3) (Fin 3) ℝ) :
    energy E B = 0 ↔ (Eᵀ = E ∧ E.trace = 0) ∧ (Bᵀ = B ∧ B.trace = 0) := by
  simp only [transpose_eq_iff_vskw_eq_zero]
  have h1 := dotProduct_self_star_nonneg (vskw E)
  have h2 := dotProduct_self_star_nonneg (vskw B)
  have z1 := dotProduct_self_star_eq_zero (v := vskw E)
  have z2 := dotProduct_self_star_eq_zero (v := vskw B)
  simp only [star_trivial] at h1 h2 z1 z2
  unfold energy
  constructor
  · intro h
    have a1 : E.trace ^ 2 = 0 := by nlinarith [sq_nonneg E.trace, sq_nonneg B.trace]
    have a2 : B.trace ^ 2 = 0 := by nlinarith [sq_nonneg E.trace, sq_nonneg B.trace]
    have a3 : vskw E ⬝ᵥ vskw E = 0 := by nlinarith [sq_nonneg E.trace, sq_nonneg B.trace]
    have a4 : vskw B ⬝ᵥ vskw B = 0 := by nlinarith [sq_nonneg E.trace, sq_nonneg B.trace]
    exact ⟨⟨z1.1 a3, pow_eq_zero_iff (n := 2) (by norm_num) |>.1 a1⟩,
      ⟨z2.1 a4, pow_eq_zero_iff (n := 2) (by norm_num) |>.1 a2⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    simp [h1, h2, h3, h4]

/-- **Thesis Prop 3.6, proof, step 3 (energy flux identity, jet level)**: if `Ė = -curl B`,
`Ḃ = curl E` and `div E = div B = 0` at a point, then `½ ∂_t e = div F`, with `e = energy E B`
and `F = flux E B` (both differentiated by the product rule: `energyD`, `fluxD`).

Thesis gap: not in the thesis; this replaces the unverified appeal to Cor 4.5 (energy proof on
`ℝ³`; field version `prop_3_6`).
Cf. [QuennevilleBelair2015], Prop 3.6, Cor 4.5. -/
theorem energy_flux (E B : Matrix (Fin 3) (Fin 3) ℝ) (dE dB : Jet4)
    (hE : dE 0 = -curl (sp dB)) (hB : dB 0 = curl (sp dE)) (hdE : div (sp dE) = 0)
    (hdB : div (sp dB) = 0) :
    (1 / 2 : ℝ) * energyD E B (dE 0) (dB 0) = ∑ c, fluxD E B (dE c.succ) (dB c.succ) c := by
  obtain ⟨h1, h2, h3, h4⟩ := violation_evolution dE dB hE hB
  rw [hdE] at h4
  rw [hdB] at h2
  simp only [energyD, fluxD, h1, h3, dotProduct, Fin.sum_univ_three]
  rw [h2, h4]
  simp [vskw_apply, invOf_eq_inv, vcurl, vskwJ, traceJet, sp, vdiv, crossProduct, Matrix.trace, leviCivita3_apply,
    Fin.sum_univ_three]
  ring

end Feec.EinsteinBianchi
