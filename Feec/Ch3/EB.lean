import Feec.Ch3.Bivector
import Feec.Ch2.Linearized

/-!
# Ch 3 §3.3–3.5: the linearized Einstein–Bianchi (EB) system

Linear algebra on jets plus genuine-derivative field versions, in a fixed Minkowski frame
(`x⁰ = t`, spatial index `c : Fin 3` ↔ coordinate `c + 1`). Matrix calculus uses the
foundation's row-wise conventions `(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}`, `(div A)_a = ∂_b A_{ab}`,
`(vskw A)_a = ½ ε_{abc} A_{bc}`; a Weyl field is `C = [[E, B], [B, -E]]` in the bivector block
form of `Feec.Ch3.Bivector` (Prop 3.3).

Coverage (thesis numbering):
* **Lemma 3.5** (jets): `trace_curl` (`tr curl A = -2 div vskw A`), `two_vskw_curl`,
  `two_vskw_curl'` (`2 vskw curl A = grad tr A - div Aᵀ = grad tr A - div A + 2 div skw A`),
  `div_skw` (`div skw A = curl vskw A`), `div_curl`; consequences `trace_curl_of_symm`,
  `curl_symm`, `curl_TSD`. Fields (`C²` on `ℝ³`): `div_curl_field`, `curl_TSD_field`.
* **Prop 3.4** (linearized second Bianchi identity ⇔ EB system): `linBianchi_iff` (jets of
  symmetric `E, B`), `linBianchi_field_iff` (differentiable fields), `linBianchi_iff_sym`
  (reduced form with `sym curl`, for trace-free `E, B`), `EBJetSym_surjective` (the 16 reduced
  equations are independent).
* **Prop 3.6** (constraint propagation): algebraic core `div_propagation`,
  `violation_evolution` (closed system for `(tr E, vskw E, tr B, vskw B)`), `energy_flux`
  (`½ ∂_t e = div F`), `energy_nonneg`, `energy_eq_zero_iff`; field versions
  `div_const_field` and the full theorem `prop_3_6` on `ℝ³` (compact spatial support, `C²`).
* **§3.5** (plane waves): `planeWave_weyl` (the linearized Riemann tensor of the TT wave is
  `[[E, B], [B, -E]]` with explicit `E, B`), `planeWave_EB` (for `f ∈ C³`, `E, B` are
  symmetric, trace-free and solve (3.3)–(3.4) at every point).

Corrections and gaps filled (details in the docstrings):
* `div` and the matrix `curl` are used before being defined; the conventions are fixed here.
* Lemma 3.5: "`A` is then trace-free" should be `curl A`; part (3) needs only symmetry,
  `div A = 0` and `grad tr A = 0`.
* Prop 3.4: the linearization misses the factor `ε`; the equivalence is pointwise and needs
  only `C¹`; it cites Prop 3.2 where Prop 3.3 is meant; of the 24 equations only 16 are
  independent (6 constraints + 10 evolution equations), not "6 + 18".
* Prop 3.6: the thesis' proof is a forward reference to Cor 4.5 ("Theorem 4.5") whose
  hypotheses are never verified (they are only conjectured in Prop 4.17); "`curl E` is TSD"
  should be `curl B`. Here: a direct proof on `ℝ³` by divergence propagation and the energy
  method.
* §3.5: `A₋` should be `Aₓ`; `f ∈ C³` (not `C²`) is needed.

Not formalized: the nonlinear EB system of §3.4 (quoted from Anderson–Choquet-Bruhat–York; it
needs the 3+1 split and extrinsic curvature; its extracted B-equation sign `+ sym curl E` must
be `-` to recover (3.4)); distributional (`H(curl)`) versions of Lemma 3.5; Prop 3.6 on
bounded domains.
-/

open Matrix

noncomputable section

namespace Feec
namespace EB

open Bivector

/-! ## The Levi-Civita symbol in table form -/

/-- `ε_{ijk}` as an explicit table. -/
theorem eps3_explicit (i j k : Fin 3) : eps3 i j k =
    ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]], ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
      ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]] i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [eps3, Matrix.det_fin_three]

/-! ## Vector calculus on jets

A first jet of a vector field `v` is `dv : Fin 3 → Fin 3 → ℝ`, `dv c = ∂_c v`. -/

/-- Vector curl on jets, `(curl v)_a = ε_{abc} ∂_b v_c`. -/
def vcurl (dv : Fin 3 → Fin 3 → ℝ) : Fin 3 → ℝ := fun a => ∑ b, ∑ c, eps3 a b c * dv b c

/-- Vector divergence on jets, `div v = ∂_c v_c`. -/
def vdiv (dv : Fin 3 → Fin 3 → ℝ) : ℝ := ∑ c, dv c c

/-- Jet of `tr A` (that is, `grad tr A`) from the jet of `A`. -/
def trJ (dA : Jet1) : Fin 3 → ℝ := fun c => (dA c).trace

/-- Jet of `vskw A` from the jet of `A`. -/
def vskwJ (dA : Jet1) : Fin 3 → Fin 3 → ℝ := fun c => vskw (dA c)

/-- Jet of `Aᵀ`. -/
def transJ (dA : Jet1) : Jet1 := fun c => (dA c)ᵀ

/-- Jet of `skw A = ½(A - Aᵀ)`. -/
def skwJ (dA : Jet1) : Jet1 := fun c => (1 / 2 : ℝ) • (dA c - (dA c)ᵀ)

/-- Symmetric part `sym A = ½(A + Aᵀ)`. -/
def symm (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (1 / 2 : ℝ) • (A + Aᵀ)

/-- A matrix is symmetric iff its axial vector vanishes. -/
theorem isSymm_iff_vskw_eq_zero (A : Matrix (Fin 3) (Fin 3) ℝ) : Aᵀ = A ↔ vskw A = 0 := by
  constructor
  · intro h
    have hs : ∀ i j, A i j = A j i := fun i j => by
      simpa [Matrix.transpose_apply] using congrFun (congrFun h j) i
    ext a
    fin_cases a <;> simp [vskw, eps3_explicit, Fin.sum_univ_three, hs 1 0, hs 2 0, hs 2 1]
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
    simp [vskw, eps3_explicit, Fin.sum_univ_three] at h0 h1 h2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply] <;> linarith

/-! ## Lemma 3.5 (pointwise, on jets) -/

/-- **Thesis Lemma 3.5 (2)**: `tr curl A = -2 div vskw A`, for an arbitrary first jet.

Thesis gap: neither the matrix `curl` (defined only inside the proof) nor the row-wise `div`
is defined before use; here `(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}` and `(div A)_a = ∂_b A_{ab}`
(foundation `curl`, `div`). The identity is pointwise; for `A ∈ H(curl)` it holds in the
distributional sense by linearity (not formalized). -/
theorem trace_curl (dA : Jet1) : (curl dA).trace = -2 * vdiv (vskwJ dA) := by
  simp [Matrix.trace, curl, vdiv, vskwJ, vskw, eps3_explicit, Fin.sum_univ_three]; ring

/-- **Thesis Lemma 3.5 (3)**: `2 vskw curl A = grad tr A - div Aᵀ`. -/
theorem two_vskw_curl (dA : Jet1) : (2 : ℝ) • vskw (curl dA) = trJ dA - div (transJ dA) := by
  ext a
  fin_cases a <;>
    simp [curl, vskw, trJ, div, transJ, Matrix.trace, eps3_explicit, Fin.sum_univ_three] <;> ring

/-- `div skw A = curl vskw A` (the vector curl of the axial vector). -/
theorem div_skw (dA : Jet1) : div (skwJ dA) = vcurl (vskwJ dA) := by
  ext a
  fin_cases a <;>
    simp [div, skwJ, vcurl, vskwJ, vskw, eps3_explicit, Fin.sum_univ_three] <;> ring

/-- **Thesis Lemma 3.5 (3)**, second form: `2 vskw curl A = grad tr A - div A + 2 div skw A`. -/
theorem two_vskw_curl' (dA : Jet1) :
    (2 : ℝ) • vskw (curl dA) = trJ dA - div dA + (2 : ℝ) • div (skwJ dA) := by
  rw [two_vskw_curl]
  ext a
  simp [div, transJ, skwJ, Fin.sum_univ_three]; ring

/-- **Thesis Lemma 3.5 (1)**: `div curl A = 0`, for a second jet `d2A b c = ∂_b ∂_c A` that is
symmetric in `(b, c)` (Schwarz; see `div_curl_field` for `C²` fields). -/
theorem div_curl (d2A : Fin 3 → Jet1) (hsym : ∀ b c, d2A b c = d2A c b) :
    div (fun b => curl (d2A b)) = 0 := by
  ext a
  fin_cases a <;>
    simp [div, curl, eps3_explicit, Fin.sum_univ_three, hsym 1 0, hsym 2 0, hsym 2 1] <;> ring

/-- Entrywise symmetry of a jet of symmetric matrices. -/
theorem jet_symm {dA : Jet1} (hsym : ∀ c, (dA c)ᵀ = dA c) (c i j : Fin 3) :
    dA c i j = dA c j i := by
  simpa [Matrix.transpose_apply] using congrFun (congrFun (hsym c) j) i

/-- **Thesis Lemma 3.5, consequence**: if `A` is symmetric, then `curl A` is trace-free.

Correction: the thesis writes "the matrix field `A` is then trace-free"; it is `curl A`. -/
theorem trace_curl_of_symm {dA : Jet1} (hsym : ∀ c, (dA c)ᵀ = dA c) : (curl dA).trace = 0 := by
  have hs := jet_symm hsym
  rw [trace_curl]
  simp [vdiv, vskwJ, vskw, eps3_explicit, Fin.sum_univ_three, hs _ 1 0, hs _ 2 0, hs _ 2 1]

/-- **Thesis Lemma 3.5, consequence** (sharpened): if `A` is symmetric with `div A = 0` and
`grad tr A = 0`, then `curl A` is symmetric. Only these three properties are used (the thesis
assumes `A` TSD). -/
theorem curl_symm {dA : Jet1} (hsym : ∀ c, (dA c)ᵀ = dA c) (htr : trJ dA = 0)
    (hdiv : div dA = 0) : (curl dA)ᵀ = curl dA := by
  rw [isSymm_iff_vskw_eq_zero]
  have h := two_vskw_curl dA
  have ht : transJ dA = dA := funext hsym
  rw [ht, htr, hdiv, sub_zero] at h
  have := congrArg (fun v => (1 / 2 : ℝ) • v) h
  simpa [smul_smul] using this

/-- **Thesis Lemma 3.5, conclusion**: `A` TSD (symmetric, trace-free, divergence-free) implies
`curl A` symmetric and trace-free, and (at second order) divergence-free (`div_curl`). -/
theorem curl_TSD {dA : Jet1} (hsym : ∀ c, (dA c)ᵀ = dA c) (htr : ∀ c, (dA c).trace = 0)
    (hdiv : div dA = 0) : (curl dA)ᵀ = curl dA ∧ (curl dA).trace = 0 :=
  ⟨curl_symm hsym (funext htr) hdiv, trace_curl_of_symm hsym⟩

/-! ## Prop 3.4 on jets: the linearized second Bianchi identity

A first jet of a spacetime matrix field is `dX : Fin 4 → Matrix`, `dX μ = ∂_μ X`, with
`μ = 0` the time direction; `sp dX` is its spatial part. -/

/-- First jet of a spacetime matrix field. -/
abbrev Jet4 := Fin 4 → Matrix (Fin 3) (Fin 3) ℝ

/-- Spatial part `(∂_1, ∂_2, ∂_3)` of a spacetime jet. -/
def sp (dX : Jet4) : Jet1 := fun c => dX c.succ

/-- The jet `∂_μ C` of the Weyl field `C = [[E, B], [B, -E]]` (block form of Prop 3.3). -/
def dWeyl (dE dB : Jet4) (μ : Fin 4) : T4 (Fin 4) := T (dE μ) (dB μ) (dB μ) (-dE μ)

/-- The linearized second Bianchi expression `∂_α C_{βγδθ} + ∂_β C_{γαδθ} + ∂_γ C_{αβδθ}`. -/
def bianchi2 (dE dB : Jet4) (α β γ δ θ : Fin 4) : ℝ :=
  dWeyl dE dB α β γ δ θ + dWeyl dE dB β γ α δ θ + dWeyl dE dB γ α β δ θ

/-- The linearized EB system (Thesis (3.3)–(3.4)) on jets:
`div E = 0`, `div B = 0`, `Ė + curl B = 0`, `Ḃ - curl E = 0`. -/
def EBJet (dE dB : Jet4) : Prop :=
  div (sp dE) = 0 ∧ div (sp dB) = 0 ∧ dE 0 + curl (sp dB) = 0 ∧ dB 0 - curl (sp dE) = 0

/-- The reduced form (Thesis Prop 3.4(c) as corrected): constraints plus the symmetric parts
of the evolution equations. -/
def EBJetSym (dE dB : Jet4) : Prop :=
  div (sp dE) = 0 ∧ div (sp dB) = 0 ∧ dE 0 + symm (curl (sp dB)) = 0 ∧
    dB 0 - symm (curl (sp dE)) = 0

/-- The Bianchi expression in bivector components. -/
theorem bianchi2_eq (dE dB : Jet4) (α β γ δ θ : Fin 4) :
    bianchi2 dE dB α β γ δ θ = sgn δ θ *
      (sgn β γ * fromBlocks (dE α) (dB α) (dB α) (-dE α) (pidx β γ) (pidx δ θ)
      + sgn γ α * fromBlocks (dE β) (dB β) (dB β) (-dE β) (pidx γ α) (pidx δ θ)
      + sgn α β * fromBlocks (dE γ) (dB γ) (dB γ) (-dE γ) (pidx α β) (pidx δ θ)) := by
  simp only [bianchi2, dWeyl, T, ofMat_apply]; ring

/-- The 24 scalar components of `EBJet`. -/
private theorem EBJet_iff_components (dE dB : Jet4) : EBJet dE dB ↔
    (∀ a, ∑ b, dE b.succ a b = 0) ∧ (∀ a, ∑ b, dB b.succ a b = 0) ∧
    (∀ a b, dE 0 a b + ∑ c, ∑ d, eps3 b c d * dB c.succ a d = 0) ∧
    (∀ a b, dB 0 a b - ∑ c, ∑ d, eps3 b c d * dE c.succ a d = 0) := by
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
    eps3_explicit, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hEB
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
    eps3_explicit, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hEB
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
    eps3_explicit, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hEB
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
    eps3_explicit, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hEB
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
    eps3_explicit, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hEB
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
    eps3_explicit, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hEB
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
Prop 3.3. Trace-freeness is not needed for this equivalence (all 24 equations are independent
on symmetric jets); it is needed for the count of 16 (`linBianchi_iff_sym`,
`EBJetSym_surjective`). The linearization step "`∇_[α W_βγ]δθ = ∂_[α C_βγ]δθ + O(ε²)`" misses
the factor `ε` on the right; this module starts from the linearized identity. -/
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
      eps3_explicit, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
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

/-- `sym A = A` for symmetric `A` (used in Thesis Prop 3.4(c)). -/
theorem symm_of_isSymm {A : Matrix (Fin 3) (Fin 3) ℝ} (h : Aᵀ = A) : symm A = A := by
  rw [symm, h, ← two_smul ℝ A, smul_smul]; norm_num

/-- `sym A` is symmetric (used in Thesis Prop 3.4(c)). -/
theorem symm_transpose (A : Matrix (Fin 3) (Fin 3) ℝ) : (symm A)ᵀ = symm A := by
  simp [symm, Matrix.transpose_add, add_comm]

/-- `tr sym A = tr A` (used in Thesis Prop 3.4(c)). -/
theorem trace_symm (A : Matrix (Fin 3) (Fin 3) ℝ) : (symm A).trace = A.trace := by
  simp [symm, Matrix.trace_add, Matrix.trace_transpose, Matrix.trace_smul]; ring

/-- **Thesis Prop 3.4**, corrected count: for jets of symmetric trace-free `E`, `B`, the linearized
Bianchi identity is equivalent to the 6 constraints `div E = div B = 0` and the symmetric parts
`Ė + sym curl B = 0`, `Ḃ - sym curl E = 0` of the evolution equations.

Correction: the thesis counts "6 constraints + 18 evolution equations". The trace parts of the
evolution equations are `0 = 0` (`trace_curl_of_symm`) and the skew parts repeat the constraints
(`curl_symm`), so the content is 6 constraints plus 10 evolution equations (each `sym curl`
equation is valued in symmetric trace-free matrices, a 5-dimensional space); see
`EBJetSym_surjective` for the independence of these 16 equations. -/
theorem linBianchi_iff_sym (dE dB : Jet4) (hE : IsSymTF dE) (hB : IsSymTF dB) :
    (∀ α β γ δ θ, bianchi2 dE dB α β γ δ θ = 0) ↔ EBJetSym dE dB := by
  rw [linBianchi_iff dE dB (fun μ => (hE μ).1) (fun μ => (hB μ).1)]
  have cE : ∀ (hd : div (sp dE) = 0), symm (curl (sp dE)) = curl (sp dE) := fun hd =>
    symm_of_isSymm (curl_symm (fun c => (hE c.succ).1) (funext fun c => (hE c.succ).2) hd)
  have cB : ∀ (hd : div (sp dB) = 0), symm (curl (sp dB)) = curl (sp dB) := fun hd =>
    symm_of_isSymm (curl_symm (fun c => (hB c.succ).1) (funext fun c => (hB c.succ).2) hd)
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, by rw [cB h2]; exact h3, by rw [cE h1]; exact h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, by rw [← cB h2]; exact h3, by rw [← cE h1]; exact h4⟩

/-- The spatial part of `Fin.cons X f` is `f`. -/
@[simp] theorem sp_cons (X : Matrix (Fin 3) (Fin 3) ℝ) (f : Jet1) :
    sp (Fin.cons X f : Jet4) = f := by
  funext c; simp [sp]

/-- A spatial jet of symmetric trace-free matrices with prescribed divergence `v`:
`∂_c A = (3/10)(v ⊗ e_c + e_c ⊗ v - (2/3) v_c I)`. -/
def divJet (v : Fin 3 → ℝ) : Jet1 := fun c => (3 / 10 : ℝ) • Matrix.of fun a b =>
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
`ℝ³ × ℝ³ × Sym₀ × Sym₀` (dimension `3 + 3 + 5 + 5 = 16`). So the 24 Bianchi components of
`linBianchi_iff_sym` have rank exactly 16: 6 constraints plus 10 evolution equations.

Thesis gap: the thesis asserts "6 constraints + 18 evolution equations" without checking
independence. -/
theorem EBJetSym_surjective (v w : Fin 3 → ℝ) (P Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hP : Pᵀ = P ∧ P.trace = 0) (hQ : Qᵀ = Q ∧ Q.trace = 0) :
    ∃ dE dB : Jet4, IsSymTF dE ∧ IsSymTF dB ∧ div (sp dE) = v ∧ div (sp dB) = w ∧
      dE 0 + symm (curl (sp dB)) = P ∧ dB 0 - symm (curl (sp dE)) = Q := by
  refine ⟨Fin.cons (P - symm (curl (divJet w))) (divJet v),
    Fin.cons (Q + symm (curl (divJet v))) (divJet w), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro μ
    refine Fin.cases ?_ (fun c => ?_) μ
    · simp only [Fin.cons_zero]
      refine ⟨by rw [Matrix.transpose_sub, symm_transpose, hP.1], ?_⟩
      rw [Matrix.trace_sub, trace_symm, trace_curl_of_symm (divJet_symm w), hP.2, sub_zero]
    · simp only [Fin.cons_succ]; exact ⟨divJet_symm v c, divJet_trace v c⟩
  · intro μ
    refine Fin.cases ?_ (fun c => ?_) μ
    · simp only [Fin.cons_zero]
      refine ⟨by rw [Matrix.transpose_add, symm_transpose, hQ.1], ?_⟩
      rw [Matrix.trace_add, trace_symm, trace_curl_of_symm (divJet_symm v), hQ.2, add_zero]
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
"Theorem 4.5"), whose hypotheses it never verifies; this step is missing. -/
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

Thesis gap: not in the thesis (it relies on Cor 4.5 instead). -/
theorem violation_evolution (dE dB : Jet4) (hE : dE 0 = -curl (sp dB))
    (hB : dB 0 = curl (sp dE)) :
    (dE 0).trace = 2 * vdiv (vskwJ (sp dB)) ∧
    vskw (dE 0) = -(1 / 2 : ℝ) • trJ (sp dB) - vcurl (vskwJ (sp dB)) +
      (1 / 2 : ℝ) • div (sp dB) ∧
    (dB 0).trace = -2 * vdiv (vskwJ (sp dE)) ∧
    vskw (dB 0) = (1 / 2 : ℝ) • trJ (sp dE) + vcurl (vskwJ (sp dE)) -
      (1 / 2 : ℝ) • div (sp dE) := by
  rw [hE, hB]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.trace_neg, trace_curl]; ring
  · ext a
    fin_cases a <;>
      simp [vskw, curl, trJ, vcurl, vskwJ, div, Matrix.trace, eps3_explicit,
        Fin.sum_univ_three] <;> ring
  · rw [trace_curl]
  · ext a
    fin_cases a <;>
      simp [vskw, curl, trJ, vcurl, vskwJ, div, Matrix.trace, eps3_explicit,
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
  simp only [isSymm_iff_vskw_eq_zero]
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
`ℝ³`; field version `prop_3_6`). -/
theorem energy_flux (E B : Matrix (Fin 3) (Fin 3) ℝ) (dE dB : Jet4)
    (hE : dE 0 = -curl (sp dB)) (hB : dB 0 = curl (sp dE)) (hdE : div (sp dE) = 0)
    (hdB : div (sp dB) = 0) :
    (1 / 2 : ℝ) * energyD E B (dE 0) (dB 0) = ∑ c, fluxD E B (dE c.succ) (dB c.succ) c := by
  obtain ⟨h1, h2, h3, h4⟩ := violation_evolution dE dB hE hB
  rw [hdE] at h4
  rw [hdB] at h2
  simp only [energyD, fluxD, h1, h3, dotProduct, Fin.sum_univ_three]
  rw [h2, h4]
  simp [vskw, vcurl, vskwJ, trJ, sp, vdiv, crossProduct, Matrix.trace, eps3_explicit,
    Fin.sum_univ_three]
  ring

/-! ## Fields: partial derivatives and genuine jets -/

section Fields

open Linearized (E4 phaseL kTT ttAmp Rjet jet2)

variable {n : ℕ}

/-- Linearity of `pd` (scalar), on `ℝⁿ`. -/
theorem pd_const_mul' {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x)
    (c : ℝ) (i : Fin n) : pd i (fun y => c * f y) x = c * pd i f x := by
  simp [pd, (hf.hasFDerivAt.const_mul c).fderiv]

/-- Linearity of `pd` (negation), on `ℝⁿ`. -/
theorem pd_neg' (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    pd i (fun y => -f y) x = -pd i f x := by
  simp [pd]

/-- Linearity of `pd` (finite sums), on `ℝⁿ`. -/
theorem pd_sum' {ι : Type*} [Fintype ι] {F : ι → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hF : ∀ c, DifferentiableAt ℝ (F c) x) (i : Fin n) :
    pd i (fun y => ∑ c, F c y) x = ∑ c, pd i (F c) x := by
  have := HasFDerivAt.fun_sum (u := Finset.univ) (fun c _ => (hF c).hasFDerivAt)
  simp [pd, this.fderiv]

/-- Partial derivatives of `C²` functions are differentiable. -/
theorem differentiable_pd' {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin n) :
    Differentiable ℝ (pd i f) :=
  ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
    (by norm_num)

/-- Schwarz on `ℝⁿ`: partial derivatives of a `C²` function commute. -/
theorem pd_comm' {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin n) (x : Fin n → ℝ) :
    pd i (pd j f) x = pd j (pd i f) x := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have key : ∀ u v : Fin n → ℝ, fderiv ℝ (fun y => fderiv ℝ f y v) x u =
      fderiv ℝ (fderiv ℝ f) x u v := by
    intro u v
    rw [fderiv_clm_apply (hd x) (differentiableAt_const v)]
    simp
  have e : ∀ v : Fin n, pd v f = fun y => fderiv ℝ f y (Pi.single v 1) := fun _ => rfl
  simp only [pd] at *
  rw [e j, e i, key, key]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

/-- Spatial jet `(∂_c A)(x)` of a matrix field on `ℝ³`. -/
def jet3 (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) : Jet1 :=
  fun c => Matrix.of fun a b => pd c (fun y => A y a b) x

/-- The matrix field `curl A`. -/
def curlF (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ := curl (jet3 A x)

/-- **Thesis Lemma 3.5 (1)** for fields: `div curl A = 0` for a `C²` matrix field on `ℝ³`.

Thesis gap: the thesis uses symmetry of second derivatives without stating any regularity;
here `A ∈ C²` (distributional version for `A ∈ H(curl)` not formalized). -/
theorem div_curl_field {A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ a b, ContDiff ℝ 2 fun y => A y a b) (x : Fin 3 → ℝ) :
    div (jet3 (curlF A) x) = 0 := by
  have hd : ∀ c a d, Differentiable ℝ (pd c fun y => A y a d) := fun c a d =>
    differentiable_pd' (hA a d) c
  have e : ∀ b, jet3 (curlF A) x b =
      curl (fun c => Matrix.of fun a d => pd b (pd c fun y => A y a d) x) := by
    intro b; ext a b'
    simp only [jet3, curlF, curl, Matrix.of_apply]
    rw [pd_sum' (fun c => (Differentiable.fun_sum fun d _ =>
      ((hd c a d).const_mul (eps3 b' c d))) x)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [pd_sum' (fun d => ((hd c a d).const_mul _) x)]
    exact Finset.sum_congr rfl fun d _ => pd_const_mul' ((hd c a d) x) _ _
  rw [show jet3 (curlF A) x = fun b => curl (fun c => Matrix.of fun a d =>
      pd b (pd c fun y => A y a d) x) from funext e]
  exact div_curl _ fun b c => by ext a d; simp [pd_comm' (hA a d)]

/-- **Thesis Lemma 3.5, conclusion** for fields: if a `C²` matrix field `A` on `ℝ³` is TSD
(symmetric, trace-free and divergence-free everywhere), then so is `curl A`. -/
theorem curl_TSD_field {A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ a b, ContDiff ℝ 2 fun y => A y a b) (hsym : ∀ y, (A y)ᵀ = A y)
    (htr : ∀ y, (A y).trace = 0) (hdiv : ∀ y, div (jet3 A y) = 0) (x : Fin 3 → ℝ) :
    (curlF A x)ᵀ = curlF A x ∧ (curlF A x).trace = 0 ∧ div (jet3 (curlF A) x) = 0 := by
  have hjs : ∀ c, (jet3 A x c)ᵀ = jet3 A x c := by
    intro c; ext i j
    simp only [jet3, Matrix.transpose_apply, Matrix.of_apply]
    congr 1; funext y
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hsym y) i) j
  have hjt : ∀ c, (jet3 A x c).trace = 0 := by
    intro c
    have hd : ∀ i, DifferentiableAt ℝ (fun y => A y i i) x := fun i =>
      ((hA i i).differentiable (by norm_num)) x
    have h1 : (jet3 A x c).trace = pd c (fun y => ∑ i, A y i i) x := by
      rw [pd_sum' hd]; rfl
    have h2 : (fun y => ∑ i, A y i i) = fun _ => 0 := funext htr
    rw [h1, h2]; simp [pd]
  obtain ⟨h1, h2⟩ := curl_TSD hjs hjt (hdiv x)
  exact ⟨h1, h2, div_curl_field hA x⟩

/-- Spacetime jet `(∂_μ X)(p)` of a matrix field on `ℝ⁴`. -/
def jet4 (M : E4 → Matrix (Fin 3) (Fin 3) ℝ) (p : E4) : Jet4 :=
  fun μ => Matrix.of fun i j => pd μ (fun y => M y i j) p

/-- Jets of symmetric fields are symmetric. -/
theorem jet4_symm {M : E4 → Matrix (Fin 3) (Fin 3) ℝ} (hM : ∀ y, (M y)ᵀ = M y) (p : E4)
    (μ : Fin 4) : (jet4 M p μ)ᵀ = jet4 M p μ := by
  ext i j
  simp only [jet4, Matrix.transpose_apply, Matrix.of_apply]
  congr 1; funext y
  simpa [Matrix.transpose_apply] using congrFun (congrFun (hM y) i) j

/-- The jet of the Weyl field `[[E, B], [B, -E]]` is `dWeyl` of the jets of `E` and `B`. -/
theorem pd_weyl {E B : E4 → Matrix (Fin 3) (Fin 3) ℝ} {p : E4}
    (hE : ∀ i j, DifferentiableAt ℝ (fun y => E y i j) p)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y => B y i j) p) (α β γ δ θ : Fin 4) :
    pd α (fun y => T (E y) (B y) (B y) (-E y) β γ δ θ) p =
      dWeyl (jet4 E p) (jet4 B p) α β γ δ θ := by
  simp only [dWeyl, T, ofMat_apply]
  generalize pidx β γ = I
  generalize pidx δ θ = J
  rcases I with i | i <;> rcases J with j | j <;>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.neg_apply, jet4, Matrix.of_apply]
  · exact pd_const_mul' (hE i j) _ _
  · exact pd_const_mul' (hB i j) _ _
  · exact pd_const_mul' (hB i j) _ _
  · simp only [mul_neg]
    rw [pd_neg', pd_const_mul' (hE i j)]

/-- **Thesis Prop 3.4** (field version): let `E, B : ℝ⁴ → Sym(3)` be differentiable and
`C = [[E, B], [B, -E]]`. At each point, the linearized second Bianchi identity
`∂_α C_{βγδθ} + ∂_β C_{γαδθ} + ∂_γ C_{αβδθ} = 0` holds iff `div E = div B = 0`,
`Ė + curl B = 0` and `Ḃ - curl E = 0` there.

Thesis gap: the equivalence is pointwise and only needs `C ∈ C¹` (differentiability at the
point suffices); see `linBianchi_iff` for the remaining corrections. -/
theorem linBianchi_field_iff {E B : E4 → Matrix (Fin 3) (Fin 3) ℝ} (p : E4)
    (hEs : ∀ y, (E y)ᵀ = E y) (hBs : ∀ y, (B y)ᵀ = B y)
    (hE : ∀ i j, DifferentiableAt ℝ (fun y => E y i j) p)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y => B y i j) p) :
    (∀ α β γ δ θ, pd α (fun y => T (E y) (B y) (B y) (-E y) β γ δ θ) p +
        pd β (fun y => T (E y) (B y) (B y) (-E y) γ α δ θ) p +
        pd γ (fun y => T (E y) (B y) (B y) (-E y) α β δ θ) p = 0) ↔
      EBJet (jet4 E p) (jet4 B p) := by
  simp only [pd_weyl hE hB]
  exact linBianchi_iff _ _ (jet4_symm hEs p) (jet4_symm hBs p)

/-! ### §3.5: plane waves -/

/-- Electric amplitude of the §3.5 plane wave (same matrix as Ch 7). -/
def ampE (Ap Ax : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-Ap, -Ax, 0; -Ax, Ap, 0; 0, 0, 0]

/-- Magnetic amplitude of the §3.5 plane wave. -/
def ampB (Ap Ax : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-Ax, Ap, 0; Ap, Ax, 0; 0, 0, 0]

/-- **Thesis §3.5** (symbol level): the linearized Riemann tensor of the TT 2-jet
`∂_i∂_j h_ab = k_i k_j A_ab s` (`k = κ(-1, 0, 0, 1)`, `A = ttAmp A₊ Aₓ`, `s = f''`) is the Weyl
tensor `[[E, B], [B, -E]]` with `E = (κ²/2) s · ampE`, `B = (κ²/2) s · ampB`.

Correction: the thesis writes the amplitudes `A₊` and `A₋`; the second is `Aₓ`. Its list of
"non-zero components" is complete only up to the Riemann symmetries; here the full tensor is
identified. -/
theorem planeWave_weyl (κ Ap Ax s : ℝ) :
    Rjet (fun i j a b => kTT κ i * kTT κ j * ttAmp Ap Ax a b * s) =
      T ((κ ^ 2 / 2 * s) • ampE Ap Ax) ((κ ^ 2 / 2 * s) • ampB Ap Ax)
        ((κ ^ 2 / 2 * s) • ampB Ap Ax) (-((κ ^ 2 / 2 * s) • ampE Ap Ax)) := by
  rw [eq_T_blocks (Linearized.Rjet_pairSkew (Linearized.ttWaveJet_props κ Ap Ax s).1)]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [blkE, blkB, blkH, blkD, toMat, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, p, q, Rjet, kTT, ttAmp, ampE, ampB] <;> ring

/-- The §3.5 electric field `E(x) = (κ²/2) f''(k·x) ampE`. -/
def waveE (κ Ap Ax : ℝ) (f : ℝ → ℝ) (y : E4) : Matrix (Fin 3) (Fin 3) ℝ :=
  (κ ^ 2 / 2 * deriv (deriv f) (phaseL (kTT κ) y)) • ampE Ap Ax

/-- The §3.5 magnetic field `B(x) = (κ²/2) f''(k·x) ampB`. -/
def waveB (κ Ap Ax : ℝ) (f : ℝ → ℝ) (y : E4) : Matrix (Fin 3) (Fin 3) ℝ :=
  (κ ^ 2 / 2 * deriv (deriv f) (phaseL (kTT κ) y)) • ampB Ap Ax

/-- The spacetime jet of `(κ²/2) f''(k·x) P` (Thesis §3.5). -/
private theorem jet4_wave {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (κ : ℝ)
    (P : Matrix (Fin 3) (Fin 3) ℝ) (p : E4) :
    jet4 (fun y => (κ ^ 2 / 2 * deriv (deriv f) (phaseL (kTT κ) y)) • P) p =
      fun μ => (κ ^ 2 / 2 * kTT κ μ * deriv (deriv (deriv f)) (phaseL (kTT κ) p)) • P := by
  have h3 : Differentiable ℝ (deriv (deriv f)) := by
    have := hf.differentiable_iteratedDeriv 2 (by norm_num)
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  funext μ; ext i j
  simp only [jet4, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have e : (fun y => κ ^ 2 / 2 * deriv (deriv f) (phaseL (kTT κ) y) * P i j) =
      fun y => (κ ^ 2 / 2 * P i j) * deriv (deriv f) (phaseL (kTT κ) y) := by
    funext y; ring
  rw [e, Linearized.pd_wave h3]
  ring

/-- **Thesis §3.5**: for `f ∈ C³`, the plane wave `h_ab = ttAmp_ab f(κ(x³ - x⁰))` produces the
linearized Weyl field `[[E, B], [B, -E]] = Rjet(∂∂h)` with `E = waveE`, `B = waveB`, and these
are symmetric, trace-free and solve the linearized EB system (3.3)–(3.4) at every point
(`div E = div B = 0`, `Ė + curl B = 0`, `Ḃ - curl E = 0`).

Thesis gap: `f ∈ C²` is assumed at first, but the EB equations involve `f'''`, so `f ∈ C³` is
needed (the thesis notes this at the end). -/
theorem planeWave_EB {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (κ Ap Ax : ℝ) (p : E4) :
    Rjet (jet2 (fun y a b => ttAmp Ap Ax a b * f (phaseL (kTT κ) y)) p) =
      T (waveE κ Ap Ax f p) (waveB κ Ap Ax f p) (waveB κ Ap Ax f p) (-waveE κ Ap Ax f p) ∧
    ((waveE κ Ap Ax f p)ᵀ = waveE κ Ap Ax f p ∧ (waveE κ Ap Ax f p).trace = 0) ∧
    ((waveB κ Ap Ax f p)ᵀ = waveB κ Ap Ax f p ∧ (waveB κ Ap Ax f p).trace = 0) ∧
    EBJet (jet4 (waveE κ Ap Ax f) p) (jet4 (waveB κ Ap Ax f) p) := by
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [Linearized.jet2_wave (hf.of_le (by norm_num))]
    simp only [waveE, waveB]
    rw [← planeWave_weyl κ Ap Ax (deriv (deriv f) (phaseL (kTT κ) p))]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [waveE, ampE]
  · simp [waveE, ampE, Matrix.trace, Fin.sum_univ_three]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [waveB, ampB]
  · simp [waveB, ampB, Matrix.trace, Fin.sum_univ_three]
  · have e1 : waveE κ Ap Ax f = fun y =>
        (κ ^ 2 / 2 * deriv (deriv f) (phaseL (kTT κ) y)) • ampE Ap Ax := rfl
    have e2 : waveB κ Ap Ax f = fun y =>
        (κ ^ 2 / 2 * deriv (deriv f) (phaseL (kTT κ) y)) • ampB Ap Ax := rfl
    rw [e1, e2, jet4_wave hf, jet4_wave hf]
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext i; fin_cases i <;> simp [div, sp, Fin.sum_univ_three, kTT, ampE]
    · ext i; fin_cases i <;> simp [div, sp, Fin.sum_univ_three, kTT, ampB]
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [curl, sp, eps3_explicit, Fin.sum_univ_three, kTT, ampE, ampB]
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [curl, sp, eps3_explicit, Fin.sum_univ_three, kTT, ampE, ampB]

end Fields

/-! ## Prop 3.6 on `ℝ³`: constraint propagation by the energy method -/

section Calculus

/-! ### Regularity and product rules for the violation energy and flux -/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {M N P Q : X → Matrix (Fin 3) (Fin 3) ℝ}

/-- Components of the violation flux (Thesis Prop 3.6, energy step). -/
theorem flux_apply (E B : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3) :
    flux E B c = 2 * E.trace * vskw B c - 2 * B.trace * vskw E c +
      4 * (vskw E ⨯₃ vskw B) c := by
  simp [flux]

/-- Components of the linearized violation flux (Thesis Prop 3.6, energy step). -/
theorem fluxD_apply (E B dE dB : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3) :
    fluxD E B dE dB c = 2 * dE.trace * vskw B c + 2 * E.trace * vskw dB c -
      2 * dB.trace * vskw E c - 2 * B.trace * vskw dE c +
      4 * ((vskw dE ⨯₃ vskw B) c + (vskw E ⨯₃ vskw dB) c) := by
  simp [fluxD]; ring

/-- `tr M` is `C¹` if `M` is (regularity for Thesis Prop 3.6). -/
theorem cd_trace (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j) :
    ContDiff ℝ 1 fun y => (M y).trace := by
  simp only [Matrix.trace, Matrix.diag]
  exact ContDiff.sum fun i _ => hM i i

/-- `vskw M` is `C¹` if `M` is (regularity for Thesis Prop 3.6). -/
theorem cd_vskw (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j) (a : Fin 3) :
    ContDiff ℝ 1 fun y => vskw (M y) a := by
  simp only [vskw]
  exact contDiff_const.mul
    (ContDiff.sum fun b _ => ContDiff.sum fun c _ => contDiff_const.mul (hM b c))

/-- Dot products of `C¹` vector fields are `C¹` (regularity for Thesis Prop 3.6). -/
theorem cd_dot {u v : X → Fin 3 → ℝ} (hu : ∀ a, ContDiff ℝ 1 fun y => u y a)
    (hv : ∀ a, ContDiff ℝ 1 fun y => v y a) : ContDiff ℝ 1 fun y => u y ⬝ᵥ v y := by
  simp only [dotProduct]
  exact ContDiff.sum fun a _ => (hu a).mul (hv a)

/-- Cross products of `C¹` vector fields are `C¹` (regularity for Thesis Prop 3.6). -/
theorem cd_cross {u v : X → Fin 3 → ℝ} (hu : ∀ a, ContDiff ℝ 1 fun y => u y a)
    (hv : ∀ a, ContDiff ℝ 1 fun y => v y a) (a : Fin 3) :
    ContDiff ℝ 1 fun y => (u y ⨯₃ v y) a := by
  fin_cases a <;> simp only [cross_apply] <;> simp
  · exact ((hu 1).mul (hv 2)).sub ((hu 2).mul (hv 1))
  · exact ((hu 2).mul (hv 0)).sub ((hu 0).mul (hv 2))
  · exact ((hu 0).mul (hv 1)).sub ((hu 1).mul (hv 0))

/-- `energyD` of `C¹` fields is `C¹` (regularity for Thesis Prop 3.6). -/
theorem cd_energyD (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j)
    (hN : ∀ i j, ContDiff ℝ 1 fun y => N y i j) (hP : ∀ i j, ContDiff ℝ 1 fun y => P y i j)
    (hQ : ∀ i j, ContDiff ℝ 1 fun y => Q y i j) :
    ContDiff ℝ 1 fun y => energyD (M y) (N y) (P y) (Q y) := by
  unfold energyD
  exact ((((contDiff_const.mul (cd_trace hM)).mul (cd_trace hP)).add
    (contDiff_const.mul (cd_dot (cd_vskw hM) (cd_vskw hP)))).add
    ((contDiff_const.mul (cd_trace hN)).mul (cd_trace hQ))).add
    (contDiff_const.mul (cd_dot (cd_vskw hN) (cd_vskw hQ)))

/-- The violation energy of `C¹` fields is `C¹` (regularity for Thesis Prop 3.6). -/
theorem cd_energy (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j)
    (hN : ∀ i j, ContDiff ℝ 1 fun y => N y i j) :
    ContDiff ℝ 1 fun y => energy (M y) (N y) := by
  unfold energy
  exact ((((cd_trace hM).pow 2).add (contDiff_const.mul (cd_dot (cd_vskw hM) (cd_vskw hM)))).add
    ((cd_trace hN).pow 2)).add (contDiff_const.mul (cd_dot (cd_vskw hN) (cd_vskw hN)))

/-- The violation flux of `C¹` fields is `C¹` (regularity for Thesis Prop 3.6). -/
theorem cd_flux (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j)
    (hN : ∀ i j, ContDiff ℝ 1 fun y => N y i j) (c : Fin 3) :
    ContDiff ℝ 1 fun y => flux (M y) (N y) c := by
  simp only [flux_apply]
  exact (((contDiff_const.mul (cd_trace hM)).mul (cd_vskw hN c)).sub
    ((contDiff_const.mul (cd_trace hN)).mul (cd_vskw hM c))).add
    (contDiff_const.mul (cd_cross (cd_vskw hM) (cd_vskw hN) c))

/-- `fluxD` of `C¹` fields is `C¹` (regularity for Thesis Prop 3.6). -/
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

/-- Derivative of `tr m(r)` along a curve (product rules for Thesis Prop 3.6). -/
theorem hd_trace (hm : ∀ i j, HasDerivAt (fun r => m r i j) (m' i j) s) :
    HasDerivAt (fun r => (m r).trace) m'.trace s := by
  simp only [Matrix.trace, Matrix.diag]
  exact HasDerivAt.fun_sum fun i _ => hm i i

/-- Derivative of `vskw m(r)` along a curve (product rules for Thesis Prop 3.6). -/
theorem hd_vskw (hm : ∀ i j, HasDerivAt (fun r => m r i j) (m' i j) s) (a : Fin 3) :
    HasDerivAt (fun r => vskw (m r) a) (vskw m' a) s := by
  simp only [vskw]
  exact (HasDerivAt.fun_sum fun b _ => HasDerivAt.fun_sum fun c _ =>
    (hm b c).const_mul _).const_mul _

/-- Product rule for the dot product (Thesis Prop 3.6). -/
theorem hd_dot {u v : ℝ → Fin 3 → ℝ} {u' v' : Fin 3 → ℝ}
    (hu : ∀ a, HasDerivAt (fun r => u r a) (u' a) s)
    (hv : ∀ a, HasDerivAt (fun r => v r a) (v' a) s) :
    HasDerivAt (fun r => u r ⬝ᵥ v r) (u' ⬝ᵥ v s + u s ⬝ᵥ v') s := by
  simp only [dotProduct]
  have := HasDerivAt.fun_sum (u := Finset.univ) fun a _ => (hu a).mul (hv a)
  convert this using 1
  rw [← Finset.sum_add_distrib]

/-- Product rule for the cross product (Thesis Prop 3.6). -/
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

/-- Chain rule for the violation energy: its derivative is `energyD` (Thesis Prop 3.6). -/
theorem hd_energy (hm : ∀ i j, HasDerivAt (fun r => m r i j) (m' i j) s)
    (hn : ∀ i j, HasDerivAt (fun r => n r i j) (n' i j) s) :
    HasDerivAt (fun r => energy (m r) (n r)) (energyD (m s) (n s) m' n') s := by
  have h := ((((hd_trace hm).pow 2).add ((hd_dot (hd_vskw hm) (hd_vskw hm)).const_mul 4)).add
    ((hd_trace hn).pow 2)).add ((hd_dot (hd_vskw hn) (hd_vskw hn)).const_mul 4)
  refine h.congr_deriv ?_
  simp only [energyD, dotProduct_comm (vskw m') (vskw (m s)),
    dotProduct_comm (vskw n') (vskw (n s))]
  push_cast; ring

/-- Chain rule for the violation flux: its derivative is `fluxD` (Thesis Prop 3.6). -/
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

section Prop36

open Linearized (E4)
open MeasureTheory Filter Topology Set

/-- The point `(t, x) ∈ ℝ⁴`. -/
def ev (t : ℝ) (x : Fin 3 → ℝ) : E4 := Fin.cons t x

/-- The time coordinate of `(t, x)`. -/
@[simp] theorem ev_zero (t : ℝ) (x : Fin 3 → ℝ) : ev t x 0 = t := rfl

/-- `(t, x) ↦ (t, x) ∈ ℝ⁴` is continuous. -/
theorem continuous_ev : Continuous fun p : ℝ × (Fin 3 → ℝ) => ev p.1 p.2 := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [ev] using continuous_fst
  · simp only [ev, Fin.cons_succ]
    exact (continuous_apply j).comp continuous_snd

/-- Time slices `x ↦ (t, x)` are smooth. -/
theorem contDiff_ev (t : ℝ) : ContDiff ℝ 1 (ev t) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [ev] using contDiff_const
  · simp only [ev, Fin.cons_succ]
    exact (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).contDiff

/-- `∂_t (t, x) = e₀`. -/
theorem hasDerivAt_ev_time (x : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ev s x) (Pi.single 0 1) t := by
  rw [hasDerivAt_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [ev, Fin.cons_zero, Pi.single_eq_same]
    exact hasDerivAt_id' t
  · simp only [ev, Fin.cons_succ]
    simpa using hasDerivAt_const t (x j)

/-- `∂_s (t, x + s e_c) = e_{c+1}`. -/
theorem hasDerivAt_ev_space (t : ℝ) (x : Fin 3 → ℝ) (c : Fin 3) :
    HasDerivAt (fun s : ℝ => ev t (x + s • Pi.single c 1)) (Pi.single c.succ 1) (0 : ℝ) := by
  rw [hasDerivAt_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [ev] using hasDerivAt_const (0 : ℝ) t
  · have h := ((hasDerivAt_id (0 : ℝ)).mul_const ((Pi.single c (1 : ℝ) : Fin 3 → ℝ) j)).const_add
      (x j)
    convert h using 1
    · funext r; simp [ev]
    · simp [Pi.single_apply, Fin.succ_inj]

/-- Time derivative of a field along `t ↦ (t, x)`. -/
theorem hasDerivAt_time {φ : E4 → ℝ} (hφ : Differentiable ℝ φ) (x : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (fun s => φ (ev s x)) (pd 0 φ (ev t x)) t :=
  (hφ (ev t x)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_ev_time x t)

/-- Spatial derivative of a field along `s ↦ (t, x + s e_c)`. -/
theorem hasDerivAt_space {φ : E4 → ℝ} (hφ : Differentiable ℝ φ) (t : ℝ) (x : Fin 3 → ℝ)
    (c : Fin 3) :
    HasDerivAt (fun s : ℝ => φ (ev t (x + s • Pi.single c 1))) (pd c.succ φ (ev t x)) (0 : ℝ) :=
  (hφ _).hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_ev_space t x c) (by simp)

/-- Spatial partial derivatives of a time slice: `∂_c (φ(t, ·)) = (∂_{c+1} φ)(t, ·)`. -/
theorem fderiv_slice {φ : E4 → ℝ} (hφ : Differentiable ℝ φ) (t : ℝ) (x : Fin 3 → ℝ)
    (c : Fin 3) : fderiv ℝ (fun y => φ (ev t y)) x (Pi.single c 1) = pd c.succ φ (ev t x) := by
  have hg : DifferentiableAt ℝ (fun y => φ (ev t y)) x :=
    (hφ _).comp x ((contDiff_ev t).differentiable (by norm_num) x)
  have hl : HasDerivAt (fun s : ℝ => x + s • Pi.single c (1 : ℝ)) (Pi.single c 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single c (1 : ℝ))).const_add x
  have h1 := hg.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
  exact h1.unique (hasDerivAt_space hφ t x c)

/-- `f(t) = f(0)` for `t ≥ 0` if `f' = 0` on `t > 0`. -/
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

/-- If two functions agree on `{t > 0}`, so do their partial derivatives there. -/
theorem pd_congr_pos {f g : E4 → ℝ} (h : ∀ Z : E4, 0 < Z 0 → f Z = g Z) {Y : E4}
    (hY : 0 < Y 0) (μ : Fin 4) : pd μ f Y = pd μ g Y := by
  have ho : IsOpen {Z : E4 | 0 < Z 0} := isOpen_lt continuous_const (continuous_apply 0)
  have he : f =ᶠ[𝓝 Y] g := Filter.eventuallyEq_of_mem (ho.mem_nhds hY) fun Z hZ => h Z hZ
  simp only [pd, he.fderiv_eq]

/-- Second spacetime jet `∂_μ ∂_ν M` of a matrix field. -/
def jet42 (M : E4 → Matrix (Fin 3) (Fin 3) ℝ) (Y : E4) : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℝ :=
  fun μ ν => Matrix.of fun i j => pd μ (pd ν fun Z => M Z i j) Y

/-- Pointwise TSD: symmetric, trace-free and (row-wise) divergence-free in space. -/
def TSDAt (M : E4 → Matrix (Fin 3) (Fin 3) ℝ) (Y : E4) : Prop :=
  (M Y)ᵀ = M Y ∧ (M Y).trace = 0 ∧ div (sp (jet4 M Y)) = 0

variable {E B : E4 → Matrix (Fin 3) (Fin 3) ℝ}

/-- `∂_μ` of `curl B` is `curl` of the jet of `∂_μ B`. -/
theorem pd_curl (hB : ∀ i j, ContDiff ℝ 2 fun Y => B Y i j) (Y : E4) (μ : Fin 4) (i j : Fin 3) :
    pd μ (fun Z => curl (sp (jet4 B Z)) i j) Y = curl (sp (jet42 B Y μ)) i j := by
  have hd : ∀ c a d, Differentiable ℝ (pd c fun Z => B Z a d) := fun c a d =>
    differentiable_pd' (hB a d) c
  simp only [curl, sp, jet4, jet42, Matrix.of_apply]
  rw [pd_sum' (fun c => (Differentiable.fun_sum fun d _ =>
    ((hd c.succ i d).const_mul (eps3 j c d))) Y)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pd_sum' (fun d => ((hd c.succ i d).const_mul _) Y)]
  exact Finset.sum_congr rfl fun d _ => pd_const_mul' ((hd c.succ i d) Y) _ _

/-- **Thesis Prop 3.6, step 1** (field version): the divergence constraints propagate for
`t ≥ 0`, by `∂_t div E = -div curl B = 0` (`div_propagation`). -/
theorem div_const_field (hEc : ∀ i j, ContDiff ℝ 2 fun Y => E Y i j)
    (hBc : ∀ i j, ContDiff ℝ 2 fun Y => B Y i j)
    (hEeq : ∀ Y : E4, 0 < Y 0 → jet4 E Y 0 = -curl (sp (jet4 B Y)))
    (hBeq : ∀ Y : E4, 0 < Y 0 → jet4 B Y 0 = curl (sp (jet4 E Y)))
    (x : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    div (sp (jet4 E (ev t x))) = div (sp (jet4 E (ev 0 x))) ∧
      div (sp (jet4 B (ev t x))) = div (sp (jet4 B (ev 0 x))) := by
  -- the second jets at `Y` with `Y 0 > 0` satisfy the hypotheses of `div_propagation`
  have prop : ∀ Y : E4, 0 < Y 0 → div (fun c : Fin 3 => jet42 E Y 0 c.succ) = 0 ∧
      div (fun c : Fin 3 => jet42 B Y 0 c.succ) = 0 := by
    intro Y hY
    refine div_propagation (jet42 E Y) (jet42 B Y) ?_ ?_ ?_ ?_
    · intro μ ν; ext i j; exact pd_comm' (hEc i j) μ ν Y
    · intro μ ν; ext i j; exact pd_comm' (hBc i j) μ ν Y
    · intro c; ext i j
      have h := pd_congr_pos (f := pd 0 fun Z => E Z i j)
        (g := fun Z => -curl (sp (jet4 B Z)) i j)
        (fun Z hZ => by
          rw [show pd 0 (fun Z => E Z i j) Z = jet4 E Z 0 i j from rfl, hEeq Z hZ]; rfl)
        hY c.succ
      simp only [jet42, Matrix.of_apply, Matrix.neg_apply] at h ⊢
      rw [h, pd_neg', pd_curl hBc]
    · intro c; ext i j
      have h := pd_congr_pos (f := pd 0 fun Z => B Z i j)
        (g := fun Z => curl (sp (jet4 E Z)) i j)
        (fun Z hZ => by rw [show pd 0 (fun Z => B Z i j) Z = jet4 B Z 0 i j from rfl, hBeq Z hZ])
        hY c.succ
      simp only [jet42, Matrix.of_apply] at h ⊢
      rw [h, pd_curl hEc]
  have key : ∀ (M : E4 → Matrix (Fin 3) (Fin 3) ℝ), (∀ i j, ContDiff ℝ 2 fun Y => M Y i j) →
      (∀ Y : E4, 0 < Y 0 → div (fun c : Fin 3 => jet42 M Y 0 c.succ) = 0) →
      div (sp (jet4 M (ev t x))) = div (sp (jet4 M (ev 0 x))) := by
    intro M hM hP
    ext a
    have hd : ∀ b : Fin 3, Differentiable ℝ (pd b.succ fun Z => M Z a b) := fun b =>
      differentiable_pd' (hM a b) _
    have hψ : Differentiable ℝ fun Y => ∑ b : Fin 3, pd b.succ (fun Z => M Z a b) Y :=
      Differentiable.fun_sum fun b _ => hd b
    have hzero : ∀ s, 0 < s →
        pd 0 (fun Y => ∑ b : Fin 3, pd b.succ (fun Z => M Z a b) Y) (ev s x) = 0 := by
      intro s hs
      have := congrFun (hP (ev s x) hs) a
      simp only [div, jet42, Matrix.of_apply, Pi.zero_apply] at this
      rw [pd_sum' (fun b => hd b _)]
      exact this
    have := const_of_deriv_pos (hasDerivAt_time hψ x) hzero t ht
    simpa [div, sp, jet4] using this
  exact ⟨key E hEc fun Y hY => (prop Y hY).1, key B hBc fun Y hY => (prop Y hY).2⟩

/-- Derivative along a coordinate line through `Y`. -/
theorem hasDerivAt_line {φ : E4 → ℝ} {Y : E4} (hφ : DifferentiableAt ℝ φ Y) (μ : Fin 4) :
    HasDerivAt (fun r : ℝ => φ (Y + r • Pi.single μ 1)) (pd μ φ Y) (0 : ℝ) := by
  have hl : HasDerivAt (fun r : ℝ => Y + r • Pi.single μ (1 : ℝ)) (Pi.single μ 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single μ (1 : ℝ))).const_add Y
  exact hφ.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)

/-- The partial derivatives of the violation flux of `C¹` fields (product rule). -/
theorem pd_flux (hE1 : ∀ i j, ContDiff ℝ 1 fun Y => E Y i j)
    (hB1 : ∀ i j, ContDiff ℝ 1 fun Y => B Y i j) (Y : E4) (μ : Fin 4) (c : Fin 3) :
    pd μ (fun Y => flux (E Y) (B Y) c) Y =
      fluxD (E Y) (B Y) (jet4 E Y μ) (jet4 B Y μ) c := by
  have h1 := hasDerivAt_line ((cd_flux hE1 hB1 c).differentiable (by norm_num) Y) μ
  have h2 := hd_flux (m := fun r => E (Y + r • Pi.single μ 1))
    (n := fun r => B (Y + r • Pi.single μ 1))
    (fun i j => hasDerivAt_line ((hE1 i j).differentiable (by norm_num) Y) μ)
    (fun i j => hasDerivAt_line ((hB1 i j).differentiable (by norm_num) Y) μ) c
  simp only [zero_smul, add_zero] at h2
  exact h1.unique h2

/-- `vskw 0 = 0`. -/
@[simp] theorem vskw_zero : vskw 0 = 0 := by
  ext a; simp [vskw]

/-- `energyD` vanishes where the fields vanish (Thesis Prop 3.6, compact support). -/
theorem energyD_zero_left (dE dB : Matrix (Fin 3) (Fin 3) ℝ) : energyD 0 0 dE dB = 0 := by
  simp [energyD]

/-- `fluxD` vanishes where the fields vanish (Thesis Prop 3.6, compact support). -/
theorem fluxD_zero_left (dE dB : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3) :
    fluxD 0 0 dE dB c = 0 := by
  simp [fluxD]

/-- **Thesis Prop 3.6** (constraint propagation for the linearized EB system), on `ℝ³`.
Let `E, B : ℝ⁴ → ℝ^{3×3}` be `C²` (jointly in `(t, x)`), vanish for `x` outside a fixed compact
`K ⊆ ℝ³` (uniformly in `t`), and solve `Ė = -curl B`, `Ḃ = curl E` for `t > 0`. If `E(0, ·)` and
`B(0, ·)` are TSD (symmetric, trace-free, divergence-free), then `E(t, ·)` and `B(t, ·)` are
TSD for all `t ≥ 0`.

Thesis gap: the thesis argues by "Theorem 4.5" (i.e. Cor 4.5), with neither the domain, the
boundary conditions nor the functional-analytic hypotheses of Cor 4.5 (skew-adjointness,
`P_K D(L) ⊆ D(L)`, density) specified or verified; on bounded domains these are exactly the
hypotheses later only conjectured in Prop 4.17. Correction: we state the result on `ℝ³` with
compact spatial support and prove it directly, by (1) `∂_t div E = -div curl B = 0`
(`div_const_field`) and (2) the energy method for the violations `(tr E, vskw E, tr B, vskw B)`:
`½ ∂_t e = div F` (`energy_flux`), so `∫ e(t) dx` is constant, and `e(0) = 0`, `e ≥ 0` give
`e(t) ≡ 0` (`energy_eq_zero_iff`). Also: "Similarly, `curl E` is TSD" should read `curl B`. -/
theorem prop_3_6 (hEc : ∀ i j, ContDiff ℝ 2 fun Y => E Y i j)
    (hBc : ∀ i j, ContDiff ℝ 2 fun Y => B Y i j) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    (hsupp : ∀ t x, x ∉ K → E (ev t x) = 0 ∧ B (ev t x) = 0)
    (hEeq : ∀ Y : E4, 0 < Y 0 → jet4 E Y 0 = -curl (sp (jet4 B Y)))
    (hBeq : ∀ Y : E4, 0 < Y 0 → jet4 B Y 0 = curl (sp (jet4 E Y)))
    (h0 : ∀ x, TSDAt E (ev 0 x) ∧ TSDAt B (ev 0 x)) (t : ℝ) (ht : 0 ≤ t) (x : Fin 3 → ℝ) :
    TSDAt E (ev t x) ∧ TSDAt B (ev t x) := by
  -- regularity
  have hE1 : ∀ i j, ContDiff ℝ 1 fun Y => E Y i j := fun i j => (hEc i j).of_le (by norm_num)
  have hB1 : ∀ i j, ContDiff ℝ 1 fun Y => B Y i j := fun i j => (hBc i j).of_le (by norm_num)
  have hEd : ∀ i j, Differentiable ℝ fun Y => E Y i j := fun i j =>
    (hE1 i j).differentiable (by norm_num)
  have hBd : ∀ i j, Differentiable ℝ fun Y => B Y i j := fun i j =>
    (hB1 i j).differentiable (by norm_num)
  have hEp : ∀ μ i j, ContDiff ℝ 1 fun Y => jet4 E Y μ i j := fun μ i j =>
    Linearized.contDiff_pd (hEc i j) (by norm_num) μ
  have hBp : ∀ μ i j, ContDiff ℝ 1 fun Y => jet4 B Y μ i j := fun μ i j =>
    Linearized.contDiff_pd (hBc i j) (by norm_num) μ
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
    hΦe.continuous.comp (contDiff_ev s).continuous
  have he'_cont : ∀ s, Continuous fun y =>
      energyD (E (ev s y)) (B (ev s y)) (jet4 E (ev s y) 0) (jet4 B (ev s y) 0) := fun s =>
    hΦe'.continuous.comp (contDiff_ev s).continuous
  have he_int : ∀ s, Integrable fun y => energy (E (ev s y)) (B (ev s y)) := fun s =>
    (he_cont s).integrable_of_hasCompactSupport (HasCompactSupport.intro hK fun y hy => by
      simp [(hsupp s y hy).1, (hsupp s y hy).2, energy])
  have hzero' : ∀ s y, y ∉ K →
      energyD (E (ev s y)) (B (ev s y)) (jet4 E (ev s y) 0) (jet4 B (ev s y) 0) = 0 := by
    intro s y hy
    rw [(hsupp s y hy).1, (hsupp s y hy).2, energyD_zero_left]
  -- the spatial integrals of the flux divergence vanish
  have hflux : ∀ s c, ∫ y, fluxD (E (ev s y)) (B (ev s y)) (jet4 E (ev s y) c.succ)
      (jet4 B (ev s y) c.succ) c = 0 := by
    intro s c
    have hΦ : Differentiable ℝ fun Y => flux (E Y) (B Y) c :=
      (cd_flux hE1 hB1 c).differentiable (by norm_num)
    have hg : Differentiable ℝ fun y => flux (E (ev s y)) (B (ev s y)) c :=
      hΦ.comp ((contDiff_ev s).differentiable (by norm_num))
    have hg' : (fun y => fderiv ℝ (fun y => flux (E (ev s y)) (B (ev s y)) c) y
        (Pi.single c 1)) = fun y => fluxD (E (ev s y)) (B (ev s y)) (jet4 E (ev s y) c.succ)
          (jet4 B (ev s y) c.succ) c := by
      funext y
      rw [fderiv_slice hΦ s y c, pd_flux hE1 hB1]
    have hG'int : Integrable fun y => fluxD (E (ev s y)) (B (ev s y))
        (jet4 E (ev s y) c.succ) (jet4 B (ev s y) c.succ) c :=
      ((cd_fluxD hE1 hB1 (hEp c.succ) (hBp c.succ) c).continuous.comp
        (contDiff_ev s).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hK fun y hy => by
          simp only [Function.comp_apply]
          rw [(hsupp s y hy).1, (hsupp s y hy).2, fluxD_zero_left])
    have hgint : Integrable fun y => flux (E (ev s y)) (B (ev s y)) c :=
      ((cd_flux hE1 hB1 c).continuous.comp (contDiff_ev s).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hK fun y hy => by
          simp only [Function.comp_apply]
          simp [(hsupp s y hy).1, (hsupp s y hy).2, flux])
    have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun _ : Fin 3 → ℝ => (1 : ℝ)) (g := fun y => flux (E (ev s y)) (B (ev s y)) c)
      (v := Pi.single c 1) (by simp) (by simpa [hg'] using hG'int) (by simpa using hgint)
      (fun _ _ => differentiableAt_const _) (fun y _ => hg y)
    simpa [hg'] using ibp
  -- differentiation under the integral sign
  have hI : ∀ s, HasDerivAt (fun r => ∫ y, energy (E (ev r y)) (B (ev r y)))
      (∫ y, energyD (E (ev s y)) (B (ev s y)) (jet4 E (ev s y) 0) (jet4 B (ev s y) 0)) s := by
    intro s
    set S := (fun p : ℝ × (Fin 3 → ℝ) => ev p.1 p.2) '' (Metric.closedBall s 1 ×ˢ K)
    have hS : IsCompact S := ((isCompact_closedBall s 1).prod hK).image continuous_ev
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
      · rw [hzero' r y hy, indicator_of_notMem hy, norm_zero]
    · exact (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
    · exact Eventually.of_forall fun y r _ =>
        hd_energy (m := fun r => E (ev r y)) (n := fun r => B (ev r y))
          (fun i j => hasDerivAt_time (hEd i j) y r) (fun i j => hasDerivAt_time (hBd i j) y r)
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
    rw [integral_const_mul, integral_finsetSum]
    · simp [hflux]
    · intro c _
      exact ((cd_fluxD hE1 hB1 (hEp c.succ) (hBp c.succ) c).continuous.comp
        (contDiff_ev s).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hK fun y hy => by
          simp only [Function.comp_apply]
          rw [(hsupp s y hy).1, (hsupp s y hy).2, fluxD_zero_left])
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

end Prop36

end EB
end Feec
