module

public import Feec.Ch2.Linearized
public import Feec.Ch3.Bivector
public import Feec.Physics.EinsteinBianchi.Propagation

/-!
# Ch 3 §3.3–3.5: the linearized Einstein–Bianchi (EB) system (shim)

Strangler shim over `Feec.Physics.EinsteinBianchi.{System,Fields,Propagation}` (namespace
`Feec.EinsteinBianchi`) and `Feec.Algebra.MatrixSymbol` (Lemma 3.5, once, over any commutative
ring). The old foundation `curl`, `div`, `vskw`, `eps3` are bridged by `curl_eq`, `div_eq`,
`vskw_eq`, `eps3_eq_leviCivita3`. Every declaration keeps its old statement.

## References

* [QuennevilleBelair2015], Ch. 3 (§3.2–§3.5: Prop 3.4, Lemma 3.5, Prop 3.6), §2.8, §4.3
* [Bel1958], [Friedrich1996], [ACBY1997], [Wald1984], [Alcubierre2008]
-/

open Matrix

@[expose] public noncomputable section

namespace Feec

/-! ### Bridges from the foundation's component calculus -/

/-- The determinant definition `eps3` is the Levi-Civita symbol `leviCivita3 ℝ`. -/
theorem eps3_eq_leviCivita3 (i j k : Fin 3) : eps3 i j k = leviCivita3 ℝ i j k := by
  unfold eps3 leviCivita3 leviCivita
  congr 1
  ext r s
  fin_cases r <;> simp [Pi.single_apply, Matrix.one_apply, eq_comm] <;> congr

theorem curl_eq (dA : Jet1) : curl dA = MatrixSymbol.curl dA := by
  ext a b; simp [curl, MatrixSymbol.curl, eps3_eq_leviCivita3]

theorem div_eq (dA : Jet1) : div dA = MatrixSymbol.div dA := rfl

theorem vskw_eq (A : Matrix (Fin 3) (Fin 3) ℝ) : vskw A = MatrixSymbol.vskw A := by
  ext a
  simp [vskw, MatrixSymbol.vskw, MatrixSymbol.axial, eps3_eq_leviCivita3, invOf_eq_inv]

namespace EB

open Bivector

/-- `ε_{ijk}` as an explicit table. -/
theorem eps3_explicit (i j k : Fin 3) : eps3 i j k =
    ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]], ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
      ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]] i j k :=
  by rw [eps3_eq_leviCivita3]; exact leviCivita3_apply i j k

/-- Vector curl on jets, `(curl v)_a = ε_{abc} ∂_b v_c`. -/
abbrev vcurl (dv : Fin 3 → Fin 3 → ℝ) : Fin 3 → ℝ :=
  MatrixSymbol.vcurl dv

/-- Vector divergence on jets, `div v = ∂_c v_c`. -/
abbrev vdiv (dv : Fin 3 → Fin 3 → ℝ) : ℝ :=
  MatrixSymbol.vdiv dv

/-- Jet of `tr A` (that is, `grad tr A`) from the jet of `A`. -/
abbrev trJ (dA : Jet1) : Fin 3 → ℝ :=
  MatrixSymbol.traceJet dA

/-- Jet of `vskw A` from the jet of `A`. -/
abbrev vskwJ (dA : Jet1) : Fin 3 → Fin 3 → ℝ :=
  EinsteinBianchi.vskwJ dA

/-- Jet of `Aᵀ`. -/
abbrev transJ (dA : Jet1) : Jet1 :=
  MatrixSymbol.transposeJet dA

/-- Jet of `skw A = ½(A - Aᵀ)`. -/
abbrev skwJ (dA : Jet1) : Jet1 :=
  EinsteinBianchi.skwJ dA

/-- Symmetric part `sym A = ½(A + Aᵀ)`. -/
abbrev symm (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  EinsteinBianchi.symPart A

/-- A matrix is symmetric iff its axial vector vanishes. -/
theorem isSymm_iff_vskw_eq_zero (A : Matrix (Fin 3) (Fin 3) ℝ) : Aᵀ = A ↔ vskw A = 0 :=
  by rw [vskw_eq]; exact MatrixSymbol.transpose_eq_iff_vskw_eq_zero A

/-- **Thesis Lemma 3.5 (2)**: `tr curl A = -2 div vskw A`, for an arbitrary first jet.

Thesis gap: neither the matrix `curl` (defined only inside the proof) nor the row-wise `div`
is defined before use; here `(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}` and `(div A)_a = ∂_b A_{ab}`
(foundation `curl`, `div`). The identity is pointwise; for `A ∈ H(curl)` it holds in the
distributional sense by linearity (not formalized).

See [QuennevilleBelair2015, Lemma 3.5]. -/
theorem trace_curl (dA : Jet1) : (curl dA).trace = -2 * vdiv (vskwJ dA) :=
  by rw [curl_eq]; exact MatrixSymbol.trace_curl_eq_vskw dA

/-- **Thesis Lemma 3.5 (3)**: `2 vskw curl A = grad tr A - div Aᵀ`.
See [QuennevilleBelair2015, Lemma 3.5]. -/
theorem two_vskw_curl (dA : Jet1) : (2 : ℝ) • vskw (curl dA) = trJ dA - div (transJ dA) :=
  by rw [curl_eq, vskw_eq]; exact MatrixSymbol.two_smul_vskw_curl dA

/-- `div skw A = curl vskw A` (the vector curl of the axial vector). -/
theorem div_skw (dA : Jet1) : div (skwJ dA) = vcurl (vskwJ dA) :=
  by
  ext a
  fin_cases a <;>
    simp [div, EinsteinBianchi.skwJ, MatrixSymbol.vcurl, EinsteinBianchi.vskwJ,
      MatrixSymbol.vskw_apply, leviCivita3_apply, Fin.sum_univ_three, invOf_eq_inv] <;> ring

/-- **Thesis Lemma 3.5 (3)**, second form: `2 vskw curl A = grad tr A - div A + 2 div skw A`. -/
theorem two_vskw_curl' (dA : Jet1) :
    (2 : ℝ) • vskw (curl dA) = trJ dA - div dA + (2 : ℝ) • div (skwJ dA) :=
  by
  rw [two_vskw_curl]
  ext a
  simp [div, MatrixSymbol.transposeJet, EinsteinBianchi.skwJ,
    Fin.sum_univ_three]
  ring

/-- **Thesis Lemma 3.5 (1)**: `div curl A = 0`, for a second jet `d2A b c = ∂_b ∂_c A` that is
symmetric in `(b, c)` (Schwarz; see `div_curl_field` for `C²` fields).
See [QuennevilleBelair2015, Lemma 3.5]. -/
theorem div_curl (d2A : Fin 3 → Jet1) (hsym : ∀ b c, d2A b c = d2A c b) :
    div (fun b => curl (d2A b)) = 0 :=
  by simp only [curl_eq]; exact MatrixSymbol.div_curl d2A hsym

/-- Entrywise symmetry of a jet of symmetric matrices. -/
theorem jet_symm {dA : Jet1} (hsym : ∀ c, (dA c)ᵀ = dA c) (c i j : Fin 3) :
    dA c i j = dA c j i :=
  EinsteinBianchi.jet_symm hsym c i j

/-- **Thesis Lemma 3.5, consequence**: if `A` is symmetric, then `curl A` is trace-free.

Correction: the thesis writes "the matrix field `A` is then trace-free"; it is `curl A`. -/
theorem trace_curl_of_symm {dA : Jet1} (hsym : ∀ c, (dA c)ᵀ = dA c) : (curl dA).trace = 0 :=
  by rw [curl_eq]; exact MatrixSymbol.trace_curl_of_transpose_eq hsym

/-- **Thesis Lemma 3.5, consequence** (sharpened): if `A` is symmetric with `div A = 0` and
`grad tr A = 0`, then `curl A` is symmetric. Only these three properties are used (the thesis
assumes `A` TSD). -/
theorem curl_symm {dA : Jet1} (hsym : ∀ c, (dA c)ᵀ = dA c) (htr : trJ dA = 0)
    (hdiv : div dA = 0) : (curl dA)ᵀ = curl dA :=
  by rw [curl_eq]; exact MatrixSymbol.transpose_curl_eq hsym htr hdiv

/-- **Thesis Lemma 3.5, conclusion**: `A` TSD (symmetric, trace-free, divergence-free) implies
`curl A` symmetric and trace-free, and (at second order) divergence-free (`div_curl`).
See [QuennevilleBelair2015, Lemma 3.5 and proof of Prop 3.6]. -/
theorem curl_TSD {dA : Jet1} (hsym : ∀ c, (dA c)ᵀ = dA c) (htr : ∀ c, (dA c).trace = 0)
    (hdiv : div dA = 0) : (curl dA)ᵀ = curl dA ∧ (curl dA).trace = 0 :=
  by rw [curl_eq]; exact MatrixSymbol.curl_isTSD hsym htr hdiv

/-- First jet of a spacetime matrix field. -/
abbrev Jet4 :=
  EinsteinBianchi.Jet4

/-- Spatial part `(∂_1, ∂_2, ∂_3)` of a spacetime jet. -/
abbrev sp (dX : Jet4) : Jet1 :=
  EinsteinBianchi.sp dX

/-- The jet `∂_μ C` of the Weyl field `C = [[E, B], [B, -E]]` (block form of Prop 3.3).
See [QuennevilleBelair2015, Prop 3.3]; the decomposition goes back to [Bel1958]. -/
abbrev dWeyl (dE dB : Jet4) (μ : Fin 4) : T4 (Fin 4) :=
  EinsteinBianchi.dWeyl dE dB μ

/-- The linearized second Bianchi expression `∂_α C_{βγδθ} + ∂_β C_{γαδθ} + ∂_γ C_{αβδθ}`. -/
abbrev bianchi2 (dE dB : Jet4) (α β γ δ θ : Fin 4) : ℝ :=
  EinsteinBianchi.bianchi2 dE dB α β γ δ θ

/-- The linearized EB system (Thesis (3.3)–(3.4)) on jets:
`div E = 0`, `div B = 0`, `Ė + curl B = 0`, `Ḃ - curl E = 0`.
See [QuennevilleBelair2015, §3.4, Prop 3.4]; cf. the nonlinear EB system of [Friedrich1996]
and [ACBY1997]. -/
abbrev EBJet (dE dB : Jet4) : Prop :=
  EinsteinBianchi.EBJet dE dB

/-- The reduced form (Thesis Prop 3.4, count refinement): constraints plus the symmetric parts
of the evolution equations. -/
abbrev EBJetSym (dE dB : Jet4) : Prop :=
  EinsteinBianchi.EBJetSym dE dB

/-- The Bianchi expression in bivector components. -/
theorem bianchi2_eq (dE dB : Jet4) (α β γ δ θ : Fin 4) :
    bianchi2 dE dB α β γ δ θ = sgn δ θ *
      (sgn β γ * fromBlocks (dE α) (dB α) (dB α) (-dE α) (pidx β γ) (pidx δ θ)
      + sgn γ α * fromBlocks (dE β) (dB β) (dB β) (-dE β) (pidx γ α) (pidx δ θ)
      + sgn α β * fromBlocks (dE γ) (dB γ) (dB γ) (-dE γ) (pidx α β) (pidx δ θ)) :=
  EinsteinBianchi.bianchi2_eq dE dB α β γ δ θ

/-- The cyclic sum in `bianchi2_eq` at a fixed second bivector `J`. -/
abbrev cyc3 (dE dB : Jet4) (α β γ : Fin 4) (J : Ix) : ℝ :=
  EinsteinBianchi.cyc3 dE dB α β γ J

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

See [QuennevilleBelair2015, Prop 3.4]; the nonlinear analogue is in [Friedrich1996]
(cf. [ACBY1997]). -/
theorem linBianchi_iff (dE dB : Jet4) (hE : ∀ μ, (dE μ)ᵀ = dE μ) (hB : ∀ μ, (dB μ)ᵀ = dB μ) :
    (∀ α β γ δ θ, bianchi2 dE dB α β γ δ θ = 0) ↔ EBJet dE dB :=
  EinsteinBianchi.linBianchi_iff dE dB hE hB

/-- Jets of symmetric trace-free matrices (pointwise TSD up to the divergence condition). -/
abbrev IsSymTF (dX : Jet4) : Prop :=
  EinsteinBianchi.IsSymTF dX

/-- `sym A = A` for symmetric `A` (used in Thesis Prop 3.4, count refinement). -/
theorem symm_of_isSymm {A : Matrix (Fin 3) (Fin 3) ℝ} (h : Aᵀ = A) : symm A = A :=
  EinsteinBianchi.symPart_of_transpose_eq h

/-- `sym A` is symmetric (used in Thesis Prop 3.4, count refinement). -/
theorem symm_transpose (A : Matrix (Fin 3) (Fin 3) ℝ) : (symm A)ᵀ = symm A :=
  EinsteinBianchi.transpose_symPart A

/-- `tr sym A = tr A` (used in Thesis Prop 3.4, count refinement). -/
theorem trace_symm (A : Matrix (Fin 3) (Fin 3) ℝ) : (symm A).trace = A.trace :=
  EinsteinBianchi.trace_symPart A

/-- **Thesis Prop 3.4**, corrected count: for jets of symmetric trace-free `E`, `B`, the linearized
Bianchi identity is equivalent to the 6 constraints `div E = div B = 0` and the symmetric parts
`Ė + sym curl B = 0`, `Ḃ - sym curl E = 0` of the evolution equations.

Refinement: the thesis counts "6 constraints + 18 evolution equations" (at most 24
conditions); only 16 of them are independent on symmetric trace-free jets. The trace parts of the
evolution equations are `0 = 0` (`trace_curl_of_symm`) and the skew parts repeat the constraints
(`curl_symm`), so the content is 6 constraints plus 10 evolution equations (each `sym curl`
equation is valued in symmetric trace-free matrices, a 5-dimensional space); see
`EBJetSym_surjective` for the independence of these 16 equations.

See [QuennevilleBelair2015, §3.4, Prop 3.4]. -/
theorem linBianchi_iff_sym (dE dB : Jet4) (hE : IsSymTF dE) (hB : IsSymTF dB) :
    (∀ α β γ δ θ, bianchi2 dE dB α β γ δ θ = 0) ↔ EBJetSym dE dB :=
  EinsteinBianchi.linBianchi_iff_sym dE dB hE hB

/-- The spatial part of `Fin.cons X f` is `f`. -/
theorem sp_cons (X : Matrix (Fin 3) (Fin 3) ℝ) (f : Jet1) :
    sp (Fin.cons X f : Jet4) = f :=
  EinsteinBianchi.sp_cons X f

/-- A spatial jet of symmetric trace-free matrices with prescribed divergence `v`:
`∂_c A = (3/10)(v ⊗ e_c + e_c ⊗ v - (2/3) v_c I)`. -/
abbrev divJet (v : Fin 3 → ℝ) : Jet1 :=
  EinsteinBianchi.divJet v

/-- `divJet v` is a jet of symmetric matrices (Thesis Prop 3.4, count). -/
theorem divJet_symm (v : Fin 3 → ℝ) (c : Fin 3) : (divJet v c)ᵀ = divJet v c :=
  EinsteinBianchi.divJet_symm v c

/-- `divJet v` is a jet of trace-free matrices (Thesis Prop 3.4, count). -/
theorem divJet_trace (v : Fin 3 → ℝ) (c : Fin 3) : (divJet v c).trace = 0 :=
  EinsteinBianchi.divJet_trace v c

/-- `div (divJet v) = v` (Thesis Prop 3.4, count). -/
theorem div_divJet (v : Fin 3 → ℝ) : div (divJet v) = v :=
  EinsteinBianchi.div_divJet v

/-- **Thesis Prop 3.4**, independence of the 16 equations: on jets of symmetric trace-free
`E`, `B`, the map `(dE, dB) ↦ (div E, div B, Ė + sym curl B, Ḃ - sym curl E)` is onto
`ℝ³ × ℝ³ × Sym₀ × Sym₀` (dimension `3 + 3 + 5 + 5 = 16`). Together with `linBianchi_iff_sym`,
on such jets the Bianchi identity is equivalent to 16 independent equations: 6 constraints
plus 10 evolution equations.

Refinement: the thesis counts "6 constraints + 18 evolution equations" (at most 24
conditions) without determining how many are independent; the answer is 16.

See [QuennevilleBelair2015, §3.4, Prop 3.4]. -/
theorem EBJetSym_surjective (v w : Fin 3 → ℝ) (P Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hP : Pᵀ = P ∧ P.trace = 0) (hQ : Qᵀ = Q ∧ Q.trace = 0) :
    ∃ dE dB : Jet4, IsSymTF dE ∧ IsSymTF dB ∧ div (sp dE) = v ∧ div (sp dB) = w ∧
      dE 0 + symm (curl (sp dB)) = P ∧ dB 0 - symm (curl (sp dE)) = Q :=
  by simp only [curl_eq]; exact EinsteinBianchi.EBJetSym_surjective v w P Q hP hQ

/-- **Thesis Prop 3.6, proof, step 1 (jet level)**: if `Ė = -curl B` and `Ḃ = curl E`, then
`∂_t div E = 0` and `∂_t div B = 0`. Here `d2E μ c = ∂_μ ∂_c E` are second jets, symmetric in
`(μ, c)`. The divergence constraints thus propagate without any uniqueness argument
(field version: `div_const_field`).

Thesis gap: the thesis proves Prop 3.6 only by a forward reference to Cor 4.5 (cited as
"Theorem 4.5"), whose hypotheses it never verifies; this step is missing.

See [QuennevilleBelair2015, Prop 3.6, Cor 4.5]. -/
theorem div_propagation (d2E d2B : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℝ)
    (hsE : ∀ μ ν, d2E μ ν = d2E ν μ) (hsB : ∀ μ ν, d2B μ ν = d2B ν μ)
    (hE : ∀ c : Fin 3, d2E c.succ 0 = -curl (sp (d2B c.succ)))
    (hB : ∀ c : Fin 3, d2B c.succ 0 = curl (sp (d2E c.succ))) :
    div (fun c : Fin 3 => d2E 0 c.succ) = 0 ∧ div (fun c : Fin 3 => d2B 0 c.succ) = 0 :=
  by simp only [curl_eq] at hE hB; exact EinsteinBianchi.div_propagation d2E d2B hsE hsB hE hB

/-- **Thesis Prop 3.6, proof, step 2 (closed system for the violations)**: write `a = tr E`,
`α = vskw E`, `b = tr B`, `β = vskw B`. If `Ė = -curl B` and `Ḃ = curl E` (first jets), then
`ȧ = 2 div β`, `α̇ = -½ grad b - curl β + ½ div B`, `ḃ = -2 div α`,
`β̇ = ½ grad a + curl α - ½ div E`.
With `div E = div B = 0` (step 1), `(a, α, b, β)` solves a closed homogeneous first-order system.

Thesis gap: not in the thesis (it relies on Cor 4.5 instead).
Cf. [QuennevilleBelair2015, Prop 3.6, Cor 4.5]. -/
theorem violation_evolution (dE dB : Jet4) (hE : dE 0 = -curl (sp dB))
    (hB : dB 0 = curl (sp dE)) :
    (dE 0).trace = 2 * vdiv (vskwJ (sp dB)) ∧
    vskw (dE 0) = -(1 / 2 : ℝ) • trJ (sp dB) - vcurl (vskwJ (sp dB)) +
      (1 / 2 : ℝ) • div (sp dB) ∧
    (dB 0).trace = -2 * vdiv (vskwJ (sp dE)) ∧
    vskw (dB 0) = (1 / 2 : ℝ) • trJ (sp dE) + vcurl (vskwJ (sp dE)) -
      (1 / 2 : ℝ) • div (sp dE) :=
  by simp only [curl_eq, vskw_eq] at hE hB ⊢; exact EinsteinBianchi.violation_evolution dE dB hE hB

/-- The violation energy density `e = (tr E)² + 4|vskw E|² + (tr B)² + 4|vskw B|²`
(zero iff `E` and `B` are symmetric and trace-free). -/
abbrev energy (E B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  EinsteinBianchi.energy E B

/-- The violation flux `F = 2 (tr E) vskw B - 2 (tr B) vskw E + 4 vskw E × vskw B`. -/
abbrev flux (E B : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  EinsteinBianchi.flux E B

/-- Directional derivative of `energy` at `(E, B)` in the direction `(dE, dB)`. -/
abbrev energyD (E B dE dB : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  EinsteinBianchi.energyD E B dE dB

/-- Directional derivative of `flux` at `(E, B)` in the direction `(dE, dB)`. -/
abbrev fluxD (E B dE dB : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  EinsteinBianchi.fluxD E B dE dB

/-- `e ≥ 0`. -/
theorem energy_nonneg (E B : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ energy E B :=
  EinsteinBianchi.energy_nonneg E B

/-- `e = 0` iff `E` and `B` are symmetric and trace-free. -/
theorem energy_eq_zero_iff (E B : Matrix (Fin 3) (Fin 3) ℝ) :
    energy E B = 0 ↔ (Eᵀ = E ∧ E.trace = 0) ∧ (Bᵀ = B ∧ B.trace = 0) :=
  EinsteinBianchi.energy_eq_zero_iff E B

/-- **Thesis Prop 3.6, proof, step 3 (energy flux identity, jet level)**: if `Ė = -curl B`,
`Ḃ = curl E` and `div E = div B = 0` at a point, then `½ ∂_t e = div F`, with `e = energy E B`
and `F = flux E B` (both differentiated by the product rule: `energyD`, `fluxD`).

Thesis gap: not in the thesis; this replaces the unverified appeal to Cor 4.5 (energy proof on
`ℝ³`; field version `prop_3_6`).
Cf. [QuennevilleBelair2015, Prop 3.6, Cor 4.5]. -/
theorem energy_flux (E B : Matrix (Fin 3) (Fin 3) ℝ) (dE dB : Jet4)
    (hE : dE 0 = -curl (sp dB)) (hB : dB 0 = curl (sp dE)) (hdE : div (sp dE) = 0)
    (hdB : div (sp dB) = 0) :
    (1 / 2 : ℝ) * energyD E B (dE 0) (dB 0) = ∑ c, fluxD E B (dE c.succ) (dB c.succ) c :=
  by simp only [curl_eq] at hE hB; exact EinsteinBianchi.energy_flux E B dE dB hE hB hdE hdB

section Fields

open Linearized (E4 phaseL kTT ttAmp Rjet jet2)

variable {n : ℕ}

/-- Linearity of `pd` (scalar), on `ℝⁿ`. -/
theorem pd_const_mul' {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x)
    (c : ℝ) (i : Fin n) : pd i (fun y => c * f y) x = c * pd i f x :=
  partialDeriv_const_smul hf c i

/-- Linearity of `pd` (negation), on `ℝⁿ`. -/
theorem pd_neg' (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    pd i (fun y => -f y) x = -pd i f x :=
  partialDeriv_neg f i x

/-- Linearity of `pd` (finite sums), on `ℝⁿ`. -/
theorem pd_sum' {ι : Type*} [Fintype ι] {F : ι → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hF : ∀ c, DifferentiableAt ℝ (F c) x) (i : Fin n) :
    pd i (fun y => ∑ c, F c y) x = ∑ c, pd i (F c) x :=
  partialDeriv_sum Finset.univ (fun c _ => hF c) i

/-- Partial derivatives of `C²` functions are differentiable. -/
theorem differentiable_pd' {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin n) :
    Differentiable ℝ (pd i f) :=
  hf.differentiable_partialDeriv le_rfl i

/-- Schwarz on `ℝⁿ`: partial derivatives of a `C²` function commute. -/
theorem pd_comm' {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin n) (x : Fin n → ℝ) :
    pd i (pd j f) x = pd j (pd i f) x :=
  partialDeriv_comm hf i j x

/-- Spatial jet `(∂_c A)(x)` of a matrix field on `ℝ³`. -/
abbrev jet3 (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) : Jet1 :=
  EinsteinBianchi.jet3 A x

/-- The matrix field `curl A`. -/
abbrev curlF (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  EinsteinBianchi.curlF A x

/-- **Thesis Lemma 3.5 (1)** for fields: `div curl A = 0` for a `C²` matrix field on `ℝ³`.

Thesis gap: the thesis uses symmetry of second derivatives without stating any regularity;
here `A ∈ C²` (distributional version for `A ∈ H(curl)` not formalized).
See [QuennevilleBelair2015, Lemma 3.5]. -/
theorem div_curl_field {A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ a b, ContDiff ℝ 2 fun y => A y a b) (x : Fin 3 → ℝ) :
    div (jet3 (curlF A) x) = 0 :=
  EinsteinBianchi.div_curl_field hA x

/-- **Thesis Lemma 3.5, conclusion** for fields: if a `C²` matrix field `A` on `ℝ³` is TSD
(symmetric, trace-free and divergence-free everywhere), then so is `curl A`.
See [QuennevilleBelair2015, Lemma 3.5 and proof of Prop 3.6]. -/
theorem curl_TSD_field {A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ a b, ContDiff ℝ 2 fun y => A y a b) (hsym : ∀ y, (A y)ᵀ = A y)
    (htr : ∀ y, (A y).trace = 0) (hdiv : ∀ y, div (jet3 A y) = 0) (x : Fin 3 → ℝ) :
    (curlF A x)ᵀ = curlF A x ∧ (curlF A x).trace = 0 ∧ div (jet3 (curlF A) x) = 0 :=
  EinsteinBianchi.curl_TSD_field hA hsym htr hdiv x

/-- Spacetime jet `(∂_μ X)(p)` of a matrix field on `ℝ⁴`. -/
abbrev jet4 (M : E4 → Matrix (Fin 3) (Fin 3) ℝ) (p : E4) : Jet4 :=
  EinsteinBianchi.jet4 M p

/-- Jets of symmetric fields are symmetric. -/
theorem jet4_symm {M : E4 → Matrix (Fin 3) (Fin 3) ℝ} (hM : ∀ y, (M y)ᵀ = M y) (p : E4)
    (μ : Fin 4) : (jet4 M p μ)ᵀ = jet4 M p μ :=
  EinsteinBianchi.jet4_symm hM p μ

/-- The jet of the Weyl field `[[E, B], [B, -E]]` is `dWeyl` of the jets of `E` and `B`. -/
theorem pd_weyl {E B : E4 → Matrix (Fin 3) (Fin 3) ℝ} {p : E4}
    (hE : ∀ i j, DifferentiableAt ℝ (fun y => E y i j) p)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y => B y i j) p) (α β γ δ θ : Fin 4) :
    pd α (fun y => T (E y) (B y) (B y) (-E y) β γ δ θ) p =
      dWeyl (jet4 E p) (jet4 B p) α β γ δ θ :=
  EinsteinBianchi.pd_weyl hE hB α β γ δ θ

/-- **Thesis Prop 3.4** (field version): let `E, B : ℝ⁴ → Sym(3)` be differentiable and
`C = [[E, B], [B, -E]]`. At each point, the linearized second Bianchi identity
`∂_α C_{βγδθ} + ∂_β C_{γαδθ} + ∂_γ C_{αβδθ} = 0` holds iff `div E = div B = 0`,
`Ė + curl B = 0` and `Ḃ - curl E = 0` there.

Thesis gap: the equivalence is pointwise and only needs `C ∈ C¹` (differentiability at the
point suffices); see `linBianchi_iff` for the remaining corrections.

See [QuennevilleBelair2015, Prop 3.4]. -/
theorem linBianchi_field_iff {E B : E4 → Matrix (Fin 3) (Fin 3) ℝ} (p : E4)
    (hEs : ∀ y, (E y)ᵀ = E y) (hBs : ∀ y, (B y)ᵀ = B y)
    (hE : ∀ i j, DifferentiableAt ℝ (fun y => E y i j) p)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y => B y i j) p) :
    (∀ α β γ δ θ, pd α (fun y => T (E y) (B y) (B y) (-E y) β γ δ θ) p +
        pd β (fun y => T (E y) (B y) (B y) (-E y) γ α δ θ) p +
        pd γ (fun y => T (E y) (B y) (B y) (-E y) α β δ θ) p = 0) ↔
      EBJet (jet4 E p) (jet4 B p) :=
  EinsteinBianchi.linBianchi_field_iff p hEs hBs hE hB

/-- Electric amplitude of the §3.5 plane wave (same matrix as Ch 7). -/
abbrev ampE (Ap Ax : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  EinsteinBianchi.ampE Ap Ax

/-- Magnetic amplitude of the §3.5 plane wave. -/
abbrev ampB (Ap Ax : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  EinsteinBianchi.ampB Ap Ax

/-- **Thesis §3.5** (symbol level): the linearized Riemann tensor of the TT 2-jet
`∂_i∂_j h_ab = k_i k_j A_ab s` (`k = κ(-1, 0, 0, 1)`, `A = ttAmp A₊ Aₓ`, `s = f''`) is the Weyl
tensor `[[E, B], [B, -E]]` with `E = (κ²/2) s · ampE`, `B = (κ²/2) s · ampB`.

Correction: the thesis writes the amplitudes `A₊` and `A₋`; the second is `Aₓ`. Its list of
"non-zero components" is complete only up to the Riemann symmetries; here the full tensor is
identified.

See [QuennevilleBelair2015, §3.5] (TT plane waves: §2.8); cf. [Wald1984, §4.4]. -/
theorem planeWave_weyl (κ Ap Ax s : ℝ) :
    Rjet (fun i j a b => kTT κ i * kTT κ j * ttAmp Ap Ax a b * s) =
      T ((κ ^ 2 / 2 * s) • ampE Ap Ax) ((κ ^ 2 / 2 * s) • ampB Ap Ax)
        ((κ ^ 2 / 2 * s) • ampB Ap Ax) (-((κ ^ 2 / 2 * s) • ampE Ap Ax)) :=
  EinsteinBianchi.planeWave_weyl κ Ap Ax s

/-- The §3.5 electric field `E(x) = (κ²/2) f''(k·x) ampE`. -/
abbrev waveE (κ Ap Ax : ℝ) (f : ℝ → ℝ) (y : E4) : Matrix (Fin 3) (Fin 3) ℝ :=
  EinsteinBianchi.waveE κ Ap Ax f y

/-- The §3.5 magnetic field `B(x) = (κ²/2) f''(k·x) ampB`. -/
abbrev waveB (κ Ap Ax : ℝ) (f : ℝ → ℝ) (y : E4) : Matrix (Fin 3) (Fin 3) ℝ :=
  EinsteinBianchi.waveB κ Ap Ax f y

/-- **Thesis §3.5**: for `f ∈ C³`, the plane wave `h_ab = ttAmp_ab f(κ(x³ - x⁰))` produces the
linearized Weyl field `[[E, B], [B, -E]] = Rjet(∂∂h)` with `E = waveE`, `B = waveB`, and these
are symmetric, trace-free and solve the linearized EB system (3.3)–(3.4) at every point
(`div E = div B = 0`, `Ė + curl B = 0`, `Ḃ - curl E = 0`).

Remark: the thesis assumes `f ∈ C²` so that `h` solves the wave equation, and then `f ∈ C³`
for the EB equations (which involve `f'''`); we assume `f ∈ C³`, as the thesis does here.

See [QuennevilleBelair2015, §3.5] (TT plane waves: §2.8); cf. [Wald1984, §4.4]. -/
theorem planeWave_EB {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (κ Ap Ax : ℝ) (p : E4) :
    Rjet (jet2 (fun y a b => ttAmp Ap Ax a b * f (phaseL (kTT κ) y)) p) =
      T (waveE κ Ap Ax f p) (waveB κ Ap Ax f p) (waveB κ Ap Ax f p) (-waveE κ Ap Ax f p) ∧
    ((waveE κ Ap Ax f p)ᵀ = waveE κ Ap Ax f p ∧ (waveE κ Ap Ax f p).trace = 0) ∧
    ((waveB κ Ap Ax f p)ᵀ = waveB κ Ap Ax f p ∧ (waveB κ Ap Ax f p).trace = 0) ∧
    EBJet (jet4 (waveE κ Ap Ax f) p) (jet4 (waveB κ Ap Ax f) p) :=
  EinsteinBianchi.planeWave_EB hf κ Ap Ax p

end Fields

section Calculus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {M N P Q : X → Matrix (Fin 3) (Fin 3) ℝ}

/-- Components of the violation flux (Thesis Prop 3.6, energy step). -/
theorem flux_apply (E B : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3) :
    flux E B c = 2 * E.trace * vskw B c - 2 * B.trace * vskw E c +
      4 * (vskw E ⨯₃ vskw B) c :=
  by simp only [vskw_eq]; exact EinsteinBianchi.flux_apply E B c

/-- Components of the linearized violation flux (Thesis Prop 3.6, energy step). -/
theorem fluxD_apply (E B dE dB : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3) :
    fluxD E B dE dB c = 2 * dE.trace * vskw B c + 2 * E.trace * vskw dB c -
      2 * dB.trace * vskw E c - 2 * B.trace * vskw dE c +
      4 * ((vskw dE ⨯₃ vskw B) c + (vskw E ⨯₃ vskw dB) c) :=
  by simp only [vskw_eq]; exact EinsteinBianchi.fluxD_apply E B dE dB c

/-- `tr M` is `C¹` if `M` is (regularity for Thesis Prop 3.6). -/
theorem cd_trace (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j) :
    ContDiff ℝ 1 fun y => (M y).trace :=
  EinsteinBianchi.cd_trace hM

/-- `vskw M` is `C¹` if `M` is (regularity for Thesis Prop 3.6). -/
theorem cd_vskw (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j) (a : Fin 3) :
    ContDiff ℝ 1 fun y => vskw (M y) a :=
  by simp only [vskw_eq]; exact EinsteinBianchi.cd_vskw hM a

/-- Dot products of `C¹` vector fields are `C¹` (regularity for Thesis Prop 3.6). -/
theorem cd_dot {u v : X → Fin 3 → ℝ} (hu : ∀ a, ContDiff ℝ 1 fun y => u y a)
    (hv : ∀ a, ContDiff ℝ 1 fun y => v y a) : ContDiff ℝ 1 fun y => u y ⬝ᵥ v y :=
  EinsteinBianchi.cd_dot hu hv

/-- Cross products of `C¹` vector fields are `C¹` (regularity for Thesis Prop 3.6). -/
theorem cd_cross {u v : X → Fin 3 → ℝ} (hu : ∀ a, ContDiff ℝ 1 fun y => u y a)
    (hv : ∀ a, ContDiff ℝ 1 fun y => v y a) (a : Fin 3) :
    ContDiff ℝ 1 fun y => (u y ⨯₃ v y) a :=
  EinsteinBianchi.cd_cross hu hv a

/-- `energyD` of `C¹` fields is `C¹` (regularity for Thesis Prop 3.6). -/
theorem cd_energyD (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j)
    (hN : ∀ i j, ContDiff ℝ 1 fun y => N y i j) (hP : ∀ i j, ContDiff ℝ 1 fun y => P y i j)
    (hQ : ∀ i j, ContDiff ℝ 1 fun y => Q y i j) :
    ContDiff ℝ 1 fun y => energyD (M y) (N y) (P y) (Q y) :=
  EinsteinBianchi.cd_energyD hM hN hP hQ

/-- The violation energy of `C¹` fields is `C¹` (regularity for Thesis Prop 3.6). -/
theorem cd_energy (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j)
    (hN : ∀ i j, ContDiff ℝ 1 fun y => N y i j) :
    ContDiff ℝ 1 fun y => energy (M y) (N y) :=
  EinsteinBianchi.cd_energy hM hN

/-- The violation flux of `C¹` fields is `C¹` (regularity for Thesis Prop 3.6). -/
theorem cd_flux (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j)
    (hN : ∀ i j, ContDiff ℝ 1 fun y => N y i j) (c : Fin 3) :
    ContDiff ℝ 1 fun y => flux (M y) (N y) c :=
  EinsteinBianchi.cd_flux hM hN c

/-- `fluxD` of `C¹` fields is `C¹` (regularity for Thesis Prop 3.6). -/
theorem cd_fluxD (hM : ∀ i j, ContDiff ℝ 1 fun y => M y i j)
    (hN : ∀ i j, ContDiff ℝ 1 fun y => N y i j) (hP : ∀ i j, ContDiff ℝ 1 fun y => P y i j)
    (hQ : ∀ i j, ContDiff ℝ 1 fun y => Q y i j) (c : Fin 3) :
    ContDiff ℝ 1 fun y => fluxD (M y) (N y) (P y) (Q y) c :=
  EinsteinBianchi.cd_fluxD hM hN hP hQ c

variable {m n : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {m' n' : Matrix (Fin 3) (Fin 3) ℝ} {s : ℝ}

/-- Derivative of `tr m(r)` along a curve (product rules for Thesis Prop 3.6). -/
theorem hd_trace (hm : ∀ i j, HasDerivAt (fun r => m r i j) (m' i j) s) :
    HasDerivAt (fun r => (m r).trace) m'.trace s :=
  EinsteinBianchi.hd_trace hm

/-- Derivative of `vskw m(r)` along a curve (product rules for Thesis Prop 3.6). -/
theorem hd_vskw (hm : ∀ i j, HasDerivAt (fun r => m r i j) (m' i j) s) (a : Fin 3) :
    HasDerivAt (fun r => vskw (m r) a) (vskw m' a) s :=
  by simp only [vskw_eq]; exact EinsteinBianchi.hd_vskw hm a

/-- Product rule for the dot product (Thesis Prop 3.6). -/
theorem hd_dot {u v : ℝ → Fin 3 → ℝ} {u' v' : Fin 3 → ℝ}
    (hu : ∀ a, HasDerivAt (fun r => u r a) (u' a) s)
    (hv : ∀ a, HasDerivAt (fun r => v r a) (v' a) s) :
    HasDerivAt (fun r => u r ⬝ᵥ v r) (u' ⬝ᵥ v s + u s ⬝ᵥ v') s :=
  EinsteinBianchi.hd_dot hu hv

/-- Product rule for the cross product (Thesis Prop 3.6). -/
theorem hd_cross {u v : ℝ → Fin 3 → ℝ} {u' v' : Fin 3 → ℝ}
    (hu : ∀ a, HasDerivAt (fun r => u r a) (u' a) s)
    (hv : ∀ a, HasDerivAt (fun r => v r a) (v' a) s) (a : Fin 3) :
    HasDerivAt (fun r => (u r ⨯₃ v r) a) ((u' ⨯₃ v s + u s ⨯₃ v') a) s :=
  EinsteinBianchi.hd_cross hu hv a

/-- Chain rule for the violation energy: its derivative is `energyD` (Thesis Prop 3.6). -/
theorem hd_energy (hm : ∀ i j, HasDerivAt (fun r => m r i j) (m' i j) s)
    (hn : ∀ i j, HasDerivAt (fun r => n r i j) (n' i j) s) :
    HasDerivAt (fun r => energy (m r) (n r)) (energyD (m s) (n s) m' n') s :=
  EinsteinBianchi.hd_energy hm hn

/-- Chain rule for the violation flux: its derivative is `fluxD` (Thesis Prop 3.6). -/
theorem hd_flux (hm : ∀ i j, HasDerivAt (fun r => m r i j) (m' i j) s)
    (hn : ∀ i j, HasDerivAt (fun r => n r i j) (n' i j) s) (c : Fin 3) :
    HasDerivAt (fun r => flux (m r) (n r) c) (fluxD (m s) (n s) m' n' c) s :=
  EinsteinBianchi.hd_flux hm hn c

end Calculus

section Prop36

open Linearized (E4)
open MeasureTheory Filter Topology Set

/-- The point `(t, x) ∈ ℝ⁴`. -/
abbrev ev (t : ℝ) (x : Fin 3 → ℝ) : E4 :=
  EinsteinBianchi.ev t x

/-- The time coordinate of `(t, x)`. -/
theorem ev_zero (t : ℝ) (x : Fin 3 → ℝ) : ev t x 0 = t :=
  rfl

/-- `(t, x) ↦ (t, x) ∈ ℝ⁴` is continuous. -/
theorem continuous_ev : Continuous fun p : ℝ × (Fin 3 → ℝ) => ev p.1 p.2 :=
  continuous_finCons

/-- Time slices `x ↦ (t, x)` are smooth. -/
theorem contDiff_ev (t : ℝ) : ContDiff ℝ 1 (ev t) :=
  contDiff_finCons_right t

/-- `∂_t (t, x) = e₀`. -/
theorem hasDerivAt_ev_time (x : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ev s x) (Pi.single 0 1) t :=
  hasDerivAt_finCons_left x t

/-- `∂_s (t, x + s e_c) = e_{c+1}`. -/
theorem hasDerivAt_ev_space (t : ℝ) (x : Fin 3 → ℝ) (c : Fin 3) :
    HasDerivAt (fun s : ℝ => ev t (x + s • Pi.single c 1)) (Pi.single c.succ 1) (0 : ℝ) :=
  hasDerivAt_finCons_right_add_smul t x c 0

/-- Time derivative of a field along `t ↦ (t, x)`. -/
theorem hasDerivAt_time {φ : E4 → ℝ} (hφ : Differentiable ℝ φ) (x : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (fun s => φ (ev s x)) (pd 0 φ (ev t x)) t :=
  (hφ (ev t x)).hasDerivAt_finCons_left

/-- Spatial derivative of a field along `s ↦ (t, x + s e_c)`. -/
theorem hasDerivAt_space {φ : E4 → ℝ} (hφ : Differentiable ℝ φ) (t : ℝ) (x : Fin 3 → ℝ)
    (c : Fin 3) :
    HasDerivAt (fun s : ℝ => φ (ev t (x + s • Pi.single c 1))) (pd c.succ φ (ev t x)) (0 : ℝ) :=
  (hφ _).hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_finCons_right_add_smul t x c 0) (by simp [ev])

/-- Spatial partial derivatives of a time slice: `∂_c (φ(t, ·)) = (∂_{c+1} φ)(t, ·)`. -/
theorem fderiv_slice {φ : E4 → ℝ} (hφ : Differentiable ℝ φ) (t : ℝ) (x : Fin 3 → ℝ)
    (c : Fin 3) : fderiv ℝ (fun y => φ (ev t y)) x (Pi.single c 1) = pd c.succ φ (ev t x) :=
  partialDeriv_comp_finCons (hφ _) c

/-- `f(t) = f(0)` for `t ≥ 0` if `f' = 0` on `t > 0`. -/
theorem const_of_deriv_pos {f f' : ℝ → ℝ} (hd : ∀ t, HasDerivAt f (f' t) t)
    (h0 : ∀ t, 0 < t → f' t = 0) (t : ℝ) (ht : 0 ≤ t) : f t = f 0 :=
  EinsteinBianchi.const_of_deriv_pos hd h0 t ht

/-- If two functions agree on `{t > 0}`, so do their partial derivatives there. -/
theorem pd_congr_pos {f g : E4 → ℝ} (h : ∀ Z : E4, 0 < Z 0 → f Z = g Z) {Y : E4}
    (hY : 0 < Y 0) (μ : Fin 4) : pd μ f Y = pd μ g Y :=
  EinsteinBianchi.partialDeriv_congr_pos h hY μ

/-- Second spacetime jet `∂_μ ∂_ν M` of a matrix field. -/
abbrev jet42 (M : E4 → Matrix (Fin 3) (Fin 3) ℝ) (Y : E4) : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℝ :=
  EinsteinBianchi.jet42 M Y

/-- Pointwise TSD: symmetric, trace-free and (row-wise) divergence-free in space. -/
abbrev TSDAt (M : E4 → Matrix (Fin 3) (Fin 3) ℝ) (Y : E4) : Prop :=
  EinsteinBianchi.TSDAt M Y

variable {E B : E4 → Matrix (Fin 3) (Fin 3) ℝ}

/-- `∂_μ` of `curl B` is `curl` of the jet of `∂_μ B`. -/
theorem pd_curl (hB : ∀ i j, ContDiff ℝ 2 fun Y => B Y i j) (Y : E4) (μ : Fin 4) (i j : Fin 3) :
    pd μ (fun Z => curl (sp (jet4 B Z)) i j) Y = curl (sp (jet42 B Y μ)) i j :=
  by
  simp only [curl_eq]; exact EinsteinBianchi.partialDeriv_curl hB Y μ i j

/-- **Thesis Prop 3.6, step 1** (field version): the divergence constraints propagate for
`t ≥ 0`, by `∂_t div E = -div curl B = 0` (`div_propagation`). -/
theorem div_const_field (hEc : ∀ i j, ContDiff ℝ 2 fun Y => E Y i j)
    (hBc : ∀ i j, ContDiff ℝ 2 fun Y => B Y i j)
    (hEeq : ∀ Y : E4, 0 < Y 0 → jet4 E Y 0 = -curl (sp (jet4 B Y)))
    (hBeq : ∀ Y : E4, 0 < Y 0 → jet4 B Y 0 = curl (sp (jet4 E Y)))
    (x : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    div (sp (jet4 E (ev t x))) = div (sp (jet4 E (ev 0 x))) ∧
      div (sp (jet4 B (ev t x))) = div (sp (jet4 B (ev 0 x))) :=
  by
  simp only [curl_eq] at hEeq hBeq
  exact EinsteinBianchi.div_const_field hEc hBc hEeq hBeq x t ht

/-- Derivative along a coordinate line through `Y`. -/
theorem hasDerivAt_line {φ : E4 → ℝ} {Y : E4} (hφ : DifferentiableAt ℝ φ Y) (μ : Fin 4) :
    HasDerivAt (fun r : ℝ => φ (Y + r • Pi.single μ 1)) (pd μ φ Y) (0 : ℝ) :=
  EinsteinBianchi.hasDerivAt_line hφ μ

/-- The partial derivatives of the violation flux of `C¹` fields (product rule). -/
theorem pd_flux (hE1 : ∀ i j, ContDiff ℝ 1 fun Y => E Y i j)
    (hB1 : ∀ i j, ContDiff ℝ 1 fun Y => B Y i j) (Y : E4) (μ : Fin 4) (c : Fin 3) :
    pd μ (fun Y => flux (E Y) (B Y) c) Y =
      fluxD (E Y) (B Y) (jet4 E Y μ) (jet4 B Y μ) c :=
  EinsteinBianchi.partialDeriv_flux hE1 hB1 Y μ c

/-- `vskw 0 = 0`. -/
theorem vskw_zero : vskw 0 = 0 :=
  by rw [vskw_eq]; exact EinsteinBianchi.vskw_zero

/-- `energyD` vanishes where the fields vanish (Thesis Prop 3.6, compact support). -/
theorem energyD_zero_left (dE dB : Matrix (Fin 3) (Fin 3) ℝ) : energyD 0 0 dE dB = 0 :=
  EinsteinBianchi.energyD_zero_left dE dB

/-- `fluxD` vanishes where the fields vanish (Thesis Prop 3.6, compact support). -/
theorem fluxD_zero_left (dE dB : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3) :
    fluxD 0 0 dE dB c = 0 :=
  EinsteinBianchi.fluxD_zero_left dE dB c

/-- **Thesis Prop 3.6** (constraint propagation for the linearized EB system), on `ℝ³`.
Let `E, B : ℝ⁴ → ℝ^{3×3}` be `C²` (jointly in `(t, x)`), have compact spatial support locally
uniformly in time (for each `s` a compact `K_s ⊆ ℝ³` containing the spatial supports for all
`|r - s| ≤ 1`), and solve `Ė = -curl B`, `Ḃ = curl E` for `t > 0`. If `E(0, ·)` and `B(0, ·)`
are TSD (symmetric, trace-free, divergence-free), then `E(t, ·)` and `B(t, ·)` are TSD for all
`t ≥ 0`.

The support hypothesis is local in time on purpose: by finite propagation speed it holds for
solutions with compactly supported Cauchy data, whereas a support set uniform in all `t` would
force (via the strong Huygens principle for the wave equation satisfied by TSD solutions) `E` and
`B` to vanish, making the statement vacuous.

Thesis gap: the thesis argues by "Theorem 4.5" (i.e. Cor 4.5), with neither the domain, the
boundary conditions nor the functional-analytic hypotheses of Cor 4.5 (skew-adjointness,
`P_K D(L) ⊆ D(L)`, density) specified or verified; on bounded domains these are exactly the
hypotheses later only conjectured in Prop 4.17. Correction: we state the result on `ℝ³` with
compact spatial support and prove it directly, by (1) `∂_t div E = -div curl B = 0`
(`div_const_field`) and (2) the energy method for the violations `(tr E, vskw E, tr B, vskw B)`:
`½ ∂_t e = div F` (`energy_flux`), so `∫ e(t) dx` is constant, and `e(0) = 0`, `e ≥ 0` give
`e(t) ≡ 0` (`energy_eq_zero_iff`). Also: "Similarly, `curl E` is TSD" should read `curl B`.

See [QuennevilleBelair2015, Prop 3.6] (thesis proof via [QuennevilleBelair2015, Cor 4.5]). -/
theorem prop_3_6 (hEc : ∀ i j, ContDiff ℝ 2 fun Y => E Y i j)
    (hBc : ∀ i j, ContDiff ℝ 2 fun Y => B Y i j)
    (hsupp : ∀ s : ℝ, ∃ K : Set (Fin 3 → ℝ), IsCompact K ∧
      ∀ r ∈ Metric.closedBall s 1, ∀ x ∉ K, E (ev r x) = 0 ∧ B (ev r x) = 0)
    (hEeq : ∀ Y : E4, 0 < Y 0 → jet4 E Y 0 = -curl (sp (jet4 B Y)))
    (hBeq : ∀ Y : E4, 0 < Y 0 → jet4 B Y 0 = curl (sp (jet4 E Y)))
    (h0 : ∀ x, TSDAt E (ev 0 x) ∧ TSDAt B (ev 0 x)) (t : ℝ) (ht : 0 ≤ t) (x : Fin 3 → ℝ) :
    TSDAt E (ev t x) ∧ TSDAt B (ev t x) :=
  by
  simp only [curl_eq] at hEeq hBeq
  exact EinsteinBianchi.tsd_propagates hEc hBc hsupp hEeq hBeq h0 t ht x

open scoped ContDiff

/-- Spatial projection `(t, x) ↦ x` as a continuous linear map. -/
abbrev spProj : E4 →L[ℝ] (Fin 3 → ℝ) :=
  spatialProj ℝ 3

/-- `spProj (t, x) = x`. -/
theorem spProj_ev (t : ℝ) (x : Fin 3 → ℝ) : spProj (ev t x) = x :=
  spatialProj_finCons t x

/-- Chain rule for a field that depends only on the spatial variables. -/
theorem pd_spProj {f : (Fin 3 → ℝ) → ℝ} (hf : Differentiable ℝ f) (μ : Fin 4) (Y : E4) :
    pd μ (fun Y => f (spProj Y)) Y = fderiv ℝ f (spProj Y) (spProj (Pi.single μ 1)) :=
  by
  unfold pd
  rw [show (fun Y => f (spProj Y)) = f ∘ spProj from rfl,
    fderiv_comp Y (hf _) (spatialProj ℝ 3).differentiableAt, (spatialProj ℝ 3).fderiv]
  rfl

/-- A field that depends only on `x` has vanishing time derivative. -/
theorem pd_spProj_zero {f : (Fin 3 → ℝ) → ℝ} (hf : Differentiable ℝ f) (Y : E4) :
    pd 0 (fun Y => f (spProj Y)) Y = 0 :=
  partialDeriv_zero_comp_spatialProj (hf _)

/-- Spatial partials of a field that depends only on `x`. -/
theorem pd_spProj_succ {f : (Fin 3 → ℝ) → ℝ} (hf : Differentiable ℝ f) (c : Fin 3) (Y : E4) :
    pd c.succ (fun Y => f (spProj Y)) Y = pd c f (spProj Y) :=
  partialDeriv_succ_comp_spatialProj (hf _) c

/-- Partial derivatives of smooth functions on `ℝ³` are smooth. -/
theorem contDiff_pd3 {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (pd i f) :=
  hf.partialDeriv (by simp) i

/-- `tsupport (∂_i f) ⊆ tsupport f`. -/
theorem tsupport_pd_subset (f : (Fin 3 → ℝ) → ℝ) (i : Fin 3) : tsupport (pd i f) ⊆ tsupport f :=
  tsupport_partialDeriv_subset f i

/-- A differentiable compactly supported function with vanishing partials is zero. -/
theorem eq_zero_of_pd_eq_zero {f : (Fin 3 → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (hc : HasCompactSupport f) (h : ∀ i x, pd i f x = 0) (x : Fin 3 → ℝ) : f x = 0 :=
  eq_zero_of_partialDeriv_eq_zero hf hc h x

/-- A fixed smooth bump function on `ℝ³` (equal to `1` near `0`). -/
abbrev bump3 : ContDiffBump (0 : Fin 3 → ℝ) :=
  EinsteinBianchi.bump3

/-- The static field `E(t, x) = ∇²φ(x)` built from `φ = bump3`. -/
abbrev hessField (Y : E4) : Matrix (Fin 3) (Fin 3) ℝ :=
  EinsteinBianchi.hessField Y

/-- Entries of the Hessian of `bump3` are smooth. -/
theorem contDiff_hess (a b : Fin 3) : ContDiff ℝ ∞ (pd a (pd b bump3)) :=
  EinsteinBianchi.contDiff_hess a b

/-- Non-vacuity of the hypotheses of `prop_3_6` other than TSD initial data: the static fields
`E = ∇²φ`, `B = 0` with `φ` a smooth bump are `C²`, have compact spatial support, solve the
linearized EB system, and are nonzero. (They are not TSD at `t = 0`, since `tr E = Δφ ≢ 0`; a
nonzero solution with TSD data, e.g. the linearized Weyl field of a TT wave with compactly
supported Cauchy data, needs the solution theory of the wave equation and is not constructed.) -/
theorem prop_3_6_hyps_nonvacuous :
    ∃ E B : E4 → Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, ContDiff ℝ 2 fun Y => E Y i j) ∧ (∀ i j, ContDiff ℝ 2 fun Y => B Y i j) ∧
      (∀ s : ℝ, ∃ K : Set (Fin 3 → ℝ), IsCompact K ∧
        ∀ r ∈ Metric.closedBall s 1, ∀ x ∉ K, E (ev r x) = 0 ∧ B (ev r x) = 0) ∧
      (∀ Y : E4, 0 < Y 0 → jet4 E Y 0 = -curl (sp (jet4 B Y))) ∧
      (∀ Y : E4, 0 < Y 0 → jet4 B Y 0 = curl (sp (jet4 E Y))) ∧
      ∃ x, E (ev 0 x) ≠ 0 :=
  by
  simp only [curl_eq]; exact EinsteinBianchi.propagation_hyps_nonvacuous

end Prop36

end EB
end Feec
