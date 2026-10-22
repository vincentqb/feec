module

public import Feec.Algebra.LeviCivita
public import Feec.Algebra.TransverseTraceless
public import Mathlib.Tactic.LinearCombination

/-!
# Matrix calculus in three dimensions: jets and symbols

Row-wise vector calculus of `3 × 3` matrix fields, at the level of jets (`dA c = ∂_c A`) and of
Fourier symbols (`∂_c ↦ ξ_c`), over any commutative ring. Conventions (thesis Lemma 3.5):

* `(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}` (row-wise curl), `(div A)_a = ∂_b A_{ab}`;
* `axial A = (ε_{abc} A_{bc})_a`, `vskw A = ½ axial A` (the axial vector of `skw A`),
  `mskw v = (ε_{abc} v_c)_{ab}` (the skew matrix with `vskw (mskw v) = v`).

## Main results (thesis Lemma 3.5, proved once)

* `trace_curl`: `tr curl A = -div axial A` (`= -2 div vskw A`);
* `axial_curl`: `axial curl A = grad tr A - div Aᵀ` (`2 vskw curl A = …`);
* `div_sub_transpose`: `div (A - Aᵀ) = curl axial A` (`div skw A = curl vskw A`);
* `div_curl`: `div curl A = 0` for symmetric second jets;
* `transpose_eq_iff_axial_eq_zero`, `trace_curl_of_transpose_eq`, `transpose_curl_eq`,
  `curl_isTSD`: if `A` is symmetric, trace-free and divergence-free, so is `curl A`;
* symbols: `curlSymbol ξ A = curl (ξ ⊗ A)`, `curlSymbol_mem_ttSub` (the curl symbol maps the TSD
  fibre `TT.ttSub ξ` to itself).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §3.4 (Lemma 3.5), §4.10–4.11 (its use in Props 4.17 and 4.19)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Matrix

@[expose] public noncomputable section

namespace Feec.MatrixSymbol

variable {R : Type*} [CommRing R]

/-! ### Definitions -/

/-- Row-wise curl of a first jet, `(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}`. [QuennevilleBelair2015], Lemma 3.5 -/
def curl (dA : Fin 3 → Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun a b => ∑ c, ∑ d, leviCivita3 R b c d * dA c a d

/-- Row-wise divergence of a first jet, `(div A)_a = ∂_b A_{ab}`. [QuennevilleBelair2015], Lemma 3.5 -/
def div (dA : Fin 3 → Matrix (Fin 3) (Fin 3) R) : Fin 3 → R := fun a => ∑ b, dA b a b

/-- The axial vector `(ε_{abc} A_{bc})_a = 2 vskw A`. -/
def axial (A : Matrix (Fin 3) (Fin 3) R) : Fin 3 → R :=
  fun a => ∑ b, ∑ c, leviCivita3 R a b c * A b c

/-- `vskw A = ½ ε_{abc} A_{bc}`, the axial vector of the skew part. [QuennevilleBelair2015], Lemma 3.5 -/
def vskw [Invertible (2 : R)] (A : Matrix (Fin 3) (Fin 3) R) : Fin 3 → R := (⅟(2 : R)) • axial A

/-- The skew matrix `(mskw v)_{ab} = ε_{abc} v_c`, inverse to `vskw` on skew matrices. -/
def mskw (v : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun a b => ∑ c, leviCivita3 R a b c * v c

/-- Vector curl of a first jet `dv b c = ∂_b v_c`, `(curl v)_a = ε_{abc} ∂_b v_c`. -/
def vcurl (dv : Fin 3 → Fin 3 → R) : Fin 3 → R := fun a => ∑ b, ∑ c, leviCivita3 R a b c * dv b c

/-- Vector divergence of a first jet, `div v = ∂_c v_c`. -/
def vdiv (dv : Fin 3 → Fin 3 → R) : R := ∑ c, dv c c

/-- The jet of `tr A`, i.e. `grad tr A`. -/
def traceJet (dA : Fin 3 → Matrix (Fin 3) (Fin 3) R) : Fin 3 → R := fun c => (dA c).trace

/-- The jet of `Aᵀ`. -/
def transposeJet (dA : Fin 3 → Matrix (Fin 3) (Fin 3) R) : Fin 3 → Matrix (Fin 3) (Fin 3) R :=
  fun c => (dA c)ᵀ

/-- The symbol jet `∂_c ↦ ξ_c`: `(ξ ⊗ A) c = ξ_c A`. -/
def symbolJet (ξ : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) : Fin 3 → Matrix (Fin 3) (Fin 3) R :=
  fun c => ξ c • A

/-- The curl symbol `(curl_ξ A)_{ab} = ε_{bcd} ξ_c A_{ad}`. -/
def curlSymbol (ξ : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  curl (symbolJet ξ A)

/-! ### Elementary identities -/

theorem curl_apply (dA : Fin 3 → Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    curl dA a b = ∑ c, ∑ d, leviCivita3 R b c d * dA c a d := rfl

theorem curl_smul (r : R) (dA : Fin 3 → Matrix (Fin 3) (Fin 3) R) :
    curl (fun c => r • dA c) = r • curl dA := by
  ext a b
  simp only [curl, of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem curl_neg (dA : Fin 3 → Matrix (Fin 3) (Fin 3) R) : curl (-dA) = -curl dA := by
  ext a b; simp [curl]

theorem div_symbolJet (ξ : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) :
    div (symbolJet ξ A) = A *ᵥ ξ := by
  ext a; simp [div, symbolJet, mulVec, dotProduct, mul_comm]

theorem traceJet_symbolJet (ξ : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) :
    traceJet (symbolJet ξ A) = A.trace • ξ := by
  ext c; simp [traceJet, symbolJet, trace_smul, mul_comm]

theorem axial_apply_zero (A : Matrix (Fin 3) (Fin 3) R) : axial A 0 = A 1 2 - A 2 1 := by
  simp [axial, leviCivita3_apply, Fin.sum_univ_three]; ring

theorem axial_apply_one (A : Matrix (Fin 3) (Fin 3) R) : axial A 1 = A 2 0 - A 0 2 := by
  simp [axial, leviCivita3_apply, Fin.sum_univ_three]; ring

theorem axial_apply_two (A : Matrix (Fin 3) (Fin 3) R) : axial A 2 = A 0 1 - A 1 0 := by
  simp [axial, leviCivita3_apply, Fin.sum_univ_three]; ring

theorem axial_add (A B : Matrix (Fin 3) (Fin 3) R) : axial (A + B) = axial A + axial B := by
  ext a; simp [axial, mul_add, Finset.sum_add_distrib]

/-- A matrix is symmetric iff its axial vector vanishes (no division by `2` is needed). -/
theorem transpose_eq_iff_axial_eq_zero (A : Matrix (Fin 3) (Fin 3) R) :
    Aᵀ = A ↔ axial A = 0 := by
  constructor
  · intro h
    have hs : ∀ i j, A i j = A j i := fun i j => by
      simpa [transpose_apply] using congrFun (congrFun h j) i
    ext a
    fin_cases a <;> simp [axial_apply_zero, axial_apply_one, axial_apply_two, hs 1 2, hs 2 0,
      hs 0 1]
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
    simp only [axial_apply_zero, axial_apply_one, axial_apply_two, Pi.zero_apply,
      sub_eq_zero] at h0 h1 h2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transpose_apply, h0, h1, h2]

/-! ### Lemma 3.5 on jets -/

/-- **Lemma 3.5 (2)**: `tr curl A = -div axial A` (i.e. `-2 div vskw A`). [QuennevilleBelair2015], Lemma 3.5 -/
theorem trace_curl (dA : Fin 3 → Matrix (Fin 3) (Fin 3) R) :
    (curl dA).trace = -vdiv (fun c => axial (dA c)) := by
  simp [trace, curl, vdiv, axial, leviCivita3_apply, Fin.sum_univ_three]; ring

/-- **Lemma 3.5 (3)**: `axial curl A = grad tr A - div Aᵀ` (i.e. `2 vskw curl A = …`).
[QuennevilleBelair2015], Lemma 3.5 -/
theorem axial_curl (dA : Fin 3 → Matrix (Fin 3) (Fin 3) R) :
    axial (curl dA) = traceJet dA - div (transposeJet dA) := by
  ext a
  fin_cases a <;>
    simp [curl, axial, traceJet, div, transposeJet, trace, leviCivita3_apply,
      Fin.sum_univ_three] <;> ring

/-- `div (A - Aᵀ) = curl axial A` (i.e. `div skw A = curl vskw A`). [QuennevilleBelair2015], Lemma 3.5 -/
theorem div_sub_transpose (dA : Fin 3 → Matrix (Fin 3) (Fin 3) R) :
    div (dA - transposeJet dA) = vcurl (fun c => axial (dA c)) := by
  ext a
  fin_cases a <;>
    simp [div, transposeJet, vcurl, axial, leviCivita3_apply, Fin.sum_univ_three] <;> ring

/-- **Lemma 3.5 (1)**: `div curl A = 0` for a second jet `d2A b c = ∂_b ∂_c A` symmetric in
`(b, c)`. [QuennevilleBelair2015], Lemma 3.5 -/
theorem div_curl (d2A : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) R)
    (hsym : ∀ b c, d2A b c = d2A c b) : div (fun b => curl (d2A b)) = 0 := by
  ext a
  fin_cases a <;>
    simp [div, curl, leviCivita3_apply, Fin.sum_univ_three, hsym 1 0, hsym 2 0, hsym 2 1] <;> ring

/-- Lemma 3.5, consequence: the curl of a symmetric matrix field is trace-free.
[QuennevilleBelair2015], Lemma 3.5 -/
theorem trace_curl_of_transpose_eq {dA : Fin 3 → Matrix (Fin 3) (Fin 3) R}
    (hsym : ∀ c, (dA c)ᵀ = dA c) : (curl dA).trace = 0 := by
  rw [trace_curl]
  have : ∀ c, axial (dA c) = 0 := fun c => (transpose_eq_iff_axial_eq_zero _).1 (hsym c)
  simp [vdiv, this]

/-- Lemma 3.5, consequence (sharpened): if `A` is symmetric with `div A = 0` and
`grad tr A = 0`, then `curl A` is symmetric. [QuennevilleBelair2015], Lemma 3.5 -/
theorem transpose_curl_eq {dA : Fin 3 → Matrix (Fin 3) (Fin 3) R}
    (hsym : ∀ c, (dA c)ᵀ = dA c) (htr : traceJet dA = 0) (hdiv : div dA = 0) :
    (curl dA)ᵀ = curl dA := by
  rw [transpose_eq_iff_axial_eq_zero, axial_curl, htr, show transposeJet dA = dA from funext hsym,
    hdiv, sub_zero]

/-- **Lemma 3.5, conclusion** (first-jet part): `A` symmetric, trace-free and divergence-free
implies `curl A` symmetric and trace-free (its divergence vanishes by `div_curl`).
[QuennevilleBelair2015], Lemma 3.5 -/
theorem curl_isTSD {dA : Fin 3 → Matrix (Fin 3) (Fin 3) R} (hsym : ∀ c, (dA c)ᵀ = dA c)
    (htr : ∀ c, (dA c).trace = 0) (hdiv : div dA = 0) :
    (curl dA)ᵀ = curl dA ∧ (curl dA).trace = 0 :=
  ⟨transpose_curl_eq hsym (funext htr) hdiv, trace_curl_of_transpose_eq hsym⟩

/-! ### `vskw` forms (with `½`) -/

section Half

variable [Invertible (2 : R)]

theorem vskw_apply (A : Matrix (Fin 3) (Fin 3) R) (a : Fin 3) :
    vskw A a = ⅟2 * ∑ b, ∑ c, leviCivita3 R a b c * A b c := rfl

theorem two_smul_vskw (A : Matrix (Fin 3) (Fin 3) R) : (2 : R) • vskw A = axial A := by
  rw [vskw, smul_smul, mul_invOf_self, one_smul]

/-- **Lemma 3.5 (2)**: `tr curl A = -2 div vskw A`. [QuennevilleBelair2015], Lemma 3.5 -/
theorem trace_curl_eq_vskw (dA : Fin 3 → Matrix (Fin 3) (Fin 3) R) :
    (curl dA).trace = -2 * vdiv (fun c => vskw (dA c)) := by
  rw [trace_curl]
  simp only [vdiv, ← two_smul_vskw, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- **Lemma 3.5 (3)**: `2 vskw curl A = grad tr A - div Aᵀ`. [QuennevilleBelair2015], Lemma 3.5 -/
theorem two_smul_vskw_curl (dA : Fin 3 → Matrix (Fin 3) (Fin 3) R) :
    (2 : R) • vskw (curl dA) = traceJet dA - div (transposeJet dA) := by
  rw [two_smul_vskw, axial_curl]

theorem transpose_eq_iff_vskw_eq_zero (A : Matrix (Fin 3) (Fin 3) R) :
    Aᵀ = A ↔ vskw A = 0 := by
  rw [transpose_eq_iff_axial_eq_zero, ← two_smul_vskw]
  constructor
  · intro h
    have := congrArg (fun v => (⅟2 : R) • v) h
    simpa [smul_smul] using this
  · intro h; rw [h, smul_zero]

end Half

/-! ### Lemma 3.5 on symbols -/

theorem symbolJet_symm (ξ : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) (b c : Fin 3) :
    ξ b • symbolJet ξ A c = ξ c • symbolJet ξ A b := by
  simp [symbolJet, smul_smul, mul_comm]

/-- `curl_ξ A ξ = 0`: the symbol of `div curl = 0`. -/
theorem curlSymbol_mulVec_self (ξ : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) :
    curlSymbol ξ A *ᵥ ξ = 0 := by
  have h := div_curl (fun b c => ξ b • symbolJet ξ A c) (fun b c => symbolJet_symm ξ A b c)
  have e : (fun b => curl (fun c => ξ b • symbolJet ξ A c)) = symbolJet ξ (curlSymbol ξ A) := by
    funext b; rw [curl_smul]; rfl
  rwa [e, div_symbolJet] at h

/-- **Lemma 3.5 on the symbol**: the curl symbol maps the TSD fibre (symmetric, trace-free,
`A ξ = 0`) at `ξ` to itself. [QuennevilleBelair2015], Lemma 3.5 -/
theorem curlSymbol_mem_ttSub {ξ : Fin 3 → R} {A : Matrix (Fin 3) (Fin 3) R}
    (hA : A ∈ TT.ttSub ξ) : curlSymbol ξ A ∈ TT.ttSub ξ := by
  obtain ⟨h1, h2, h3⟩ := hA
  have hs : ∀ c, (symbolJet ξ A c)ᵀ = symbolJet ξ A c := fun c => by
    simp [symbolJet, transpose_smul, h1]
  refine ⟨?_, trace_curl_of_transpose_eq hs, curlSymbol_mulVec_self ξ A⟩
  exact transpose_curl_eq hs (by rw [traceJet_symbolJet, h2, zero_smul])
    (by rw [div_symbolJet, h3])

/-- `curl_ξ` is linear in `A`. -/
def curlSymbolₗ (ξ : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R →ₗ[R] Matrix (Fin 3) (Fin 3) R where
  toFun := curlSymbol ξ
  map_add' A B := by
    ext a b; simp [curlSymbol, curl, symbolJet, mul_add, Finset.sum_add_distrib]
  map_smul' r A := by
    ext a b
    simp only [curlSymbol, curl, symbolJet, of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
      RingHom.id_apply]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Feec.MatrixSymbol
