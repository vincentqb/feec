module

public import Feec.Ch4.TorusGroup
public import Feec.Ch4.TorusWeak

/-!
# Thesis Prop 4.19 on the flat torus `𝕋³`: the strong-symmetry complex

Prop 4.19 ([QuennevilleBelair2015, §4.11]) propagates the TSD constraint (symmetric, trace-free,
divergence-free) for the Hodge wave (4.18) of the strong-symmetry complex (4.16)
`H̊²(R) --grad grad--> H̊(curl, S) --curl--> L²(T)`, with adjoints (4.17)
`L²(R) <--div div-- H(div div, S) <--sym curl-- H(sym curl, T)`, `W0 = L²(R)`, `W1 = L²(S)`,
`W2 = L²(T)` (`R` scalars, `S` symmetric, `T` trace-free matrices), under projection and density
"conjectures". This file builds the periodic analogue on `𝕋³ = ℝ³/ℤ³`, proves all of these
hypotheses there, and proves the periodic Prop 4.19 with no hypothesis beyond the solution.

## Model

As in `Feec.Ch4.Torus`, fields are modelled by their Fourier coefficients, as real Hilbert spaces:
`L2R = ℓ²(ℤ³; ℂ)` (`scalarFourier`: `L²(𝕋³; ℂ) ≃ₗᵢ L2R`), `L2S = ℓ²(ℤ³; S)`,
`L2T = ℓ²(ℤ³; T)`, with `S = symSub`, `T = trSub` as subspaces of `ℂ³ˣ³`. `embL2` embeds `L2S`,
`L2T` isometrically into `L2M = ℓ²(ℤ³; ℂ³ˣ³)`, with range the `S`- resp. `T`-valued sequences
(`mem_fibreSub_iff_embL2`); under `Feec.Torus.matrixFourier` these are exactly the Fourier
coefficients of symmetric resp. trace-free `L²` matrix fields (`matrixFourier_mem_sym`,
`matrixFourier_mem_tr`). The operators are Fourier multipliers with `ξ = 2πk`:
`grad grad u ↦ -u ξ ξᵀ` (`hessS`), row-wise `curl A ↦ i (ξ × A_a)_a` (`curlS`, valued in `T`),
`div div A ↦ -ξᵀ A ξ` (`divdivS`), `sym curl ρ ↦ sym (i (ξ × ρ_a)_a)` (`symCurlS`). The spaces
`H²(R)`, `H(curl, S)`, `H(div div, S)`, `H(sym curl, T)`, `H¹(S)` are the corresponding
weighted-`ℓ²` conditions (`mulDomain`; `mem_H2R_iff`). As in `Feec.Ch4.Torus`, the identification
of these multipliers with weak derivatives is not formalized, and the theorems are stated for
complex-valued fields viewed as a real Hilbert space; the real-valued fields of the thesis are the
conjugate-symmetric coefficient sequences, and are preserved (section *Real-valued fields*).

## Main results

* Fibre algebra: `curlSym_mem_trSub` (`curl S ⊆ T`), `curlSym_hessM` (`curl grad grad = 0`),
  `adjoint_hessS` (`(grad grad)* = div div`), `adjoint_curlS` (**`curl* = sym curl`** for
  `curl : S → T`), `curlS_projS`/`symCurlS_projT` (`P_TSD` commutes with `curl` and
  `sym curl`), `norm_freq_mul_norm_projS_le` (`|ξ| ‖P_TSD A‖ ≤ ‖curl_ξ A‖`), `divdivS_eq_zero`.
* `symComplex : HilbertComplex2 L2R L2S L2T`, the periodic complex (4.16): closed, densely
  defined, `curl ∘ grad grad = 0`; `adjoint_hessT`/`adjoint_hessT_domain`,
  `adjoint_curlST`/`adjoint_curlST_domain` (the adjoint complex (4.17)).
* The thesis' hypotheses, proved: `projS_mem_HcurlS_HdivdivS`
  (`P_TSD (H(curl, S) ∩ H(div div, S)) ⊆ H(curl, S) ∩ H(div div, S)`), `projT_mem_HsymCurlT`
  (`P_TSD H(sym curl, T) ⊆ H(sym curl, T)`), `projS_mem_H1S` (`P_TSD H(curl, S) ⊆ H¹(S)`),
  `dense_HcurlS_L2TSDS`, `dense_HsymCurlT_L2TSDT` (the density hypotheses).
* All hypotheses of `Feec.Constraints.prop_4_17` for `S1 = S2 = L²(TSD)`: `L2TSDS_le_ker`,
  `projKc_mem_domL`, `curlST_mem_L2TSDT`, `adjoint_curlST_mem_L2TSDS`; hence
  **`prop_4_19_torus`** and its group form `prop_4_19_torus_group`.
* **Existence**: `symGroup`, an explicit Stone group (`Feec.UnitaryGroupGenerator`) for `-L`,
  built as the fibrewise exponential of the skew symbol `waveSymS` (`waveSymS_skew`) with the
  machinery of `Feec.Ch4.TorusGroup` (`mulGroup`, `totL2`) and `UnitaryGroupGenerator.transport`;
  its generator domain is exactly `D(L)` (`mem_domain_neg_waveOp_sym_iff`,
  `neg_waveOp_sym_apply`). Hence **`prop_4_19_torus_exists`** (a strong solution exists for all
  TSD data `E₀ ∈ H(curl, S)`, `B₀ ∈ H(sym curl, T)`, and it propagates the constraints),
  `prop_4_19_torus_symGroup` (unconditional group form), `dense_domL_sym`,
  `mem_closure_domL_inf_Kc_sym` (`D(L) ∩ K` dense in `K`), and `prop_4_19_torus_iff`.
* **Closed range** (the thesis defers it to its next chapter): `symComplex_closedRange`, from the
  uniform fibre preimage bounds `hessS_preimage` and `curlS_preimage` (the latter via
  `norm_divR_sq_le_curlR`: `|A ξ| ≤ |ξ × A|` for symmetric `A` with `ξᵀ A ξ = 0`) and the
  general `isClosed_range_mulOp`; hence the Hodge decomposition without closures
  `symComplex_hodge`.
* Bridge to the `ℂ³ˣ³`-valued model of `Feec.Ch4.Torus` (Prop 4.17): `map_embL2_L2TSDS`,
  `map_embL2_L2TSDT` (`embL2` maps both `L²(TSD)`s onto `Feec.Torus.L2TSD`), `embL2_projS`,
  `embL2_projT`, `embL2_sym_mem_Hcurl_iff`, `curlT_embL2` (`curl` on `S` is the matrix curl),
  `embL2_adjoint_curlST_apply` (`curl* = sym ∘ curl`).
* **Real-valued fields** (conjugate-symmetric coefficients, as `Feec.Torus.IsReal`): `IsRealR`,
  `IsRealS`, `IsRealT` (`isRealR_scalarFourier_iff`: `f̄ = f`; `isRealS_iff_embL2`,
  `isRealT_iff_embL2`: the matrix `IsReal`). They are preserved by `P_TSD` (`isRealS_projS`,
  `isRealT_projT`), `grad grad` (`isRealS_hessT`), `curl` (`isRealT_curlST`), `div div`
  (`isRealR_divdiv`), `sym curl` (`isRealS_symCurl`) and the group (`isRealTot_symGroup`, all
  `t ∈ ℝ`); every strong solution with real data is real (`isRealTot_of_isStrongSolution`), and
  **`prop_4_19_torus_exists_real`** is Prop 4.19 on `𝕋³` within real fields. Physical-space
  bridges for matrix fields: `isRealS_iff_entries`, `isRealT_iff_entries` (every entry
  real-valued), with `exists_embL2_sym`, `exists_embL2_tr`. The real fields form closed
  subspaces `realR`, `realS`, `realT`, `realTot` (`isClosed_realTot`), preserved by `I - P_TSD`
  (`isRealS_sub_projS`, `isRealT_sub_projT`); `K ∩ realTot` is invariant
  (`symGroup_mem_Kc_inf_realTot`). **Real Hodge decomposition** `symComplex_hodge_real` (all
  three pieces real), with real potentials (`exists_real_hessT_preimage`,
  `exists_real_symCurl_preimage`), via the reflection-conjugation `reflL2`.
* **Prop 4.19 on the real Hilbert space**: a Stone group restricts to a closed invariant
  subspace, generated by the restricted generator (`restrictGroup`, `restrictGen`); hence
  `symGroupReal` on `realTot`, generated by `symGenReal` (the restriction of `-L`), and
  **`prop_4_19_torus_real_space`** (existence on the real space, and every real strong solution
  propagates the constraints and solves the reduced system) with `real_space_unique`.

## Correction

Checked against the thesis text:
* The spaces and adjoints of (4.16)/(4.17) are right: `curl` maps `S` into `T`
  (`curlSym_mem_trSub`), its adjoint `L²(T) → L²(S)` is `sym curl = P_S curl` with domain
  `H(sym curl, T)` (`adjoint_curlS`, `adjoint_curlST_domain`), and `(grad grad)* = div div`
  with no sign (`adjoint_hessS`: the symbol `-ξ ξᵀ` is self-adjoint).
* The initial-data space in the statement of Prop 4.19,
  `H² × H(curl, S) ∩ H̊(div div, S) × H̊(sym curl, T)`, misplaces the boundary conditions; it
  should be `D(L) = H̊²(R) × (H̊(curl, S) ∩ H(div div, S)) × H(sym curl, T)`, as in the proof
  and in the solution spaces after (4.17). On `𝕋³` there are no boundary conditions.
* In the solution space after (4.17), `E ∈ C¹([0, T]; L²(M))` is imprecise rather than wrong
  (`E` takes values in the closed subspace `L²(S) = W1`, so it is equally `C¹` into `L²(S)`);
  in the proof, `-grad(H̊²(R) ∩ 0)` should read `-grad grad(H̊²(R) ∩ {0})`.
* In the proof's third itemized check, `div div(H̊(curl, S) ∩ L²(TSD)) = 0` applies `div div`
  outside its domain `H(div div, S)` as written; it is meaningful because
  `L²(TSD) ⊆ H(div div, S)` (`L2TSDS_le_HdivdivS`), and the relevant set is the middle factor
  of `D(L) ∩ K`, as in `L2TSDS_le_ker`.
* The projection and density "conjectures" are theorems on `𝕋³` (see above), and the density
  ones are not needed (`prop_4_17`). The projections `P_{L²(TSD)}` in `L²(S)`, `L²(T)` agree
  with the one in `L²(M)` (`coe_projS`, `coe_projT`, `embL2_projS`, `embL2_projT`), so the
  thesis' notation is unambiguous.
* "If we show that these complexes are closed, there is a unique solution": existence and
  uniqueness need only skew-adjointness of `L` (`symGroup` is built without closed range);
  closed range holds anyway on `𝕋³` (`symComplex_closedRange`).

What remains open: the bounded-domain setting of the thesis (`H̊²`, `H̊(curl, S)`), where the
projection conjecture is not settled here (cf. the docstring of `Feec.Constraints.prop_4_17`
and `Feec.Ch4.BoundedDomain` for the matrix complex of Prop 4.17).

## References

* [QuennevilleBelair2015], §3.4 (Lemma 3.5), §4.11 ((4.16)–(4.18), Prop 4.19), §4.10
  (Prop 4.17, the analogous matrix complex)
* [ArnoldHu2021], [Eastwood2000] (the `grad grad`–`curl`–`div` complex of symmetric and
  trace-free matrix fields, from the BGG construction)
* [ACBY1997] (the Einstein–Bianchi system)
* [AFW2010], [Arnold2018], [BruningLesch1992] (Hilbert complexes)
* [Pazy1983], §1.10 (unitary groups and Stone's theorem, behind `Feec.UnitaryGroupGenerator`)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace
open LinearPMap Set

namespace Feec.TorusSym

open Feec.Torus

section Fibre

/-- The transpose of a matrix, as a real-linear map. -/
def trM : Mat3 →L[ℝ] Mat3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => mat fun a b => M (b, a)
      map_add' := fun M N => by ext ⟨a, b⟩; simp
      map_smul' := fun r M => by ext ⟨a, b⟩; simp }

/-- Entries of `trM M = Mᵀ`. -/
theorem trM_apply (M : Mat3) (a b : Fin 3) : trM M (a, b) = M (b, a) := rfl

/-- Transposition is self-adjoint. -/
theorem inner_trM (X A : Mat3) : ⟪trM X, A⟫ = ⟪X, trM A⟫ := by
  simp only [inner_mat, trM_apply]
  exact Finset.sum_comm

/-- The symmetric part `sym M = (M + Mᵀ)/2`. -/
def symM : Mat3 →L[ℝ] Mat3 := (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ Mat3 + trM)

/-- Entries of `sym M`. -/
theorem symM_apply (M : Mat3) (a b : Fin 3) :
    symM M (a, b) = (1 / 2 : ℝ) • (M (a, b) + M (b, a)) := rfl

/-- The symmetric matrices `S`. -/
def symSub : Submodule ℝ Mat3 where
  carrier := {M | ∀ a b, M (a, b) = M (b, a)}
  zero_mem' := by simp
  add_mem' := fun {M N} hM hN a b => by simp [hM a b, hN a b]
  smul_mem' := fun r M hM a b => by simp [hM a b]

/-- The trace-free matrices `T`. -/
def trSub : Submodule ℝ Mat3 where
  carrier := {M | ∑ a, M (a, a) = 0}
  zero_mem' := by simp
  add_mem' := fun {M N} hM hN => by
    simp only [Set.mem_ofPred_eq] at *; simp [Finset.sum_add_distrib, hM, hN]
  smul_mem' := fun r M hM => by
    simp only [Set.mem_ofPred_eq] at *; simp [Complex.real_smul, ← Finset.mul_sum, hM]

/-- Membership in `S`. -/
theorem mem_symSub {M : Mat3} : M ∈ symSub ↔ ∀ a b, M (a, b) = M (b, a) := Iff.rfl

/-- Membership in `T`. -/
theorem mem_trSub {M : Mat3} : M ∈ trSub ↔ ∑ a, M (a, a) = 0 := Iff.rfl

/-- Symmetric matrices are fixed by transposition. -/
theorem trM_of_mem_symSub {M : Mat3} (hM : M ∈ symSub) : trM M = M := by
  ext ⟨a, b⟩; exact (hM a b).symm

/-- `sym M` is symmetric. -/
theorem symM_mem_symSub (M : Mat3) : symM M ∈ symSub := fun a b => by
  simp only [symM_apply, add_comm]

/-- `sym` fixes symmetric matrices. -/
theorem symM_of_mem_symSub {M : Mat3} (hM : M ∈ symSub) : symM M = M := by
  ext ⟨a, b⟩; rw [symM_apply, ← hM a b, ← two_smul ℝ, smul_smul]; norm_num

/-- `sym` is self-adjoint. -/
theorem inner_symM (X A : Mat3) : ⟪symM X, A⟫ = ⟪X, symM A⟫ := by
  simp only [symM, _root_.smul_apply, _root_.add_apply,
    ContinuousLinearMap.id_apply, inner_smul_left, inner_smul_right, inner_add_left,
    inner_add_right, inner_trM]
  simp

/-- Against a symmetric matrix, `sym` can be dropped: `⟪sym X, A⟫ = ⟪X, A⟫`. -/
theorem inner_symM_of_mem {X A : Mat3} (hA : A ∈ symSub) : ⟪symM X, A⟫ = ⟪X, A⟫ := by
  rw [inner_symM, symM_of_mem_symSub hA]

/-- TSD matrices are symmetric. -/
theorem tsd_le_symSub (ξ : Freq) : tsd ξ ≤ symSub := fun _ h => h.1

/-- TSD matrices are trace-free. -/
theorem tsd_le_trSub (ξ : Freq) : tsd ξ ≤ trSub := fun _ h => h.2.1

/-- `sym` maps the TSD fibre to itself (it fixes it). -/
theorem symM_mem_tsd {ξ : Freq} {M : Mat3} (hM : M ∈ tsd ξ) : symM M ∈ tsd ξ := by
  rwa [symM_of_mem_symSub (tsd_le_symSub ξ hM)]

/-- The curl of a symmetric matrix is trace-free (`curl : S → T`, so (4.16) is well typed).

See [QuennevilleBelair2015, §3.4, Lemma 3.5 and §4.11, (4.16)]. -/
theorem curlSym_mem_trSub (ξ : Freq) {M : Mat3} (hM : M ∈ symSub) : curlSym ξ M ∈ trSub := by
  have s10 := hM 1 0; have s20 := hM 2 0; have s21 := hM 2 1
  simp only [mem_trSub, Fin.sum_univ_three, curlSym_apply, jM_apply, curlR_apply, cross]
  simp [s10, s20, s21]
  ring

/-- The Hessian symbol `c ↦ -c ξ ξᵀ` (`∂_a ∂_b ↦ (i ξ_a)(i ξ_b)`), with values in matrices. -/
def hessM (ξ : Freq) : ℂ →L[ℝ] Mat3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => mat fun a b => -(c * ξ a * ξ b)
      map_add' := fun c d => by ext ⟨a, b⟩; simp; ring
      map_smul' := fun r c => by ext ⟨a, b⟩; simp [Complex.real_smul]; ring }

/-- Entries of the Hessian symbol. -/
theorem hessM_apply (ξ : Freq) (c : ℂ) (a b : Fin 3) : hessM ξ c (a, b) = -(c * ξ a * ξ b) := rfl

/-- The Hessian symbol is an outer product `(-c ξ) ξᵀ`. -/
theorem hessM_eq_outer (ξ : Freq) (c : ℂ) : hessM ξ c = outer (vec fun a => -(c * ξ a)) ξ := by
  ext ⟨a, b⟩; simp [hessM_apply, outer]

/-- `‖ξ ξᵀ c‖ = |ξ|² |c|` (Frobenius norm). -/
theorem norm_hessM (ξ : Freq) (c : ℂ) : ‖hessM ξ c‖ = ‖ξ‖ ^ 2 * ‖c‖ := by
  have h : ‖hessM ξ c‖ ^ 2 = (‖ξ‖ ^ 2 * ‖c‖) ^ 2 := by
    rw [norm_sq_mat, mul_pow, norm_sq_freq, Complex.sq_norm, Complex.normSq_apply]
    simp only [hessM_apply, Fin.sum_univ_three]
    simp [Complex.mul_re, Complex.mul_im]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h

/-- Hessians are symmetric. -/
theorem hessM_mem_symSub (ξ : Freq) (c : ℂ) : hessM ξ c ∈ symSub := fun a b => by
  simp only [hessM_apply]; ring

/-- `curl ∘ grad grad = 0` on the symbol level. -/
theorem curlSym_hessM (ξ : Freq) (c : ℂ) : curlSym ξ (hessM ξ c) = 0 := by
  rw [hessM_eq_outer, curlSym_outer]

/-- Symmetric matrices `S`, the fibre of `W1 = L²(S)`. -/
abbrev Sym3 := ↥symSub
/-- Trace-free matrices `T`, the fibre of `W2 = L²(T)`. -/
abbrev Tr3 := ↥trSub

/-- The fibre of `grad grad : H²(R) → H(curl, S)`: `c ↦ -c ξ ξᵀ ∈ S`. -/
def hessS (ξ : Freq) : ℂ →L[ℝ] Sym3 := (hessM ξ).codRestrict symSub (hessM_mem_symSub ξ)

/-- The fibre of `curl : H(curl, S) → L²(T)`. -/
def curlS (ξ : Freq) : Sym3 →L[ℝ] Tr3 :=
  (curlSym ξ ∘L symSub.subtypeL).codRestrict trSub fun M => curlSym_mem_trSub ξ M.2

/-- The fibre of `div div : H(div div, S) → L²(R)`: `A ↦ -ξᵀ A ξ`. -/
def divdivS (ξ : Freq) : Sym3 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => -∑ a, ∑ b, (A : Mat3) (a, b) * ξ a * ξ b
      map_add' := fun A B => by
        simp [add_mul, Finset.sum_add_distrib]; ring
      map_smul' := fun r A => by
        simp [Complex.real_smul, Finset.mul_sum, mul_assoc] }

/-- The fibre of `sym curl : H(sym curl, T) → L²(S)`. -/
def symCurlS (ξ : Freq) : Tr3 →L[ℝ] Sym3 :=
  (symM ∘L curlSym ξ ∘L trSub.subtypeL).codRestrict symSub fun _ => symM_mem_symSub _

/-- `hessS ξ c` is the Hessian symbol. -/
theorem coe_hessS (ξ : Freq) (c : ℂ) : (hessS ξ c : Mat3) = hessM ξ c := rfl

/-- `curlS ξ A` is the curl symbol of `A`. -/
theorem coe_curlS (ξ : Freq) (A : Sym3) : (curlS ξ A : Mat3) = curlSym ξ A := rfl

/-- `symCurlS ξ ρ = sym (curl_ξ ρ)`. -/
theorem coe_symCurlS (ξ : Freq) (ρ : Tr3) : (symCurlS ξ ρ : Mat3) = symM (curlSym ξ ρ) := rfl

/-- Entries of `sym curl`: `(sym curl_ξ ρ)_{ab} = ((curl_ξ ρ)_{ab} + (curl_ξ ρ)_{ba}) / 2`. -/
theorem symCurlS_apply (ξ : Freq) (ρ : Tr3) (a b : Fin 3) :
    (symCurlS ξ ρ : Mat3) (a, b) =
      (1 / 2 : ℝ) • (curlSym ξ ρ (a, b) + curlSym ξ ρ (b, a)) := rfl

/-- `divdivS ξ A = -∑ ξ_a ξ_b A_{ab}`. -/
theorem divdivS_apply (ξ : Freq) (A : Sym3) :
    divdivS ξ A = -∑ a, ∑ b, (A : Mat3) (a, b) * ξ a * ξ b := rfl

/-- `curl_ξ` is symmetric for the real inner product. -/
theorem inner_curlSym (ξ : Freq) (A B : Mat3) : ⟪curlSym ξ A, B⟫ = ⟪A, curlSym ξ B⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_curlSym]

/-- **`(grad grad)* = div div`** fibrewise, as in the adjoint complex (4.17).

See [QuennevilleBelair2015, §4.11, (4.17)]. -/
theorem adjoint_hessS (ξ : Freq) : ContinuousLinearMap.adjoint (hessS ξ) = divdivS ξ := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun A c => ?_).symm
  rw [Submodule.coe_inner, coe_hessS, divdivS_apply, Complex.inner, inner_mat]
  simp only [hessM_apply, Fin.sum_univ_three]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- **`curl* = sym curl`** fibrewise (`curl : S → T`), as in the adjoint complex (4.17).

See [QuennevilleBelair2015, §4.11, (4.17)]. -/
theorem adjoint_curlS (ξ : Freq) : ContinuousLinearMap.adjoint (curlS ξ) = symCurlS ξ := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun ρ A => ?_).symm
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_symCurlS, coe_curlS,
    inner_symM_of_mem A.2, inner_curlSym]

/-- The TSD fibre inside `S`. -/
def tsdS (ξ : Freq) : Submodule ℝ Sym3 := (tsd ξ).comap symSub.subtype

/-- The TSD fibre inside `T`. -/
def tsdT (ξ : Freq) : Submodule ℝ Tr3 := (tsd ξ).comap trSub.subtype

/-- The orthogonal projection onto `K ≤ U`, computed inside `U`, is the ambient projection. -/
theorem coe_starProjection_comap {U K : Submodule ℝ Mat3} (h : K ≤ U) (x : U) :
    ((K.comap U.subtype).starProjection x : Mat3) = K.starProjection (x : Mat3) := by
  have hmem : K.starProjection (x : Mat3) ∈ U := h (K.starProjection_apply_mem _)
  have : (K.comap U.subtype).starProjection x = ⟨_, hmem⟩ := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (K.starProjection_apply_mem _) fun w hw => ?_
    rw [Submodule.coe_inner]
    exact K.starProjection_inner_eq_zero _ _ hw
  rw [this]

/-- The TSD projection in `S` is the ambient TSD projection. -/
theorem coe_projS (ξ : Freq) (A : Sym3) :
    ((tsdS ξ).starProjection A : Mat3) = (tsd ξ).starProjection (A : Mat3) :=
  coe_starProjection_comap (tsd_le_symSub ξ) A

/-- The TSD projection in `T` is the ambient TSD projection. -/
theorem coe_projT (ξ : Freq) (ρ : Tr3) :
    ((tsdT ξ).starProjection ρ : Mat3) = (tsd ξ).starProjection (ρ : Mat3) :=
  coe_starProjection_comap (tsd_le_trSub ξ) ρ

/-- `P_TSD ∘ sym = P_TSD` (TSD matrices are symmetric). -/
theorem proj_symM (ξ : Freq) (X : Mat3) :
    (tsd ξ).starProjection (symM X) = (tsd ξ).starProjection X := by
  rw [starProjection_comm_of_selfAdj _ symM inner_symM (fun _ h => symM_mem_tsd h),
    symM_of_mem_symSub (tsd_le_symSub _ ((tsd ξ).starProjection_apply_mem _))]

/-- `curl P_TSD = P_TSD curl` on `S` (values in `T`). -/
theorem curlS_projS (ξ : Freq) (A : Sym3) :
    curlS ξ ((tsdS ξ).starProjection A) = (tsdT ξ).starProjection (curlS ξ A) := by
  apply Subtype.ext
  rw [coe_curlS, coe_projS, coe_projT, coe_curlS, proj_curlSym]

/-- `sym curl P_TSD = P_TSD sym curl` on `T` (values in `S`). -/
theorem symCurlS_projT (ξ : Freq) (ρ : Tr3) :
    symCurlS ξ ((tsdT ξ).starProjection ρ) = (tsdS ξ).starProjection (symCurlS ξ ρ) := by
  apply Subtype.ext
  rw [coe_symCurlS, coe_projT, coe_projS, coe_symCurlS, proj_symM, ← proj_curlSym,
    symM_of_mem_symSub (tsd_le_symSub _ ((tsd ξ).starProjection_apply_mem _))]

/-- Fibre estimate for `H(curl, S)`: `‖curl P_TSD A‖ ≤ ‖curl A‖`. -/
theorem norm_curlS_projS_le (ξ : Freq) (A : Sym3) :
    ‖curlS ξ ((tsdS ξ).starProjection A)‖ ≤ ‖curlS ξ A‖ := by
  rw [curlS_projS]; exact Submodule.norm_starProjection_apply_le _ _

/-- Fibre estimate for `H(sym curl, T)`: `‖sym curl P_TSD ρ‖ ≤ ‖sym curl ρ‖`. -/
theorem norm_symCurlS_projT_le (ξ : Freq) (ρ : Tr3) :
    ‖symCurlS ξ ((tsdT ξ).starProjection ρ)‖ ≤ ‖symCurlS ξ ρ‖ := by
  rw [symCurlS_projT]; exact Submodule.norm_starProjection_apply_le _ _

/-- Key `H¹` fibre estimate on `S`: `|ξ| ‖P_TSD A‖ ≤ ‖curl A‖`. -/
theorem norm_freq_mul_norm_projS_le (ξ : Freq) (A : Sym3) :
    ‖ξ‖ * ‖(tsdS ξ).starProjection A‖ ≤ ‖curlS ξ A‖ := by
  rw [← Submodule.norm_coe, ← Submodule.norm_coe (curlS ξ A), coe_projS, coe_curlS]
  exact norm_freq_mul_norm_proj_le _ _

/-- TSD matrices are `div div`-free on the symbol level. -/
theorem divdivS_eq_zero {ξ : Freq} {A : Sym3} (hA : A ∈ tsdS ξ) : divdivS ξ A = 0 := by
  have h : ∀ a, ∑ b, (A : Mat3) (a, b) * ξ b = 0 := hA.2.2
  rw [divdivS_apply, neg_eq_zero]
  refine Finset.sum_eq_zero fun a _ => ?_
  calc ∑ b, (A : Mat3) (a, b) * ξ a * ξ b = ξ a * ∑ b, (A : Mat3) (a, b) * ξ b := by
        rw [Finset.mul_sum]; congr 1; ext b; ring
    _ = 0 := by rw [h a, mul_zero]

end Fibre

section Periodic

open HilbertComplex2 Constraints

/-- Fourier coefficients of scalar fields, `W0 = L²(𝕋³; ℂ)`. -/
abbrev L2R := L2 Z3 ℂ
/-- Fourier coefficients of symmetric-matrix fields, `W1 = L²(𝕋³; S)`. -/
abbrev L2S := L2 Z3 Sym3
/-- Fourier coefficients of trace-free-matrix fields, `W2 = L²(𝕋³; T)`. -/
abbrev L2T := L2 Z3 Tr3

/-- The periodic `grad grad : H²(R) → L²(S)` on the Fourier side. -/
def hessT : L2R →ₗ.[ℝ] L2S := mulOp fun k => hessS (freq k)
/-- The periodic row-wise `curl : H(curl, S) → L²(T)` on the Fourier side. -/
def curlST : L2S →ₗ.[ℝ] L2T := mulOp fun k => curlS (freq k)
/-- `H²(R)`: `(|ξ_k|² u_k)_k ∈ ℓ²`, as the domain of `grad grad`. -/
def H2R : Submodule ℝ L2R := mulDomain fun k => hessS (freq k)
/-- `H²(R)` is the weighted space `(|ξ_k|² u_k)_k ∈ ℓ²`. -/
theorem mem_H2R_iff {u : L2R} : u ∈ H2R ↔ Memℓp (fun k => ‖freq k‖ ^ 2 * ‖u k‖) 2 := by
  change Memℓp _ 2 ↔ _
  rw [← memℓp_norm_iff]
  have : ∀ k, ‖hessS (freq k) ((u : L2R) k)‖ = ‖freq k‖ ^ 2 * ‖(u : L2R) k‖ := fun k => by
    rw [← Submodule.norm_coe, coe_hessS, norm_hessM]
  simp only [this]

/-- `H(curl, S)`. -/
def HcurlS : Submodule ℝ L2S := mulDomain fun k => curlS (freq k)
/-- `H(div div, S)`. -/
def HdivdivS : Submodule ℝ L2S := mulDomain fun k => divdivS (freq k)
/-- `H(sym curl, T)`. -/
def HsymCurlT : Submodule ℝ L2T := mulDomain fun k => symCurlS (freq k)
/-- `H¹(S)`: `(|ξ_k| A_k)_k ∈ ℓ²`. -/
def H1S : Submodule ℝ L2S := mulDomain fun k => ‖freq k‖ • ContinuousLinearMap.id ℝ Sym3
/-- `L²(TSD)` as a subspace of `L²(S)`. -/
def L2TSDS : Submodule ℝ L2S := fibreSub fun k => tsdS (freq k)
/-- `L²(TSD)` as a subspace of `L²(T)`. -/
def L2TSDT : Submodule ℝ L2T := fibreSub fun k => tsdT (freq k)

/-- `L²(TSD) ⊆ L²(S)` is closed, so admits an orthogonal projection. -/
instance : L2TSDS.HasOrthogonalProjection :=
  inferInstanceAs (fibreSub fun k => tsdS (freq k)).HasOrthogonalProjection

/-- `L²(TSD) ⊆ L²(T)` is closed, so admits an orthogonal projection. -/
instance : L2TSDT.HasOrthogonalProjection :=
  inferInstanceAs (fibreSub fun k => tsdT (freq k)).HasOrthogonalProjection

/-- `(grad grad)* = div div`, with domain `H(div div, S)`. -/
theorem adjoint_hessT : hessT† = mulOp fun k => divdivS (freq k) := by
  rw [hessT, adjoint_mulOp]; simp only [adjoint_hessS]

/-- `curl* = sym curl`, with domain `H(sym curl, T)`. -/
theorem adjoint_curlST : curlST† = mulOp fun k => symCurlS (freq k) := by
  rw [curlST, adjoint_mulOp]; simp only [adjoint_curlS]

/-- The domain of `(grad grad)*` is `H(div div, S)`. -/
theorem adjoint_hessT_domain : hessT†.domain = HdivdivS := by rw [adjoint_hessT]; rfl

/-- The domain of `curl*` is `H(sym curl, T)`. -/
theorem adjoint_curlST_domain : curlST†.domain = HsymCurlT := by rw [adjoint_curlST]; rfl

/-- **The periodic strong-symmetry complex (4.16)**
`H²(R) --grad grad--> H(curl, S) --curl--> L²(T)` on `𝕋³`.

See [QuennevilleBelair2015, §4.11, (4.16)]; cf. [ArnoldHu2021]. -/
def symComplex : HilbertComplex2 L2R L2S L2T where
  d0 := hessT
  d1 := curlST
  dense0 := dense_mulDomain _
  dense1 := dense_mulDomain _
  closed0 := isClosed_mulOp _
  closed1 := isClosed_mulOp _
  map_mem x := by
    change Memℓp _ 2
    convert (zero_memℓp : Memℓp (0 : Z3 → Tr3) 2) using 1
    funext k
    exact Subtype.ext (curlSym_hessM (freq k) ((x : L2R) k))
  comp_zero x := by
    refine lp.ext (funext fun k => ?_)
    rw [lp.coeFn_zero, Pi.zero_apply]
    exact Subtype.ext (curlSym_hessM (freq k) ((x : L2R) k))

/-- `P_TSD` on `L²(S)` acts fibrewise. -/
theorem projS_apply (A : L2S) (k : Z3) :
    L2TSDS.starProjection A k = (tsdS (freq k)).starProjection (A k) :=
  starProjection_fibreSub_apply _ A k

/-- `P_TSD` on `L²(T)` acts fibrewise. -/
theorem projT_apply (ρ : L2T) (k : Z3) :
    L2TSDT.starProjection ρ k = (tsdT (freq k)).starProjection (ρ k) :=
  starProjection_fibreSub_apply _ ρ k

/-- `P_TSD H(curl, S) ⊆ H(curl, S)`. -/
theorem projS_mem_HcurlS {A : L2S} (hA : A ∈ HcurlS) : L2TSDS.starProjection A ∈ HcurlS := by
  change Memℓp _ 2
  refine Memℓp.mono' hA fun k => ?_
  rw [projS_apply]
  exact norm_curlS_projS_le _ _

/-- `P_TSD H(curl, S) ⊆ H¹(S)`. -/
theorem projS_mem_H1S {A : L2S} (hA : A ∈ HcurlS) : L2TSDS.starProjection A ∈ H1S := by
  change Memℓp _ 2
  refine Memℓp.mono' hA fun k => ?_
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, norm_smul, norm_norm,
    projS_apply]
  exact norm_freq_mul_norm_projS_le _ _

/-- `P_TSD H(sym curl, T) ⊆ H(sym curl, T)`. -/
theorem projT_mem_HsymCurlT {ρ : L2T} (hρ : ρ ∈ HsymCurlT) :
    L2TSDT.starProjection ρ ∈ HsymCurlT := by
  change Memℓp _ 2
  refine Memℓp.mono' hρ fun k => ?_
  rw [projT_apply]
  exact norm_symCurlS_projT_le _ _

/-- `L²(TSD) ⊆ H(div div, S)`. -/
theorem L2TSDS_le_HdivdivS : L2TSDS ≤ HdivdivS := fun A hA => by
  change Memℓp _ 2
  convert (zero_memℓp : Memℓp (0 : Z3 → ℂ) 2) using 1
  funext k
  exact divdivS_eq_zero (hA k)

/-- `P_TSD (H(curl, S) ∩ H(div div, S)) ⊆ H(curl, S) ∩ H(div div, S)` (first hypothesis of
Prop 4.19). -/
theorem projS_mem_HcurlS_HdivdivS {A : L2S} (hA : A ∈ HcurlS ⊓ HdivdivS) :
    L2TSDS.starProjection A ∈ HcurlS ⊓ HdivdivS :=
  ⟨projS_mem_HcurlS hA.1, L2TSDS_le_HdivdivS (L2TSDS.starProjection_apply_mem A)⟩

/-- `L²(TSD) ⊆ ker div div` (`hS1` of `prop_4_17`). -/
theorem L2TSDS_le_ker : L2TSDS ≤ symComplex.d0†.ker := by
  intro A hA
  change A ∈ hessT†.ker
  have hdom : A ∈ hessT†.domain := adjoint_hessT_domain ▸ L2TSDS_le_HdivdivS hA
  refine LinearPMap.mem_ker_iff.2 ⟨⟨A, hdom⟩, rfl, lp.ext (funext fun k => ?_)⟩
  have h := adjoint_mulOp_apply (fun k => hessS (freq k)) ⟨A, hdom⟩ k
  rw [adjoint_hessS] at h
  rw [lp.coeFn_zero, Pi.zero_apply]
  exact h.trans (divdivS_eq_zero (hA k))

/-- `curl` maps `H(curl, S) ∩ L²(TSD)` into `L²(TSD)` (`hd1` of `prop_4_17`).

See [QuennevilleBelair2015, §3.4, Lemma 3.5]. -/
theorem curlST_mem_L2TSDT (u : symComplex.d1.domain) (hu : (u : L2S) ∈ L2TSDS) :
    symComplex.d1 u ∈ L2TSDT := fun k => curlSym_mem_tsd (hu k)

/-- `curl* = sym curl` maps `H(sym curl, T) ∩ L²(TSD)` into `L²(TSD)` (`hd1s` of
`prop_4_17`). -/
theorem adjoint_curlST_mem_L2TSDS (ρ : symComplex.d1†.domain) (hρ : (ρ : L2T) ∈ L2TSDT) :
    symComplex.d1† ρ ∈ L2TSDS := fun k => by
  have h := adjoint_mulOp_apply (fun k => curlS (freq k)) ρ k
  rw [adjoint_curlS] at h
  change ((symComplex.d1† ρ k : Sym3) : Mat3) ∈ tsd (freq k)
  exact h ▸ symM_mem_tsd (curlSym_mem_tsd (hρ k))

/-- **The projection hypothesis of Prop 4.19 holds on `𝕋³`** (`hPD` of `prop_4_17`):
`P_K D(L) ⊆ D(L)` for `K = {0} × L²(TSD) × L²(TSD)`, where
`D(L) = H²(R) × (H(curl, S) ∩ H(div div, S)) × H(sym curl, T)`.

See [QuennevilleBelair2015, §4.11, Prop 4.19] (first itemized hypothesis of Thm 4.4/4.5). -/
theorem projKc_mem_domL : ∀ x ∈ symComplex.domL,
    projKc L2R L2TSDS L2TSDT x ∈ symComplex.domL := by
  intro x hx
  rw [Constraints.mem_domL] at hx ⊢
  rw [tot_projKc]
  refine ⟨symComplex.d0.domain.zero_mem, ⟨projS_mem_HcurlS hx.2.1.1, ?_⟩, ?_⟩
  · exact (LinearPMap.mem_ker_iff.1 (L2TSDS_le_ker (L2TSDS.starProjection_apply_mem _))).elim
      fun y hy => hy.1 ▸ y.2
  · have h : (tot L2R L2S L2T x).2.2 ∈ HsymCurlT := by
      have := hx.2.2; change _ ∈ curlST†.domain at this; rwa [adjoint_curlST_domain] at this
    change _ ∈ curlST†.domain
    rw [adjoint_curlST_domain]
    exact projT_mem_HsymCurlT h

/-- Finitely supported sequences in a fibrewise subspace lie in the domain of any multiplier, so
`D(m) ∩ fibreSub K` is dense in `fibreSub K`. -/
theorem mem_closure_mulDomain_inf_fibreSub {ι E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (m : ι → E →L[ℝ] F) (K : ι → Submodule ℝ E) {u : L2 ι E} (hu : u ∈ fibreSub K) :
    u ∈ closure ((mulDomain m ⊓ fibreSub K : Submodule ℝ (L2 ι E)) : Set (L2 ι E)) := by
  classical
  have h := lp.hasSum_single (p := 2) (by norm_num) u
  refine mem_closure_of_tendsto h (Filter.Eventually.of_forall fun s => ?_)
  refine Submodule.sum_mem _ fun i _ => ⟨single_mem_mulDomain m i (u i), fun j => ?_⟩
  by_cases hji : j = i
  · subst hji; simpa using hu j
  · simp [hji]

/-- The density hypothesis of Prop 4.19 for `E`: `H(curl, S) ∩ L²(TSD)` is dense in `L²(TSD)`
(proved, though `prop_4_17` does not need it). -/
theorem dense_HcurlS_L2TSDS {A : L2S} (hA : A ∈ L2TSDS) :
    A ∈ closure ((HcurlS ⊓ L2TSDS : Submodule ℝ L2S) : Set L2S) :=
  mem_closure_mulDomain_inf_fibreSub _ _ hA

/-- The density hypothesis of Prop 4.19 for `B`: `H(sym curl, T) ∩ L²(TSD)` is dense in
`L²(TSD)` (proved, though `prop_4_17` does not need it). -/
theorem dense_HsymCurlT_L2TSDT {ρ : L2T} (hρ : ρ ∈ L2TSDT) :
    ρ ∈ closure ((HsymCurlT ⊓ L2TSDT : Submodule ℝ L2T) : Set L2T) :=
  mem_closure_mulDomain_inf_fibreSub _ _ hρ

/-- **Thesis Prop 4.19 on `𝕋³`, unconditional.** For the periodic strong-symmetry complex
(4.16) `H²(R) → H(curl, S) → L²(T)` and its Hodge wave (4.18) (`ξ' = -L ξ`:
`σ' = div div E`, `E' = -grad grad σ - sym curl B`, `B' = curl E`), any strong solution with
data `(0, E₀, B₀)`, `E₀, B₀ ∈ L²(TSD)`, keeps `σ ≡ 0` and `E, B ∈ L²(TSD)` for all
`t ∈ [0, T]`, and `(E, B)` solves the reduced system. No projection or density hypothesis is
assumed: they are proved (`projKc_mem_domL`, `dense_HcurlS_L2TSDS`, `dense_HsymCurlT_L2TSDT`).
Such solutions exist (`prop_4_19_torus_exists`, via the constructed group `symGroup`), so the
statement is not vacuous.

Correction: the thesis works on a bounded domain, where it leaves
`P_{L²(TSD)} (H̊(curl, S) ∩ H(div div, S)) ⊆ H̊(curl, S) ∩ H(div div, S)` and
`P_{L²(TSD)} H(sym curl, T) ⊆ H(sym curl, T)` (and two density statements) as hypotheses. This
theorem concerns the *periodic analogue* (no boundary conditions), where the analogues of all
four are theorems (`projS_mem_HcurlS_HdivdivS`, `projT_mem_HsymCurlT`, and the density lemmas);
the bounded-domain conjectures are not settled here. The thesis' initial-data space
`H² × H(curl, S) ∩ H̊(div div, S) × H̊(sym curl, T)` misplaces the boundary conditions; the data
here are in `L²(TSD)` with the solution in `D(L)`, as in the thesis' proof.

See [QuennevilleBelair2015, §4.11, Prop 4.19]; cf. [ACBY1997], [ArnoldHu2021]. -/
theorem prop_4_19_torus {T : ℝ} {E₀ : L2S} {B₀ : L2T} {U : ℝ → Tot L2R L2S L2T}
    (hE₀ : E₀ ∈ L2TSDS) (hB₀ : B₀ ∈ L2TSDT)
    (hU : IsStrongSolution (-symComplex.waveOp) T (ini L2R E₀ B₀) 0 U) :
    (∀ t ∈ Icc 0 T, U t ∈ Kc L2R L2TSDS L2TSDT) ∧
      IsReducedSolution symComplex T E₀ B₀ (fun t => (tot L2R L2S L2T (U t)).2.1)
        (fun t => (tot L2R L2S L2T (U t)).2.2) :=
  prop_4_17 L2TSDS_le_ker projKc_mem_domL curlST_mem_L2TSDT adjoint_curlST_mem_L2TSDS hE₀ hB₀ hU

/-- Group form of `prop_4_19_torus`: for any Stone group for `-L`
(`Feec.UnitaryGroupGenerator`; one is constructed below, `symGroup`), every orbit starting in
`D(L) ∩ K` stays in `K = {0} × L²(TSD) × L²(TSD)` for `t ≥ 0`.

See [QuennevilleBelair2015, Prop 4.19 and Thm 4.3]; cf. [Pazy1983, §1.10]. -/
theorem prop_4_19_torus_group (G : UnitaryGroupGenerator (-symComplex.waveOp)) {t : ℝ}
    (ht : 0 ≤ t) {x : Tot L2R L2S L2T} (hx : x ∈ symComplex.domL)
    (hxK : x ∈ Kc L2R L2TSDS L2TSDT) : G.S t x ∈ Kc L2R L2TSDS L2TSDT :=
  Kc_propagate L2TSDS_le_ker projKc_mem_domL curlST_mem_L2TSDT adjoint_curlST_mem_L2TSDS
    (isStrongSolution_orbit G t ⟨x, hx⟩) hxK t ⟨ht, le_rfl⟩

end Periodic

section Group

open HilbertComplex2 Constraints Filter

/-- The fibre `ℂ × S × T` of the state `(σ, E, B)` at one frequency. -/
abbrev FibS := Tot ℂ Sym3 Tr3

/-- `curl_ξ ∘ (grad grad)_ξ = 0` on `S` (fibre form of `d1 d0 = 0`). -/
theorem curlS_hessS (ξ : Freq) (c : ℂ) : curlS ξ (hessS ξ c) = 0 :=
  Subtype.ext (curlSym_hessM ξ c)

/-- **The fibre symbol of `-L` for (4.16)** at the frequency `ξ`:
`(c, A, ρ) ↦ (div div_ξ A, -(grad grad)_ξ c - sym curl_ξ ρ, curl_ξ A)`, i.e.
`-L(σ, E, B) = (d0* E, -d0 σ - d1* B, d1 E)` with `d0 = grad grad`, `d0* = div div`,
`d1 = curl`, `d1* = sym curl` (the system (4.18)). -/
def waveSymS (ξ : Freq) : FibS →L[ℝ] FibS :=
  (Constraints.totL (W0 := ℂ) (W1 := Sym3) (W2 := Tr3)).symm.toContinuousLinearMap ∘L
    ((divdivS ξ ∘L (ContinuousLinearMap.fst ℝ Sym3 Tr3 ∘L ContinuousLinearMap.snd ℝ ℂ _)).prod
      ((-(hessS ξ ∘L ContinuousLinearMap.fst ℝ ℂ (Sym3 × Tr3)) -
          symCurlS ξ ∘L (ContinuousLinearMap.snd ℝ Sym3 Tr3 ∘L ContinuousLinearMap.snd ℝ ℂ _)).prod
        (curlS ξ ∘L (ContinuousLinearMap.fst ℝ Sym3 Tr3 ∘L ContinuousLinearMap.snd ℝ ℂ _))))
    ∘L (Constraints.totL (W0 := ℂ) (W1 := Sym3) (W2 := Tr3)).toContinuousLinearMap

/-- `waveSymS` in coordinates. -/
theorem tot_waveSymS (ξ : Freq) (x : FibS) :
    tot _ _ _ (waveSymS ξ x) = (divdivS ξ (tot _ _ _ x).2.1,
      -(hessS ξ (tot _ _ _ x).1) - symCurlS ξ (tot _ _ _ x).2.2, curlS ξ (tot _ _ _ x).2.1) := by
  simp [waveSymS]

/-- `⟪div div_ξ A, c⟫ = ⟪A, (grad grad)_ξ c⟫` (`adjoint_hessS`). -/
theorem inner_divdivS_left (ξ : Freq) (A : Sym3) (c : ℂ) :
    ⟪divdivS ξ A, c⟫ = ⟪A, hessS ξ c⟫ := by
  rw [← adjoint_hessS, ContinuousLinearMap.adjoint_inner_left]

/-- `⟪sym curl_ξ ρ, A⟫ = ⟪ρ, curl_ξ A⟫` (`adjoint_curlS`). -/
theorem inner_symCurlS_left (ξ : Freq) (ρ : Tr3) (A : Sym3) :
    ⟪symCurlS ξ ρ, A⟫ = ⟪ρ, curlS ξ A⟫ := by
  rw [← adjoint_curlS, ContinuousLinearMap.adjoint_inner_left]

/-- **The fibre symbols are skew**: `⟪W_ξ x, y⟫ = -⟪x, W_ξ y⟫`. -/
theorem waveSymS_skew (ξ : Freq) (x y : FibS) : ⟪waveSymS ξ x, y⟫ = -⟪x, waveSymS ξ y⟫ := by
  rw [inner_tot, inner_tot, tot_waveSymS, tot_waveSymS]
  simp only [inner_neg_left, inner_neg_right, inner_sub_left, inner_sub_right]
  have h1 := inner_divdivS_left ξ (tot _ _ _ x).2.1 (tot _ _ _ y).1
  have h2 := inner_divdivS_left ξ (tot _ _ _ y).2.1 (tot _ _ _ x).1
  have h3 := inner_symCurlS_left ξ (tot _ _ _ x).2.2 (tot _ _ _ y).2.1
  have h4 := inner_symCurlS_left ξ (tot _ _ _ y).2.2 (tot _ _ _ x).2.1
  have c1 := real_inner_comm (tot _ _ _ x).1 (divdivS ξ (tot _ _ _ y).2.1)
  have c2 := real_inner_comm (tot _ _ _ y).2.1 (hessS ξ (tot _ _ _ x).1)
  have c3 := real_inner_comm (tot _ _ _ x).2.1 (symCurlS ξ (tot _ _ _ y).2.2)
  have c4 := real_inner_comm (tot _ _ _ y).2.2 (curlS ξ (tot _ _ _ x).2.1)
  linarith

/-- `⟪(grad grad)_ξ c, sym curl_ξ ρ⟫ = 0` (`curl grad grad = 0`). -/
theorem inner_hessS_symCurlS (ξ : Freq) (c : ℂ) (ρ : Tr3) :
    ⟪hessS ξ c, symCurlS ξ ρ⟫ = 0 := by
  rw [real_inner_comm, inner_symCurlS_left, curlS_hessS, inner_zero_right]

/-- `‖W_ξ x‖² = ‖div div A‖² + ‖grad grad c‖² + ‖sym curl ρ‖² + ‖curl A‖²`. -/
theorem norm_sq_waveSymS (ξ : Freq) (x : FibS) :
    ‖waveSymS ξ x‖ ^ 2 = ‖divdivS ξ (tot _ _ _ x).2.1‖ ^ 2 + ‖hessS ξ (tot _ _ _ x).1‖ ^ 2 +
      ‖symCurlS ξ (tot _ _ _ x).2.2‖ ^ 2 + ‖curlS ξ (tot _ _ _ x).2.1‖ ^ 2 := by
  rw [norm_sq_tot, tot_waveSymS]
  rw [sub_eq_add_neg, ← neg_add, norm_neg, norm_add_sq_real, inner_hessS_symCurlS]
  ring

/-- The fibre symbols of `-L` on the frequency lattice. -/
def waveSymSK (k : Z3) : FibS →L[ℝ] FibS := waveSymS (freq k)

/-- The Fourier-side identification `ℓ²(ℤ³; ℂ × S × T) ≃ ℓ²(ℂ) × ℓ²(S) × ℓ²(T)`. -/
abbrev ΦS : L2 Z3 FibS ≃ₗᵢ[ℝ] Tot L2R L2S L2T := totL2

/-- Coordinates of `ΦS⁻¹ y` at the mode `k`. -/
theorem tot_ΦS_symm_apply (y : Tot L2R L2S L2T) (k : Z3) :
    tot _ _ _ (ΦS.symm y k) = ((tot _ _ _ y).1 k, (tot _ _ _ y).2.1 k, (tot _ _ _ y).2.2 k) := by
  rw [totL2_symm_apply, LinearEquiv.apply_symm_apply]

/-- Coordinates of `ΦS v` at the mode `k`. -/
theorem tot_ΦS_apply (v : L2 Z3 FibS) (k : Z3) :
    ((tot _ _ _ (ΦS v)).1 k, (tot _ _ _ (ΦS v)).2.1 k, (tot _ _ _ (ΦS v)).2.2 k) =
      tot _ _ _ (v k) :=
  tot_totL2Fun v k

/-- `D(L)` for (4.16) on the Fourier side: `σ ∈ H²(R)`, `E ∈ H(curl, S) ∩ H(div div, S)`,
`B ∈ H(sym curl, T)`, as four weighted-`ℓ²` conditions. -/
theorem mem_domL_sym_iff_summable (y : Tot L2R L2S L2T) :
    y ∈ symComplex.domL ↔
      (Summable fun k => ‖hessS (freq k) ((tot _ _ _ y).1 k)‖ ^ 2) ∧
      (Summable fun k => ‖curlS (freq k) ((tot _ _ _ y).2.1 k)‖ ^ 2) ∧
      (Summable fun k => ‖divdivS (freq k) ((tot _ _ _ y).2.1 k)‖ ^ 2) ∧
      (Summable fun k => ‖symCurlS (freq k) ((tot _ _ _ y).2.2 k)‖ ^ 2) := by
  rw [Constraints.mem_domL]
  have h2 : symComplex.d1†.domain = HsymCurlT := adjoint_curlST_domain
  have h1 : symComplex.d0†.domain = HdivdivS := adjoint_hessT_domain
  rw [midDomain, Submodule.mem_inf, h1, h2]
  have e0 : (tot _ _ _ y).1 ∈ symComplex.d0.domain ↔
      Summable fun k => ‖hessS (freq k) ((tot _ _ _ y).1 k)‖ ^ 2 := memℓp_two_iff
  have e1 : (tot _ _ _ y).2.1 ∈ symComplex.d1.domain ↔
      Summable fun k => ‖curlS (freq k) ((tot _ _ _ y).2.1 k)‖ ^ 2 := memℓp_two_iff
  have e2 : (tot _ _ _ y).2.1 ∈ HdivdivS ↔
      Summable fun k => ‖divdivS (freq k) ((tot _ _ _ y).2.1 k)‖ ^ 2 := memℓp_two_iff
  have e3 : (tot _ _ _ y).2.2 ∈ HsymCurlT ↔
      Summable fun k => ‖symCurlS (freq k) ((tot _ _ _ y).2.2 k)‖ ^ 2 := memℓp_two_iff
  constructor
  · rintro ⟨a, ⟨b, c⟩, d⟩; exact ⟨e0.1 a, e1.1 b, e2.1 c, e3.1 d⟩
  · rintro ⟨a, b, c, d⟩; exact ⟨e0.2 a, ⟨e1.2 b, e2.2 c⟩, e3.2 d⟩

/-- The multiplier domain of the fibre symbols, as the same four weighted-`ℓ²` conditions (the
cross term vanishes, `inner_hessS_symCurlS`). -/
theorem mem_mulDomain_waveSymSK (v : L2 Z3 FibS) :
    v ∈ mulDomain waveSymSK ↔
      (Summable fun k => ‖hessS (freq k) (tot _ _ _ (v k)).1‖ ^ 2) ∧
      (Summable fun k => ‖curlS (freq k) (tot _ _ _ (v k)).2.1‖ ^ 2) ∧
      (Summable fun k => ‖divdivS (freq k) (tot _ _ _ (v k)).2.1‖ ^ 2) ∧
      (Summable fun k => ‖symCurlS (freq k) (tot _ _ _ (v k)).2.2‖ ^ 2) := by
  rw [mem_mulDomain, memℓp_two_iff]
  set D : Z3 → ℝ := fun k => ‖divdivS (freq k) (tot _ _ _ (v k)).2.1‖ ^ 2
  set G : Z3 → ℝ := fun k => ‖hessS (freq k) (tot _ _ _ (v k)).1‖ ^ 2
  set C2 : Z3 → ℝ := fun k => ‖symCurlS (freq k) (tot _ _ _ (v k)).2.2‖ ^ 2
  set C1 : Z3 → ℝ := fun k => ‖curlS (freq k) (tot _ _ _ (v k)).2.1‖ ^ 2
  have e : (fun k => ‖waveSymSK k (v k)‖ ^ 2) = D + G + C2 + C1 :=
    funext fun k => norm_sq_waveSymS _ _
  have hD : 0 ≤ D := fun _ => sq_nonneg _
  have hG : 0 ≤ G := fun _ => sq_nonneg _
  have hC2 : 0 ≤ C2 := fun _ => sq_nonneg _
  have hC1 : 0 ≤ C1 := fun _ => sq_nonneg _
  rw [e, summable_add_iff_of_nonneg (add_nonneg (add_nonneg hD hG) hC2) hC1,
    summable_add_iff_of_nonneg (add_nonneg hD hG) hC2, summable_add_iff_of_nonneg hD hG]
  tauto

/-- **Domain identification**: `D(L) = ΦS D(mulOp waveSymSK)`. -/
theorem mem_domain_neg_waveOp_sym_iff (y : Tot L2R L2S L2T) :
    y ∈ (-symComplex.waveOp).domain ↔ ΦS.symm y ∈ (mulOp waveSymSK).domain := by
  change y ∈ symComplex.domL ↔ ΦS.symm y ∈ mulDomain waveSymSK
  rw [mem_domL_sym_iff_summable, mem_mulDomain_waveSymSK]
  simp only [tot_ΦS_symm_apply]

/-- `(grad grad)* = div div` fibrewise, applied. -/
theorem adjoint_hessT_apply (u : hessT†.domain) (k : Z3) :
    (hessT† u : L2R) k = divdivS (freq k) ((u : L2S) k) := by
  have h := adjoint_mulOp_apply (fun k => hessS (freq k)) u k
  rw [adjoint_hessS] at h
  exact h

/-- `curl* = sym curl` fibrewise, applied. -/
theorem adjoint_curlST_apply (u : curlST†.domain) (k : Z3) :
    (curlST† u : L2S) k = symCurlS (freq k) ((u : L2T) k) := by
  have h := adjoint_mulOp_apply (fun k => curlS (freq k)) u k
  rw [adjoint_curlS] at h
  exact h

/-- First coordinate of `L` at the mode `k`: `-(div div E)_k`. -/
theorem symWaveOp_c0 (y : symComplex.waveOp.domain) (k : Z3) :
    ((tot _ _ _ (symComplex.waveOp y)).1 : L2R) k =
      -divdivS (freq k) ((tot _ _ _ (y : Tot L2R L2S L2T)).2.1 k) := by
  rw [Constraints.tot_waveOp]
  change -((symComplex.d0† (symComplex.prV1s ⟨y.1, y.2⟩) : L2R) k) = _
  rw [neg_inj]
  exact adjoint_hessT_apply (symComplex.prV1s ⟨y.1, y.2⟩) k

/-- Second coordinate of `L` at the mode `k`: `(grad grad σ + sym curl B)_k`. -/
theorem symWaveOp_c1 (y : symComplex.waveOp.domain) (k : Z3) :
    ((tot _ _ _ (symComplex.waveOp y)).2.1 : L2S) k =
      hessS (freq k) ((tot _ _ _ (y : Tot L2R L2S L2T)).1 k) +
        symCurlS (freq k) ((tot _ _ _ (y : Tot L2R L2S L2T)).2.2 k) := by
  rw [Constraints.tot_waveOp]
  change (symComplex.d0 (symComplex.pr0 ⟨y.1, y.2⟩) : L2S) k +
    (symComplex.d1† (symComplex.prV2s ⟨y.1, y.2⟩) : L2S) k = _
  have h2 : (symComplex.d1† (symComplex.prV2s ⟨y.1, y.2⟩) : L2S) k =
      symCurlS (freq k) ((tot _ _ _ (y : Tot L2R L2S L2T)).2.2 k) :=
    adjoint_curlST_apply (symComplex.prV2s ⟨y.1, y.2⟩) k
  rw [h2]
  rfl

/-- Third coordinate of `L` at the mode `k`: `-(curl E)_k`. -/
theorem symWaveOp_c2 (y : symComplex.waveOp.domain) (k : Z3) :
    ((tot _ _ _ (symComplex.waveOp y)).2.2 : L2T) k =
      -curlS (freq k) ((tot _ _ _ (y : Tot L2R L2S L2T)).2.1 k) := by
  rw [Constraints.tot_waveOp]
  rfl

set_option maxHeartbeats 1000000 in
/-- **Operator identification**: `-L = ΦS ∘ mulOp waveSymSK ∘ ΦS⁻¹` on `D(L)`. -/
theorem neg_waveOp_sym_apply (y : (-symComplex.waveOp).domain) :
    (-symComplex.waveOp) y = ΦS (mulOp waveSymSK
      ⟨ΦS.symm y, (mem_domain_neg_waveOp_sym_iff y).1 y.2⟩) := by
  rw [← LinearIsometryEquiv.symm_apply_eq]
  refine lp.ext (funext fun k => ?_)
  rw [mulOp_apply]
  apply (tot ℂ Sym3 Tr3).injective
  have hR : tot ℂ Sym3 Tr3 (waveSymSK k (ΦS.symm y k)) =
      (divdivS (freq k) ((tot _ _ _ (y : Tot L2R L2S L2T)).2.1 k),
        -(hessS (freq k) ((tot _ _ _ (y : Tot L2R L2S L2T)).1 k)) -
          symCurlS (freq k) ((tot _ _ _ (y : Tot L2R L2S L2T)).2.2 k),
        curlS (freq k) ((tot _ _ _ (y : Tot L2R L2S L2T)).2.1 k)) := by
    rw [waveSymSK, tot_waveSymS, tot_ΦS_symm_apply]
  have hw : tot _ _ _ ((-symComplex.waveOp) y) =
      -tot _ _ _ (symComplex.waveOp ⟨y.1, y.2⟩) := by
    rw [LinearPMap.neg_apply]
    exact (tot L2R L2S L2T).map_neg _
  have e0 := symWaveOp_c0 ⟨y.1, y.2⟩ k
  have e1 := symWaveOp_c1 ⟨y.1, y.2⟩ k
  have e2 := symWaveOp_c2 ⟨y.1, y.2⟩ k
  refine (tot_ΦS_symm_apply _ k).trans (Eq.trans ?_ hR.symm)
  rw [hw]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change -((tot _ _ _ (symComplex.waveOp ⟨y.1, y.2⟩)).1 : L2R) k = _
    rw [e0, neg_neg]
  · change -((tot _ _ _ (symComplex.waveOp ⟨y.1, y.2⟩)).2.1 : L2S) k = _
    rw [e1, neg_add', sub_eq_add_neg]
  · change -((tot _ _ _ (symComplex.waveOp ⟨y.1, y.2⟩)).2.2 : L2T) k = _
    rw [e2, neg_neg]

/-- **Existence for (4.18) on `𝕋³`: the Stone group of `-L`**, built fibrewise. Each fibre
symbol `waveSymS ξ` is a skew operator on the finite-dimensional fibre `ℂ × S × T`, so
`exp(t W_ξ)` is orthogonal; the multiplier group `mulGroup` on `ℓ²(ℤ³; ℂ × S × T)` is transported to `L²(R) × L²(S) × L²(T)` by `ΦS`. This is the instance of
Thm 4.3 (Stone's theorem) that the thesis invokes for (4.18), constructed here without Stone's
theorem.

See [QuennevilleBelair2015, §4.11, (4.18) and Thm 4.3]; cf. [Pazy1983, §1.10]. -/
def symGroup : UnitaryGroupGenerator (-symComplex.waveOp) :=
  (mulGroup waveSymSK fun k => waveSymS_skew (freq k)).transport ΦS
    mem_domain_neg_waveOp_sym_iff neg_waveOp_sym_apply

/-- The group acts fibrewise by `exp(t W_ξ)`: `ΦS⁻¹ (S t y) = (exp(t W_{ξ_k}) (ΦS⁻¹ y)_k)_k`. -/
theorem symGroup_S_apply (t : ℝ) (y : Tot L2R L2S L2T) (k : Z3) :
    ΦS.symm (symGroup.S t y) k = NormedSpace.exp (t • waveSymSK k) (ΦS.symm y k) := by
  change ΦS.symm (ΦS _) k = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- `ini E₀ B₀ = (0, E₀, B₀) ∈ D(L)` when `E₀ ∈ H(curl, S) ∩ L²(TSD)` and `B₀ ∈ H(sym curl, T)`
(the `div div` condition is automatic, `L2TSDS_le_HdivdivS`). -/
theorem ini_mem_domL_sym {E₀ : L2S} {B₀ : L2T} (hE₀ : E₀ ∈ L2TSDS) (hE : E₀ ∈ HcurlS)
    (hB : B₀ ∈ HsymCurlT) : ini L2R E₀ B₀ ∈ symComplex.domL := by
  rw [Constraints.mem_domL]
  simp only [ini, LinearEquiv.apply_symm_apply]
  refine ⟨Submodule.zero_mem _, ⟨hE, ?_⟩, ?_⟩
  · change E₀ ∈ hessT†.domain
    rw [adjoint_hessT_domain]; exact L2TSDS_le_HdivdivS hE₀
  · change B₀ ∈ curlST†.domain
    rw [adjoint_curlST_domain]; exact hB

/-- **Thesis Prop 4.19 on `𝕋³`, with existence.** For data `E₀ ∈ H(curl, S) ∩ L²(TSD)`,
`B₀ ∈ H(sym curl, T) ∩ L²(TSD)`, the Hodge wave (4.18) of the strong-symmetry complex has a
strong solution on `[0, T]` with data `(0, E₀, B₀)` (the orbit of `symGroup`), and every such
solution keeps `σ ≡ 0`, `E, B ∈ L²(TSD)` and solves the reduced system. No hypothesis remains
besides the data.

See [QuennevilleBelair2015, §4.11, Prop 4.19 and Thm 4.3]. -/
theorem prop_4_19_torus_exists (T : ℝ) {E₀ : L2S} {B₀ : L2T} (hE₀ : E₀ ∈ L2TSDS)
    (hB₀ : B₀ ∈ L2TSDT) (hE : E₀ ∈ HcurlS) (hB : B₀ ∈ HsymCurlT) :
    ∃ U : ℝ → Tot L2R L2S L2T,
      IsStrongSolution (-symComplex.waveOp) T (ini L2R E₀ B₀) 0 U ∧
      (∀ t ∈ Icc 0 T, U t ∈ Kc L2R L2TSDS L2TSDT) ∧
      IsReducedSolution symComplex T E₀ B₀ (fun t => (tot L2R L2S L2T (U t)).2.1)
        (fun t => (tot L2R L2S L2T (U t)).2.2) := by
  have hU := isStrongSolution_orbit symGroup T ⟨_, ini_mem_domL_sym hE₀ hE hB⟩
  exact ⟨_, hU, prop_4_19_torus hE₀ hB₀ hU⟩

/-- Group form of Prop 4.19 on `𝕋³`, unconditional: orbits of the constructed group `symGroup`
starting in `D(L) ∩ K` stay in `K = {0} × L²(TSD) × L²(TSD)` for `t ≥ 0`. -/
theorem prop_4_19_torus_symGroup {t : ℝ} (ht : 0 ≤ t) {x : Tot L2R L2S L2T}
    (hx : x ∈ symComplex.domL) (hxK : x ∈ Kc L2R L2TSDS L2TSDT) :
    symGroup.S t x ∈ Kc L2R L2TSDS L2TSDT :=
  prop_4_19_torus_group symGroup ht hx hxK

/-- `D(L)` is dense (it is the image of the dense multiplier domain under `ΦS`). -/
theorem dense_domL_sym : Dense (symComplex.domL : Set (Tot L2R L2S L2T)) := by
  have h : (symComplex.domL : Set (Tot L2R L2S L2T)) = ΦS '' (mulDomain waveSymSK) := by
    ext y
    constructor
    · intro hy
      exact ⟨ΦS.symm y, (mem_domain_neg_waveOp_sym_iff y).1 hy, ΦS.apply_symm_apply y⟩
    · rintro ⟨v, hv, rfl⟩
      refine (mem_domain_neg_waveOp_sym_iff _).2 ?_
      change ΦS.symm (ΦS v) ∈ mulDomain waveSymSK
      rwa [LinearIsometryEquiv.symm_apply_apply]
  rw [h]
  exact ΦS.surjective.denseRange.dense_image ΦS.continuous (dense_mulDomain _)

/-- `D(L) ∩ K` is dense in `K` (`hdense` of `prop_4_17_iff`): `P_K` maps the dense `D(L)` into
`D(L) ∩ K` (`projKc_mem_domL`) and fixes `K`. -/
theorem mem_closure_domL_inf_Kc_sym {x : Tot L2R L2S L2T} (hx : x ∈ Kc L2R L2TSDS L2TSDT) :
    x ∈ closure ((symComplex.domL : Set (Tot L2R L2S L2T)) ∩ Kc L2R L2TSDS L2TSDT) := by
  have hfix : projKc L2R L2TSDS L2TSDT x = x := by
    rw [← starProjection_Kc]; exact Submodule.starProjection_eq_self_iff.2 hx
  have h1 : projKc L2R L2TSDS L2TSDT x ∈
      closure (projKc L2R L2TSDS L2TSDT '' (symComplex.domL : Set (Tot L2R L2S L2T))) :=
    image_closure_subset_closure_image (projKc L2R L2TSDS L2TSDT).continuous
      ⟨x, dense_domL_sym x, rfl⟩
  rw [hfix] at h1
  refine closure_mono ?_ h1
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨projKc_mem_domL y hy, projKc_mem _ _ _ y⟩

/-- **Prop 4.19 on `𝕋³`, characterization form** (`prop_4_17_iff` for the constructed group):
the TSD constraints propagate for all data in `K` iff `P_K D(L) ⊆ D(L)`. Both sides hold here
(`projKc_mem_domL`); the statement records that the projection hypothesis is exactly what is
needed. -/
theorem prop_4_19_torus_iff :
    (∀ (T : ℝ) (U₀ : Tot L2R L2S L2T) (U : ℝ → Tot L2R L2S L2T), U₀ ∈ Kc L2R L2TSDS L2TSDT →
      IsStrongSolution (-symComplex.waveOp) T U₀ 0 U → ∀ t ∈ Icc 0 T,
        U t ∈ Kc L2R L2TSDS L2TSDT) ↔
      ∀ x ∈ symComplex.domL, projKc L2R L2TSDS L2TSDT x ∈ symComplex.domL :=
  prop_4_17_iff symGroup L2TSDS_le_ker curlST_mem_L2TSDT adjoint_curlST_mem_L2TSDS
    fun _ hk => mem_closure_domL_inf_Kc_sym hk

end Group

section ClosedRange

open HilbertComplex2

/-- The range of a multiplier with uniformly bounded fibre preimages is fibrewise:
`range (mulOp m) = {v | ∀ i, v i ∈ range (m i)}`. -/
theorem range_mulOp_eq {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (m : ι → E →L[ℝ] F) {C : ℝ}
    (hC : ∀ i x, ∃ x', m i x' = m i x ∧ ‖x'‖ ≤ C * ‖m i x‖) :
    (LinearMap.range (mulOp m).toFun : Set (L2 ι F)) =
      {v | ∀ i, v i ∈ LinearMap.range (m i : E →ₗ[ℝ] F)} := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩ i
    exact ⟨(u : L2 ι E) i, rfl⟩
  · intro hv
    choose x hx using hv
    choose x' hx' using fun i => hC i (x i)
    have hmem : Memℓp x' 2 := by
      refine (lp.memℓp (C • v)).mono' fun i => ?_
      calc ‖x' i‖ ≤ C * ‖m i (x i)‖ := (hx' i).2
        _ = C * ‖v i‖ := congrArg (fun z => C * ‖z‖) (hx i)
        _ ≤ |C| * ‖v i‖ := by gcongr; exact le_abs_self C
        _ = ‖(C • v : L2 ι F) i‖ := by
          rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    have hfun : (fun i => m i (x' i)) = ⇑v := funext fun i => (hx' i).1.trans (hx i)
    have hu : (⟨x', hmem⟩ : L2 ι E) ∈ mulDomain m := by
      change Memℓp (fun i => m i (x' i)) 2
      rw [hfun]; exact lp.memℓp v
    refine ⟨⟨⟨x', hmem⟩, hu⟩, lp.ext (funext fun i => ?_)⟩
    exact (hx' i).1.trans (hx i)

/-- **Closed range of multipliers**: if every fibre value `m i x` has a preimage of norm
`≤ C ‖m i x‖` (`C` uniform in `i`), the multiplier has closed range. -/
theorem isClosed_range_mulOp {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (m : ι → E →L[ℝ] F) {C : ℝ} (hC : ∀ i x, ∃ x', m i x' = m i x ∧ ‖x'‖ ≤ C * ‖m i x‖) :
    IsClosed (LinearMap.range (mulOp m).toFun : Set (L2 ι F)) := by
  rw [range_mulOp_eq m hC]
  have : {v : L2 ι F | ∀ i, v i ∈ LinearMap.range (m i : E →ₗ[ℝ] F)} =
      ⋂ i, (fun v : L2 ι F => v i) ⁻¹' (LinearMap.range (m i : E →ₗ[ℝ] F) : Set F) := by
    ext; simp
  rw [this]
  exact isClosed_iInter fun i => (Submodule.closed_of_finiteDimensional _).preimage
    (lp.evalCLM ℝ (fun _ : ι => F) 2 i).continuous

/-- The lattice frequencies are `0` or of size `≥ 2π`: `freq k = 0 ∨ 4π² ≤ |ξ_k|²`. -/
theorem freq_eq_zero_or (k : Z3) : freq k = 0 ∨ 4 * Real.pi ^ 2 ≤ ‖freq k‖ ^ 2 := by
  by_cases hk : k = 0
  · left; subst hk; ext j; simp [freq]
  · right
    obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
      by_contra h; push Not at h; exact hk (funext h)
    have h1 : (1 : ℝ) ≤ (k j : ℝ) ^ 2 := by
      have h0 : (0 : ℤ) < k j ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj))
      have : (1 : ℤ) ≤ k j ^ 2 := h0
      exact_mod_cast this
    rw [norm_sq_freq]
    have hle : (freq k) j ^ 2 ≤ ∑ c, (freq k) c ^ 2 :=
      Finset.single_le_sum (f := fun c => (freq k) c ^ 2) (fun c _ => sq_nonneg _)
        (Finset.mem_univ j)
    have hfj : (freq k) j = 2 * Real.pi * k j := rfl
    rw [hfj] at hle
    nlinarith [Real.pi_pos]

/-- `freq k = 0 ∨ 2 ≤ |ξ_k|²`. -/
theorem freq_eq_zero_or_two_le (k : Z3) : freq k = 0 ∨ 2 ≤ ‖freq k‖ ^ 2 :=
  (freq_eq_zero_or k).imp_right fun h => le_trans (by nlinarith [Real.two_le_pi]) h

/-- `‖M‖² = ∑ₐ ∑_b |M_{ab}|²`. -/
theorem norm_sq_mat_eq (M : Mat3) : ‖M‖ ^ 2 = ∑ a, ∑ b, ‖M (a, b)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]

/-- Cauchy–Schwarz: `|∑ₐ ξ_a z_a|² ≤ |ξ|² ∑ₐ |z_a|²` (`ξ` real, `z` complex). -/
theorem norm_sum_freq_mul_sq_le (ξ : Freq) (z : Fin 3 → ℂ) :
    ‖∑ a, (ξ a : ℂ) * z a‖ ^ 2 ≤ ‖ξ‖ ^ 2 * ∑ a, ‖z a‖ ^ 2 := by
  rw [norm_sq_freq]
  simp only [Complex.sq_norm, Complex.normSq_apply, Fin.sum_univ_three]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  nlinarith [sq_nonneg (ξ 0 * (z 1).re - ξ 1 * (z 0).re), sq_nonneg (ξ 0 * (z 2).re - ξ 2 * (z 0).re),
    sq_nonneg (ξ 1 * (z 2).re - ξ 2 * (z 1).re), sq_nonneg (ξ 0 * (z 1).im - ξ 1 * (z 0).im),
    sq_nonneg (ξ 0 * (z 2).im - ξ 2 * (z 0).im), sq_nonneg (ξ 1 * (z 2).im - ξ 2 * (z 1).im)]

/-- Lagrange identity for one complex vector: `|ξ × v|² + |v · ξ|² = |ξ|² |v|²`. -/
theorem lagrange_vec (ξ : Freq) (v : Fin 3 → ℂ) :
    ∑ b, ‖cross ξ v b‖ ^ 2 + ‖∑ a, v a * ξ a‖ ^ 2 = ‖ξ‖ ^ 2 * ∑ a, ‖v a‖ ^ 2 := by
  rw [norm_sq_freq]
  simp only [Complex.sq_norm, Complex.normSq_apply, Fin.sum_univ_three, cross]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- For symmetric `x`, `ξ × (x ξ) = ξᵀ (curl_ξ x)`, i.e. `(ξ × (x ξ))_b = ∑ₐ ξ_a (ξ × x_a)_b`. -/
theorem cross_divR_eq (ξ : Freq) {x : Mat3} (hx : x ∈ symSub) (b : Fin 3) :
    cross ξ (fun a => divR ξ x a) b = ∑ a, (ξ a : ℂ) * curlR ξ x (a, b) := by
  have s10 := hx 1 0; have s20 := hx 2 0; have s21 := hx 2 1
  fin_cases b <;> simp [cross, divR_apply, curlR_apply, Fin.sum_univ_three, s10, s20, s21] <;> ring

/-- **Fibre estimate for closed range of `curl` on `S`**: for symmetric `x` with
`ξᵀ x ξ = 0`, `|x ξ| ≤ |ξ × x|` (row-wise curl). Proof: `|ξ|² |x ξ|² = |ξ × (x ξ)|²` (Lagrange,
`ξ · x ξ = 0`), `ξ × (x ξ) = ξᵀ (curl_ξ x)` by symmetry, and Cauchy–Schwarz. -/
theorem norm_divR_sq_le_curlR (ξ : Freq) {x : Mat3} (hx : x ∈ symSub)
    (h0 : ∑ a, divR ξ x a * ξ a = 0) : ‖divR ξ x‖ ^ 2 ≤ ‖curlR ξ x‖ ^ 2 := by
  have hL := lagrange_vec ξ (fun a => divR ξ x a)
  simp only [h0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at hL
  have hC : ∑ b, ‖cross ξ (fun a => divR ξ x a) b‖ ^ 2 ≤ ‖ξ‖ ^ 2 * ‖curlR ξ x‖ ^ 2 := by
    simp_rw [cross_divR_eq ξ hx]
    calc ∑ b, ‖∑ a, (ξ a : ℂ) * curlR ξ x (a, b)‖ ^ 2
        ≤ ∑ b, ‖ξ‖ ^ 2 * ∑ a, ‖curlR ξ x (a, b)‖ ^ 2 :=
          Finset.sum_le_sum fun b _ => norm_sum_freq_mul_sq_le ξ _
      _ = ‖ξ‖ ^ 2 * ‖curlR ξ x‖ ^ 2 := by
          rw [← Finset.mul_sum, norm_sq_mat_eq, Finset.sum_comm]
  have hv : ‖divR ξ x‖ ^ 2 = ∑ a, ‖divR ξ x a‖ ^ 2 := EuclideanSpace.norm_sq_eq _
  rcases eq_or_lt_of_le (sq_nonneg ‖ξ‖) with h | h
  · have hξ : ξ = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h.symm)
    have : divR ξ x = 0 := by ext a; simp [divR_apply, hξ]
    rw [this, norm_zero]; exact le_trans (by norm_num) (sq_nonneg _)
  · rw [hv]
    exact le_of_mul_le_mul_left (hL ▸ hC) h

/-- The curl symbol vanishes at `ξ = 0`. -/
theorem curlS_zero (A : Sym3) : curlS 0 A = 0 := by
  have h := norm_curlSym_le 0 (A : Mat3)
  rw [norm_zero, zero_mul] at h
  exact Subtype.ext (norm_le_zero_iff.1 h)

/-- The Hessian symbol vanishes at `ξ = 0`. -/
theorem hessS_zero (c : ℂ) : hessS 0 c = 0 := by
  apply Subtype.ext
  rw [coe_hessS, ZeroMemClass.coe_zero, ← norm_eq_zero, norm_hessM, norm_zero]
  simp

/-- Fibre preimages for `grad grad`: at a lattice frequency, `c` itself works with constant `1`
(`|ξ|² ≥ 1` unless `ξ = 0`). -/
theorem hessS_preimage (k : Z3) (c : ℂ) :
    ∃ c', hessS (freq k) c' = hessS (freq k) c ∧ ‖c'‖ ≤ 1 * ‖hessS (freq k) c‖ := by
  rcases freq_eq_zero_or k with h | h
  · exact ⟨0, by rw [h, hessS_zero, hessS_zero], by simp⟩
  · refine ⟨c, rfl, ?_⟩
    rw [one_mul, ← Submodule.norm_coe, coe_hessS, norm_hessM]
    exact le_mul_of_one_le_left (norm_nonneg _) (by nlinarith [Real.two_le_pi])

/-- **Fibre preimages for `curl : S → T`** with constant `1`: for `|ξ|² ≥ 2` (or `ξ = 0`), every
`curl_ξ A` is `curl_ξ X` with `‖X‖ ≤ ‖curl_ξ A‖`, namely `X = A - (ξᵀ A ξ / |ξ|⁴) ξ ξᵀ`
(the component of `A` orthogonal to the kernel `ℂ ξ ξᵀ`, up to the choice of complement):
`|ξ|² ‖X‖² = ‖curl X‖² + ‖X ξ‖² ≤ 2 ‖curl X‖²` by `norm_divR_sq_le_curlR`. -/
theorem curlS_preimage (ξ : Freq) (hξ : ξ = 0 ∨ 2 ≤ ‖ξ‖ ^ 2) (A : Sym3) :
    ∃ X, curlS ξ X = curlS ξ A ∧ ‖X‖ ≤ 1 * ‖curlS ξ A‖ := by
  rcases hξ with rfl | hξ
  · exact ⟨0, by rw [curlS_zero, curlS_zero], by simp⟩
  have hs : ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 ≠ 0 := by
    rw [norm_sq_freq, Fin.sum_univ_three] at hξ; linarith
  have hD0 : ((ξ 0 : ℂ) ^ 2 + (ξ 1 : ℂ) ^ 2 + (ξ 2 : ℂ) ^ 2) ^ 2 ≠ 0 := by
    have h := Complex.ofReal_ne_zero.2 hs
    push_cast at h
    exact pow_ne_zero 2 h
  obtain ⟨t, key⟩ : ∃ t : ℂ, t * ((ξ 0 : ℂ) ^ 2 + (ξ 1 : ℂ) ^ 2 + (ξ 2 : ℂ) ^ 2) ^ 2 =
      ∑ a, ∑ b, (A : Mat3) (a, b) * ξ b * ξ a := ⟨_, div_mul_cancel₀ _ hD0⟩
  refine ⟨A + hessS ξ t, by rw [_root_.map_add, curlS_hessS, add_zero], ?_⟩
  set X : Sym3 := A + hessS ξ t with hX
  have hXc : (X : Mat3) = (A : Mat3) + hessM ξ t := rfl
  have h0 : ∑ a, divR ξ (X : Mat3) a * ξ a = 0 := by
    rw [hXc]
    simp only [_root_.map_add, PiLp.add_apply, divR_apply, hessM_apply, Fin.sum_univ_three]
      at key ⊢
    linear_combination -key
  have hlag := lagrange ξ (X : Mat3)
  have hdiv := norm_divR_sq_le_curlR ξ X.2 h0
  have hcurl : ‖curlS ξ A‖ = ‖curlR ξ (X : Mat3)‖ := by
    rw [← Submodule.norm_coe, ← norm_curlSym, ← coe_curlS, hX, _root_.map_add, curlS_hessS, add_zero]
  rw [one_mul, hcurl, ← Submodule.norm_coe]
  have hsq : ‖(X : Mat3)‖ ^ 2 ≤ ‖curlR ξ (X : Mat3)‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(X : Mat3)‖, sq_nonneg ‖curlR ξ (X : Mat3)‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- **The periodic strong-symmetry complex (4.16) is closed** (closed ranges): the thesis defers
this ("we show in the next chapter that these complexes are closed"); on `𝕋³` it follows from
the fibre preimage bounds `hessS_preimage` (`|ξ|² ≥ 4π²` off `ξ = 0`) and `curlS_preimage`.

See [QuennevilleBelair2015, §4.11, after (4.18)]; cf. [AFW2010] (closed Hilbert complexes). -/
theorem symComplex_closedRange : symComplex.ClosedRange :=
  ⟨isClosed_range_mulOp (fun k => hessS (freq k)) (C := 1) fun k c => hessS_preimage k c,
    isClosed_range_mulOp (fun k => curlS (freq k)) (C := 1) fun k A =>
      curlS_preimage (freq k) (freq_eq_zero_or_two_le k) A⟩

/-- **Hodge decomposition of `L²(S)` on `𝕋³`, without closures** (Thesis Thm 4.1 for the
complex (4.16)): `L²(S) = grad grad H²(R) ⊕ ℌ ⊕ sym curl H(sym curl, T)`, pairwise orthogonal.

See [QuennevilleBelair2015, Thm 4.1 and §4.11]. -/
theorem symComplex_hodge :
    LinearMap.range symComplex.d0.toFun ⊔ symComplex.harmonic ⊔
        LinearMap.range symComplex.d1†.toFun = ⊤ ∧
      LinearMap.range symComplex.d0.toFun ⟂ symComplex.harmonic ∧
      symComplex.harmonic ⟂ LinearMap.range symComplex.d1†.toFun ∧
      LinearMap.range symComplex.d0.toFun ⟂ LinearMap.range symComplex.d1†.toFun :=
  symComplex.hodge_W_of_closedRange symComplex_closedRange

end ClosedRange

section Model

open MeasureTheory

/-- Fibrewise inclusion `ℓ²(ℤ³; U) → ℓ²(ℤ³; ℂ³ˣ³)` for a subspace `U` of matrices
(`U = S` gives `L2S`, `U = T` gives `L2T`). -/
def embL2 (U : Submodule ℝ Mat3) : L2 Z3 U →ₗᵢ[ℝ] L2M where
  toFun u := ⟨fun k => ((u k : U) : Mat3),
    (lp.memℓp u).mono' fun k => le_of_eq (Submodule.norm_coe _)⟩
  map_add' u v := rfl
  map_smul' r u := rfl
  norm_map' u := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1

/-- `embL2` forgets the constraint fibrewise. -/
theorem embL2_apply (U : Submodule ℝ Mat3) (u : L2 Z3 U) (k : Z3) :
    embL2 U u k = (u k : Mat3) := rfl

/-- The range of `embL2 U` is the fibrewise subspace of `U`-valued coefficient sequences. -/
theorem mem_fibreSub_iff_embL2 (U : Submodule ℝ Mat3) {A : L2M} :
    A ∈ fibreSub (fun _ : Z3 => U) ↔ ∃ u, embL2 U u = A := by
  constructor
  · intro hA
    refine ⟨(⟨fun k => (⟨A k, hA k⟩ : U), (lp.memℓp A).mono' fun k => le_of_eq ?_⟩ : L2 Z3 U),
      rfl⟩
    exact Submodule.norm_coe (⟨A k, hA k⟩ : U)
  · rintro ⟨u, rfl⟩ k
    exact (u k).2

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Ch4.Torus` (equal to the default `volume`,
`Feec.Torus.measureSpace_unitAddCircle_eq`). -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- Scalar fields: `L²(𝕋³; ℂ) ≃ₗᵢ L2R` (Parseval), the model of `W0 = L²(R)`. -/
def scalarFourier : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) ≃ₗᵢ[ℂ] L2R :=
  UnitAddTorus.mFourierBasis.repr

/-- `scalarFourier f k` is the `k`-th Fourier coefficient of `f`. -/
theorem scalarFourier_apply (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))) (k : Z3) :
    scalarFourier f k = UnitAddTorus.mFourierCoeff f k :=
  UnitAddTorus.mFourierBasis_repr f k

/-- **`L²(𝕋³; S)` is modelled by `L2S`**: a matrix field is symmetric iff its Fourier
coefficients are, i.e. iff `matrixFourier f` lies in the range of `embL2 symSub`. -/
theorem matrixFourier_mem_sym
    (f : PiLp 2 (fun _ : Fin 3 × Fin 3 => Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))))) :
    matrixFourier f ∈ fibreSub (fun _ : Z3 => symSub) ↔ ∀ a b, f (a, b) = f (b, a) := by
  constructor
  · intro h a b
    apply UnitAddTorus.mFourierBasis.repr.injective
    refine lp.ext (funext fun k => ?_)
    rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierBasis_repr, ← matrixFourier_apply,
      ← matrixFourier_apply]
    exact h k a b
  · intro h k a b
    rw [matrixFourier_apply, matrixFourier_apply, h a b]

/-- The trace of the Fourier coefficients is the Fourier coefficient of the trace. -/
theorem sum_matrixFourier_diag
    (f : PiLp 2 (fun _ : Fin 3 × Fin 3 => Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))))
    (k : Z3) :
    ∑ a, matrixFourier f k (a, a) = UnitAddTorus.mFourierBasis.repr (∑ a, f (a, a)) k := by
  rw [map_sum, lp.coeFn_sum, Finset.sum_apply]
  simp [matrixFourier_apply, UnitAddTorus.mFourierBasis_repr]

/-- **`L²(𝕋³; T)` is modelled by `L2T`**: a matrix field is trace-free iff its Fourier
coefficients are, i.e. iff `matrixFourier f` lies in the range of `embL2 trSub`. -/
theorem matrixFourier_mem_tr
    (f : PiLp 2 (fun _ : Fin 3 × Fin 3 => Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))))) :
    matrixFourier f ∈ fibreSub (fun _ : Z3 => trSub) ↔ ∑ a, f (a, a) = 0 := by
  constructor
  · intro h
    apply UnitAddTorus.mFourierBasis.repr.injective
    rw [_root_.map_zero]
    refine lp.ext (funext fun k => ?_)
    rw [← sum_matrixFourier_diag, lp.coeFn_zero, Pi.zero_apply]
    exact h k
  · intro h k
    change ∑ a, matrixFourier f k (a, a) = 0
    rw [sum_matrixFourier_diag, h, _root_.map_zero, lp.coeFn_zero, Pi.zero_apply]

end Model

section Bridge

/-! ### Relation to the `ℂ³ˣ³`-valued model of `Feec.Ch4.Torus` -/

/-- `L²(TSD) ⊆ L²(S)` is the TSD subspace of `Feec.Torus` seen through `embL2`. -/
theorem embL2_sym_mem_L2TSD_iff (A : L2S) : embL2 symSub A ∈ L2TSD ↔ A ∈ L2TSDS := Iff.rfl

/-- `L²(TSD) ⊆ L²(T)` is the TSD subspace of `Feec.Torus` seen through `embL2`. -/
theorem embL2_tr_mem_L2TSD_iff (ρ : L2T) : embL2 trSub ρ ∈ L2TSD ↔ ρ ∈ L2TSDT := Iff.rfl

/-- **`embL2` maps `L²(TSD) ⊆ L²(S)` onto `Feec.Torus.L2TSD`** (TSD fields are symmetric). -/
theorem map_embL2_L2TSDS : L2TSDS.map (embL2 symSub).toLinearMap = L2TSD := by
  ext A
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro hA
    obtain ⟨u, rfl⟩ := (mem_fibreSub_iff_embL2 symSub).1 fun k => tsd_le_symSub _ (hA k)
    exact ⟨u, hA, rfl⟩

/-- **`embL2` maps `L²(TSD) ⊆ L²(T)` onto `Feec.Torus.L2TSD`** (TSD fields are trace-free). -/
theorem map_embL2_L2TSDT : L2TSDT.map (embL2 trSub).toLinearMap = L2TSD := by
  ext A
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro hA
    obtain ⟨u, rfl⟩ := (mem_fibreSub_iff_embL2 trSub).1 fun k => tsd_le_trSub _ (hA k)
    exact ⟨u, hA, rfl⟩

/-- The TSD projections agree: `embL2 (P_TSD A) = P_TSD (embL2 A)` for `A ∈ L²(S)`. -/
theorem embL2_projS (A : L2S) :
    embL2 symSub (L2TSDS.starProjection A) = L2TSD.starProjection (embL2 symSub A) :=
  lp.ext (funext fun k => by
    rw [embL2_apply, projS_apply, coe_projS, projTSD_apply]; rfl)

/-- The TSD projections agree: `embL2 (P_TSD ρ) = P_TSD (embL2 ρ)` for `ρ ∈ L²(T)`. -/
theorem embL2_projT (ρ : L2T) :
    embL2 trSub (L2TSDT.starProjection ρ) = L2TSD.starProjection (embL2 trSub ρ) :=
  lp.ext (funext fun k => by
    rw [embL2_apply, projT_apply, coe_projT, projTSD_apply]; rfl)

/-- `H(curl, S)` is `Feec.Torus.Hcurl` restricted to symmetric fields. -/
theorem embL2_sym_mem_Hcurl_iff (A : L2S) : embL2 symSub A ∈ Hcurl ↔ A ∈ HcurlS := by
  change Memℓp (fun k => curlSym (freq k) ((A k : Sym3) : Mat3)) 2 ↔
    Memℓp (fun k => curlS (freq k) (A k)) 2
  rw [← memℓp_norm_iff, ← memℓp_norm_iff (f := fun k => curlS (freq k) (A k))]
  simp only [← coe_curlS, Submodule.norm_coe]

/-- **`curl` on `H(curl, S)` is the curl of `Feec.Torus` (the matrix complex of Prop 4.17)**:
`curlT (embL2 A) = embL2 (curlST A)`. -/
theorem curlT_embL2 (A : curlST.domain) :
    curlT ⟨embL2 symSub A, (embL2_sym_mem_Hcurl_iff A).2 A.2⟩ = embL2 trSub (curlST A) := rfl

/-- **`sym curl` is `sym ∘` the curl of `Feec.Torus`**:
`embL2 (curl* ρ)_k = sym (curl_ξ ρ_k)`. -/
theorem embL2_adjoint_curlST_apply (ρ : curlST†.domain) (k : Z3) :
    embL2 symSub (curlST† ρ) k = symM (curlSym (freq k) ((ρ : L2T) k)) := by
  rw [embL2_apply, adjoint_curlST_apply, coe_symCurlS]

end Bridge

open HilbertComplex2 Constraints

/-! ## Real-valued fields

Real fields have conjugate-symmetric Fourier coefficients; the operators of (4.16)/(4.17), the
TSD projections and the group `symGroup` preserve them, so Prop 4.19 holds within real fields. -/

section Real

/-- Entrywise conjugation commutes with `sym`. -/
theorem symM_conjM (M : Mat3) : symM (conjM M) = conjM (symM M) := by
  ext ⟨a, b⟩; simp [symM_apply, conjM_apply, Complex.real_smul, map_ofNat]

/-- Entrywise conjugation preserves `S`. -/
theorem conjM_mem_symSub {M : Mat3} (hM : M ∈ symSub) : conjM M ∈ symSub := fun a b => by
  simp [conjM_apply, mem_symSub.1 hM a b]

/-- Entrywise conjugation preserves `T`. -/
theorem conjM_mem_trSub {M : Mat3} (hM : M ∈ trSub) : conjM M ∈ trSub := by
  rw [mem_trSub] at hM ⊢
  simpa [conjM_apply] using congrArg (starRingEnd ℂ) hM

/-- Entrywise conjugation of symmetric matrices. -/
def conjS : Sym3 →L[ℝ] Sym3 :=
  (conjM ∘L symSub.subtypeL).codRestrict symSub fun A => conjM_mem_symSub A.2

/-- Entrywise conjugation of trace-free matrices. -/
def conjT : Tr3 →L[ℝ] Tr3 :=
  (conjM ∘L trSub.subtypeL).codRestrict trSub fun ρ => conjM_mem_trSub ρ.2

/-- `conjS` is `conjM` on the underlying matrix. -/
@[simp] theorem coe_conjS (A : Sym3) : (conjS A : Mat3) = conjM A := rfl

/-- `conjT` is `conjM` on the underlying matrix. -/
@[simp] theorem coe_conjT (ρ : Tr3) : (conjT ρ : Mat3) = conjM ρ := rfl

/-- Entrywise conjugation is an involution. -/
theorem conjM_conjM (M : Mat3) : conjM (conjM M) = M := by
  ext ⟨a, b⟩; simp [conjM_apply]

/-- `conjS` is an involution. -/
theorem conjS_conjS (A : Sym3) : conjS (conjS A) = A := Subtype.ext (conjM_conjM _)

/-- `conjT` is an involution. -/
theorem conjT_conjT (ρ : Tr3) : conjT (conjT ρ) = ρ := Subtype.ext (conjM_conjM _)

/-- Hessian symbol and conjugation: `(grad grad)_{-ξ} c̄ = conj ((grad grad)_ξ c)`. -/
theorem hessM_neg_conj (ξ : Freq) (c : ℂ) :
    hessM (-ξ) ((starRingEnd ℂ) c) = conjM (hessM ξ c) := by
  ext ⟨a, b⟩; simp [hessM_apply, conjM_apply]

/-- Curl symbol and conjugation: `curl_{-ξ} M̄ = conj (curl_ξ M)` (the symbol `i ξ ×` is
odd in `ξ` and purely imaginary). -/
theorem curlSym_neg_conjM (ξ : Freq) (M : Mat3) :
    curlSym (-ξ) (conjM M) = conjM (curlSym ξ M) := by
  ext ⟨a, b⟩
  fin_cases b <;> simp [curlSym_apply, jM_apply, curlR_apply, cross, conjM_apply] <;> ring

/-- `grad grad` symbol on `S` and conjugation. -/
theorem hessS_neg_conj (ξ : Freq) (c : ℂ) :
    hessS (-ξ) ((starRingEnd ℂ) c) = conjS (hessS ξ c) :=
  Subtype.ext (hessM_neg_conj ξ c)

/-- `curl : S → T` symbol and conjugation. -/
theorem curlS_neg_conjS (ξ : Freq) (A : Sym3) : curlS (-ξ) (conjS A) = conjT (curlS ξ A) :=
  Subtype.ext (curlSym_neg_conjM ξ A)

/-- `sym curl : T → S` symbol and conjugation. -/
theorem symCurlS_neg_conjT (ξ : Freq) (ρ : Tr3) :
    symCurlS (-ξ) (conjT ρ) = conjS (symCurlS ξ ρ) := by
  apply Subtype.ext
  rw [coe_symCurlS, coe_conjS, coe_symCurlS, coe_conjT, curlSym_neg_conjM, symM_conjM]

/-- `div div : S → R` symbol and conjugation (`-ξᵀ A ξ` is even in `ξ`). -/
theorem divdivS_neg_conjS (ξ : Freq) (A : Sym3) :
    divdivS (-ξ) (conjS A) = (starRingEnd ℂ) (divdivS ξ A) := by
  simp [divdivS_apply, conjM_apply]

/-- The TSD projection in `S` and conjugation (`tsd (-ξ) = tsd ξ`, conjugation-invariant). -/
theorem projS_neg_conjS (ξ : Freq) (A : Sym3) :
    (tsdS (-ξ)).starProjection (conjS A) = conjS ((tsdS ξ).starProjection A) := by
  apply Subtype.ext
  rw [coe_projS, coe_conjS, coe_conjS, coe_projS, tsd_neg]
  exact starProjection_comm_of_selfAdj _ conjM inner_conjM (fun _ h => conjM_mem_tsd h) _

/-- The TSD projection in `T` and conjugation. -/
theorem projT_neg_conjT (ξ : Freq) (ρ : Tr3) :
    (tsdT (-ξ)).starProjection (conjT ρ) = conjT ((tsdT ξ).starProjection ρ) := by
  apply Subtype.ext
  rw [coe_projT, coe_conjT, coe_conjT, coe_projT, tsd_neg]
  exact starProjection_comm_of_selfAdj _ conjM inner_conjM (fun _ h => conjM_mem_tsd h) _

/-- Fourier coefficients of a real-valued scalar field: `û(-k) = conj û(k)`
(`isRealR_scalarFourier_iff`). -/
def IsRealR (u : L2R) : Prop := ∀ k, u (-k) = (starRingEnd ℂ) (u k)
/-- Fourier coefficients of a real-valued symmetric-matrix field: `Â(-k) = conj Â(k)`
(`isRealS_iff_embL2`, cf. `Feec.TorusWeak.isReal_matrixFourier_iff`). -/
def IsRealS (A : L2S) : Prop := ∀ k, A (-k) = conjS (A k)
/-- Fourier coefficients of a real-valued trace-free-matrix field: `ρ̂(-k) = conj ρ̂(k)`
(`isRealT_iff_embL2`). -/
def IsRealT (ρ : L2T) : Prop := ∀ k, ρ (-k) = conjT (ρ k)

/-- `P_TSD` on `L²(S)` maps real fields to real fields. -/
theorem isRealS_projS {A : L2S} (hA : IsRealS A) : IsRealS (L2TSDS.starProjection A) :=
  fun k => by rw [projS_apply, projS_apply, hA, freq_neg, projS_neg_conjS]

/-- `P_TSD` on `L²(T)` maps real fields to real fields. -/
theorem isRealT_projT {ρ : L2T} (hρ : IsRealT ρ) : IsRealT (L2TSDT.starProjection ρ) :=
  fun k => by rw [projT_apply, projT_apply, hρ, freq_neg, projT_neg_conjT]

/-- `grad grad : H²(R) → L²(S)` maps real fields to real fields. -/
theorem isRealS_hessT (u : hessT.domain) (hu : IsRealR u) : IsRealS (hessT u) := fun k => by
  change hessS (freq (-k)) ((u : L2R) (-k)) = conjS (hessS (freq k) ((u : L2R) k))
  rw [hu, freq_neg, hessS_neg_conj]

/-- `curl : H(curl, S) → L²(T)` maps real fields to real fields. -/
theorem isRealT_curlST (A : curlST.domain) (hA : IsRealS A) : IsRealT (curlST A) := fun k => by
  change curlS (freq (-k)) ((A : L2S) (-k)) = conjT (curlS (freq k) ((A : L2S) k))
  rw [hA, freq_neg, curlS_neg_conjS]

/-- `div div = (grad grad)* : H(div div, S) → L²(R)` maps real fields to real fields. -/
theorem isRealR_divdiv (A : hessT†.domain) (hA : IsRealS A) : IsRealR (hessT† A) := fun k => by
  rw [adjoint_hessT_apply, adjoint_hessT_apply, hA, freq_neg, divdivS_neg_conjS]

/-- `sym curl = curl* : H(sym curl, T) → L²(S)` maps real fields to real fields. -/
theorem isRealS_symCurl (ρ : curlST†.domain) (hρ : IsRealT ρ) : IsRealS (curlST† ρ) := fun k => by
  rw [adjoint_curlST_apply, adjoint_curlST_apply, hρ, freq_neg, symCurlS_neg_conjT]

end Real

section RealGroup

open HilbertComplex2 Constraints

/-- `ℚ`-algebra structure on fibre operators, for `NormedSpace.exp` (as in
`Feec.Ch4.Existence`). -/
local instance instNormedAlgebraRatFibS : NormedAlgebra ℚ (FibS →L[ℝ] FibS) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

/-- Complex conjugation `ℂ → ℂ` as a real-linear map. -/
def conjC : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap

/-- `conjC` is complex conjugation. -/
@[simp] theorem conjC_apply (c : ℂ) : conjC c = (starRingEnd ℂ) c := rfl

/-- Fibrewise conjugation `(c, A, ρ) ↦ (c̄, Ā, ρ̄)` on `ℂ × S × T`. -/
def conjFib : FibS →L[ℝ] FibS :=
  (Constraints.totL (W0 := ℂ) (W1 := Sym3) (W2 := Tr3)).symm.toContinuousLinearMap ∘L
    (conjC.prodMap (conjS.prodMap conjT)) ∘L
    (Constraints.totL (W0 := ℂ) (W1 := Sym3) (W2 := Tr3)).toContinuousLinearMap

/-- `conjFib` in coordinates. -/
theorem tot_conjFib (x : FibS) :
    tot _ _ _ (conjFib x) = ((starRingEnd ℂ) (tot _ _ _ x).1, conjS (tot _ _ _ x).2.1,
      conjT (tot _ _ _ x).2.2) := by
  simp [conjFib]; rfl

/-- `conjFib` is an involution. -/
theorem conjFib_mul_self : conjFib * conjFib = 1 := by
  ext1 x
  apply (tot ℂ Sym3 Tr3).injective
  simp [tot_conjFib, conjS_conjS, conjT_conjT]

/-- `conjFib` as a unit (it is an involution). -/
def conjFibU : (FibS →L[ℝ] FibS)ˣ := ⟨conjFib, conjFib, conjFib_mul_self, conjFib_mul_self⟩

/-- The fibre symbol of `-L` intertwines the conjugations at `ξ` and `-ξ`:
`W_{-ξ} x̄ = conj (W_ξ x)`. -/
theorem waveSymS_neg_conjFib (ξ : Freq) (x : FibS) :
    waveSymS (-ξ) (conjFib x) = conjFib (waveSymS ξ x) := by
  apply (tot ℂ Sym3 Tr3).injective
  rw [tot_waveSymS, tot_conjFib, tot_conjFib, tot_waveSymS]
  simp only [divdivS_neg_conjS, hessS_neg_conj, symCurlS_neg_conjT, curlS_neg_conjS,
    _root_.map_sub, _root_.map_neg]

/-- `W_{-ξ} = J W_ξ J` with `J = conjFib`. -/
theorem waveSymS_neg (ξ : Freq) : waveSymS (-ξ) = conjFib * waveSymS ξ * conjFib := by
  ext1 x
  change _ = conjFib (waveSymS ξ (conjFib x))
  rw [← waveSymS_neg_conjFib]
  exact congrArg (waveSymS (-ξ))
    (congrArg (fun f : FibS →L[ℝ] FibS => f x) conjFib_mul_self).symm

/-- `exp(t W_{-ξ}) x̄ = conj (exp(t W_ξ) x)` (`NormedSpace.exp_units_conj`). -/
theorem exp_waveSymS_neg_conjFib (t : ℝ) (ξ : Freq) (v : FibS) :
    NormedSpace.exp (t • waveSymS (-ξ)) (conjFib v) =
      conjFib (NormedSpace.exp (t • waveSymS ξ) v) := by
  have h : t • waveSymS (-ξ) = (conjFibU : FibS →L[ℝ] FibS) * (t • waveSymS ξ) *
      ↑conjFibU⁻¹ := by
    rw [waveSymS_neg, mul_smul_comm, smul_mul_assoc]; rfl
  rw [h, NormedSpace.exp_units_conj]
  change conjFib (NormedSpace.exp (t • waveSymS ξ) (conjFib (conjFib v))) = _
  rw [show conjFib (conjFib v) = v from
    congrArg (fun f : FibS →L[ℝ] FibS => f v) conjFib_mul_self]

/-- A state `(σ, E, B)` is real-valued: all three components have conjugate-symmetric
coefficients. -/
def IsRealTot (y : Tot L2R L2S L2T) : Prop :=
  IsRealR (tot _ _ _ y).1 ∧ IsRealS (tot _ _ _ y).2.1 ∧ IsRealT (tot _ _ _ y).2.2

/-- Reality of a state on the Fourier side: `v(-k) = J v(k)` for `v = ΦS⁻¹ y`. -/
theorem isRealTot_iff (y : Tot L2R L2S L2T) :
    IsRealTot y ↔ ∀ k, ΦS.symm y (-k) = conjFib (ΦS.symm y k) := by
  have e : ∀ k, ΦS.symm y (-k) = conjFib (ΦS.symm y k) ↔
      (tot _ _ _ y).1 (-k) = (starRingEnd ℂ) ((tot _ _ _ y).1 k) ∧
        (tot _ _ _ y).2.1 (-k) = conjS ((tot _ _ _ y).2.1 k) ∧
        (tot _ _ _ y).2.2 (-k) = conjT ((tot _ _ _ y).2.2 k) := fun k => by
    rw [← (tot ℂ Sym3 Tr3).injective.eq_iff, tot_conjFib, tot_ΦS_symm_apply, tot_ΦS_symm_apply]
    simp only [Prod.mk.injEq]
  simp only [e, forall_and]
  rfl

/-- **The group `symGroup` preserves real-valued states**, for all `t ∈ ℝ`: it acts fibrewise
by `exp(t W_{ξ_k})` (`symGroup_S_apply`) and these intertwine the conjugations at `±k`
(`exp_waveSymS_neg_conjFib`). -/
theorem isRealTot_symGroup (t : ℝ) {y : Tot L2R L2S L2T} (hy : IsRealTot y) :
    IsRealTot (symGroup.S t y) := by
  rw [isRealTot_iff] at hy ⊢
  intro k
  rw [symGroup_S_apply, symGroup_S_apply, hy k, waveSymSK, waveSymSK, freq_neg,
    exp_waveSymS_neg_conjFib]

/-- Real data `E₀`, `B₀` give a real initial state `(0, E₀, B₀)`. -/
theorem isRealTot_ini {E₀ : L2S} {B₀ : L2T} (hE : IsRealS E₀) (hB : IsRealT B₀) :
    IsRealTot (ini L2R E₀ B₀) := by
  refine ⟨fun k => ?_, ?_, ?_⟩ <;> simp only [tot_ini]
  · simp
  · exact hE
  · exact hB

/-- **Every strong solution of (4.18) on `𝕋³` with real data is real**: by uniqueness
(`Feec.Constraints.strong_unique`, `L` skew-symmetric) it is the orbit of `symGroup`, which
preserves reality (`isRealTot_symGroup`). -/
theorem isRealTot_of_isStrongSolution {T : ℝ} {U₀ : Tot L2R L2S L2T} {U : ℝ → Tot L2R L2S L2T}
    (hU : IsStrongSolution (-symComplex.waveOp) T U₀ 0 U) (hU₀ : IsRealTot U₀) :
    ∀ t ∈ Icc 0 T, IsRealTot (U t) := by
  intro t ht
  have h0 : U₀ ∈ (-symComplex.waveOp).domain := hU.init ▸ hU.mem 0 ⟨le_rfl, ht.1.trans ht.2⟩
  rw [strong_unique _ symGroup.isSkewSymm hU (isStrongSolution_orbit symGroup T ⟨U₀, h0⟩) ht]
  exact isRealTot_symGroup t hU₀

/-- **Thesis Prop 4.19 on `𝕋³` for real-valued fields.** For real data
`E₀ ∈ H(curl, S) ∩ L²(TSD)`, `B₀ ∈ H(sym curl, T) ∩ L²(TSD)` (`IsRealS`, `IsRealT`), the Hodge
wave (4.18) has a strong solution on `[0, T]` with data `(0, E₀, B₀)` that keeps `σ ≡ 0`,
`E, B ∈ L²(TSD)`, solves the reduced system, and is real-valued at every time. It is the unique
strong solution (`Feec.Constraints.strong_unique`), and every strong solution with real data is
real (`isRealTot_of_isStrongSolution`).

Modelling note: the fields of the thesis (the electric and magnetic parts of the Weyl tensor,
[ACBY1997]) are real-valued; complex coefficients are a choice of this formalization (Fourier
model), not an error of the thesis. `prop_4_19_torus_exists` is proved for complex coefficients
viewed as a real Hilbert space, and this theorem recovers the real statement as the
conjugation-invariant part (on the real Hilbert space itself: `prop_4_19_torus_real_space`).

See [QuennevilleBelair2015, §4.11, Prop 4.19 and Thm 4.3]. -/
theorem prop_4_19_torus_exists_real (T : ℝ) {E₀ : L2S} {B₀ : L2T} (hE₀ : E₀ ∈ L2TSDS)
    (hB₀ : B₀ ∈ L2TSDT) (hE : E₀ ∈ HcurlS) (hB : B₀ ∈ HsymCurlT) (hEr : IsRealS E₀)
    (hBr : IsRealT B₀) :
    ∃ U : ℝ → Tot L2R L2S L2T,
      IsStrongSolution (-symComplex.waveOp) T (ini L2R E₀ B₀) 0 U ∧
      (∀ t ∈ Icc 0 T, U t ∈ Kc L2R L2TSDS L2TSDT) ∧
      IsReducedSolution symComplex T E₀ B₀ (fun t => (tot L2R L2S L2T (U t)).2.1)
        (fun t => (tot L2R L2S L2T (U t)).2.2) ∧
      ∀ t, IsRealTot (U t) := by
  have hU := isStrongSolution_orbit symGroup T ⟨_, ini_mem_domL_sym hE₀ hE hB⟩
  exact ⟨_, hU, (prop_4_19_torus hE₀ hB₀ hU).1, (prop_4_19_torus hE₀ hB₀ hU).2,
    fun t => isRealTot_symGroup t (isRealTot_ini hEr hBr)⟩

end RealGroup

section RealBridge

open MeasureTheory

/-- `IsRealS` is `Feec.Torus.IsReal` of the underlying `ℂ³ˣ³`-valued sequence. -/
theorem isRealS_iff_embL2 (A : L2S) : IsRealS A ↔ Feec.Torus.IsReal (embL2 symSub A) :=
  forall_congr' fun k => by
    rw [embL2_apply, embL2_apply, ← coe_conjS]; exact Subtype.ext_iff

/-- `IsRealT` is `Feec.Torus.IsReal` of the underlying `ℂ³ˣ³`-valued sequence. -/
theorem isRealT_iff_embL2 (ρ : L2T) : IsRealT ρ ↔ Feec.Torus.IsReal (embL2 trSub ρ) :=
  forall_congr' fun k => by
    rw [embL2_apply, embL2_apply, ← coe_conjT]; exact Subtype.ext_iff

attribute [local instance] Feec.Torus.instMeasureSpaceUnitAddCircle_feec in
/-- **Real-valued scalar fields**: `f ∈ L²(𝕋³; ℂ)` is real-valued (`f̄ = f`) iff its Fourier
coefficients satisfy `IsRealR`. -/
theorem isRealR_scalarFourier_iff (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))) :
    IsRealR (scalarFourier f) ↔ star f = f := by
  rw [Feec.TorusWeak.star_eq_self_iff]
  simp only [IsRealR, scalarFourier_apply]

end RealBridge

section RealEntries

open MeasureTheory

attribute [local instance] Feec.Torus.instMeasureSpaceUnitAddCircle_feec

/-- Every symmetric `L²` matrix field has its Fourier coefficients in `L2S`. -/
theorem exists_embL2_sym
    (f : PiLp 2 (fun _ : Fin 3 × Fin 3 => Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))))
    (hf : ∀ a b, f (a, b) = f (b, a)) : ∃ A : L2S, embL2 symSub A = matrixFourier f :=
  (mem_fibreSub_iff_embL2 symSub).1 ((matrixFourier_mem_sym f).2 hf)

/-- Every trace-free `L²` matrix field has its Fourier coefficients in `L2T`. -/
theorem exists_embL2_tr
    (f : PiLp 2 (fun _ : Fin 3 × Fin 3 => Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))))
    (hf : ∑ a, f (a, a) = 0) : ∃ ρ : L2T, embL2 trSub ρ = matrixFourier f :=
  (mem_fibreSub_iff_embL2 trSub).1 ((matrixFourier_mem_tr f).2 hf)

/-- **Real-valued symmetric-matrix fields, in physical space**: if `A ∈ L2S` are the Fourier
coefficients of the `L²` matrix field `f` (which is then symmetric, `matrixFourier_mem_sym`;
such `A` exists for every symmetric `f`, `exists_embL2_sym`), then `IsRealS A` iff every entry
of `f` is real-valued. Composes `isRealS_iff_embL2` and
`Feec.TorusWeak.isReal_matrixFourier_iff`. -/
theorem isRealS_iff_entries
    (f : PiLp 2 (fun _ : Fin 3 × Fin 3 => Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))))
    {A : L2S} (hA : embL2 symSub A = matrixFourier f) :
    IsRealS A ↔ ∀ p, star (f p) = f p := by
  rw [isRealS_iff_embL2, hA]
  exact Feec.TorusWeak.isReal_matrixFourier_iff f

/-- **Real-valued trace-free-matrix fields, in physical space**: if `ρ ∈ L2T` are the Fourier
coefficients of the `L²` matrix field `f` (`exists_embL2_tr`), then `IsRealT ρ` iff every entry
of `f` is real-valued. -/
theorem isRealT_iff_entries
    (f : PiLp 2 (fun _ : Fin 3 × Fin 3 => Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))))
    {ρ : L2T} (hρ : embL2 trSub ρ = matrixFourier f) :
    IsRealT ρ ↔ ∀ p, star (f p) = f p := by
  rw [isRealT_iff_embL2, hρ]
  exact Feec.TorusWeak.isReal_matrixFourier_iff f

end RealEntries

section RealSubspaces

/-! ### The real fields as closed subspaces, and the reflection-conjugation -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Conjugate-symmetric sequences `u(-k) = c (u k)` for a fibre conjugation `c`. -/
def realSub (c : E →L[ℝ] E) : Submodule ℝ (L2 Z3 E) where
  carrier := {u | ∀ k, u (-k) = c (u k)}
  zero_mem' := fun k => by simp
  add_mem' := fun {u v} hu hv k => by simp [hu k, hv k]
  smul_mem' := fun r u hu k => by simp [hu k]

/-- Membership in `realSub c`, by definition. -/
theorem mem_realSub {c : E →L[ℝ] E} {u : L2 Z3 E} : u ∈ realSub c ↔ ∀ k, u (-k) = c (u k) :=
  Iff.rfl

/-- `realSub c` is closed. -/
theorem isClosed_realSub (c : E →L[ℝ] E) : IsClosed (realSub c : Set (L2 Z3 E)) := by
  have : (realSub c : Set (L2 Z3 E)) = ⋂ k, {u : L2 Z3 E | u (-k) = c (u k)} := by
    ext; simp [mem_realSub]
  rw [this]
  exact isClosed_iInter fun k => isClosed_eq (lp.evalCLM ℝ (fun _ : Z3 => E) 2 (-k)).continuous
    (c.continuous.comp (lp.evalCLM ℝ (fun _ : Z3 => E) 2 k).continuous)

/-- `k ↦ c (u (-k))` is in `ℓ²` for an isometric `c`. -/
theorem memℓp_reflL2 (c : E →L[ℝ] E) (hc : ∀ x, ‖c x‖ = ‖x‖) (u : L2 Z3 E) :
    Memℓp (fun k => c (u (-k))) 2 := by
  rw [memℓp_two_iff]
  simp only [hc]
  exact (Equiv.neg Z3).summable_iff.2 (memℓp_two_iff.1 (lp.memℓp u))

/-- The reflection-conjugation `(J u)(k) = c (u (-k))` on `ℓ²(ℤ³; E)`; `u` is real iff
`J u = u` (`mem_realSub_iff_reflL2`). -/
def reflL2 (c : E →L[ℝ] E) (hc : ∀ x, ‖c x‖ = ‖x‖) : L2 Z3 E →ₗ[ℝ] L2 Z3 E where
  toFun u := ⟨fun k => c (u (-k)), memℓp_reflL2 c hc u⟩
  map_add' u v := lp.ext (funext fun k => by
    change c ((u + v : L2 Z3 E) (-k)) = c (u (-k)) + c (v (-k))
    rw [lp.coeFn_add, Pi.add_apply, _root_.map_add])
  map_smul' r u := lp.ext (funext fun k => by
    change c ((r • u : L2 Z3 E) (-k)) = r • c (u (-k))
    rw [lp.coeFn_smul, Pi.smul_apply, _root_.map_smul])

/-- `reflL2` applied. -/
theorem reflL2_apply (c : E →L[ℝ] E) (hc : ∀ x, ‖c x‖ = ‖x‖) (u : L2 Z3 E) (k : Z3) :
    reflL2 c hc u k = c (u (-k)) := rfl

/-- `reflL2` is an involution for an involutive `c`. -/
theorem reflL2_reflL2 {c : E →L[ℝ] E} (hc : ∀ x, ‖c x‖ = ‖x‖) (hcc : ∀ x, c (c x) = x)
    (u : L2 Z3 E) : reflL2 c hc (reflL2 c hc u) = u :=
  lp.ext (funext fun k => by simp only [reflL2_apply, neg_neg, hcc])

/-- Real sequences are the fixed points of `reflL2`. -/
theorem mem_realSub_iff_reflL2 {c : E →L[ℝ] E} (hc : ∀ x, ‖c x‖ = ‖x‖)
    (hcc : ∀ x, c (c x) = x) {u : L2 Z3 E} : u ∈ realSub c ↔ reflL2 c hc u = u := by
  constructor
  · intro hu
    exact lp.ext (funext fun k => by rw [reflL2_apply, hu, hcc])
  · intro hu k
    conv_lhs => rw [← hu]
    rw [reflL2_apply, neg_neg]

variable {m : Z3 → E →L[ℝ] F} {cE : E →L[ℝ] E} {cF : F →L[ℝ] F}

/-- A multiplier intertwining the conjugations at `±k` preserves its domain under `reflL2`. -/
theorem reflL2_mem_mulDomain (hcE : ∀ x, ‖cE x‖ = ‖x‖) (hcF : ∀ x, ‖cF x‖ = ‖x‖)
    (hm : ∀ k x, m k (cE x) = cF (m (-k) x)) {u : L2 Z3 E} (hu : u ∈ mulDomain m) :
    reflL2 cE hcE u ∈ mulDomain m := by
  change Memℓp (fun k => m k (cE (u (-k)))) 2
  simp_rw [hm]
  exact memℓp_reflL2 cF hcF (⟨fun k => m k (u k), hu⟩ : L2 Z3 F)

/-- A multiplier intertwining the conjugations at `±k` commutes with `reflL2`. -/
theorem mulOp_reflL2 (hcE : ∀ x, ‖cE x‖ = ‖x‖) (hcF : ∀ x, ‖cF x‖ = ‖x‖)
    (hm : ∀ k x, m k (cE x) = cF (m (-k) x)) (u : (mulOp m).domain) :
    mulOp m ⟨reflL2 cE hcE u, reflL2_mem_mulDomain hcE hcF hm u.2⟩ =
      reflL2 cF hcF (mulOp m u) :=
  lp.ext (funext fun k => hm k _)

/-- `reflL2` preserves the range of such a multiplier. -/
theorem reflL2_mem_range_mulOp (hcE : ∀ x, ‖cE x‖ = ‖x‖) (hcF : ∀ x, ‖cF x‖ = ‖x‖)
    (hm : ∀ k x, m k (cE x) = cF (m (-k) x)) {v : L2 Z3 F} (hv : v ∈ LinearMap.range (mulOp m).toFun) :
    reflL2 cF hcF v ∈ LinearMap.range (mulOp m).toFun := by
  obtain ⟨u, rfl⟩ := hv
  exact ⟨⟨_, reflL2_mem_mulDomain hcE hcF hm u.2⟩, mulOp_reflL2 hcE hcF hm u⟩

/-- `reflL2` preserves the kernel of such a multiplier. -/
theorem reflL2_mem_ker_mulOp (hcE : ∀ x, ‖cE x‖ = ‖x‖) (hcF : ∀ x, ‖cF x‖ = ‖x‖)
    (hm : ∀ k x, m k (cE x) = cF (m (-k) x)) {u : L2 Z3 E} (hu : u ∈ (mulOp m).ker) :
    reflL2 cE hcE u ∈ (mulOp m).ker := by
  obtain ⟨y, hy, rfl⟩ := hu
  have hy' : (mulOp m).toFun y = 0 := hy
  refine ⟨⟨_, reflL2_mem_mulDomain hcE hcF hm y.2⟩, ?_, rfl⟩
  change mulOp m _ = 0
  rw [mulOp_reflL2 hcE hcF hm y]
  change reflL2 cF hcF ((mulOp m).toFun y) = 0
  rw [hy', _root_.map_zero]

/-- A real element of the range of such a multiplier has a real preimage: average a preimage
`u` with `reflL2 u`. -/
theorem exists_real_preimage_mulOp (hcE : ∀ x, ‖cE x‖ = ‖x‖) (hcF : ∀ x, ‖cF x‖ = ‖x‖)
    (hm : ∀ k x, m k (cE x) = cF (m (-k) x)) (hcc : ∀ x, cE (cE x) = x) (hcc' : ∀ x, cF (cF x) = x)
    {v : L2 Z3 F} (hv : v ∈ LinearMap.range (mulOp m).toFun) (hvr : v ∈ realSub cF) :
    ∃ u : (mulOp m).domain, (u : L2 Z3 E) ∈ realSub cE ∧ mulOp m u = v := by
  obtain ⟨u, rfl⟩ := hv
  set u' : (mulOp m).domain := ⟨_, reflL2_mem_mulDomain hcE hcF hm u.2⟩
  have hu' : mulOp m u' = mulOp m u :=
    (mulOp_reflL2 hcE hcF hm u).trans ((mem_realSub_iff_reflL2 hcF hcc').1 hvr)
  refine ⟨(1 / 2 : ℝ) • (u + u'), ?_, ?_⟩
  · rw [mem_realSub_iff_reflL2 hcE hcc]
    change reflL2 cE hcE ((1 / 2 : ℝ) • ((u : L2 Z3 E) + reflL2 cE hcE u)) =
      (1 / 2 : ℝ) • ((u : L2 Z3 E) + reflL2 cE hcE u)
    rw [LinearMap.map_smul, LinearMap.map_add, reflL2_reflL2 hcE hcc, add_comm]
  · change (mulOp m).toFun ((1 / 2 : ℝ) • (u + u')) = (mulOp m).toFun u
    rw [LinearMap.map_smul, LinearMap.map_add]
    change (1 / 2 : ℝ) • (mulOp m u + mulOp m u') = mulOp m u
    rw [hu', ← two_smul ℝ, smul_smul]
    norm_num

/-- Three pairwise orthogonal vectors summing to zero vanish. -/
theorem eq_zero_of_isOrtho3 {U V W : Submodule ℝ E} (hUV : U ⟂ V) (hVW : V ⟂ W) (hUW : U ⟂ W)
    {x y z : E} (hx : x ∈ U) (hy : y ∈ V) (hz : z ∈ W) (h : x + y + z = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have ex := congrArg (fun w => ⟪x, w⟫) h
  have ey := congrArg (fun w => ⟪y, w⟫) h
  have ez := congrArg (fun w => ⟪z, w⟫) h
  simp only [inner_add_right, inner_zero_right] at ex ey ez
  rw [hUV.inner_eq hx hy, hUW.inner_eq hx hz, add_zero, add_zero] at ex
  rw [hUV.symm.inner_eq hy hx, hVW.inner_eq hy hz, zero_add, add_zero] at ey
  rw [hUW.symm.inner_eq hz hx, hVW.symm.inner_eq hz hy, zero_add, zero_add] at ez
  exact ⟨inner_self_eq_zero.1 ex, inner_self_eq_zero.1 ey, inner_self_eq_zero.1 ez⟩

end RealSubspaces

section RealHodge

/-! ### Real fields: closed subspaces, complementary projections, Hodge pieces -/

open HilbertComplex2 Constraints

/-- Entrywise conjugation is isometric. -/
theorem norm_conjM (M : Mat3) : ‖conjM M‖ = ‖M‖ := by
  have h : ‖conjM M‖ ^ 2 = ‖M‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_conjM, conjM_conjM]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- `conjS` is isometric. -/
theorem norm_conjS (A : Sym3) : ‖conjS A‖ = ‖A‖ := by
  rw [← Submodule.norm_coe, coe_conjS, norm_conjM, Submodule.norm_coe]

/-- `conjT` is isometric. -/
theorem norm_conjT (ρ : Tr3) : ‖conjT ρ‖ = ‖ρ‖ := by
  rw [← Submodule.norm_coe, coe_conjT, norm_conjM, Submodule.norm_coe]

/-- `conjC` is isometric. -/
theorem norm_conjC (c : ℂ) : ‖conjC c‖ = ‖c‖ := by simp

/-- `conjC` is an involution. -/
theorem conjC_conjC (c : ℂ) : conjC (conjC c) = c := by simp

/-- Real scalar fields, as a closed subspace of `L2R` (`isClosed_realR`). -/
abbrev realR : Submodule ℝ L2R := realSub conjC
/-- Real symmetric-matrix fields, as a closed subspace of `L2S`. -/
abbrev realS : Submodule ℝ L2S := realSub conjS
/-- Real trace-free-matrix fields, as a closed subspace of `L2T`. -/
abbrev realT : Submodule ℝ L2T := realSub conjT

/-- `IsRealR` is membership in `realR`. -/
theorem isRealR_iff_mem (u : L2R) : IsRealR u ↔ u ∈ realR := Iff.rfl
/-- `IsRealS` is membership in `realS`. -/
theorem isRealS_iff_mem (A : L2S) : IsRealS A ↔ A ∈ realS := Iff.rfl
/-- `IsRealT` is membership in `realT`. -/
theorem isRealT_iff_mem (ρ : L2T) : IsRealT ρ ↔ ρ ∈ realT := Iff.rfl

/-- Real states `(σ, E, B)`, as a subspace of `Tot L2R L2S L2T`. -/
def realTot : Submodule ℝ (Tot L2R L2S L2T) :=
  (realR.prod (realS.prod realT)).comap (tot L2R L2S L2T).toLinearMap

/-- `IsRealTot` is membership in `realTot`. -/
theorem isRealTot_iff_mem (y : Tot L2R L2S L2T) : IsRealTot y ↔ y ∈ realTot := Iff.rfl

/-- The real states form a closed subspace. -/
theorem isClosed_realTot : IsClosed (realTot : Set (Tot L2R L2S L2T)) := by
  have h : (realTot : Set (Tot L2R L2S L2T)) =
      (Constraints.totL (W0 := L2R) (W1 := L2S) (W2 := L2T)) ⁻¹'
        ((realR : Set L2R) ×ˢ ((realS : Set L2S) ×ˢ (realT : Set L2T))) := by
    ext y; rfl
  rw [h]
  exact ((isClosed_realSub _).prod ((isClosed_realSub _).prod (isClosed_realSub _))).preimage
    (Constraints.totL (W0 := L2R) (W1 := L2S) (W2 := L2T)).continuous

instance : CompleteSpace realTot := isClosed_realTot.completeSpace_coe

/-- The complementary projection `I - P_TSD` on `L²(S)` preserves real fields. -/
theorem isRealS_sub_projS {A : L2S} (hA : IsRealS A) :
    IsRealS (A - L2TSDS.starProjection A) :=
  realS.sub_mem hA (isRealS_projS hA)

/-- The complementary projection `I - P_TSD` on `L²(T)` preserves real fields. -/
theorem isRealT_sub_projT {ρ : L2T} (hρ : IsRealT ρ) :
    IsRealT (ρ - L2TSDT.starProjection ρ) :=
  realT.sub_mem hρ (isRealT_projT hρ)

/-- **Real constrained states are invariant**: for `x ∈ D(L) ∩ K` real, `symGroup.S t x` is real
and in `K` for `t ≥ 0`. -/
theorem symGroup_mem_Kc_inf_realTot {t : ℝ} (ht : 0 ≤ t) {x : Tot L2R L2S L2T}
    (hx : x ∈ symComplex.domL) (hxK : x ∈ Kc L2R L2TSDS L2TSDT ⊓ realTot) :
    symGroup.S t x ∈ Kc L2R L2TSDS L2TSDT ⊓ realTot :=
  ⟨prop_4_19_torus_symGroup ht hx hxK.1, isRealTot_symGroup t hxK.2⟩

/-- The reflection-conjugation on `L2R`. -/
abbrev reflR : L2R →ₗ[ℝ] L2R := reflL2 conjC norm_conjC
/-- The reflection-conjugation on `L2S`. -/
abbrev reflS : L2S →ₗ[ℝ] L2S := reflL2 conjS norm_conjS
/-- The reflection-conjugation on `L2T`. -/
abbrev reflT : L2T →ₗ[ℝ] L2T := reflL2 conjT norm_conjT

/-- `hessS_neg_conj` in the form used by `reflL2`. -/
theorem hessS_conj (k : Z3) (c : ℂ) :
    hessS (freq k) (conjC c) = conjS (hessS (freq (-k)) c) := by
  rw [conjC_apply, ← hessS_neg_conj, freq_neg, neg_neg]

/-- `curlS_neg_conjS` in the form used by `reflL2`. -/
theorem curlS_conj (k : Z3) (A : Sym3) :
    curlS (freq k) (conjS A) = conjT (curlS (freq (-k)) A) := by
  rw [← curlS_neg_conjS, freq_neg, neg_neg]

/-- `divdivS_neg_conjS` in the form used by `reflL2`. -/
theorem divdivS_conj (k : Z3) (A : Sym3) :
    divdivS (freq k) (conjS A) = conjC (divdivS (freq (-k)) A) := by
  rw [conjC_apply, ← divdivS_neg_conjS, freq_neg, neg_neg]

/-- `symCurlS_neg_conjT` in the form used by `reflL2`. -/
theorem symCurlS_conj (k : Z3) (ρ : Tr3) :
    symCurlS (freq k) (conjT ρ) = conjS (symCurlS (freq (-k)) ρ) := by
  rw [← symCurlS_neg_conjT, freq_neg, neg_neg]

/-- `reflS` preserves `range (grad grad)`. -/
theorem reflS_mem_range_d0 {A : L2S} (hA : A ∈ LinearMap.range symComplex.d0.toFun) :
    reflS A ∈ LinearMap.range symComplex.d0.toFun :=
  reflL2_mem_range_mulOp (m := fun k => hessS (freq k)) norm_conjC norm_conjS hessS_conj hA

/-- `reflS` preserves `range (sym curl)`. -/
theorem reflS_mem_range_d1adj {A : L2S} (hA : A ∈ LinearMap.range symComplex.d1†.toFun) :
    reflS A ∈ LinearMap.range symComplex.d1†.toFun := by
  change A ∈ LinearMap.range (curlST†).toFun at hA
  change reflS A ∈ LinearMap.range (curlST†).toFun
  rw [adjoint_curlST] at hA ⊢
  exact reflL2_mem_range_mulOp norm_conjT norm_conjS symCurlS_conj hA

/-- `reflS` preserves the harmonic fields `ker curl ∩ ker div div`. -/
theorem reflS_mem_harmonic {A : L2S} (hA : A ∈ symComplex.harmonic) :
    reflS A ∈ symComplex.harmonic := by
  change A ∈ curlST.ker ⊓ (hessT†).ker at hA
  change reflS A ∈ curlST.ker ⊓ (hessT†).ker
  rw [adjoint_hessT] at hA ⊢
  exact ⟨reflL2_mem_ker_mulOp norm_conjS norm_conjT curlS_conj hA.1,
    reflL2_mem_ker_mulOp norm_conjS norm_conjC divdivS_conj hA.2⟩

/-- **Real Hodge decomposition of `L²(S)` on `𝕋³`**: a real field `A` splits as
`A = grad grad u + h + sym curl ρ` (`symComplex_hodge`) with all three pieces real; this is
the unique decomposition, and `J = reflS` maps each summand to itself
(`reflS_mem_range_d0`, `reflS_mem_harmonic`, `reflS_mem_range_d1adj`). The potentials can be
chosen real as well (`exists_real_hessT_preimage`, `exists_real_symCurl_preimage`). -/
theorem symComplex_hodge_real {A : L2S} (hA : IsRealS A) :
    ∃ a ∈ LinearMap.range symComplex.d0.toFun, ∃ h ∈ symComplex.harmonic,
      ∃ b ∈ LinearMap.range symComplex.d1†.toFun,
        A = a + h + b ∧ IsRealS a ∧ IsRealS h ∧ IsRealS b := by
  obtain ⟨hsup, h0H, hH1, h01⟩ := symComplex_hodge
  have hmem : A ∈ LinearMap.range symComplex.d0.toFun ⊔ symComplex.harmonic ⊔
      LinearMap.range symComplex.d1†.toFun := hsup ▸ Submodule.mem_top
  obtain ⟨y, hy, b, hb, rfl⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨a, ha, h, hh, rfl⟩ := Submodule.mem_sup.1 hy
  refine ⟨a, ha, h, hh, b, hb, rfl, ?_⟩
  have hJ : reflS (a + h + b) = a + h + b :=
    (mem_realSub_iff_reflL2 norm_conjS conjS_conjS).1 hA
  rw [LinearMap.map_add, LinearMap.map_add] at hJ
  have hsum : (reflS a - a) + (reflS h - h) + (reflS b - b) = 0 := by
    rw [← sub_eq_zero] at hJ
    rw [← hJ]; abel
  obtain ⟨e1, e2, e3⟩ := eq_zero_of_isOrtho3 h0H hH1 h01
    (Submodule.sub_mem _ (reflS_mem_range_d0 ha) ha)
    (Submodule.sub_mem _ (reflS_mem_harmonic hh) hh)
    (Submodule.sub_mem _ (reflS_mem_range_d1adj hb) hb) hsum
  exact ⟨(mem_realSub_iff_reflL2 norm_conjS conjS_conjS).2 (sub_eq_zero.1 e1),
    (mem_realSub_iff_reflL2 norm_conjS conjS_conjS).2 (sub_eq_zero.1 e2),
    (mem_realSub_iff_reflL2 norm_conjS conjS_conjS).2 (sub_eq_zero.1 e3)⟩

/-- A real field in `range (grad grad)` is `grad grad u` for a real `u ∈ H²(R)`. -/
theorem exists_real_hessT_preimage {A : L2S} (hA : A ∈ LinearMap.range symComplex.d0.toFun)
    (hAr : IsRealS A) : ∃ u : hessT.domain, IsRealR u ∧ hessT u = A :=
  exists_real_preimage_mulOp (m := fun k => hessS (freq k)) norm_conjC norm_conjS hessS_conj
    conjC_conjC conjS_conjS hA hAr

/-- A real field in `range (sym curl)` is `sym curl ρ` for a real `ρ ∈ H(sym curl, T)`. -/
theorem exists_real_symCurl_preimage {A : L2S}
    (hA : A ∈ LinearMap.range symComplex.d1†.toFun) (hAr : IsRealS A) :
    ∃ ρ : L2T, ρ ∈ HsymCurlT ∧ IsRealT ρ ∧
      ∃ hρ : ρ ∈ curlST†.domain, curlST† ⟨ρ, hρ⟩ = A := by
  change A ∈ LinearMap.range (curlST†).toFun at hA
  have hA' := hA
  rw [adjoint_curlST] at hA'
  obtain ⟨ρ, hρr, hρ⟩ := exists_real_preimage_mulOp (m := fun k => symCurlS (freq k))
    norm_conjT norm_conjS symCurlS_conj conjT_conjT conjS_conjS hA' hAr
  have hdom : (ρ : L2T) ∈ curlST†.domain := adjoint_curlST_domain ▸ ρ.2
  refine ⟨ρ, ρ.2, hρr, hdom, ?_⟩
  rw [← hρ]
  exact lp.ext (funext fun k => adjoint_curlST_apply ⟨ρ, hdom⟩ k)

end RealHodge

section RealSpace

/-! ### Prop 4.19 on the real Hilbert space of real fields

A Stone group restricts to a closed invariant subspace, with generator the restriction of `L`
(`restrictGroup`). Applied to `realTot` and `symGroup`, this gives the real Hodge wave
equation as an evolution on the real Hilbert space itself. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A derivative of a curve in a closed subspace lies in the subspace. -/
theorem hasDerivAt_mem_of_isClosed {V : Submodule ℝ E} (hV : IsClosed (V : Set E))
    {g : ℝ → E} {d : E} {t : ℝ} (hg : HasDerivAt g d t) (hgV : ∀ s, g s ∈ V) : d ∈ V := by
  rw [hasDerivAt_iff_tendsto_slope] at hg
  exact hV.mem_of_tendsto hg (Filter.Eventually.of_forall fun s => by
    rw [slope_def_module]
    exact V.smul_mem _ (V.sub_mem (hgV s) (hgV t)))

/-- Derivatives of curves in a subspace are computed in the ambient space. -/
theorem hasDerivAt_subtype_iff {V : Submodule ℝ E} {f : ℝ → V} {d : V} {t : ℝ} :
    HasDerivAt f d t ↔ HasDerivAt (fun s => (f s : E)) (d : E) t := by
  simp only [hasDerivAt_iff_tendsto_slope]
  rw [tendsto_subtype_rng]
  refine Iff.of_eq (congrArg (fun φ => Filter.Tendsto φ _ _) (funext fun s => ?_))
  simp [slope_def_module]

variable {L : E →ₗ.[ℝ] E} (G : UnitaryGroupGenerator L) (V : Submodule ℝ E)
  (hVc : IsClosed (V : Set E)) (hV : ∀ t, ∀ x ∈ V, G.S t x ∈ V)

include hVc hV in
/-- The generator maps `D(L) ∩ V` into `V` (difference quotients of the group stay in `V`). -/
theorem gen_mem_of_invariant (x : L.domain) (hx : (x : E) ∈ V) : L x ∈ V :=
  hasDerivAt_mem_of_isClosed hVc (G.hasDerivAt_zero x) fun s => hV s _ hx

/-- The restriction of the generator to an invariant closed subspace `V`:
`D = D(L) ∩ V`, `x ↦ L x`. -/
def restrictGen : V →ₗ.[ℝ] V where
  domain := L.domain.comap V.subtype
  toFun :=
    { toFun := fun x => ⟨L ⟨x.1.1, x.2⟩, gen_mem_of_invariant G V hVc hV ⟨x.1.1, x.2⟩ x.1.2⟩
      map_add' := fun x y => Subtype.ext (by
        change L ⟨_, _⟩ = L ⟨_, _⟩ + L ⟨_, _⟩
        rw [← LinearPMap.map_add]; rfl)
      map_smul' := fun r x => Subtype.ext (by
        change L ⟨_, _⟩ = r • L ⟨_, _⟩
        rw [← LinearPMap.map_smul]; rfl) }

/-- The restricted generator is `L` on `D(L) ∩ V`. -/
theorem coe_restrictGen_apply (x : (restrictGen G V hVc hV).domain) :
    ((restrictGen G V hVc hV x : V) : E) = L ⟨x.1.1, x.2⟩ := rfl

/-- The restricted group, as a map on `V`. -/
def restrictS (t : ℝ) : V →L[ℝ] V :=
  (G.S t ∘L V.subtypeL).codRestrict V fun x => hV t x x.2

/-- `restrictS` is `S t` on `V`. -/
theorem coe_restrictS_apply (t : ℝ) (x : V) : ((restrictS G V hV t x : V) : E) = G.S t x := rfl

/-- **A Stone group restricts to a closed invariant subspace**, generated by the restriction of
the generator (`restrictGen`). -/
def restrictGroup [CompleteSpace V] : UnitaryGroupGenerator (restrictGen G V hVc hV) where
  S := restrictS G V hV
  map_zero := by
    ext x; simp [coe_restrictS_apply, G.map_zero]
  map_add s t := by
    ext x; simp [coe_restrictS_apply, G.map_add]
  norm_map t x := by
    rw [← Submodule.norm_coe, coe_restrictS_apply, G.norm_map, Submodule.norm_coe]
  continuous_apply x := (G.continuous_apply x).subtype_mk _
  mem_domain_iff x := by
    change (x : E) ∈ L.domain ↔ _
    rw [G.mem_domain_iff]
    constructor
    · rintro ⟨d, hd⟩
      have hd' := hd.hasDerivAt
      have hdV : (d 1) ∈ V := hasDerivAt_mem_of_isClosed hVc hd' fun s => hV s _ x.2
      exact (hasDerivAt_subtype_iff (d := ⟨d 1, hdV⟩).2 hd').differentiableAt
    · intro h
      have := (V.subtypeL.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h.hasDerivAt).differentiableAt
      exact this
  hasDerivAt_zero x := hasDerivAt_subtype_iff.2 (G.hasDerivAt_zero ⟨x.1.1, x.2⟩)

/-- A strong solution in `V` of the restricted problem is a strong solution in `E`. -/
theorem isStrongSolution_coe {T : ℝ} {x₀ : V} {U : ℝ → V}
    (hU : IsStrongSolution (restrictGen G V hVc hV) T x₀ 0 U) :
    IsStrongSolution L T x₀ 0 (fun t => (U t : E)) := by
  refine ⟨fun t ht => hU.mem t ht, fun t ht => ?_, by rw [hU.init]⟩
  have h := V.subtypeL.hasFDerivAt.comp_hasDerivWithinAt t (hU.deriv t ht)
  simp only [Pi.zero_apply, add_zero] at h ⊢
  exact h

end RealSpace

section RealProp419

open HilbertComplex2 Constraints

/-- `realTot` is invariant under `symGroup` (`isRealTot_symGroup`). -/
theorem symGroup_mem_realTot (t : ℝ) (x : Tot L2R L2S L2T) (hx : x ∈ realTot) :
    symGroup.S t x ∈ realTot :=
  isRealTot_symGroup t hx

/-- **The Hodge wave operator `-L` of (4.18) on the real Hilbert space of real states**: the
restriction of `-L` to `D(L) ∩ realTot` (`coe_restrictGen_apply`). -/
abbrev symGenReal : realTot →ₗ.[ℝ] realTot :=
  restrictGen symGroup realTot isClosed_realTot symGroup_mem_realTot

/-- **Stone group of the real Hodge wave equation**: the restriction of `symGroup` to the real
states, generated by `symGenReal`. -/
def symGroupReal : UnitaryGroupGenerator symGenReal :=
  restrictGroup symGroup realTot isClosed_realTot symGroup_mem_realTot

/-- The real initial state `(0, E₀, B₀)`. -/
def iniReal {E₀ : L2S} {B₀ : L2T} (hEr : IsRealS E₀) (hBr : IsRealT B₀) : realTot :=
  ⟨ini L2R E₀ B₀, isRealTot_ini hEr hBr⟩

/-- **Thesis Prop 4.19 on `𝕋³`, on the real Hilbert space of real fields.** Let
`E₀ ∈ H(curl, S) ∩ L²(TSD)`, `B₀ ∈ H(sym curl, T) ∩ L²(TSD)` be real. The real Hodge wave
equation `U' = -L U` on `realTot` (`symGenReal`, the restriction of `-L`) has a strong
solution with data `(0, E₀, B₀)` (the orbit of `symGroupReal`), it is unique
(`Feec.Constraints.strong_unique`, `symGroupReal.isSkewSymm`), and **every** strong solution
of the real problem keeps `σ ≡ 0`, `E, B ∈ L²(TSD)` and solves the reduced system: it is a
strong solution of the complex-coefficient problem (`isStrongSolution_coe`), to which
`prop_4_19_torus` applies.

See [QuennevilleBelair2015, §4.11, Prop 4.19 and Thm 4.3]. -/
theorem prop_4_19_torus_real_space (T : ℝ) {E₀ : L2S} {B₀ : L2T} (hE₀ : E₀ ∈ L2TSDS)
    (hB₀ : B₀ ∈ L2TSDT) (hE : E₀ ∈ HcurlS) (hB : B₀ ∈ HsymCurlT) (hEr : IsRealS E₀)
    (hBr : IsRealT B₀) :
    (∃ U : ℝ → realTot, IsStrongSolution symGenReal T (iniReal hEr hBr) 0 U) ∧
      ∀ U : ℝ → realTot, IsStrongSolution symGenReal T (iniReal hEr hBr) 0 U →
        (∀ t ∈ Icc 0 T, (U t : Tot L2R L2S L2T) ∈ Kc L2R L2TSDS L2TSDT) ∧
        IsReducedSolution symComplex T E₀ B₀ (fun t => (tot L2R L2S L2T (U t)).2.1)
          (fun t => (tot L2R L2S L2T (U t)).2.2) := by
  refine ⟨⟨_, isStrongSolution_orbit symGroupReal T
    ⟨iniReal hEr hBr, ini_mem_domL_sym hE₀ hE hB⟩⟩, fun U hU => ?_⟩
  exact prop_4_19_torus hE₀ hB₀
    (isStrongSolution_coe symGroup realTot isClosed_realTot symGroup_mem_realTot hU)

/-- Uniqueness for the real problem: two strong solutions of `U' = -L U` on `realTot` with the
same data agree on `[0, T]`. -/
theorem real_space_unique {T : ℝ} {x₀ : realTot} {U U' : ℝ → realTot}
    (hU : IsStrongSolution symGenReal T x₀ 0 U) (hU' : IsStrongSolution symGenReal T x₀ 0 U') :
    EqOn U U' (Icc 0 T) :=
  strong_unique _ symGroupReal.isSkewSymm hU hU'

end RealProp419

end Feec.TorusSym
