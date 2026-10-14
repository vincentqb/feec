module

public import Feec.Ch4.Torus

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
complex-valued fields viewed as a real Hilbert space.

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
* In the solution space after (4.17), `E ∈ C¹([0, T]; L²(M))` should read `L²(S) = W1`; in the
  proof, `-grad(H̊²(R) ∩ 0)` should read `-grad grad(H̊²(R) ∩ {0})`.
* The projection and density "conjectures" are theorems on `𝕋³` (see above), and the density
  ones are not needed (`prop_4_17`). The projections `P_{L²(TSD)}` in `L²(S)`, `L²(T)` agree
  with the one in `L²(M)` (`coe_projS`, `coe_projT`), so the thesis' notation is unambiguous.

What remains open: the bounded-domain setting of the thesis (`H̊²`, `H̊(curl, S)`), where the
projection conjecture is not settled here (cf. the docstring of `Feec.Constraints.prop_4_17`);
the closed-range property of (4.16) ("we show in the next chapter that these complexes are
closed"), which `prop_4_19_torus` does not need; and the existence of solutions, which is not
constructed: `prop_4_19_torus` quantifies over strong solutions, and `prop_4_19_torus_group`
assumes a Stone group (`Feec.UnitaryGroupGenerator`) for `-L`.

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
  rw [mem_domL] at hx ⊢
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

/-- Group form of `prop_4_19_torus`: given a Stone group for `-L` (the existence input,
`Feec.UnitaryGroupGenerator`), every orbit starting in `D(L) ∩ K` stays in
`K = {0} × L²(TSD) × L²(TSD)` for `t ≥ 0`.

See [QuennevilleBelair2015, Prop 4.19 and Thm 4.3]; cf. [Pazy1983, §1.10]. -/
theorem prop_4_19_torus_group (G : UnitaryGroupGenerator (-symComplex.waveOp)) {t : ℝ}
    (ht : 0 ≤ t) {x : Tot L2R L2S L2T} (hx : x ∈ symComplex.domL)
    (hxK : x ∈ Kc L2R L2TSDS L2TSDT) : G.S t x ∈ Kc L2R L2TSDS L2TSDT :=
  Kc_propagate L2TSDS_le_ker projKc_mem_domL curlST_mem_L2TSDT adjoint_curlST_mem_L2TSDS
    (isStrongSolution_orbit G t ⟨x, hx⟩) hxK t ⟨ht, le_rfl⟩

end Periodic

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

end Feec.TorusSym
