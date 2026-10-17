module

public import Feec.Legacy.Torus.Group
public import Feec.Legacy.Torus.Weak

/-!
# Thesis Prop 4.19 on the flat torus `𝕋³`: the strong-symmetry complex

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use.
Most of the original module was re-derived in the general layers (see
`docs/migration/map.tsv`); what remains is listed below.

## Contents

* `TorusSym.trM`: The transpose of a matrix, as a real-linear map.
* `TorusSym.trM_apply`: Entries of `trM M = Mᵀ`.
* `TorusSym.inner_trM`: Transposition is self-adjoint.
* `TorusSym.symM`: The symmetric part `sym M = (M + Mᵀ)/2`.
* `TorusSym.symM_apply`: Entries of `sym M`.
* `TorusSym.symSub`: The symmetric matrices `S`.
* `TorusSym.trSub`: The trace-free matrices `T`.
* `TorusSym.mem_symSub`: Membership in `S`.
* `TorusSym.mem_trSub`: Membership in `T`.
* `TorusSym.symM_mem_symSub`: `sym M` is symmetric.
* `TorusSym.symM_of_mem_symSub`: `sym` fixes symmetric matrices.
* `TorusSym.inner_symM`: `sym` is self-adjoint.
* `TorusSym.inner_symM_of_mem`: Against a symmetric matrix, `sym` can be dropped: `⟪sym X, A⟫ = ⟪X, A⟫`.
* `TorusSym.tsd_le_symSub`: TSD matrices are symmetric.
* `TorusSym.tsd_le_trSub`: TSD matrices are trace-free.
* `TorusSym.symM_mem_tsd`: `sym` maps the TSD fibre to itself (it fixes it).
* `TorusSym.curlSym_mem_trSub`: The curl of a symmetric matrix is trace-free (`curl : S → T`, so (4.16) is well typed).
* `TorusSym.hessM`: The Hessian symbol `c ↦ -c ξ ξᵀ` (`∂_a ∂_b ↦ (i ξ_a)(i ξ_b)`), with values in matrices.
* `TorusSym.hessM_apply`: Entries of the Hessian symbol.
* `TorusSym.hessM_eq_outer`: The Hessian symbol is an outer product `(-c ξ) ξᵀ`.
* `TorusSym.norm_hessM`: `‖ξ ξᵀ c‖ = |ξ|² |c|` (Frobenius norm).
* `TorusSym.hessM_mem_symSub`: Hessians are symmetric.
* `TorusSym.curlSym_hessM`: `curl ∘ grad grad = 0` on the symbol level.
* `TorusSym.Sym3`: Symmetric matrices `S`, the fibre of `W1 = L²(S)`.
* `TorusSym.Tr3`: Trace-free matrices `T`, the fibre of `W2 = L²(T)`.
* `TorusSym.hessS`: The fibre of `grad grad : H²(R) → H(curl, S)`: `c ↦ -c ξ ξᵀ ∈ S`.
* `TorusSym.curlS`: The fibre of `curl : H(curl, S) → L²(T)`.
* `TorusSym.divdivS`: The fibre of `div div : H(div div, S) → L²(R)`: `A ↦ -ξᵀ A ξ`.
* `TorusSym.symCurlS`: The fibre of `sym curl : H(sym curl, T) → L²(S)`.
* `TorusSym.coe_hessS`: `hessS ξ c` is the Hessian symbol.
* `TorusSym.coe_curlS`: `curlS ξ A` is the curl symbol of `A`.
* `TorusSym.coe_symCurlS`: `symCurlS ξ ρ = sym (curl_ξ ρ)`.
* `TorusSym.divdivS_apply`: `divdivS ξ A = -∑ ξ_a ξ_b A_{ab}`.
* `TorusSym.inner_curlSym`: `curl_ξ` is symmetric for the real inner product.
* `TorusSym.adjoint_hessS`: **`(grad grad)* = div div`** fibrewise, as in the adjoint complex (4.17).
* `TorusSym.adjoint_curlS`: **`curl* = sym curl`** fibrewise (`curl : S → T`), as in the adjoint complex (4.17).
* `TorusSym.tsdS`: The TSD fibre inside `S`.
* `TorusSym.tsdT`: The TSD fibre inside `T`.
* `TorusSym.coe_starProjection_comap`: The orthogonal projection onto `K ≤ U`, computed inside `U`, is the ambient projection.
* `TorusSym.coe_projS`: The TSD projection in `S` is the ambient TSD projection.
* `TorusSym.coe_projT`: The TSD projection in `T` is the ambient TSD projection.
* `TorusSym.proj_symM`: `P_TSD ∘ sym = P_TSD` (TSD matrices are symmetric).
* `TorusSym.curlS_projS`: `curl P_TSD = P_TSD curl` on `S` (values in `T`).
* `TorusSym.symCurlS_projT`: `sym curl P_TSD = P_TSD sym curl` on `T` (values in `S`).
* `TorusSym.norm_curlS_projS_le`: Fibre estimate for `H(curl, S)`: `‖curl P_TSD A‖ ≤ ‖curl A‖`.
* `TorusSym.norm_symCurlS_projT_le`: Fibre estimate for `H(sym curl, T)`: `‖sym curl P_TSD ρ‖ ≤ ‖sym curl ρ‖`.
* `TorusSym.divdivS_eq_zero`: TSD matrices are `div div`-free on the symbol level.
* `TorusSym.L2R`: Fourier coefficients of scalar fields, `W0 = L²(𝕋³; ℂ)`.
* `TorusSym.L2S`: Fourier coefficients of symmetric-matrix fields, `W1 = L²(𝕋³; S)`.
* `TorusSym.L2T`: Fourier coefficients of trace-free-matrix fields, `W2 = L²(𝕋³; T)`.
* `TorusSym.hessT`: The periodic `grad grad : H²(R) → L²(S)` on the Fourier side.
* `TorusSym.curlST`: The periodic row-wise `curl : H(curl, S) → L²(T)` on the Fourier side.
* `TorusSym.HcurlS`: `H(curl, S)`.
* `TorusSym.HdivdivS`: `H(div div, S)`.
* `TorusSym.HsymCurlT`: `H(sym curl, T)`.
* `TorusSym.L2TSDS`: `L²(TSD)` as a subspace of `L²(S)`.
* `TorusSym.L2TSDT`: `L²(TSD)` as a subspace of `L²(T)`.
* `TorusSym.adjoint_hessT`: `(grad grad)* = div div`, with domain `H(div div, S)`.
* `TorusSym.adjoint_curlST`: `curl* = sym curl`, with domain `H(sym curl, T)`.
* `TorusSym.adjoint_hessT_domain`: The domain of `(grad grad)*` is `H(div div, S)`.
* `TorusSym.adjoint_curlST_domain`: The domain of `curl*` is `H(sym curl, T)`.
* `TorusSym.symComplex`: **The periodic strong-symmetry complex (4.16)** `H²(R) --grad grad--> H(curl, S) --curl--> L²(T)` on `𝕋³`.
* `TorusSym.projS_apply`: `P_TSD` on `L²(S)` acts fibrewise.
* `TorusSym.projT_apply`: `P_TSD` on `L²(T)` acts fibrewise.
* `TorusSym.projS_mem_HcurlS`: `P_TSD H(curl, S) ⊆ H(curl, S)`.
* `TorusSym.projT_mem_HsymCurlT`: `P_TSD H(sym curl, T) ⊆ H(sym curl, T)`.
* `TorusSym.L2TSDS_le_HdivdivS`: `L²(TSD) ⊆ H(div div, S)`.
* `TorusSym.L2TSDS_le_ker`: `L²(TSD) ⊆ ker div div` (`hS1` of `Kc_propagates`).
* `TorusSym.curlST_mem_L2TSDT`: `curl` maps `H(curl, S) ∩ L²(TSD)` into `L²(TSD)` (`hd1` of `Kc_propagates`).
* `TorusSym.adjoint_curlST_mem_L2TSDS`: `curl* = sym curl` maps `H(sym curl, T) ∩ L²(TSD)` into `L²(TSD)` (`hd1s` of `Kc_propagates`).
* `TorusSym.projKc_mem_domL`: **The projection hypothesis of Prop 4.19 holds on `𝕋³`** (`hPD` of `Kc_propagates`): `P_K D(L) ⊆ D(L)` for `K = {0} × L²(TSD) × L²(TSD)`, where `D(L) = H²(R) × (H(curl, S) ∩ H(div div, S)) × H(sym curl, T)`.
* `TorusSym.curlS_hessS`: `curl_ξ ∘ (grad grad)_ξ = 0` on `S` (fibre form of `d1 d0 = 0`).
* `TorusSym.adjoint_curlST_apply`: `curl* = sym curl` fibrewise, applied.
* `TorusSym.range_mulOp_eq`: The range of a multiplier with uniformly bounded fibre preimages is fibrewise: `range (mulOp m) = {v | ∀ i, v i ∈ range (m i)}`.
* `TorusSym.isClosed_range_mulOp`: **Closed range of multipliers**: if every fibre value `m i x` has a preimage of norm `≤ C ‖m i x‖` (`C` uniform in `i`), the multiplier has closed range.
* `TorusSym.freq_eq_zero_or`: The lattice frequencies are `0` or of size `≥ 2π`: `freq k = 0 ∨ 4π² ≤ |ξ_k|²`.
* `TorusSym.freq_eq_zero_or_two_le`: `freq k = 0 ∨ 2 ≤ |ξ_k|²`.
* `TorusSym.norm_sq_mat_eq`: `‖M‖² = ∑ₐ ∑_b |M_{ab}|²`.
* `TorusSym.norm_sum_freq_mul_sq_le`: Cauchy–Schwarz: `|∑ₐ ξ_a z_a|² ≤ |ξ|² ∑ₐ |z_a|²` (`ξ` real, `z` complex).
* `TorusSym.lagrange_vec`: Lagrange identity for one complex vector: `|ξ × v|² + |v · ξ|² = |ξ|² |v|²`.
* `TorusSym.cross_divR_eq`: For symmetric `x`, `ξ × (x ξ) = ξᵀ (curl_ξ x)`, i.e.
* `TorusSym.norm_divR_sq_le_curlR`: **Fibre estimate for closed range of `curl` on `S`**: for symmetric `x` with `ξᵀ x ξ = 0`, `|x ξ| ≤ |ξ × x|` (row-wise curl).
* `TorusSym.curlS_zero`: The curl symbol vanishes at `ξ = 0`.
* `TorusSym.hessS_zero`: The Hessian symbol vanishes at `ξ = 0`.
* `TorusSym.hessS_preimage`: Fibre preimages for `grad grad`: at a lattice frequency, `c` itself works with constant `1` (`|ξ|² ≥ 1` unless `ξ = 0`).
* `TorusSym.curlS_preimage`: **Fibre preimages for `curl : S → T`** with constant `1`: for `|ξ|² ≥ 2` (or `ξ = 0`), every `curl_ξ A` is `curl_ξ X` with `‖X‖ ≤ ‖curl_ξ A‖`, namely `X = A - (ξᵀ A ξ / |ξ|⁴) ξ ξᵀ` (the component of `A` orthogonal to the kernel `ℂ ξ ξᵀ`, up to the choice of complement): `|ξ|² ‖X‖² = ‖curl X‖² + ‖X ξ‖² ≤ 2 ‖curl X‖²` by `norm_divR_sq_le_curlR`.
* `TorusSym.symComplex_closedRange`: **The periodic strong-symmetry complex (4.16) is closed** (closed ranges): the thesis defers this ("we show in the next chapter that these complexes are closed"); on `𝕋³` it follows from the fibre preimage bounds `hessS_preimage` (`|ξ|² ≥ 4π²` off `ξ = 0`) and `curlS_preimage`.
* `TorusSym.symComplex_hodge`: **Hodge decomposition of `L²(S)` on `𝕋³`, without closures** (Thesis Thm 4.1 for the complex (4.16)): `L²(S) = grad grad H²(R) ⊕ ℌ ⊕ sym curl H(sym curl, T)`, pairwise orthogonal.
* `TorusSym.embL2`: Fibrewise inclusion `ℓ²(ℤ³; U) → ℓ²(ℤ³; ℂ³ˣ³)` for a subspace `U` of matrices (`U = S` gives `L2S`, `U = T` gives `L2T`).
* `TorusSym.embL2_apply`: `embL2` forgets the constraint fibrewise.
* `TorusSym.scalarFourier`: Scalar fields: `L²(𝕋³; ℂ) ≃ₗᵢ L2R` (Parseval), the model of `W0 = L²(R)`.
* `TorusSym.scalarFourier_apply`: `scalarFourier f k` is the `k`-th Fourier coefficient of `f`.
* `TorusSym.embL2_sym_mem_Hcurl_iff`: `H(curl, S)` is `Feec.Legacy.Torus.Hcurl` restricted to symmetric fields.
* `TorusSym.curlT_embL2`: **`curl` on `H(curl, S)` is the curl of `Feec.Legacy.Torus` (the matrix complex of Prop 4.17)**: `curlT (embL2 A) = embL2 (curlST A)`.
* `TorusSym.symM_conjM`: Entrywise conjugation commutes with `sym`.
* `TorusSym.conjM_mem_symSub`: Entrywise conjugation preserves `S`.
* `TorusSym.conjM_mem_trSub`: Entrywise conjugation preserves `T`.
* `TorusSym.conjS`: Entrywise conjugation of symmetric matrices.
* `TorusSym.conjT`: Entrywise conjugation of trace-free matrices.
* `TorusSym.coe_conjS`: `conjS` is `conjM` on the underlying matrix.
* `TorusSym.coe_conjT`: `conjT` is `conjM` on the underlying matrix.
* `TorusSym.conjM_conjM`: Entrywise conjugation is an involution.
* `TorusSym.conjS_conjS`: `conjS` is an involution.
* `TorusSym.conjT_conjT`: `conjT` is an involution.
* `TorusSym.hessM_neg_conj`: Hessian symbol and conjugation: `(grad grad)_{-ξ} c̄ = conj ((grad grad)_ξ c)`.
* `TorusSym.curlSym_neg_conjM`: Curl symbol and conjugation: `curl_{-ξ} M̄ = conj (curl_ξ M)` (the symbol `i ξ ×` is odd in `ξ` and purely imaginary).
* `TorusSym.hessS_neg_conj`: `grad grad` symbol on `S` and conjugation.
* `TorusSym.curlS_neg_conjS`: `curl : S → T` symbol and conjugation.
* `TorusSym.symCurlS_neg_conjT`: `sym curl : T → S` symbol and conjugation.
* `TorusSym.divdivS_neg_conjS`: `div div : S → R` symbol and conjugation (`-ξᵀ A ξ` is even in `ξ`).
* `TorusSym.IsRealR`: Fourier coefficients of a real-valued scalar field: `û(-k) = conj û(k)` (`isRealR_scalarFourier_iff`).
* `TorusSym.IsRealS`: Fourier coefficients of a real-valued symmetric-matrix field: `Â(-k) = conj Â(k)` (`isRealS_iff_embL2`, cf.
* `TorusSym.IsRealT`: Fourier coefficients of a real-valued trace-free-matrix field: `ρ̂(-k) = conj ρ̂(k)` (`isRealT_iff_embL2`).
* `TorusSym.conjC`: Complex conjugation `ℂ → ℂ` as a real-linear map.
* `TorusSym.conjC_apply`: `conjC` is complex conjugation.
* `TorusSym.isRealS_iff_embL2`: `IsRealS` is `Feec.Legacy.Torus.IsReal` of the underlying `ℂ³ˣ³`-valued sequence.
* `TorusSym.isRealT_iff_embL2`: `IsRealT` is `Feec.Legacy.Torus.IsReal` of the underlying `ℂ³ˣ³`-valued sequence.
* `TorusSym.isRealR_scalarFourier_iff`: **Real-valued scalar fields**: `f ∈ L²(𝕋³; ℂ)` is real-valued (`f̄ = f`) iff its Fourier coefficients satisfy `IsRealR`.
* `TorusSym.realSub`: Conjugate-symmetric sequences `u(-k) = c (u k)` for a fibre conjugation `c`.
* `TorusSym.memℓp_reflL2`: `k ↦ c (u (-k))` is in `ℓ²` for an isometric `c`.
* `TorusSym.reflL2`: The reflection-conjugation `(J u)(k) = c (u (-k))` on `ℓ²(ℤ³; E)`; `u` is real iff `J u = u` (`mem_realSub_iff_reflL2`).
* `TorusSym.reflL2_apply`: `reflL2` applied.
* `TorusSym.reflL2_reflL2`: `reflL2` is an involution for an involutive `c`.
* `TorusSym.mem_realSub_iff_reflL2`: Real sequences are the fixed points of `reflL2`.
* `TorusSym.reflL2_mem_mulDomain`: A multiplier intertwining the conjugations at `±k` preserves its domain under `reflL2`.
* `TorusSym.mulOp_reflL2`: A multiplier intertwining the conjugations at `±k` commutes with `reflL2`.
* `TorusSym.reflL2_mem_range_mulOp`: `reflL2` preserves the range of such a multiplier.
* `TorusSym.reflL2_mem_ker_mulOp`: `reflL2` preserves the kernel of such a multiplier.
* `TorusSym.exists_real_preimage_mulOp`: A real element of the range of such a multiplier has a real preimage: average a preimage `u` with `reflL2 u`.
* `TorusSym.eq_zero_of_isOrtho3`: Three pairwise orthogonal vectors summing to zero vanish.
* `TorusSym.norm_conjM`: Entrywise conjugation is isometric.
* `TorusSym.norm_conjS`: `conjS` is isometric.
* `TorusSym.norm_conjT`: `conjT` is isometric.
* `TorusSym.norm_conjC`: `conjC` is isometric.
* `TorusSym.conjC_conjC`: `conjC` is an involution.
* `TorusSym.reflR`: The reflection-conjugation on `L2R`.
* `TorusSym.reflS`: The reflection-conjugation on `L2S`.
* `TorusSym.reflT`: The reflection-conjugation on `L2T`.
* `TorusSym.hessS_conj`: `hessS_neg_conj` in the form used by `reflL2`.
* `TorusSym.curlS_conj`: `curlS_neg_conjS` in the form used by `reflL2`.
* `TorusSym.divdivS_conj`: `divdivS_neg_conjS` in the form used by `reflL2`.
* `TorusSym.symCurlS_conj`: `symCurlS_neg_conjT` in the form used by `reflL2`.
* `TorusSym.reflS_mem_range_d0`: `reflS` preserves `range (grad grad)`.
* `TorusSym.reflS_mem_range_d1adj`: `reflS` preserves `range (sym curl)`.
* `TorusSym.reflS_mem_harmonic`: `reflS` preserves the harmonic fields `ker curl ∩ ker div div`.
* `TorusSym.symComplex_hodge_real`: **Real Hodge decomposition of `L²(S)` on `𝕋³`**: a real field `A` splits as `A = grad grad u + h + sym curl ρ` (`symComplex_hodge`) with all three pieces real; this is the unique decomposition, and `J = reflS` maps each summand to itself (`reflS_mem_range_d0`, `reflS_mem_harmonic`, `reflS_mem_range_d1adj`).
* `TorusSym.exists_real_hessT_preimage`: A real field in `range (grad grad)` is `grad grad u` for a real `u ∈ H²(R)`.
* `TorusSym.exists_real_symCurl_preimage`: A real field in `range (sym curl)` is `sym curl ρ` for a real `ρ ∈ H(sym curl, T)`.

## References

* [QuennevilleBelair2015], §3.4 (Lemma 3.5), §4.11 ((4.16)–(4.18), Prop 4.19), §4.10
  (Prop 4.17, the analogous matrix complex)
* [ArnoldHu2021], [Eastwood2000] (the `grad grad`–`curl`–`div` complex of symmetric and
  trace-free matrix fields, from the BGG construction)
* [ACBY1997] (the Einstein–Bianchi system)
* [AFW2010], [Arnold2018], [BruningLesch1992] (Hilbert complexes)
* [Pazy1983], §1.10 (unitary groups and Stone's theorem, behind `Feec.Legacy.UnitaryGroupGenerator`)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace
open LinearPMap Set

namespace Feec.Legacy.TorusSym

open Feec.Legacy.Torus

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

/-- `H(curl, S)`. -/
def HcurlS : Submodule ℝ L2S := mulDomain fun k => curlS (freq k)
/-- `H(div div, S)`. -/
def HdivdivS : Submodule ℝ L2S := mulDomain fun k => divdivS (freq k)
/-- `H(sym curl, T)`. -/
def HsymCurlT : Submodule ℝ L2T := mulDomain fun k => symCurlS (freq k)
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

/-- `L²(TSD) ⊆ ker div div` (`hS1` of `Kc_propagates`). -/
theorem L2TSDS_le_ker : L2TSDS ≤ symComplex.d0†.ker := by
  intro A hA
  change A ∈ hessT†.ker
  have hdom : A ∈ hessT†.domain := adjoint_hessT_domain ▸ L2TSDS_le_HdivdivS hA
  refine LinearPMap.mem_ker_iff.2 ⟨⟨A, hdom⟩, rfl, lp.ext (funext fun k => ?_)⟩
  have h := adjoint_mulOp_apply (fun k => hessS (freq k)) ⟨A, hdom⟩ k
  rw [adjoint_hessS] at h
  rw [lp.coeFn_zero, Pi.zero_apply]
  exact h.trans (divdivS_eq_zero (hA k))

/-- `curl` maps `H(curl, S) ∩ L²(TSD)` into `L²(TSD)` (`hd1` of `Kc_propagates`).

See [QuennevilleBelair2015, §3.4, Lemma 3.5]. -/
theorem curlST_mem_L2TSDT (u : symComplex.d1.domain) (hu : (u : L2S) ∈ L2TSDS) :
    symComplex.d1 u ∈ L2TSDT := fun k => curlSym_mem_tsd (hu k)

/-- `curl* = sym curl` maps `H(sym curl, T) ∩ L²(TSD)` into `L²(TSD)` (`hd1s` of
`Kc_propagates`). -/
theorem adjoint_curlST_mem_L2TSDS (ρ : symComplex.d1†.domain) (hρ : (ρ : L2T) ∈ L2TSDT) :
    symComplex.d1† ρ ∈ L2TSDS := fun k => by
  have h := adjoint_mulOp_apply (fun k => curlS (freq k)) ρ k
  rw [adjoint_curlS] at h
  change ((symComplex.d1† ρ k : Sym3) : Mat3) ∈ tsd (freq k)
  exact h ▸ symM_mem_tsd (curlSym_mem_tsd (hρ k))

/-- **The projection hypothesis of Prop 4.19 holds on `𝕋³`** (`hPD` of `Kc_propagates`):
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

end Periodic

section Group

open HilbertComplex2 Constraints Filter

/-- `curl_ξ ∘ (grad grad)_ξ = 0` on `S` (fibre form of `d1 d0 = 0`). -/
theorem curlS_hessS (ξ : Freq) (c : ℂ) : curlS ξ (hessS ξ c) = 0 :=
  Subtype.ext (curlSym_hessM ξ c)

/-- `curl* = sym curl` fibrewise, applied. -/
theorem adjoint_curlST_apply (u : curlST†.domain) (k : Z3) :
    (curlST† u : L2S) k = symCurlS (freq k) ((u : L2T) k) := by
  have h := adjoint_mulOp_apply (fun k => curlS (freq k)) u k
  rw [adjoint_curlS] at h
  exact h

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

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Legacy.Torus.Basic` (equal to the default `volume`,
`Feec.Legacy.Torus.measureSpace_unitAddCircle_eq`). -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- Scalar fields: `L²(𝕋³; ℂ) ≃ₗᵢ L2R` (Parseval), the model of `W0 = L²(R)`. -/
def scalarFourier : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) ≃ₗᵢ[ℂ] L2R :=
  UnitAddTorus.mFourierBasis.repr

/-- `scalarFourier f k` is the `k`-th Fourier coefficient of `f`. -/
theorem scalarFourier_apply (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))) (k : Z3) :
    scalarFourier f k = UnitAddTorus.mFourierCoeff f k :=
  UnitAddTorus.mFourierBasis_repr f k

end Model

section Bridge

/-! ### Relation to the `ℂ³ˣ³`-valued model of `Feec.Legacy.Torus.Basic` -/

/-- `H(curl, S)` is `Feec.Legacy.Torus.Hcurl` restricted to symmetric fields. -/
theorem embL2_sym_mem_Hcurl_iff (A : L2S) : embL2 symSub A ∈ Hcurl ↔ A ∈ HcurlS := by
  change Memℓp (fun k => curlSym (freq k) ((A k : Sym3) : Mat3)) 2 ↔
    Memℓp (fun k => curlS (freq k) (A k)) 2
  rw [← memℓp_norm_iff, ← memℓp_norm_iff (f := fun k => curlS (freq k) (A k))]
  simp only [← coe_curlS, Submodule.norm_coe]

/-- **`curl` on `H(curl, S)` is the curl of `Feec.Legacy.Torus` (the matrix complex of Prop 4.17)**:
`curlT (embL2 A) = embL2 (curlST A)`. -/
theorem curlT_embL2 (A : curlST.domain) :
    curlT ⟨embL2 symSub A, (embL2_sym_mem_Hcurl_iff A).2 A.2⟩ = embL2 trSub (curlST A) := rfl

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

/-- Fourier coefficients of a real-valued scalar field: `û(-k) = conj û(k)`
(`isRealR_scalarFourier_iff`). -/
def IsRealR (u : L2R) : Prop := ∀ k, u (-k) = (starRingEnd ℂ) (u k)
/-- Fourier coefficients of a real-valued symmetric-matrix field: `Â(-k) = conj Â(k)`
(`isRealS_iff_embL2`, cf. `Feec.Legacy.TorusWeak.isReal_matrixFourier_iff`). -/
def IsRealS (A : L2S) : Prop := ∀ k, A (-k) = conjS (A k)
/-- Fourier coefficients of a real-valued trace-free-matrix field: `ρ̂(-k) = conj ρ̂(k)`
(`isRealT_iff_embL2`). -/
def IsRealT (ρ : L2T) : Prop := ∀ k, ρ (-k) = conjT (ρ k)

end Real

section RealGroup

open HilbertComplex2 Constraints

/-- Complex conjugation `ℂ → ℂ` as a real-linear map. -/
def conjC : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap

/-- `conjC` is complex conjugation. -/
@[simp] theorem conjC_apply (c : ℂ) : conjC c = (starRingEnd ℂ) c := rfl

end RealGroup

section RealBridge

open MeasureTheory

/-- `IsRealS` is `Feec.Legacy.Torus.IsReal` of the underlying `ℂ³ˣ³`-valued sequence. -/
theorem isRealS_iff_embL2 (A : L2S) : IsRealS A ↔ Feec.Legacy.Torus.IsReal (embL2 symSub A) :=
  forall_congr' fun k => by
    rw [embL2_apply, embL2_apply, ← coe_conjS]; exact Subtype.ext_iff

/-- `IsRealT` is `Feec.Legacy.Torus.IsReal` of the underlying `ℂ³ˣ³`-valued sequence. -/
theorem isRealT_iff_embL2 (ρ : L2T) : IsRealT ρ ↔ Feec.Legacy.Torus.IsReal (embL2 trSub ρ) :=
  forall_congr' fun k => by
    rw [embL2_apply, embL2_apply, ← coe_conjT]; exact Subtype.ext_iff

attribute [local instance] Feec.Legacy.Torus.instMeasureSpaceUnitAddCircle_feec in
/-- **Real-valued scalar fields**: `f ∈ L²(𝕋³; ℂ)` is real-valued (`f̄ = f`) iff its Fourier
coefficients satisfy `IsRealR`. -/
theorem isRealR_scalarFourier_iff (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))) :
    IsRealR (scalarFourier f) ↔ star f = f := by
  rw [Feec.Legacy.TorusWeak.star_eq_self_iff]
  simp only [IsRealR, scalarFourier_apply]

end RealBridge

section RealEntries

open MeasureTheory

attribute [local instance] Feec.Legacy.Torus.instMeasureSpaceUnitAddCircle_feec

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

end Feec.Legacy.TorusSym
