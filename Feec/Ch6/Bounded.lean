module

public import Feec.Ch4.BoundedSym

/-!
# Chapter 6 on bounded domains: the BGG weak-symmetry system does not propagate TSD

Does the bounded-domain failure of Props 4.17/4.19 (`Feec.Ch4.BoundedDomain`,
`Feec.Ch4.BoundedSym`) affect the method the thesis actually builds and runs? The Ch. 6 method
([QuennevilleBelair2015, §6.1, §6.3]) is the Hodge wave equation of the BGG complex (5.1),
with the symmetry of `E` imposed weakly through the variable `M` (and, in (6.2), the constraint
`dσ = Sφ` through a Lagrange multiplier `λ`); the Ch. 7 experiments run (4.14) and (4.15).
§6.3 states the boundary conditions explicitly ("Dirichlet boundary conditions for the 0-forms,
and null tangent component for the 1-forms"; Table 6.1: `H̊¹`, `H̊¹(V)`, `H̊(curl, M)`), so a
bounded domain with these conditions is the setting of the thesis' method; no periodic or
whole-space version is considered there. This file builds the continuous Ch. 6 system on every
bounded open `Ω ⊆ ℝ³` and answers the question.

## Verdict

On every nonempty bounded open `Ω ⊆ ℝ³`, for the TSD datum
`(σ, u, (M, B))(0) = (0, 0, (0, β))`, `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)` (symmetric, trace-free,
divergence-free, `M = 0`), the continuous Ch. 6 problem (6.1) has a unique strong solution
(Stone's theorem), and on every `[0, T]`, `T > 0` (`bggComplex_verdict`):
* `σ ≡ 0` and `div div u ≡ 0` weakly: these propagate for all data (`bggComplex_prop_4_16`);
* `u(t) ∉ L²(TSD)` for some `t ∈ [0, T]` (`bggComplex_not_propagate`, for any `E₀`, any `M₀`);
* the magnetic field `B(t)` is not symmetric for some `t ∈ [0, T]`
  (`bggComplex_B_not_symm`, for any `E₀`, any `M₀`).
So imposing the symmetry of `E` weakly does not cure the bounded-domain failure: the Ch. 6
continuous problem loses the TSD constraint exactly as (4.14) and (4.18) do. Both refutations
hold for every Hilbert complex whose second operator is `u ↦ (S₁ u, curl u)` on `H̊(curl, M)`,
whatever its first operator (`IsSkwCurl`, `B_not_symm_of_isSkwCurl`,
`not_propagate_of_isSkwCurl`), so they do not depend on how the thesis' `Γ` is realised.

The loss of symmetry of `B` is new also for Ch. 4: from `(0, E₀, β)` it holds for (4.14)
(`thesisComplex_B_not_symm`), for the reduced system (4.15) (`thesisComplex_reduced_B_not_symm`),
which are the two systems run in Ch. 7, and for (4.18) with `B ∈ L²(T)`
(`symComplexB_B_not_symm`). The earlier refutations only showed that `(E, B)` leaves
`L²(TSD)²`.

## The mathematics

1. *Mean from the skew part of the curl* (`inner_curl_skewLin`): for `E ∈ H̊(curl, M)` and the
   skew field `Ψ_{ab} = skewOf (x_a e_b)` (no boundary condition, `curl Ψ_{ab} = δ_{ab} I -
   e_a e_bᵀ`), `⟪curl E, Ψ_{ab}⟫ = δ_{ab} ∫ tr E - ∫ E_{ab}`. Hence `∫ E = 0` whenever `curl E`
   is symmetric (`integral_eq_zero_of_curl_symm`; no condition on `E` itself), and
   `⟪E, diag(1, -1, 0)⟫ = ⟪curl E, Ψ_{11} - Ψ_{00}⟫`.
2. *`B` loses symmetry* (`exists_not_symm_of_path`): if `Ḃ = curl E` and `B` stays symmetric
   on `[0, T]`, then `⟪Ḃ, Ψ_{ab}⟫ = 0`, so `⟪E(t), diag(1, -1, 0)⟫ ≡ 0`; but its derivative at
   `0` is `⟪Ė(0), diag(1, -1, 0)⟫ = ⟪-curl β, diag(1, -1, 0)⟫ = 2|Ω| ≠ 0`. Only the
   `B`-equation `Ḃ = curl E`, the boundary condition `E ∈ H̊(curl, M)` and `Ė(0)` enter.
3. *The Ch. 6 operator* (`smoothPair_mem_adjoint`, `adjoint_betaPair_of_isSkwCurl`): for `C¹`
   magnetic data with no boundary condition, `(m, Ψ) ∈ D(d1*)` with
   `d1* (m, Ψ) = S₁* m + curl Ψ`; `S₁* m` is skew, hence orthogonal to `diag(1, -1, 0)`, so
   `u̇(0) = -d1* (m, β)` pairs to `2|Ω|` with `diag(1, -1, 0)` for every `m`.
4. *`u` leaves `L²(TSD)`*: `Feec.BoundedDomain.not_propagate_of_adjoint` (TSD fields in
   `H̊(curl, M)` lie in `L²(TSD₀) ⊥ diag(1, -1, 0)`).

## Model

As in `Feec.Ch4.BoundedDomain` and `Feec.Ch4.BoundedSym` (graph closures of classical operators
on `C_c^∞`, weak derivatives, `L²(Ω; ℝ³ˣ³)` as nine copies of `L²(Ω)`). The complex (5.1) of the
§6.3 application, with `S₀ = I` and `S₁ = 2 vskw` (`skwL`, the normalization for which
`curl S₀ = -S₁ grad`), is `bggComplex`:
`L²(Ω) ⊇ H̊²(Ω) --grad grad--> H̊(curl, M) --(S₁, curl)--> L²(Ω; ℝ³) × L²(Ω; ℝ³ˣ³)`.
The thesis' `Γ = {(σ, φ) ∈ H̊¹ × H̊¹(V) : grad σ = φ}` with the norm `‖σ‖` is identified with
its `σ`-projection, so `Γ̄ = L²(Ω)` and `(0 d)(σ, grad σ) = grad grad σ`; we take for the domain
the closure `H̊²(Ω)` of `C_c^∞(Ω)` in the graph norm (`hessM`). The `σ`-projection of `Γ`,
`{σ ∈ H̊¹ : grad σ ∈ H̊¹(V)}`, contains `H̊²(Ω)` and equals it on Lipschitz domains (not
formalized); the refutations do not use this choice (`IsSkwCurl`). A strong solution of the Hodge
wave equation of `bggComplex` solves (6.1) (`bggComplex_eq61`), with
`(σ, u, (M, B)) ↔ (σ, u, (M, ρ))` in the thesis' notation.

## Main results

* Complex (5.1) on `Ω`: `skwCurl` (closed, `isClosed_skwCurl`), `hessM` (closed, densely defined,
  symmetric values, `curl grad grad = 0`), `bggComplex`, `mem_ker_adjoint_hessM_iff`
  (`ker (grad grad)* = H(div div, M, 0)`), `TSD_le_ker_bgg`; `hodgeWave_weak_eqs`,
  `bggComplex_eq61` ((6.1a)–(6.1d) for strong solutions).
* What propagates: `bggComplex_prop_4_16` (`σ ≡ 0`, `div div u ≡ 0`, existence, uniqueness).
* What does not: `bggComplex_not_propagate`, `bggComplex_B_not_symm`, `bggComplex_verdict`;
  for Ch. 4/7: `thesisComplex_B_not_symm`, `thesisComplex_reduced_B_not_symm`,
  `symComplexB_B_not_symm`; the abstract criteria `not_symm_of_adjoint`,
  `reduced_not_symm_of_adjoint`, `exists_not_symm_of_path`.

## Correction

[QuennevilleBelair2015, §6.1, §6.3]: the thesis states no constraint-propagation result for the
Ch. 6 method; the method is introduced (Ch. 5 introduction) as a weak-symmetry replacement for
the strong-symmetry formulation (4.16)/(4.18), whose solutions Prop 4.19 claims stay TSD. On
bounded domains with the thesis' boundary conditions the continuous
problem (6.1) does not keep TSD data TSD: `u` leaves `L²(TSD)` and `B` loses symmetry
immediately. The same holds for (4.14) and (4.15), the systems of the Ch. 7 experiments, with
homogeneous boundary conditions.

Not formalized / open: which of the algebraic constraints of `E` (symmetry, i.e. the weak
symmetry `M ≡ 0`; trace; row divergence, i.e. the multiplier `λ = (S*)⁻¹ d* u` of (6.2)) is
lost (only that one of them is, `bggComplex_not_propagate`); the multiplier form (6.2) on `Ω`
(the space `W̌¹ = H⁻¹(div, V)`); the semi-discrete method (6.5) and its finite element spaces;
whether the Ch. 7 figures (nonzero trace and skew part of `E`, Figure 7.1(c)–(d)) reflect this
effect: Ch. 7 does not state its boundary conditions, and its exact plane-wave solution does not
satisfy the homogeneous conditions treated here.

## References

* [QuennevilleBelair2015], Ch. 5 (§5.1 the complex (5.1), Prop 5.1), Ch. 6 (§6.1 (6.1)/(6.2),
  Prop 6.1; §6.3 the EB application, Table 6.1), Ch. 7 ((4.14), (4.15), Tables 7.1–7.2),
  §4.10–4.11 (Props 4.16–4.19), §3.4 (Lemma 3.5)
* [ArnoldHu2021] (the BGG construction), [AFW2007] (weakly imposed symmetry)
* [AFW2010], [BruningLesch1992] (Hilbert complexes)
* [Brezis2011] (Sobolev spaces, weak derivatives)
* [Pazy1983], §1.10 (Stone's theorem, behind `Feec.HilbertComplex2.waveGroup`)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal ContDiff Matrix LinearPMap
open MeasureTheory Set Filter Topology

namespace Feec.Ch6.Bounded

open Feec.BoundedDomain Feec.BoundedSym Feec.HilbertComplex2 Feec.Constraints

variable {Ω : Set R3}

/-! ## §1. Mean of a field in `H̊(curl, M)` from the skew part of its curl -/

/-- The linear vector field `x_a e_b` (component `b` equal to the coordinate `x_a`). -/
def linField (a b : Fin 3) : Fin 3 → R3 → ℝ := fun i => if i = b then (fun y : R3 => y a) else 0

theorem contDiff_linField (a b i : Fin 3) : ContDiff ℝ ∞ (linField a b i) := by
  unfold linField
  split_ifs
  exacts [contDiff_apply ℝ (fun _ : Fin 3 => ℝ) a, contDiff_const]

theorem pd_linField (a b m i : Fin 3) (x : R3) :
    BoundedDomain.pd m (linField a b i) x = if i = b ∧ m = a then 1 else 0 := by
  by_cases hi : i = b
  · simp only [linField, hi, ite_true, true_and]
    exact pd_coord a m x
  · simp only [linField, hi, ite_false, false_and]
    simp [BoundedDomain.pd]

/-- The skew field `skewOf (x_a e_b)` (rows `e_j × x_a e_b`), as an element of `L²(Ω; ℝ³ˣ³)`. -/
def skewLin (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (a b : Fin 3) : L2M Ω :=
  smoothField hΩ hb (skewOf (linField a b))
    (fun jk => (contDiff_skewOf (fun i => contDiff_linField a b i) jk).continuous)

/-- A skew field pairs to zero with a symmetric one. -/
theorem inner_skewLin_eq_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {C : L2M Ω}
    (hC : C ∈ symL2 Ω) (a b : Fin 3) : ⟪C, skewLin hΩ hb a b⟫ = 0 := by
  rw [skewLin, inner_smoothField]
  exact sum_integral_mul_skewOf_eq_zero hC _

/-- **The mean of `B ∈ H̊(curl, M)` is read off from the skew part of `curl B`.** For `(B, C)` in
the closure of the curl graph (`C = curl B`, electric boundary condition) and every `a, b`:
`⟪C, skewOf (x_a e_b)⟫ = δ_{ab} ∫_Ω tr B - ∫_Ω B_{ab}`. No symmetry, trace or divergence
condition on `B` is assumed. (Testing the graph closure against the non-compactly-supported
`skewOf (x_a e_b)`, whose curl is the constant `δ_{ab} I - e_a e_bᵀ`, `curlM_skewOf`.) -/
theorem inner_curl_skewLin (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B C : L2M Ω}
    (h : (B, C) ∈ closure (curlGraph Ω)) (a b : Fin 3) :
    ⟪C, skewLin hΩ hb a b⟫ = (if a = b then ∑ i, ∫ x, B (i, i) x ∂volume.restrict Ω else 0) -
      ∫ x, B (a, b) x ∂volume.restrict Ω := by
  have hvd : ∀ i, ContDiff ℝ 1 (linField a b i) := fun i =>
    (contDiff_linField a b i).of_le (by simp)
  have hdv : ∀ x, ∑ m, BoundedDomain.pd m (linField a b m) x = if a = b then 1 else 0 := by
    intro x
    simp only [pd_linField, Fin.sum_univ_three]
    fin_cases a <;> fin_cases b <;> simp
  rw [skewLin, inner_smoothField, closure_curlGraph_identity hΩ hb h (contDiff_skewOf hvd)]
  simp only [curlM_skewOf (fun i => (hvd i).differentiable one_ne_zero), hdv]
  simp only [pd_linField, integral_mul_const]
  fin_cases a <;> fin_cases b <;> simp [Fintype.sum_prod_type, Fin.sum_univ_three] <;> ring

/-- **Zero mean from a symmetric curl.** If `B ∈ H̊(curl, M)` has symmetric curl, then
`∫_Ω B = 0` (no condition on `B` itself). This sharpens
`Feec.BoundedDomain.integral_eq_zero_of_mem_TSD_of_mem_HcurlZero`, whose TSD hypothesis enters
only through the symmetry of `curl B` (Lemma 3.5) and `tr B = 0`; the trace condition is not
needed. -/
theorem integral_eq_zero_of_curl_symm (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {B C : L2M Ω} (h : (B, C) ∈ closure (curlGraph Ω)) (hC : C ∈ symL2 Ω) (a b : Fin 3) :
    ∫ x, B (a, b) x ∂volume.restrict Ω = 0 := by
  have e : ∀ a b, (if a = b then ∑ i, ∫ x, B (i, i) x ∂volume.restrict Ω else 0) -
      ∫ x, B (a, b) x ∂volume.restrict Ω = 0 := fun a b => by
    rw [← inner_curl_skewLin hΩ hb h, inner_skewLin_eq_zero hΩ hb hC]
  have e0 := e 0 0
  have e1 := e 1 1
  have e2 := e 2 2
  simp only [Fin.sum_univ_three, ite_true] at e0 e1 e2
  have htr : ∑ i, ∫ x, B (i, i) x ∂volume.restrict Ω = 0 := by
    simp only [Fin.sum_univ_three]
    linarith
  have := e a b
  rw [htr, ite_self, zero_sub, neg_eq_zero] at this
  exact this

/-- `⟪diag(1, -1, 0), diag(1, -1, 0)⟫ = 2 |Ω|`. -/
theorem inner_constField_diagA (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ⟪constField hΩ hb diagA, constField hΩ hb diagA⟫ = 2 * volume.real Ω := by
  rw [inner_constField]
  simp only [integral_constField]
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, diagA]
  ring

/-- `diag(1, -1, 0)` is symmetric. -/
theorem constField_diagA_mem_symL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    constField hΩ hb diagA ∈ symL2 Ω := fun i j => by
  refine Lp.ext ?_
  filter_upwards [coeFn_constField hΩ hb diagA (i, j), coeFn_constField hΩ hb diagA (j, i)]
    with x h1 h2
  rw [h1, h2]
  exact diagA_swap i j

/-! ## §2. The magnetic field loses symmetry: the abstract criterion -/

/-- **Core lemma (paths).** Let `E, B : ℝ → L²(Ω; ℝ³ˣ³)` with `E(t) ∈ H̊(curl, M)` and
`Ḃ(t) = curl E(t)` on `[0, T]`, `T > 0` (the `B`-equation of (4.14), (4.15), (4.18) and
(6.1d)), and `⟪Ė(0), diag(1, -1, 0)⟫ ≠ 0`. Then `B(t)` is not symmetric for some
`t ∈ [0, T]`.

Proof: if `B` stays symmetric, `⟪B(t), skewOf (x_a e_b)⟫ ≡ 0`, so its derivative
`⟪curl E(t), skewOf (x_a e_b)⟫` vanishes; by `inner_curl_skewLin` (`a = b = 0, 1`) this is
`⟪E(t), diag(1, -1, 0)⟫ ≡ 0` (the trace terms cancel since `tr diag(1, -1, 0) = 0`), whose
derivative at `0` is `⟪Ė(0), diag(1, -1, 0)⟫ ≠ 0`. -/
theorem exists_not_symm_of_path (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {T : ℝ}
    (hT : 0 < T) {E B : ℝ → L2M Ω} {E' : L2M Ω} (hE : HasDerivWithinAt E E' (Icc 0 T) 0)
    (hB : ∀ t ∈ Icc 0 T, ∃ C, HasDerivWithinAt B C (Icc 0 T) t ∧ (E t, C) ∈ closure (curlGraph Ω))
    (hE' : ⟪E', constField hΩ hb diagA⟫ ≠ 0) : ∃ t ∈ Icc 0 T, B t ∉ symL2 Ω := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  have hℓ : ∀ t ∈ Icc 0 T, ⟪E t, constField hΩ hb diagA⟫ = 0 := by
    intro t ht
    obtain ⟨C, hC, hEC⟩ := hB t ht
    have hX : ∀ a b, ⟪C, skewLin hΩ hb a b⟫ = 0 := by
      intro a b
      have h1 := (innerSL ℝ (skewLin hΩ hb a b)).hasFDerivAt.comp_hasDerivWithinAt t hC
      have h0 : HasDerivWithinAt (fun s => innerSL ℝ (skewLin hΩ hb a b) (B s)) 0 (Icc 0 T) t :=
        (hasDerivWithinAt_const t (Icc 0 T) (0 : ℝ)).congr (fun s hs => by
          rw [innerSL_apply_apply, real_inner_comm]
          exact inner_skewLin_eq_zero hΩ hb (hall s hs) a b) (by
          rw [innerSL_apply_apply, real_inner_comm]
          exact inner_skewLin_eq_zero hΩ hb (hall t ht) a b)
      have := (uniqueDiffOn_Icc hT t ht).eq_deriv _ h1 h0
      rw [real_inner_comm]
      simpa using this
    have h00 := inner_curl_skewLin hΩ hb hEC 0 0
    have h11 := inner_curl_skewLin hΩ hb hEC 1 1
    rw [hX] at h00 h11
    rw [inner_constField]
    simp [Fintype.sum_prod_type, Fin.sum_univ_three, diagA] at h00 h11 ⊢
    linarith
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hd := (innerSL ℝ (constField hΩ hb diagA)).hasFDerivAt.comp_hasDerivWithinAt 0 hE
  have hd0 : HasDerivWithinAt (fun s => innerSL ℝ (constField hΩ hb diagA) (E s)) 0
      (Icc 0 T) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) (Icc 0 T) (0 : ℝ)).congr (fun s hs => by
      rw [innerSL_apply_apply, real_inner_comm]; exact hℓ s hs) (by
      rw [innerSL_apply_apply, real_inner_comm]; exact hℓ 0 h0)
  have := (uniqueDiffOn_Icc hT 0 h0).eq_deriv _ hd hd0
  exact hE' (by rw [real_inner_comm]; simpa using this)

variable {W0 W1 W2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]

/-- **The magnetic field loses symmetry (abstract criterion, Hodge wave (4.14)).** Let
`H : W0 → W1 → W2` be a Hilbert complex, `ι : W1 → L²(Ω; ℝ³ˣ³)`, `κ : W2 → L²(Ω; ℝ³ˣ³)`
continuous linear with `κ (d1 u) = curl (ι u)` in the sense of the graph closure (electric
boundary condition: `ι u ∈ H̊(curl, M)`). If `⟪ι (d1* B₀), diag(1, -1, 0)⟫ ≠ 0`, then for any
`E₀`, every strong solution of `ξ' = -L ξ` from `(0, E₀, B₀)` has `κ B(t)` non-symmetric for some
`t ∈ [0, T]`, on every `[0, T]`, `T > 0`. (`Ė(0) = -d1* B₀`, `Ḃ = d1 E`;
`exists_not_symm_of_path`.) -/
theorem not_symm_of_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (H : HilbertComplex2 W0 W1 W2) (ι : W1 →L[ℝ] L2M Ω) (κ : W2 →L[ℝ] L2M Ω)
    (hικ : ∀ u : H.d1.domain, (ι u, κ (H.d1 u)) ∈ closure (curlGraph Ω)) {E₀ : W1} {B₀ : W2}
    (hB₀ : B₀ ∈ H.d1†.domain) (hc : ⟪ι (H.d1† ⟨B₀, hB₀⟩), constField hΩ hb diagA⟫ ≠ 0) :
    ∀ T > 0, ∀ U : ℝ → Tot W0 W1 W2, IsStrongSolution (-H.waveOp) T (ini W0 E₀ B₀) 0 U →
      ∃ t ∈ Icc 0 T, κ (tot W0 W1 W2 (U t)).2.2 ∉ symL2 Ω := by
  intro T hT U hU
  let πE : Tot W0 W1 W2 →L[ℝ] W1 := (ContinuousLinearMap.fst ℝ W1 W2).comp
    ((ContinuousLinearMap.snd ℝ W0 _).comp
      (Constraints.totL (W0 := W0) (W1 := W1) (W2 := W2)).toContinuousLinearMap)
  let πB : Tot W0 W1 W2 →L[ℝ] W2 := (ContinuousLinearMap.snd ℝ W1 W2).comp
    ((ContinuousLinearMap.snd ℝ W0 _).comp
      (Constraints.totL (W0 := W0) (W1 := W1) (W2 := W2)).toContinuousLinearMap)
  have hπE : ∀ y, πE y = (tot W0 W1 W2 y).2.1 := fun y => rfl
  have hπB : ∀ y, πB y = (tot W0 W1 W2 y).2.2 := fun y => rfl
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hp0 : H.pr0 ⟨U 0, hU.mem 0 h0⟩ = 0 := Subtype.ext (by simp [hU.init])
  have hp2 : H.prV2s ⟨U 0, hU.mem 0 h0⟩ = ⟨B₀, hB₀⟩ := Subtype.ext (by simp [hU.init])
  refine exists_not_symm_of_path hΩ hb hT (E := fun t => ι (πE (U t)))
    (B := fun t => κ (πB (U t))) (E' := ι (-(H.d1† ⟨B₀, hB₀⟩))) ?_ ?_ ?_
  · refine ((ι.comp πE).hasFDerivAt.comp_hasDerivWithinAt 0 (hU.deriv 0 h0)).congr_deriv ?_
    rw [Pi.zero_apply, add_zero, LinearPMap.neg_apply, _root_.map_neg,
      ContinuousLinearMap.comp_apply,
      hπE, Constraints.tot_waveOp]
    simp only
    rw [hp0, hp2, LinearPMap.map_zero, zero_add, _root_.map_neg]
  · intro t ht
    refine ⟨κ (H.d1 (H.prV1 ⟨U t, hU.mem t ht⟩)),
      ((κ.comp πB).hasFDerivAt.comp_hasDerivWithinAt t (hU.deriv t ht)).congr_deriv ?_,
      hικ (H.prV1 ⟨U t, hU.mem t ht⟩)⟩
    rw [Pi.zero_apply, add_zero, LinearPMap.neg_apply, _root_.map_neg,
      ContinuousLinearMap.comp_apply,
      hπB, Constraints.tot_waveOp]
    simp only
    rw [_root_.map_neg, neg_neg]
  · rw [_root_.map_neg, inner_neg_left]
    exact neg_ne_zero.2 hc

/-- The reduced-system form of `not_symm_of_adjoint` ((4.15): `Ė = -d1* B`, `Ḃ = d1 E`). -/
theorem reduced_not_symm_of_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (H : HilbertComplex2 W0 W1 W2) (ι : W1 →L[ℝ] L2M Ω) (κ : W2 →L[ℝ] L2M Ω)
    (hικ : ∀ u : H.d1.domain, (ι u, κ (H.d1 u)) ∈ closure (curlGraph Ω)) {E₀ : W1} {B₀ : W2}
    (hc : ∀ hB₀ : B₀ ∈ H.d1†.domain, ⟪ι (H.d1† ⟨B₀, hB₀⟩), constField hΩ hb diagA⟫ ≠ 0)
    {T : ℝ} (hT : 0 < T) {E : ℝ → W1} {B : ℝ → W2} (hR : IsReducedSolution H T E₀ B₀ E B) :
    ∃ t ∈ Icc 0 T, κ (B t) ∉ symL2 Ω := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  obtain rfl := hR.initB
  refine exists_not_symm_of_path hΩ hb hT (E := fun t => ι (E t)) (B := fun t => κ (B t))
    (E' := ι (-(H.d1† ⟨B 0, hR.memB 0 h0⟩))) (ι.hasFDerivAt.comp_hasDerivWithinAt 0
      (hR.derivE 0 h0)) (fun t ht => ⟨_, κ.hasFDerivAt.comp_hasDerivWithinAt t (hR.derivB t ht),
      hικ ⟨E t, hR.memE t ht⟩⟩) ?_
  rw [_root_.map_neg, inner_neg_left]
  exact neg_ne_zero.2 (hc _)

/-! ## §3. Instances: the complexes of (4.14)/(4.15) (run in Ch. 7) and (4.16) -/

/-- `β`, as an element of `L²(Ω; ℝ³ˣ³)`. -/
abbrev betaL (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : L2M Ω :=
  smoothField hΩ hb betaField (fun ij => (contDiff_one_betaField ij).continuous)

/-- `curl* β = curl β = -diag(1, -1, 0)` for the thesis' complex, and
`⟪curl* β, diag(1, -1, 0)⟫ = -2|Ω|`. -/
theorem thesisComplex_adjoint_betaL (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∃ h : betaL hΩ hb ∈ (thesisComplex hΩ hb).d1†.domain,
      ⟪(thesisComplex hΩ hb).d1† ⟨_, h⟩, constField hΩ hb diagA⟫ = -(2 * volume.real Ω) := by
  obtain ⟨h, e⟩ := smoothField_mem_adjoint hΩ hb (thesisComplex hΩ hb)
    (mem_closure_curlClosure hΩ hb) contDiff_one_betaField
  refine ⟨h, ?_⟩
  rw [e, smoothField_curlM_betaField, inner_neg_left, inner_constField_diagA]

/-- **(4.14) on bounded domains: `B` loses symmetry.** For the thesis' complex
`H̊¹(V) → H̊(curl, M) → L²(M)` (the system run in Ch. 7, Table 7.1, there with plane-wave
boundary data) on any nonempty bounded
open `Ω`, from `(0, E₀, β)` with any `E₀`, every strong solution of (4.14) on `[0, T]`, `T > 0`, has
`B(t)` non-symmetric for some `t ∈ [0, T]`, although `β` is symmetric (TSD). This sharpens
`Feec.BoundedDomain.thesisComplex_not_propagate` (which only shows `(E, B) ∉ L²(TSD)²`) by naming a
constraint that is lost: the symmetry of `B`. -/
theorem thesisComplex_B_not_symm (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (E₀ : L2M Ω) :
    ∀ T > 0, ∀ U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω),
      IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) E₀ (betaL hΩ hb)) 0 U →
        ∃ t ∈ Icc 0 T, (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2 ∉ symL2 Ω := by
  obtain ⟨h, e⟩ := thesisComplex_adjoint_betaL hΩ hb
  have := not_symm_of_adjoint hΩ hb (thesisComplex hΩ hb) (ContinuousLinearMap.id ℝ _)
    (ContinuousLinearMap.id ℝ _) (mem_closure_curlClosure hΩ hb) (E₀ := E₀) h (by
      rw [ContinuousLinearMap.id_apply, e]
      have := volume_real_pos hΩ hb hne
      linarith)
  simpa using this

/-- **(4.15) on bounded domains: `B` loses symmetry.** The reduced system `Ė = -curl* B`,
`Ḃ = curl E` (Ch. 7, Table 7.2) for the thesis' complex, from `(E₀, β)`, any `E₀`: every strong
solution has `B(t)` non-symmetric for some `t ∈ [0, T]`, `T > 0`. -/
theorem thesisComplex_reduced_B_not_symm (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (E₀ : L2M Ω) {T : ℝ} (hT : 0 < T) {E B : ℝ → L2M Ω}
    (hR : IsReducedSolution (thesisComplex hΩ hb) T E₀ (betaL hΩ hb) E B) :
    ∃ t ∈ Icc 0 T, B t ∉ symL2 Ω := by
  obtain ⟨h, e⟩ := thesisComplex_adjoint_betaL hΩ hb
  have := reduced_not_symm_of_adjoint hΩ hb (thesisComplex hΩ hb) (ContinuousLinearMap.id ℝ _)
    (ContinuousLinearMap.id ℝ _) (mem_closure_curlClosure hΩ hb) (fun h' => by
      rw [ContinuousLinearMap.id_apply, show (⟨_, h'⟩ : (thesisComplex hΩ hb).d1†.domain) =
        ⟨_, h⟩ from rfl, e]
      have := volume_real_pos hΩ hb hne
      linarith) hT hR
  simpa using this

/-- **(4.18) on bounded domains: `B ∈ L²(T)` loses symmetry.** For the strong-symmetry complex
(4.16) `H̊²(R) → H̊(curl, S) → L²(T)` (Prop 4.19), from `(0, E₀, β)`, any `E₀ ∈ L²(S)`: every
strong solution has `B(t)` non-symmetric for some `t ∈ [0, T]`, `T > 0`. -/
theorem symComplexB_B_not_symm (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (E₀ : L2S Ω) :
    ∀ T > 0, ∀ U : ℝ → Tot (L2 Ω) (L2S Ω) (L2T Ω),
      IsStrongSolution (-(symComplexB hΩ hb).waveOp) T (ini (L2 Ω) E₀ (betaT hΩ hb)) 0 U →
        ∃ t ∈ Icc 0 T, ((tot (L2 Ω) (L2S Ω) (L2T Ω) (U t)).2.2 : L2M Ω) ∉ symL2 Ω := by
  obtain ⟨h, -⟩ := betaT_mem_adjoint hΩ hb
  have := not_symm_of_adjoint hΩ hb (symComplexB hΩ hb) (symL2 Ω).subtypeL (trL2 Ω).subtypeL
    (mem_closure_curlGraph_curlS hΩ hb) (E₀ := E₀) h (by
      rw [inner_adjoint_betaT_constField hΩ hb h]
      have := volume_real_pos hΩ hb hne
      linarith)
  simpa using this

/-! ## §4. The complex (5.1) of Ch. 5–6 on a bounded domain -/

/-- The BGG map `S₁ : L²(Ω; ℝ³ˣ³) → L²(Ω; ℝ³)`, `(S₁ u)_i = u_{i+1,i+2} - u_{i+2,i+1}`, i.e.
`S₁ = 2 vskw` (the normalization for which `d S₀ = -S₁ d` holds with `S₀ = I`; see
`Feec.vskw`). Only its kernel (the symmetric fields) matters below. -/
def skwL : L2M Ω →L[ℝ] L2V Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => L2 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      PiLp.proj (𝕜 := ℝ) 2 (fun _ : Ix => L2 Ω) (i + 1, i + 2) -
        PiLp.proj (𝕜 := ℝ) 2 (fun _ : Ix => L2 Ω) (i + 2, i + 1))

theorem skwL_apply (u : L2M Ω) (i : Fin 3) : skwL u i = u (i + 1, i + 2) - u (i + 2, i + 1) :=
  rfl

/-- `S₁` vanishes on symmetric fields. -/
theorem skwL_eq_zero_of_mem_symL2 {u : L2M Ω} (hu : u ∈ symL2 Ω) : skwL u = 0 :=
  PiLp.ext fun i => by rw [skwL_apply, hu (i + 1) (i + 2), sub_self]; rfl

variable (Ω) in
/-- The top space `W² × W̃² = L²(Ω; ℝ³) × L²(Ω; ℝ³ˣ³)` of the complex (5.1) (`ℓ²` product). -/
abbrev W2B := WithLp 2 (L2V Ω × L2M Ω)

/-- The second operator of the complex (5.1), `u ↦ (S₁ u, curl u)` on `H̊(curl, M)`. -/
def skwCurl : L2M Ω →ₗ.[ℝ] W2B Ω where
  domain := (curlClosure (Ω := Ω)).domain
  toFun := (WithLp.linearEquiv 2 ℝ (L2V Ω × L2M Ω)).symm.toLinearMap ∘ₗ
    (((skwL (Ω := Ω)).toLinearMap ∘ₗ (curlClosure (Ω := Ω)).domain.subtype).prod
      (curlClosure (Ω := Ω)).toFun)

theorem skwCurl_apply (u : (skwCurl (Ω := Ω)).domain) :
    skwCurl u = WithLp.toLp 2 (skwL (u : L2M Ω),
      curlClosure (⟨u.1, u.2⟩ : (curlClosure (Ω := Ω)).domain)) := rfl

theorem skwCurl_fst (u : (skwCurl (Ω := Ω)).domain) :
    (WithLp.ofLp (skwCurl u)).1 = skwL (u : L2M Ω) := rfl

theorem skwCurl_snd (u : (skwCurl (Ω := Ω)).domain) :
    (WithLp.ofLp (skwCurl u)).2 = curlClosure (⟨u.1, u.2⟩ : (curlClosure (Ω := Ω)).domain) := rfl

/-- The graph of `skwCurl`: `(u, (m, c))` with `(u, c)` in the graph of curl and `m = S₁ u`. -/
theorem mem_graph_skwCurl {p : L2M Ω × W2B Ω} : p ∈ (skwCurl (Ω := Ω)).graph ↔
    (p.1, (WithLp.ofLp p.2).2) ∈ (curlClosure (Ω := Ω)).graph ∧
      (WithLp.ofLp p.2).1 = skwL p.1 := by
  rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨y, hy1, hy2⟩
    refine ⟨⟨⟨y.1, y.2⟩, hy1, ?_⟩, ?_⟩
    · rw [← hy2]; rfl
    · rw [← hy2, ← hy1]; rfl
  · rintro ⟨⟨y, hy1, hy2⟩, h⟩
    refine ⟨⟨y.1, y.2⟩, hy1, ?_⟩
    apply WithLp.ofLp_injective
    refine Prod.ext ?_ ?_
    · rw [h, ← hy1]; rfl
    · rw [← hy2]; rfl

/-- `skwCurl` is closed. -/
theorem isClosed_skwCurl (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (skwCurl (Ω := Ω)).IsClosed := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ (L2V Ω) (L2M Ω)
  have he : ∀ w : W2B Ω, e w = WithLp.ofLp w := fun _ => rfl
  have hg : ((skwCurl (Ω := Ω)).graph : Set (L2M Ω × W2B Ω)) =
      (fun p : L2M Ω × W2B Ω => (p.1, (e p.2).2)) ⁻¹' ((curlClosure (Ω := Ω)).graph : Set _) ∩
        {p | (e p.2).1 = skwL p.1} := by
    ext p
    simp only [SetLike.mem_coe, mem_inter_iff, mem_preimage, mem_ofPred_eq, he]
    exact mem_graph_skwCurl
  rw [LinearPMap.IsClosed, hg]
  refine IsClosed.inter (IsClosed.preimage ?_ (isClosed_curlClosure hΩ hb)) (isClosed_eq ?_ ?_)
  · exact continuous_fst.prodMk (continuous_snd.comp (e.continuous.comp continuous_snd))
  · exact continuous_fst.comp (e.continuous.comp continuous_snd)
  · exact skwL.continuous.comp continuous_fst

theorem hessGraph_closable (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∀ x ∈ (hessGraphSub Ω).topologicalClosure, x.1 = 0 → x.2 = 0 := by
  rintro ⟨u, w⟩ hx (h0 : u = 0)
  subst h0
  refine eq_zero_of_forall_integral hΩ hb fun Ψ hΨ => ?_
  rw [closure_hessGraph_identity hΩ hb hx fun ij => (hΨ ij).contDiff.of_le (by simp),
    integral_mul_eq_inner _ (memLp_of_continuous hΩ hb (continuous_divdivF fun ij =>
      (hΨ ij).contDiff.of_le (by simp))), inner_zero_left]

/-- The first operator of the complex (5.1), `grad grad : H̊²(Ω) → L²(Ω; ℝ³ˣ³)`, the closure of
the Hessian on `C_c^∞(Ω)`; under `(σ, φ) ↦ σ` it is the thesis' `(0 d) : Γ → Ṽ¹`,
`(σ, grad σ) ↦ grad grad σ` (see the module docstring for the identification of `Γ`). -/
def hessM : L2 Ω →ₗ.[ℝ] L2M Ω := (hessGraphSub Ω).topologicalClosure.toLinearPMap

theorem hessM_graph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (hessM (Ω := Ω)).graph = (hessGraphSub Ω).topologicalClosure :=
  Submodule.toLinearPMap_graph_eq _ (hessGraph_closable hΩ hb)

theorem isClosed_hessM (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (hessM (Ω := Ω)).IsClosed := by
  rw [LinearPMap.IsClosed, hessM_graph hΩ hb]
  exact Submodule.isClosed_topologicalClosure _

theorem mem_closure_hessM (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (hessM (Ω := Ω)).domain) :
    ((u : L2 Ω), hessM u) ∈ (hessGraphSub Ω).topologicalClosure :=
  Submodule.mem_graph_toLinearPMap (hessGraph_closable hΩ hb) u

theorem testFieldR_mem_graph_hessM (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {φ : R3 → ℝ}
    (hφ : IsTest Ω φ) :
    (testFieldR hφ, (hessTestField hΩ hb hφ : L2M Ω)) ∈ (hessM (Ω := Ω)).graph := by
  rw [hessM_graph hΩ hb]
  exact subset_closure (Submodule.subset_span ⟨φ, hφ, hφ.memLp.coeFn_toLp,
    coeFn_smoothField hΩ hb (hessField φ) (fun ij => (isTest_hessField hφ ij).continuous)⟩)

theorem testFieldR_mem_domain_hessM (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {φ : R3 → ℝ} (hφ : IsTest Ω φ) : testFieldR hφ ∈ (hessM (Ω := Ω)).domain := by
  obtain ⟨y, hy, -⟩ := (LinearPMap.mem_graph_iff _).1 (testFieldR_mem_graph_hessM hΩ hb hφ)
  have e : (y : L2 Ω) = testFieldR hφ := hy
  exact e ▸ y.2

theorem hessM_testFieldR (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {φ : R3 → ℝ}
    (hφ : IsTest Ω φ) :
    hessM ⟨testFieldR hφ, testFieldR_mem_domain_hessM hΩ hb hφ⟩ = hessTestField hΩ hb hφ :=
  apply_eq_of_mem_graph (testFieldR_mem_graph_hessM hΩ hb hφ) _

theorem dense_domain_hessM (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    Dense ((hessM (Ω := Ω)).domain : Set (L2 Ω)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro v hv
  refine L2_ext_of_integral hΩ hb fun g hg => ?_
  have h0 := (Submodule.mem_orthogonal' _ _).1 hv _ (testFieldR_mem_domain_hessM hΩ hb hg)
  rw [integral_mul_eq_inner _ hg.memLp, integral_mul_eq_inner _ hg.memLp, inner_zero_left]
  exact h0

/-- `grad grad H̊²` consists of symmetric fields. -/
theorem hessM_mem_symL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (hessM (Ω := Ω)).domain) : hessM u ∈ symL2 Ω := by
  have hle : hessGraphSub Ω ≤ (symL2 Ω).comap (LinearMap.snd ℝ (L2 Ω) (L2M Ω)) := by
    refine Submodule.span_le.2 ?_
    rintro ⟨v, H⟩ ⟨φ, hφ, -, hp2⟩ i j
    refine Lp.ext ?_
    filter_upwards [hp2 (i, j), hp2 (j, i)] with x h1 h2
    simp only [LinearMap.snd_apply]
    rw [h1, h2, hessField_swap (hφ.contDiff.of_le (by simp))]
  have hcl : IsClosed (((symL2 Ω).comap (LinearMap.snd ℝ (L2 Ω) (L2M Ω)) :
      Submodule ℝ (L2 Ω × L2M Ω)) : Set (L2 Ω × L2M Ω)) :=
    isClosed_symL2.preimage continuous_snd
  exact Submodule.topologicalClosure_minimal _ hle hcl (mem_closure_hessM hΩ hb u)

/-- `grad grad H̊² ⊆ H̊(curl, M)` with `curl grad grad = 0`. -/
theorem hessM_mem_closure_curlGraph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (hessM (Ω := Ω)).domain) : (hessM u, (0 : L2M Ω)) ∈ closure (curlGraph Ω) := by
  let f : L2 Ω × L2M Ω →L[ℝ] L2M Ω × L2M Ω := (ContinuousLinearMap.snd ℝ (L2 Ω) (L2M Ω)).prod 0
  have hle : hessGraphSub Ω ≤ (curlGraphSub Ω).comap (f : L2 Ω × L2M Ω →ₗ[ℝ] _) := by
    refine Submodule.span_le.2 ?_
    rintro ⟨v, H⟩ ⟨φ, hφ, -, hp2⟩
    refine ⟨hessField φ, isTest_hessField hφ, fun ij => ⟨hp2 ij, ?_⟩⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x hx
    simp only [f]
    rw [curlM_hessField hφ]
    simpa using hx
  have h := mem_closure_hessM hΩ hb u
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at h
  have := map_mem_closure f.continuous h (t := (curlGraphSub Ω : Set (L2M Ω × L2M Ω)))
    fun p hp => hle hp
  exact (by simpa [f] using this :
    (hessM u, (0 : L2M Ω)) ∈ closure ((curlGraphSub Ω : Set (L2M Ω × L2M Ω))))

theorem hessM_mem_domain_skwCurl (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (hessM (Ω := Ω)).domain) : hessM u ∈ (skwCurl (Ω := Ω)).domain :=
  mem_domain_curlClosure.2 ⟨0, hessM_mem_closure_curlGraph hΩ hb u⟩

/-- **The complex (5.1) of the Ch. 6 EB application on a bounded open `Ω ⊆ ℝ³`**:
`L²(Ω) ⊇ H̊²(Ω) --grad grad--> H̊(curl, Ω; ℝ³ˣ³) --(S₁, curl)--> L²(Ω; ℝ³) × L²(Ω; ℝ³ˣ³)`. -/
def bggComplex (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    HilbertComplex2 (L2 Ω) (L2M Ω) (W2B Ω) where
  d0 := hessM
  d1 := skwCurl
  dense0 := dense_domain_hessM hΩ hb
  dense1 := dense_domain_curlClosure hΩ hb
  closed0 := isClosed_hessM hΩ hb
  closed1 := isClosed_skwCurl hΩ hb
  map_mem := hessM_mem_domain_skwCurl hΩ hb
  comp_zero := fun u => by
    rw [skwCurl_apply]
    have h1 : skwL (hessM u) = 0 := skwL_eq_zero_of_mem_symL2 (hessM_mem_symL2 hΩ hb u)
    have h2 : curlClosure (⟨hessM u, hessM_mem_domain_skwCurl hΩ hb u⟩ :
        (curlClosure (Ω := Ω)).domain) = 0 :=
      apply_eq_of_mem_graph (by
        rw [curlClosure_graph hΩ hb]; exact hessM_mem_closure_curlGraph hΩ hb u) _
    simp only [h1]
    rw [h2]
    rfl

@[simp] theorem bggComplex_d0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (bggComplex hΩ hb).d0 = hessM := rfl

@[simp] theorem bggComplex_d1 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (bggComplex hΩ hb).d1 = skwCurl := rfl

/-- **`d1*` on smooth magnetic data**: for `m ∈ L²(Ω; ℝ³)` and a `C¹` field `Ψ` with no boundary
condition, `(m, Ψ) ∈ D(d1*)` and `d1* (m, Ψ) = S₁* m + curl Ψ`. -/
theorem smoothPair_mem_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (m : L2V Ω)
    {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) :
    ∃ h : WithLp.toLp 2 (m, smoothField hΩ hb Ψ fun ij => (hΨ ij).continuous) ∈
        (bggComplex hΩ hb).d1†.domain,
      (bggComplex hΩ hb).d1† ⟨_, h⟩ =
        ContinuousLinearMap.adjoint skwL m + smoothField hΩ hb (curlM Ψ) (continuous_curlM hΨ) := by
  have key : ∀ u : (bggComplex hΩ hb).d1.domain,
      ⟪ContinuousLinearMap.adjoint skwL m + smoothField hΩ hb (curlM Ψ) (continuous_curlM hΨ),
        (u : L2M Ω)⟫ = ⟪WithLp.toLp 2 (m, smoothField hΩ hb Ψ fun ij => (hΨ ij).continuous),
          (bggComplex hΩ hb).d1 u⟫ := fun u => by
    have hu : (bggComplex hΩ hb).d1 u = WithLp.toLp 2 (skwL (u : L2M Ω),
        curlClosure (⟨u.1, u.2⟩ : (curlClosure (Ω := Ω)).domain)) := rfl
    rw [hu, WithLp.prod_inner_apply, inner_add_left,
      ContinuousLinearMap.adjoint_inner_left]
    congr 1
    rw [real_inner_comm (u : L2M Ω), real_inner_comm (curlClosure _), inner_smoothField,
      inner_smoothField]
    exact (closure_curlGraph_identity hΩ hb (mem_closure_curlClosure hΩ hb ⟨u.1, u.2⟩) hΨ).symm
  have hmem := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq (bggComplex hΩ hb).dense1 ⟨_, hmem⟩ key⟩

/-- `(grad grad)* ⊇ div div` weakly on `L²(Ω; ℝ³ˣ³)`: if `Σ_{ij} ∫ B_{ij} ∂_i ∂_j φ = ∫ D φ` for
all `φ ∈ C_c^∞(Ω)`, then `B ∈ D(hessM*)` and `hessM* B = D`. -/
theorem adjoint_hessM_of_weak (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2M Ω}
    {D : L2 Ω} (hD : ∀ φ : R3 → ℝ, IsTest Ω φ →
      ∑ ij, ∫ x, B ij x * hessField φ ij x ∂volume.restrict Ω =
        ∫ x, D x * φ x ∂volume.restrict Ω) :
    ∃ h : B ∈ (hessM (Ω := Ω))†.domain, (hessM (Ω := Ω))† ⟨B, h⟩ = D := by
  have key : ∀ u : (hessM (Ω := Ω)).domain, ⟪D, (u : L2 Ω)⟫ = ⟪B, hessM u⟫ := by
    intro u
    let G : L2 Ω × L2M Ω →L[ℝ] ℝ := (innerSL ℝ B).comp (ContinuousLinearMap.snd ℝ _ _) -
      (innerSL ℝ D).comp (ContinuousLinearMap.fst ℝ _ _)
    have hG : ∀ p : L2 Ω × L2M Ω, G p = ⟪B, p.2⟫ - ⟪D, p.1⟫ := fun p => rfl
    have hsub : hessGraphSub Ω ≤ LinearMap.ker (G : L2 Ω × L2M Ω →ₗ[ℝ] ℝ) := by
      refine Submodule.span_le.2 ?_
      rintro ⟨v, H⟩ ⟨φ, hφ, hp1, hp2⟩
      have ev : v = testFieldR hφ := Lp.ext (hp1.trans hφ.memLp.coeFn_toLp.symm)
      have eH : H = smoothField hΩ hb (hessField φ)
          (fun ij => (isTest_hessField hφ ij).continuous) :=
        (WithLp.ext_iff 2).2 (funext fun ij =>
          Lp.ext ((hp2 ij).trans (coeFn_smoothField hΩ hb _ _ ij).symm))
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hG, ev, eH,
        sub_eq_zero]
      rw [inner_smoothField, inner_testFieldR, hD φ hφ]
    have h := Submodule.topologicalClosure_minimal _ hsub G.isClosed_ker (mem_closure_hessM hΩ hb u)
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hG, sub_eq_zero] at h
    exact h.symm
  have hmem := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq (dense_domain_hessM hΩ hb) ⟨_, hmem⟩ key⟩

/-- `ker (grad grad)* = H(div div, M, 0)`: fields with `div div B = 0` weakly
(`Σ_{ij} ∫ B_{ij} ∂_i ∂_j φ = 0` for all `φ ∈ C_c^∞(Ω)`; no boundary condition). -/
theorem mem_ker_adjoint_hessM_iff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2M Ω} :
    B ∈ (hessM (Ω := Ω))†.ker ↔ ∀ φ : R3 → ℝ, IsTest Ω φ →
      ∑ ij, ∫ x, B ij x * hessField φ ij x ∂volume.restrict Ω = 0 := by
  constructor
  · intro hB φ hφ
    obtain ⟨y, rfl, hy0⟩ := LinearPMap.mem_ker_iff.1 hB
    have e := LinearPMap.adjoint_isFormalAdjoint (dense_domain_hessM hΩ hb) y
      ⟨_, testFieldR_mem_domain_hessM hΩ hb hφ⟩
    simp only at e
    rw [hessM_testFieldR hΩ hb hφ, hessTestField, inner_smoothField, hy0, inner_zero_left] at e
    exact e.symm
  · intro hB
    obtain ⟨h, h'⟩ := adjoint_hessM_of_weak hΩ hb (D := 0) fun φ hφ => by
      rw [hB φ hφ, integral_mul_eq_inner _ hφ.memLp, inner_zero_left]
    exact LinearPMap.mem_ker_iff.2 ⟨⟨B, h⟩, rfl, h'⟩

/-- `L²(TSD) ⊆ ker (grad grad)*` (row-wise divergence-free fields have `div div = 0`). -/
theorem TSD_le_ker_bgg (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    TSD Ω ≤ (bggComplex hΩ hb).d0†.ker := fun _ hB =>
  (mem_ker_adjoint_hessM_iff hΩ hb).2 fun φ hφ =>
    hB.2.2 (fun i => BoundedDomain.pd i φ) fun i => hφ.pdiff i

/-! ## §5. The continuous Ch. 6 problem (6.1) on a bounded domain -/

/-- **Weak equations of a strong Hodge wave solution** (any Hilbert complex): writing
`U(t) = (σ, u, ρ)`, at each `t ∈ [0, T]` the derivative is `U̇(t) = (σ̇, u̇, ρ̇)` with
`(σ̇, τ) = (u, d0 τ)` for `τ ∈ V⁰`, `(u̇, v) + (d0 σ, v) + (ρ, d1 v) = 0` for `v ∈ V¹`, and
`ρ̇ = d1 u`. -/
theorem hodgeWave_weak_eqs (H : HilbertComplex2 W0 W1 W2) {T : ℝ} {U₀ : Tot W0 W1 W2}
    {U : ℝ → Tot W0 W1 W2} (hU : IsStrongSolution (-H.waveOp) T U₀ 0 U) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ∃ (hσ : (tot W0 W1 W2 (U t)).1 ∈ H.d0.domain) (hu : (tot W0 W1 W2 (U t)).2.1 ∈ H.d1.domain)
      (σ' : W0) (u' : W1) (ρ' : W2),
      HasDerivWithinAt U ((tot W0 W1 W2).symm (σ', u', ρ')) (Icc 0 T) t ∧
      (∀ τ : H.d0.domain, ⟪σ', (τ : W0)⟫ = ⟪(tot W0 W1 W2 (U t)).2.1, H.d0 τ⟫) ∧
      (∀ v : H.d1.domain, ⟪u', (v : W1)⟫ + ⟪H.d0 ⟨_, hσ⟩, (v : W1)⟫ +
        ⟪(tot W0 W1 W2 (U t)).2.2, H.d1 v⟫ = 0) ∧
      ρ' = H.d1 ⟨_, hu⟩ := by
  have hD := (Feec.Constraints.mem_domL H).1 (hU.mem t ht)
  refine ⟨hD.1, (Submodule.mem_inf.1 hD.2.1).1, H.d0† (H.prV1s ⟨U t, hU.mem t ht⟩),
    -(H.d0 (H.pr0 ⟨U t, hU.mem t ht⟩) + H.d1† (H.prV2s ⟨U t, hU.mem t ht⟩)),
    H.d1 (H.prV1 ⟨U t, hU.mem t ht⟩), ?_, ?_, ?_, rfl⟩
  · refine (hU.deriv t ht).congr_deriv ?_
    rw [Pi.zero_apply, add_zero, LinearPMap.neg_apply]
    apply (tot W0 W1 W2).injective
    rw [_root_.map_neg, Constraints.tot_waveOp, LinearEquiv.apply_symm_apply]
    simp
  · intro τ
    exact LinearPMap.adjoint_isFormalAdjoint H.dense0 _ τ
  · intro v
    have e := LinearPMap.adjoint_isFormalAdjoint H.dense1 (H.prV2s ⟨U t, hU.mem t ht⟩) v
    rw [Constraints.coe_prV2s] at e
    rw [inner_neg_left, inner_add_left, e]
    have : H.d0 (H.pr0 ⟨U t, hU.mem t ht⟩) = H.d0 ⟨_, hD.1⟩ := rfl
    rw [this]
    ring

/-- **A strong solution of the Hodge wave equation of (5.1) solves (6.1)** (with `f = 0`). Writing
`U(t) = (σ, u, (M, B))` and `U̇(t) = (σ̇, u̇, (Ṁ, Ḃ))`, at every `t ∈ [0, T]`:
`(σ̇, τ) - (u, grad grad τ) = 0` for `τ ∈ H̊²` (6.1a, with `(τ, ψ) = (τ, grad τ) ∈ Γ`);
`(u̇, v) + (grad grad σ, v) + (M, S₁ v) + (B, curl v) = 0` for `v ∈ H̊(curl, M)` (6.1b);
`Ṁ = S₁ u` (6.1c) and `Ḃ = curl u` (6.1d). -/
theorem bggComplex_eq61 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {T : ℝ}
    {U₀ : Tot (L2 Ω) (L2M Ω) (W2B Ω)} {U : ℝ → Tot (L2 Ω) (L2M Ω) (W2B Ω)}
    (hU : IsStrongSolution (-(bggComplex hΩ hb).waveOp) T U₀ 0 U) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∃ (hσ : (tot (L2 Ω) (L2M Ω) (W2B Ω) (U t)).1 ∈ (hessM (Ω := Ω)).domain)
      (hu : (tot (L2 Ω) (L2M Ω) (W2B Ω) (U t)).2.1 ∈ (curlClosure (Ω := Ω)).domain)
      (σ' : L2 Ω) (u' : L2M Ω) (ρ' : W2B Ω),
      HasDerivWithinAt U ((tot (L2 Ω) (L2M Ω) (W2B Ω)).symm (σ', u', ρ')) (Icc 0 T) t ∧
      (∀ τ : (hessM (Ω := Ω)).domain,
        ⟪σ', (τ : L2 Ω)⟫ - ⟪(tot (L2 Ω) (L2M Ω) (W2B Ω) (U t)).2.1, hessM τ⟫ = 0) ∧
      (∀ v : (curlClosure (Ω := Ω)).domain,
        ⟪u', (v : L2M Ω)⟫ + ⟪hessM ⟨_, hσ⟩, (v : L2M Ω)⟫ +
          ⟪(WithLp.ofLp (tot (L2 Ω) (L2M Ω) (W2B Ω) (U t)).2.2).1, skwL (v : L2M Ω)⟫ +
          ⟪(WithLp.ofLp (tot (L2 Ω) (L2M Ω) (W2B Ω) (U t)).2.2).2, curlClosure v⟫ = 0) ∧
      (WithLp.ofLp ρ').1 = skwL (tot (L2 Ω) (L2M Ω) (W2B Ω) (U t)).2.1 ∧
      (WithLp.ofLp ρ').2 = curlClosure ⟨_, hu⟩ := by
  obtain ⟨hσ, hu, σ', u', ρ', hd, ha, hb', hc⟩ := hodgeWave_weak_eqs (bggComplex hΩ hb) hU ht
  refine ⟨hσ, hu, σ', u', ρ', hd, fun τ => sub_eq_zero.2 (ha τ), fun v => ?_, ?_, ?_⟩
  · have := hb' ⟨v.1, v.2⟩
    have e2 : ⟪(tot (L2 Ω) (L2M Ω) (W2B Ω) (U t)).2.2, (bggComplex hΩ hb).d1 ⟨v.1, v.2⟩⟫ =
        ⟪(WithLp.ofLp (tot (L2 Ω) (L2M Ω) (W2B Ω) (U t)).2.2).1, skwL (v : L2M Ω)⟫ +
          ⟪(WithLp.ofLp (tot (L2 Ω) (L2M Ω) (W2B Ω) (U t)).2.2).2, curlClosure v⟫ := rfl
    have e3 : ⟪(bggComplex hΩ hb).d0 ⟨_, hσ⟩, (v : L2M Ω)⟫ =
        ⟪hessM ⟨_, hσ⟩, (v : L2M Ω)⟫ := rfl
    rw [e2] at this
    erw [e3] at this
    linarith
  · rw [hc]; rfl
  · rw [hc]; rfl

/-! ## §6. Ch. 6 on a bounded domain: TSD and the symmetry of `B` are not propagated -/

/-- The magnetic datum `(M₀, B₀) = (m, β)` of the Ch. 6 system. -/
abbrev betaPair (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (m : L2V Ω) : W2B Ω :=
  WithLp.toLp 2 (m, betaL hΩ hb)

/-- `(m, β) ∈ D(d1*)` and `⟪d1* (m, β), diag(1, -1, 0)⟫ = -2|Ω|`, for every `m`
(`d1* (m, β) = S₁* m + curl β`, and `S₁* m ⊥` symmetric fields). -/
theorem bggComplex_adjoint_betaPair (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (m : L2V Ω) :
    ∃ h : betaPair hΩ hb m ∈ (bggComplex hΩ hb).d1†.domain,
      ⟪(bggComplex hΩ hb).d1† ⟨_, h⟩, constField hΩ hb diagA⟫ = -(2 * volume.real Ω) := by
  obtain ⟨h, e⟩ := smoothPair_mem_adjoint hΩ hb m contDiff_one_betaField
  refine ⟨h, ?_⟩
  rw [e, smoothField_curlM_betaField, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
    skwL_eq_zero_of_mem_symL2 (constField_diagA_mem_symL2 hΩ hb), inner_zero_right, zero_add,
    inner_neg_left, inner_constField_diagA]

/-- `S₂ = {0} × L²(TSD) ⊆ L²(Ω; ℝ³) × L²(Ω; ℝ³ˣ³)`: vanishing multiplier `M`, TSD magnetic field. -/
def TSDB (Ω : Set R3) : Submodule ℝ (W2B Ω) :=
  ((⊥ : Submodule ℝ (L2V Ω)).prod (TSD Ω)).comap
    (WithLp.linearEquiv 2 ℝ (L2V Ω × L2M Ω)).toLinearMap

theorem mem_TSDB {w : W2B Ω} : w ∈ TSDB Ω ↔ (WithLp.ofLp w).1 = 0 ∧ (WithLp.ofLp w).2 ∈ TSD Ω := by
  simp [TSDB, Submodule.mem_prod]

/-- The projection `(M, B) ↦ B`. -/
def sndB : W2B Ω →L[ℝ] L2M Ω :=
  (ContinuousLinearMap.snd ℝ (L2V Ω) (L2M Ω)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ (L2V Ω) (L2M Ω)).toContinuousLinearMap

theorem sndB_apply (w : W2B Ω) : sndB w = (WithLp.ofLp w).2 := rfl

/-- The hypothesis on `d1` used in this section: `d1 u = (S₁ u, curl u)` with `u ∈ H̊(curl, M)`
(in the sense of the graph closure of curl on `C_c^∞`). It holds for `bggComplex` (whose `d0` is
`grad grad` on `H̊²`) and for every Hilbert complex `W0 → L²(Ω; ℝ³ˣ³) → W² × W̃²` with this second
operator, whatever the first operator (e.g. the thesis' `Γ` with its own domain). -/
def IsSkwCurl (H : HilbertComplex2 W0 (L2M Ω) (W2B Ω)) : Prop :=
  ∀ u : H.d1.domain, ((u : L2M Ω), (WithLp.ofLp (H.d1 u)).2) ∈ closure (curlGraph Ω) ∧
    (WithLp.ofLp (H.d1 u)).1 = skwL (u : L2M Ω)

theorem bggComplex_isSkwCurl (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    IsSkwCurl (bggComplex hΩ hb) := fun u => ⟨mem_closure_curlClosure hΩ hb ⟨u.1, u.2⟩, rfl⟩

/-- For any complex with `IsSkwCurl`: `(m, β) ∈ D(d1*)`, `d1* (m, β) = S₁* m + curl β`, and
`⟪d1* (m, β), diag(1, -1, 0)⟫ = -2|Ω|`. -/
theorem adjoint_betaPair_of_isSkwCurl (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (H : HilbertComplex2 W0 (L2M Ω) (W2B Ω)) (hH : IsSkwCurl H) (m : L2V Ω) :
    ∃ h : betaPair hΩ hb m ∈ H.d1†.domain,
      H.d1† ⟨_, h⟩ = ContinuousLinearMap.adjoint skwL m - constField hΩ hb diagA ∧
      ⟪H.d1† ⟨_, h⟩, constField hΩ hb diagA⟫ = -(2 * volume.real Ω) := by
  have hβ := contDiff_one_betaField
  have key : ∀ u : H.d1.domain,
      ⟪ContinuousLinearMap.adjoint skwL m - constField hΩ hb diagA, (u : L2M Ω)⟫ =
        ⟪betaPair hΩ hb m, H.d1 u⟫ := fun u => by
    rw [WithLp.prod_inner_apply, sub_eq_add_neg, inner_add_left,
      ContinuousLinearMap.adjoint_inner_left, (hH u).2, ← smoothField_curlM_betaField hΩ hb]
    congr 1
    rw [real_inner_comm (u : L2M Ω), WithLp.ofLp_toLp, real_inner_comm (WithLp.ofLp (H.d1 u)).2,
      inner_smoothField, inner_smoothField]
    exact (closure_curlGraph_identity hΩ hb (hH u).1 hβ).symm
  have hmem := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  have e := LinearPMap.adjoint_apply_eq H.dense1 ⟨_, hmem⟩ key
  refine ⟨hmem, e, ?_⟩
  rw [e, inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    skwL_eq_zero_of_mem_symL2 (constField_diagA_mem_symL2 hΩ hb), inner_zero_right, zero_sub,
    inner_constField_diagA]

/-- **`B` loses symmetry, for every complex with second operator `(S₁, curl)` on `H̊(curl, M)`**
(any first operator). From `(0, E₀, (m, β))`, any `E₀`, `m`: every strong solution of the Hodge
wave equation on `[0, T]`, `T > 0`, has `B(t)` non-symmetric for some `t ∈ [0, T]`. -/
theorem B_not_symm_of_isSkwCurl (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (H : HilbertComplex2 W0 (L2M Ω) (W2B Ω)) (hH : IsSkwCurl H)
    (E₀ : L2M Ω) (m : L2V Ω) :
    ∀ T > 0, ∀ U : ℝ → Tot W0 (L2M Ω) (W2B Ω),
      IsStrongSolution (-H.waveOp) T (ini W0 E₀ (betaPair hΩ hb m)) 0 U →
        ∃ t ∈ Icc 0 T, (WithLp.ofLp (tot W0 (L2M Ω) (W2B Ω) (U t)).2.2).2 ∉ symL2 Ω := by
  obtain ⟨h, -, e⟩ := adjoint_betaPair_of_isSkwCurl hΩ hb H hH m
  have := not_symm_of_adjoint hΩ hb H (ContinuousLinearMap.id ℝ _) sndB
    (fun u => (hH u).1) (E₀ := E₀) h (by
      rw [ContinuousLinearMap.id_apply, e]
      have := volume_real_pos hΩ hb hne
      linarith)
  simpa [sndB_apply] using this

/-- **`u` leaves `L²(TSD)`, for every complex with second operator `(S₁, curl)` on
`H̊(curl, M)`.** From `(0, E₀, (m, β))`: every strong solution leaves `{0} × L²(TSD) × S2` on
every `[0, T]`, `T > 0`, for every `S2`. -/
theorem not_propagate_of_isSkwCurl (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (H : HilbertComplex2 W0 (L2M Ω) (W2B Ω)) (hH : IsSkwCurl H)
    (E₀ : L2M Ω) (m : L2V Ω) (S2 : Submodule ℝ (W2B Ω)) :
    ∀ T > 0, ∀ U : ℝ → Tot W0 (L2M Ω) (W2B Ω),
      IsStrongSolution (-H.waveOp) T (ini W0 E₀ (betaPair hΩ hb m)) 0 U →
        ∃ t ∈ Icc 0 T, U t ∉ Kc W0 (TSD Ω) S2 := by
  obtain ⟨h, -, e⟩ := adjoint_betaPair_of_isSkwCurl hΩ hb H hH m
  refine not_propagate_of_adjoint hΩ hb H (ContinuousLinearMap.id ℝ _)
    (fun u hu => ⟨_, (hH ⟨u, hu⟩).1⟩) (S1 := TSD Ω) (S2 := S2) (fun u hu => hu)
    (E₀ := E₀) h (constField_mem_orth hΩ hb diagA) ?_
  rw [ContinuousLinearMap.id_apply, e]
  have := volume_real_pos hΩ hb hne
  linarith

/-- **Ch. 6 on bounded domains: `B` loses symmetry.** For the BGG complex (5.1) on any nonempty
bounded open `Ω`, from `(σ, u, (M, B))(0) = (0, E₀, (m, β))` with any `E₀`, `m`: every strong
solution of the Hodge wave equation (equivalently of (6.1), `bggComplex_eq61`) on `[0, T]`,
`T > 0`, has `B(t)` non-symmetric for some `t ∈ [0, T]`, although `β` is symmetric. -/
theorem bggComplex_B_not_symm (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (E₀ : L2M Ω) (m : L2V Ω) :
    ∀ T > 0, ∀ U : ℝ → Tot (L2 Ω) (L2M Ω) (W2B Ω),
      IsStrongSolution (-(bggComplex hΩ hb).waveOp) T (ini (L2 Ω) E₀ (betaPair hΩ hb m)) 0 U →
        ∃ t ∈ Icc 0 T, (WithLp.ofLp (tot (L2 Ω) (L2M Ω) (W2B Ω) (U t)).2.2).2 ∉ symL2 Ω :=
  B_not_symm_of_isSkwCurl hΩ hb hne _ (bggComplex_isSkwCurl hΩ hb) E₀ m

/-- **Ch. 6 on bounded domains: `u` leaves `L²(TSD)`.** In the setting of
`bggComplex_B_not_symm`, every strong solution leaves `{0} × L²(TSD) × S2` on every `[0, T]`,
`T > 0`, for every `S2 ⊆ L²(Ω; ℝ³) × L²(Ω; ℝ³ˣ³)`: since `σ ≡ 0` (`bggComplex_prop_4_16`), this
means `u(t) ∉ L²(TSD)` for some `t`. (`u(t) ∈ L²(TSD) ∩ H̊(curl, M) ⊆ L²(TSD₀) ⊥ diag(1, -1, 0)`,
`Feec.BoundedDomain.not_propagate_of_adjoint`.) -/
theorem bggComplex_not_propagate (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (E₀ : L2M Ω) (m : L2V Ω) (S2 : Submodule ℝ (W2B Ω)) :
    ∀ T > 0, ∀ U : ℝ → Tot (L2 Ω) (L2M Ω) (W2B Ω),
      IsStrongSolution (-(bggComplex hΩ hb).waveOp) T (ini (L2 Ω) E₀ (betaPair hΩ hb m)) 0 U →
        ∃ t ∈ Icc 0 T, U t ∉ Kc (L2 Ω) (TSD Ω) S2 :=
  not_propagate_of_isSkwCurl hΩ hb hne _ (bggComplex_isSkwCurl hΩ hb) E₀ m S2

/-- **Prop 4.16 for the Ch. 6 complex** (what does propagate, unconditionally): for data
`(0, E₀, ρ₀) ∈ D(L)` with `div div E₀ = 0` weakly (e.g. `E₀ ∈ L²(TSD)`, `TSD_le_ker_bgg`), the
Hodge wave equation of (5.1) has a unique strong solution on `[0, T]`, and `σ(t) = 0` and
`div div u(t) = 0` weakly for all `t`. In the multiplier form (6.2) this is the statement that
the `Γ`-constraint `dσ = Sφ` is exact and `σ` stays zero. -/
theorem bggComplex_prop_4_16 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (T : ℝ)
    {E₀ : L2M Ω} {ρ₀ : W2B Ω} (hD : ini (L2 Ω) E₀ ρ₀ ∈ (bggComplex hΩ hb).domL)
    (hE₀ : E₀ ∈ (bggComplex hΩ hb).d0†.ker) :
    ∃ U, IsStrongSolution (-(bggComplex hΩ hb).waveOp) T (ini (L2 Ω) E₀ ρ₀) 0 U ∧
      (∀ t ∈ Icc 0 T, (tot (L2 Ω) (L2M Ω) (W2B Ω) (U t)).1 = 0 ∧
        ∀ φ : R3 → ℝ, IsTest Ω φ → ∑ ij, ∫ x, (tot (L2 Ω) (L2M Ω) (W2B Ω) (U t)).2.1 ij x *
          hessField φ ij x ∂volume.restrict Ω = 0) ∧
      ∀ U', IsStrongSolution (-(bggComplex hΩ hb).waveOp) T (ini (L2 Ω) E₀ ρ₀) 0 U' →
        EqOn U U' (Icc 0 T) := by
  have hK : ini (L2 Ω) E₀ ρ₀ ∈ K (bggComplex hΩ hb) ⊤ := by
    rw [mem_K, tot_ini]
    exact ⟨rfl, hE₀, Submodule.mem_top⟩
  obtain ⟨U, hU, hUK, huniq⟩ := prop_4_16_exists_unconditional (bggComplex hΩ hb) ⊤ le_top T hD hK
  refine ⟨U, hU, fun t ht => ?_, huniq⟩
  obtain ⟨h1, h2, -⟩ := (mem_K _).1 (hUK t ht)
  exact ⟨h1, (mem_ker_adjoint_hessM_iff hΩ hb).1 h2⟩

/-- **Verdict for Ch. 6 on bounded domains** (unconditional). For the BGG weak-symmetry system
(5.1)/(6.1) with the thesis' boundary conditions (`H̊²`, `H̊(curl, M)`) on any nonempty bounded
open `Ω ⊆ ℝ³`, the TSD datum `(σ, u, (M, B))(0) = (0, 0, (0, β))` lies in `D(L)` and in
`K = {0} × L²(TSD) × ({0} × L²(TSD))`, and for every `T > 0`:
* (6.1) has a unique strong solution on `[0, T]` (Stone's theorem), with `σ ≡ 0` and
  `div div u ≡ 0` (`bggComplex_prop_4_16`);
* `u(t) ∉ L²(TSD)` for some `t ∈ [0, T]`;
* `B(t)` is not symmetric for some `t ∈ [0, T]`.

Correction: the bounded-domain failure of Props 4.17/4.19 ([QuennevilleBelair2015, §4.10–4.11])
carries over to the Ch. 6 method ([QuennevilleBelair2015, §6.1, §6.3]): imposing the symmetry of
`E` weakly does not restore TSD propagation. -/
theorem bggComplex_verdict (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ini (L2 Ω) 0 (betaPair hΩ hb 0) ∈ (bggComplex hΩ hb).domL ∧
      ini (L2 Ω) 0 (betaPair hΩ hb 0) ∈ Kc (L2 Ω) (TSD Ω) (TSDB Ω) ∧
      ∀ T > 0, ∃ U, IsStrongSolution (-(bggComplex hΩ hb).waveOp) T
          (ini (L2 Ω) 0 (betaPair hΩ hb 0)) 0 U ∧
        (∀ U', IsStrongSolution (-(bggComplex hΩ hb).waveOp) T
          (ini (L2 Ω) 0 (betaPair hΩ hb 0)) 0 U' → EqOn U U' (Icc 0 T)) ∧
        (∀ t ∈ Icc 0 T, (tot (L2 Ω) (L2M Ω) (W2B Ω) (U t)).1 = 0) ∧
        (∃ t ∈ Icc 0 T, (tot (L2 Ω) (L2M Ω) (W2B Ω) (U t)).2.1 ∉ TSD Ω) ∧
        ∃ t ∈ Icc 0 T, (WithLp.ofLp (tot (L2 Ω) (L2M Ω) (W2B Ω) (U t)).2.2).2 ∉ symL2 Ω := by
  obtain ⟨h, -⟩ := bggComplex_adjoint_betaPair hΩ hb 0
  have hD : ini (L2 Ω) 0 (betaPair hΩ hb 0) ∈ (bggComplex hΩ hb).domL := by
    rw [Feec.Constraints.mem_domL, tot_ini]
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, h⟩
  refine ⟨hD, ?_, fun T hT => ?_⟩
  · rw [mem_Kc, tot_ini]
    exact ⟨rfl, Submodule.zero_mem _, mem_TSDB.2 ⟨rfl, betaField_mem_TSD hΩ hb⟩⟩
  obtain ⟨U, hU, hσ, huniq⟩ := bggComplex_prop_4_16 hΩ hb T hD (Submodule.zero_mem _)
  refine ⟨U, hU, huniq, fun t ht => (hσ t ht).1, ?_, bggComplex_B_not_symm hΩ hb hne 0 0 T hT U hU⟩
  obtain ⟨t, ht, hn⟩ := bggComplex_not_propagate hΩ hb hne 0 0 ⊤ T hT U hU
  refine ⟨t, ht, fun hE => hn ?_⟩
  rw [mem_Kc]
  exact ⟨(hσ t ht).1, hE, Submodule.mem_top⟩

end Feec.Ch6.Bounded
