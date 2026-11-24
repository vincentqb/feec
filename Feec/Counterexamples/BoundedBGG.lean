module

public import Feec.Counterexamples.BoundedSymTSD
public import Feec.Models.BoundedDomain.BGG

/-!
# Ch. 6 on bounded domains: the BGG weak-symmetry system does not propagate TSD

The method of [QuennevilleBelair2015], Ch. 6 is the Hodge wave equation of the BGG complex
(5.1), with the symmetry of `E` imposed weakly through the multiplier `M`; §6.3 states the
boundary conditions (`H̊²`, `H̊(curl, M)`), realized on a bounded open `Ω ⊆ ℝ³` by
`Feec.Models.BoundedDomain.bggComplex`. On every nonempty bounded open `Ω`, for the TSD datum
`(σ, u, (M, B))(0) = (0, 0, (0, β))`, `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)` (`bggComplex_verdict`):

* the system has a unique strong solution, with `σ ≡ 0` and `div div u ≡ 0`
  (`Feec.Models.BoundedDomain.bggComplex_divFree_propagates`);
* `u(t) ∉ L²(TSD)` for some `t ∈ [0, T]` (`bggComplex_not_propagate`), and
* the magnetic field `B(t)` is not symmetric for some `t ∈ [0, T]` (`bggComplex_B_not_symm`).

Both refutations hold for **every** short complex whose second operator is contained in
`(S₁, curl)` on `H̊(curl, M)`, whatever its first operator (`B_not_symm`, `not_propagates`), so
they do not depend on how the thesis' `Γ` is realized.

The loss of symmetry of `B` holds also for the systems run in Ch. 7: the Hodge wave equation
(4.14), for every short complex with `d₁ ⊆ curl_min` (`thesisComplex_B_not_symm`), and the
reduced system (4.15) of the grad–curl complex (`thesisComplex_reduced_B_not_symm`), and for
(4.18) (`symComplexB_B_not_symm`).

## The mathematics

1. *Mean from the skew part of the curl* (`inner_curl_skewLin`): for `E ∈ H̊(curl, M)` and the
   skew field `Ψ_{ab} = skewOf (x_a e_b)` (no boundary condition),
   `⟪curl E, Ψ_{ab}⟫ = δ_{ab} ∫ tr E - ∫ E_{ab}`; hence `∫ E = 0` whenever `curl E` is symmetric.
2. *`B` loses symmetry* (`exists_not_symm_of_path`): if `Ḃ = curl E` and `B` stays symmetric,
   `⟪E(t), diag(1, -1, 0)⟫ ≡ 0`, whose derivative at `0` is `⟪Ė(0), diag(1, -1, 0)⟫`.
3. *The Ch. 6 operator* (`adjoint_betaPair`): `d₁† (m, β) = S₁† m + curl β`, and `S₁† m` is
   skew, so `u̇(0) = -d₁† (m, β)` pairs to `2|Ω|` with `diag(1, -1, 0)` for every `m`.
4. *`u` leaves `L²(TSD)`* (`E_not_tsd_of_adjoint`): TSD fields in `H̊(curl, M)` lie in
   `L²(TSD₀) ⊥ diag(1, -1, 0)`.

On `ℝ³` and on the torus the same system propagates TSD
(`Feec.Models.Euclidean.BGG.tsd_propagates_neg`, `Feec.Models.Torus.BGG.tsd_propagates`): the
failure is a boundary effect.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 5 (§5.1, (5.1)), Ch. 6 (§6.1, §6.3), Ch. 7 ((4.14), (4.15)), §4.10–4.11
* [D. N. Arnold, R. S. Falk, R. Winther, *Mixed finite element methods for linear elasticity with weakly imposed symmetry*][AFW2007]

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ContDiff Matrix LinearPMap
open MeasureTheory Set Filter Topology Feec.Domain Feec.Models.BoundedDomain

namespace Feec.Counterexamples.BoundedBGG

open BoundedDomainTSD

variable {Ω : Set R3}

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-! ## §1. The mean of a field in `H̊(curl, M)` from the skew part of its curl -/

/-- The linear vector field `x_a e_b`. -/
def linField (a b : Fin 3) : Fin 3 → R3 → ℝ := fun i => if i = b then (fun y : R3 => y a) else 0

theorem contDiff_linField (a b i : Fin 3) : ContDiff ℝ ∞ (linField a b i) := by
  unfold linField
  split_ifs
  exacts [contDiff_apply ℝ (fun _ : Fin 3 => ℝ) a, contDiff_const]

theorem pd_linField (a b m i : Fin 3) (x : R3) :
    partialDeriv m (linField a b i) x = if i = b ∧ m = a then 1 else 0 := by
  by_cases hi : i = b
  · simp only [linField, hi, ite_true, true_and]
    exact partialDeriv_apply_coord a m x
  · simp only [linField, hi, ite_false, false_and]
    simp [partialDeriv]

/-- The skew field `skewOf (x_a e_b)` (rows `e_j × x_a e_b`), as an element of `L²(Ω; ℝ³ˣ³)`. -/
def skewLin (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (a b : Fin 3) : L2F ℝ Ω Ix :=
  smoothField hΩ hb (skewOf (linField a b))
    (fun jk => (contDiff_skewOf (fun i => contDiff_linField a b i) jk).continuous)

/-- A skew field pairs to zero with a symmetric one. -/
theorem inner_skewLin_eq_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {C : L2F ℝ Ω Ix}
    (hC : C ∈ symSub ℝ Ω) (a b : Fin 3) : ⟪C, skewLin hΩ hb a b⟫_ℝ = 0 := by
  rw [skewLin, inner_smoothField]
  exact sum_integral_mul_skewOf_eq_zero hC _

/-- **The mean of `B ∈ H̊(curl, M)` is read off from the skew part of `curl B`**: for `(B, C)` in
the graph of `curl_min`, `⟪C, skewOf (x_a e_b)⟫ = δ_{ab} ∫_Ω tr B - ∫_Ω B_{ab}` (Green's formula
against the non-compactly-supported `skewOf (x_a e_b)`; no condition on `B` itself). -/
theorem inner_curl_skewLin (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B C : L2F ℝ Ω Ix}
    (h : (B, C) ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).graph) (a b : Fin 3) :
    ⟪C, skewLin hΩ hb a b⟫_ℝ = (if a = b then ∑ i, ∫ x, B (i, i) x ∂volume.restrict Ω else 0) -
      ∫ x, B (a, b) x ∂volume.restrict Ω := by
  obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff _).1 h
  simp only at hz1 hz2
  have hvd : ∀ i, ContDiff ℝ 1 (linField a b i) := fun i =>
    (contDiff_linField a b i).of_le (by simp)
  have hdv : ∀ x, ∑ m, partialDeriv m (linField a b m) x = if a = b then 1 else 0 := by
    intro x
    simp only [pd_linField, Fin.sum_univ_three]
    fin_cases a <;> fin_cases b <;> simp
  have e := minimal_curl_identity hΩ hb z (contDiff_skewOf hvd)
  rw [hz1, hz2] at e
  rw [skewLin, inner_smoothField, e]
  simp only [curlM_skewOf (fun i => (hvd i).differentiable one_ne_zero), hdv]
  simp only [pd_linField, mul_sub, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl fun ij _ => integral_sub ?_ ?_]
  rotate_left
  · split_ifs <;> first
      | exact integrable_zero _ _ _
      | exact (integrable_mul (B.ofLp ij) (g := fun _ => (1 : ℝ))
          (memLp_of_continuous hΩ.measurableSet hb continuous_const)).congr
          (Eventually.of_forall fun x => by simp)
  · split_ifs <;> first
      | exact integrable_zero _ _ _
      | exact (integrable_mul (B.ofLp ij) (g := fun _ => (1 : ℝ))
          (memLp_of_continuous hΩ.measurableSet hb continuous_const)).congr
          (Eventually.of_forall fun x => by simp)
  fin_cases a <;> fin_cases b <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_three]

/-- `⟪diag(1, -1, 0), diag(1, -1, 0)⟫ = 2 |Ω|`. -/
theorem inner_constField_diagA (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ⟪constField hΩ hb diagA, constField hΩ hb diagA⟫_ℝ = 2 * volume.real Ω := by
  rw [inner_constField]
  simp only [integral_constField]
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, diagA]
  ring

theorem constField_diagA_mem_symSub (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    constField hΩ hb diagA ∈ symSub ℝ Ω :=
  (constField_mem_tsd hΩ hb diagA_transpose diagA_trace).1

/-! ## §2. The magnetic field loses symmetry: the abstract criteria -/

/-- **Core lemma (paths).** Let `E, B : ℝ → L²(Ω; ℝ³ˣ³)` with `E(t) ∈ H̊(curl, M)` and
`Ḃ(t) = curl E(t)` on `[0, T]`, `T > 0`, and `⟪Ė(0), diag(1, -1, 0)⟫ ≠ 0`. Then `B(t)` is not
symmetric for some `t ∈ [0, T]`. -/
theorem exists_not_symm_of_path (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {T : ℝ}
    (hT : 0 < T) {E B : ℝ → L2F ℝ Ω Ix} {E' : L2F ℝ Ω Ix}
    (hE : HasDerivWithinAt E E' (Icc 0 T) 0)
    (hB : ∀ t ∈ Icc 0 T, ∃ C, HasDerivWithinAt B C (Icc 0 T) t ∧
      (E t, C) ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).graph)
    (hE' : ⟪E', constField hΩ hb diagA⟫_ℝ ≠ 0) : ∃ t ∈ Icc 0 T, B t ∉ symSub ℝ Ω := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  have hℓ : ∀ t ∈ Icc 0 T, ⟪E t, constField hΩ hb diagA⟫_ℝ = 0 := by
    intro t ht
    obtain ⟨C, hC, hEC⟩ := hB t ht
    have hX : ∀ a b, ⟪C, skewLin hΩ hb a b⟫_ℝ = 0 := by
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

section Criteria

variable {W₀ W₁ W₂ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [CompleteSpace W₂]

/-- The middle and last components of a strong solution of `U' = L U`: `Ė = d₀ σ - d₁† B`,
`Ḃ = d₁ E`. -/
theorem hasDerivWithinAt_components (S : ShortHilbertComplex ℝ W₀ W₁ W₂) {T : ℝ}
    {U : ℝ → PiLp 2 (ShortHilbertComplex.W3 W₀ W₁ W₂)}
    (hU : Evolution.IsStrongSolution S.wave (Icc 0 T) 0 U) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s => (U s 1 : W₁))
        ((S.wave ⟨U t, hU.mem_domain ht⟩ : PiLp 2 (ShortHilbertComplex.W3 W₀ W₁ W₂)) 1)
        (Icc 0 T) t ∧
      HasDerivWithinAt (fun s => (U s 2 : W₂))
        ((S.wave ⟨U t, hU.mem_domain ht⟩ : PiLp 2 (ShortHilbertComplex.W3 W₀ W₁ W₂)) 2)
        (Icc 0 T) t := by
  have hd := hU.hasDerivWithinAt ht
  rw [Pi.zero_apply, add_zero] at hd
  exact ⟨(PiLp.proj 2 (𝕜 := ℝ) (ShortHilbertComplex.W3 W₀ W₁ W₂)
      1).hasFDerivAt.comp_hasDerivWithinAt
      t hd,
    (PiLp.proj 2 (𝕜 := ℝ) (ShortHilbertComplex.W3 W₀ W₁ W₂) 2).hasFDerivAt.comp_hasDerivWithinAt
      t hd⟩

/-- Strong solutions for the `ℝ`-structure `instNormedSpaceRealW3` of the `𝕜`-generic layers are
strong solutions for the inner-product structure at `𝕜 = ℝ` (the two agree componentwise, but
not reducibly). -/
theorem isStrongSolution_realW3 (S : ShortHilbertComplex ℝ W₀ W₁ W₂) {I : Set ℝ}
    {F U : ℝ → PiLp 2 (ShortHilbertComplex.W3 W₀ W₁ W₂)}
    (h : Evolution.IsStrongSolution S.wave I F U) :
    @Evolution.IsStrongSolution ℝ _ _ _ _ (@PiLp.normedSpace 2 ℝ (Fin 3) _ _ _ _ _
      (fun i => ShortHilbertComplex.instNormedSpaceRealW3 (W₀ := W₀) (W₁ := W₁) (W₂ := W₂) i))
      S.wave I F U := by
  convert h using 2
  funext i
  fin_cases i <;> rfl

/-- The converse of `isStrongSolution_realW3`, for classical solutions. -/
theorem isClassicalSolution_of_realW3 (S : ShortHilbertComplex ℝ W₀ W₁ W₂) {I : Set ℝ}
    {F U : ℝ → PiLp 2 (ShortHilbertComplex.W3 W₀ W₁ W₂)}
    (h : @Evolution.IsClassicalSolution ℝ _ _ _ _ (@PiLp.normedSpace 2 ℝ (Fin 3) _ _ _ _ _
      (fun i => ShortHilbertComplex.instNormedSpaceRealW3 (W₀ := W₀) (W₁ := W₁) (W₂ := W₂) i))
      S.wave I F U) :
    Evolution.IsClassicalSolution S.wave I F U := by
  convert h using 2
  funext i
  fin_cases i <;> rfl

/-- **The magnetic field loses symmetry (abstract criterion, Hodge wave equation).** Let `S` be a
short complex, `ι : W₁ → L²(Ω; ℝ³ˣ³)`, `κ : W₂ → L²(Ω; ℝ³ˣ³)` continuous linear with
`κ (d₁ u) = curl_min (ι u)`. If `⟪ι (d₁† B₀), diag(1, -1, 0)⟫ ≠ 0`, then every strong solution
of `U' = L U` from `(0, E₀, B₀)`, any `E₀`, has `κ B(t)` non-symmetric for some `t ∈ [0, T]`, on
every `[0, T]`, `T > 0`. -/
theorem not_symm_of_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (S : ShortHilbertComplex ℝ W₀ W₁ W₂) (ι : W₁ →L[ℝ] L2F ℝ Ω Ix) (κ : W₂ →L[ℝ] L2F ℝ Ω Ix)
    (hικ : ∀ u : S.d₁.domain,
      (ι u, κ (S.d₁ u)) ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).graph)
    (B₀ : S.d₁†.domain) (hc : ⟪ι (S.d₁† B₀), constField hΩ hb diagA⟫_ℝ ≠ 0) :
    ∀ T > 0, ∀ U : ℝ → PiLp 2 (ShortHilbertComplex.W3 W₀ W₁ W₂),
      Evolution.IsStrongSolution S.wave (Icc 0 T) 0 U → (U 0 0 : W₀) = 0 →
        (U 0 2 : W₂) = (B₀ : W₂) → ∃ t ∈ Icc 0 T, κ (U t 2 : W₂) ∉ symSub ℝ Ω := by
  intro T hT U hU h0 h2
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  refine exists_not_symm_of_path hΩ hb hT (E := fun t => ι (U t 1 : W₁))
    (B := fun t => κ (U t 2 : W₂)) (E' := ι (-(S.d₁† B₀))) ?_ (fun t ht => ?_) ?_
  · have hd := (hasDerivWithinAt_components S hU h0T).1
    rw [S.wave_apply_one] at hd
    refine (ι.hasFDerivAt.comp_hasDerivWithinAt 0 hd).congr_deriv ?_
    have e0 : S.d₀ ⟨(U 0 0 : W₀), ((S.mem_wave_domain).1 (hU.mem_domain h0T)).1⟩ = 0 := by
      rw [show (⟨(U 0 0 : W₀), _⟩ : S.d₀.domain) = 0 from Subtype.ext h0, LinearPMap.map_zero]
    have e2 : (⟨(U 0 2 : W₂), (hU.mem_domain h0T).2 2 1⟩ : S.d₁†.domain) = B₀ := Subtype.ext h2
    rw [e0, zero_sub]
    erw [e2]
  · have hd := (hasDerivWithinAt_components S hU ht).2
    rw [S.wave_apply_two] at hd
    exact ⟨_, κ.hasFDerivAt.comp_hasDerivWithinAt t hd,
      hικ ⟨(U t 1 : W₁), ((S.mem_wave_domain).1 (hU.mem_domain ht)).2.1⟩⟩
  · rw [_root_.map_neg, inner_neg_left]
    exact neg_ne_zero.2 hc

/-- The reduced-system form of `not_symm_of_adjoint` ((4.15): `Ė = -d₁† B`, `Ḃ = d₁ E`). -/
theorem reduced_not_symm_of_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (S : ShortHilbertComplex ℝ W₀ W₁ W₂) (ι : W₁ →L[ℝ] L2F ℝ Ω Ix) (κ : W₂ →L[ℝ] L2F ℝ Ω Ix)
    (hικ : ∀ u : S.d₁.domain,
      (ι u, κ (S.d₁ u)) ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).graph)
    {T : ℝ} (hT : 0 < T) {E : ℝ → W₁} {B : ℝ → W₂} (hR : S.IsReducedSolution (Icc 0 T) E B)
    (hc : ⟪ι (S.d₁† ⟨B 0, hR.memB 0 ⟨le_rfl, hT.le⟩⟩), constField hΩ hb diagA⟫_ℝ ≠ 0) :
    ∃ t ∈ Icc 0 T, κ (B t) ∉ symSub ℝ Ω := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  refine exists_not_symm_of_path hΩ hb hT (E := fun t => ι (E t)) (B := fun t => κ (B t))
    (E' := ι (-(S.d₁† ⟨B 0, hR.memB 0 h0⟩))) (ι.hasFDerivAt.comp_hasDerivWithinAt 0
      (hR.derivE 0 h0)) (fun t ht => ⟨_, κ.hasFDerivAt.comp_hasDerivWithinAt t (hR.derivB t ht),
      hικ ⟨E t, hR.memE t ht⟩⟩) ?_
  rw [_root_.map_neg, inner_neg_left]
  exact neg_ne_zero.2 hc

/-- **The electric field leaves `L²(TSD)` (abstract criterion).** Let `ι : W₁ → L²(Ω; ℝ³ˣ³)` be
continuous linear with `ι D(d₁) ⊆ H̊(curl, M)`. If `⟪ι (d₁† B₀), G⟫ ≠ 0` for some
`G ⊥ L²(TSD₀)`, then every strong solution of `U' = L U` from `(0, E₀, B₀)` has
`ι E(t) ∉ L²(TSD)` for some `t ∈ [0, T]`, on every `[0, T]`, `T > 0` (only `σ(0) = 0` enters). -/
theorem E_not_tsd_of_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (S : ShortHilbertComplex ℝ W₀ W₁ W₂) (ι : W₁ →L[ℝ] L2F ℝ Ω Ix)
    (hι : ∀ u ∈ S.d₁.domain, ι u ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain)
    (B₀ : S.d₁†.domain) {G : L2F ℝ Ω Ix} (hG : G ∈ (tsd₀ Ω hΩ hb)ᗮ)
    (hc : ⟪ι (S.d₁† B₀), G⟫_ℝ ≠ 0) :
    ∀ T > 0, ∀ U : ℝ → PiLp 2 (ShortHilbertComplex.W3 W₀ W₁ W₂),
      Evolution.IsStrongSolution S.wave (Icc 0 T) 0 U → (U 0 0 : W₀) = 0 →
        (U 0 2 : W₂) = (B₀ : W₂) → ∃ t ∈ Icc 0 T, ι (U t 1 : W₁) ∉ tsd Ω := by
  intro T hT U hU h0 h2
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hmem : ∀ t ∈ Icc 0 T, ι (U t 1 : W₁) ∈ tsd₀ Ω hΩ hb := fun t ht =>
    inf_le_tsd₀ hΩ hb ⟨hall t ht, hι _ ((S.mem_wave_domain).1 (hU.mem_domain ht)).2.1⟩
  have hd := (hasDerivWithinAt_components S hU h0T).1
  rw [S.wave_apply_one] at hd
  have hm := Evolution.deriv_mem_of_eventually_mem_closed (isClosed_tsd₀ hΩ hb)
    (ι.hasFDerivAt.comp_hasDerivWithinAt 0 hd) (Evolution.neBot_nhdsWithin_Icc_diff hT h0T)
    (eventually_nhdsWithin_of_forall hmem) (hmem 0 h0T)
  have e0 : S.d₀ ⟨(U 0 0 : W₀), ((S.mem_wave_domain).1 (hU.mem_domain h0T)).1⟩ = 0 := by
    rw [show (⟨(U 0 0 : W₀), _⟩ : S.d₀.domain) = 0 from Subtype.ext h0, LinearPMap.map_zero]
  have e2 : (⟨(U 0 2 : W₂), (hU.mem_domain h0T).2 2 1⟩ : S.d₁†.domain) = B₀ := Subtype.ext h2
  rw [e0, zero_sub] at hm
  erw [e2] at hm
  have hm' : ι (S.d₁† B₀) ∈ tsd₀ Ω hΩ hb := by simpa using (tsd₀ Ω hΩ hb).neg_mem hm
  exact hc (by rw [real_inner_comm]; exact (Submodule.mem_orthogonal' _ _).1 hG _ hm')

end Criteria

/-! ## §3. Instances: the systems (4.14) and (4.15) run in Ch. 7, and (4.18) -/

section Instances

variable {W₀ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]

/-- `d₁† β = curl β = -diag(1, -1, 0)` for every short complex with `d₁ ⊆ curl_min` (the
grad–curl complex of (4.14) among them), and `⟪d₁† β, diag(1, -1, 0)⟫ = -2|Ω|`. -/
theorem thesisComplex_adjoint_betaL (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))
    (hd₁ : S.d₁ ≤ (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) :
    ∃ h : betaL2 hΩ hb ∈ S.d₁†.domain,
      ⟪S.d₁† ⟨_, h⟩, constField hΩ hb diagA⟫_ℝ = -(2 * volume.real Ω) := by
  obtain ⟨h, e⟩ := betaL2_mem_adjoint hΩ hb S hd₁
  exact ⟨h, by rw [e, inner_neg_left, inner_constField_diagA]⟩

/-- **(4.14) on bounded domains: `B` loses symmetry**, for every boundary condition containing
`n × E = 0`. For every short complex `W₀ → L²(M) → L²(M)` with `d₁ ⊆ curl_min` (the grad–curl
complex `H̊¹ → H̊(curl, M) → L²(M)` of (4.14) among them) on a nonempty bounded open `Ω`, from
`(0, E₀, β)` with any `E₀`, every strong solution on `[0, T]`, `T > 0`, has `B(t)` non-symmetric
for some `t`, although `β` is symmetric (TSD). [QuennevilleBelair2015], (4.14), Ch. 7 -/
theorem thesisComplex_B_not_symm (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))
    (hd₁ : S.d₁ ≤ (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) :
    ∀ T > 0, ∀ U : ℝ → PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix)),
      Evolution.IsStrongSolution S.wave (Icc 0 T) 0 U →
        (U 0 0 : W₀) = 0 → (U 0 2 : L2F ℝ Ω Ix) = betaL2 hΩ hb →
          ∃ t ∈ Icc 0 T, (U t 2 : L2F ℝ Ω Ix) ∉ symSub ℝ Ω := by
  obtain ⟨h, e⟩ := thesisComplex_adjoint_betaL hΩ hb S hd₁
  intro T hT U hU h0 h2
  refine not_symm_of_adjoint hΩ hb S (ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.id ℝ _)
    (fun u => ?_) ⟨_, h⟩
    (by rw [ContinuousLinearMap.id_apply, e]; have := volume_real_pos hΩ hb hne; linarith)
    T hT U hU h0 h2
  have hu : S.d₁ u = (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω ⟨u, hd₁.1 u.2⟩ := hd₁.2 rfl
  change ((u : L2F ℝ Ω Ix), S.d₁ u) ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).graph
  rw [hu]
  exact LinearPMap.mem_graph ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) ⟨u, hd₁.1 u.2⟩

end Instances

/-- **(4.15) on bounded domains: `B` loses symmetry.** The reduced system `Ė = -curl† B`,
`Ḃ = curl E` of the grad–curl complex, from `(E₀, β)`, any `E₀`: every strong solution has `B(t)`
non-symmetric for some `t ∈ [0, T]`, `T > 0`. [QuennevilleBelair2015], (4.15), Ch. 7 -/
theorem thesisComplex_reduced_B_not_symm (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) {T : ℝ} (hT : 0 < T) {E B : ℝ → L2F ℝ Ω Ix}
    (hR : (gradCurl ℝ hΩ).IsReducedSolution (Icc 0 T) E B) (hB : B 0 = betaL2 hΩ hb) :
    ∃ t ∈ Icc 0 T, B t ∉ symSub ℝ Ω := by
  obtain ⟨h, e⟩ := thesisComplex_adjoint_betaL hΩ hb (gradCurl ℝ hΩ) le_rfl
  have hR' := reduced_not_symm_of_adjoint hΩ hb (gradCurl ℝ hΩ) (ContinuousLinearMap.id ℝ _)
    (ContinuousLinearMap.id ℝ _) (fun u => ((gradCurl ℝ hΩ).d₁.mem_graph u)) hT hR (by
      have e' : (⟨B 0, hR.memB 0 ⟨le_rfl, hT.le⟩⟩ : (gradCurl ℝ hΩ).d₁†.domain) = ⟨_, h⟩ :=
        Subtype.ext hB
      rw [ContinuousLinearMap.id_apply, e', e]
      have := volume_real_pos hΩ hb hne
      linarith)
  simpa using hR'

/-- **(4.18) on bounded domains: `B ∈ L²(T)` loses symmetry.** For the complex (4.16)
`H̊² → H̊(curl, S) → L²(T)`, from `(0, E₀, β)`, any `E₀ ∈ L²(S)`: every strong solution has
`B(t)` non-symmetric for some `t ∈ [0, T]`, `T > 0`. [QuennevilleBelair2015], (4.18) -/
theorem symComplexB_B_not_symm (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ∀ T > 0, ∀ U : ℝ → PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ Ω) (symSub ℝ Ω) (trSub ℝ Ω)),
      Evolution.IsStrongSolution (hessCurl ℝ hΩ).wave (Icc 0 T) 0 U → (U 0 0 : L2 ℝ Ω) = 0 →
        (U 0 2 : trSub ℝ Ω) = BoundedSymTSD.betaT hΩ hb →
          ∃ t ∈ Icc 0 T, Subtype.val (U t 2 : trSub ℝ Ω) ∉ symSub ℝ Ω := by
  obtain ⟨h, e⟩ := BoundedSymTSD.betaT_mem_adjoint hΩ hb (hessCurl ℝ hΩ) le_rfl
  intro T hT U hU h0 h2
  exact not_symm_of_adjoint hΩ hb (hessCurl ℝ hΩ) (symSub ℝ Ω).subtypeL (trSub ℝ Ω).subtypeL
    (hessCurl_d₁_graph_map hΩ) ⟨_, h⟩ (by
      rw [e]
      change ⟪-constField hΩ hb diagA, constField hΩ hb diagA⟫_ℝ ≠ 0
      rw [inner_neg_left, inner_constField_diagA]
      have := volume_real_pos hΩ hb hne
      linarith) T hT U hU h0 h2

/-! ## §4. Ch. 6 on a bounded domain: TSD and the symmetry of `B` are not propagated -/

/-- The magnetic datum `(M₀, B₀) = (m, β)` of the Ch. 6 system. -/
abbrev betaPair (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (m : L2F ℝ Ω (Fin 3)) : W2B ℝ Ω :=
  WithLp.toLp 2 (m, betaL2 hΩ hb)

/-- **`d₁† (m, β)`** for every complex with `d₁ ⊆ (S₁, curl)` on `H̊(curl, M)`:
`(m, β) ∈ D(d₁†)`, `d₁† (m, β) = S₁† m - diag(1, -1, 0)`, and
`⟪d₁† (m, β), diag(1, -1, 0)⟫ = -2|Ω|` (`S₁† m` is orthogonal to symmetric fields). -/
theorem adjoint_betaPair (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {W₀ : Type}
    [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (W2B ℝ Ω)) (hd₁ : S.d₁ ≤ (bggComplex ℝ hΩ).d₁)
    (m : L2F ℝ Ω (Fin 3)) :
    ∃ h : betaPair hΩ hb m ∈ S.d₁†.domain,
      S.d₁† ⟨_, h⟩ = ContinuousLinearMap.adjoint (skwL ℝ Ω) m - constField hΩ hb diagA ∧
      ⟪S.d₁† ⟨_, h⟩, constField hΩ hb diagA⟫_ℝ = -(2 * volume.real Ω) := by
  obtain ⟨h, e⟩ := smoothPair_mem_adjoint hΩ hb S hd₁ m (Ψ := betaField)
    fun ij => (contDiff_betaField ij).of_le (by simp)
  have e' : S.d₁† ⟨_, h⟩ = ContinuousLinearMap.adjoint (skwL ℝ Ω) m - constField hΩ hb diagA := by
    rw [e, curl_betaL2, sub_eq_add_neg]
  refine ⟨h, e', ?_⟩
  have e2 := congrArg (⟪·, constField hΩ hb diagA⟫_ℝ) e'
  rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    skwL_eq_zero_of_mem_symSub (constField_diagA_mem_symSub hΩ hb), inner_zero_right, zero_sub,
    inner_constField_diagA] at e2
  exact e2

variable (Ω) in
/-- `{0} × L²(TSD) ⊆ L²(Ω; ℝ³) × L²(Ω; ℝ³ˣ³)`: vanishing multiplier `M`, TSD magnetic field. -/
def tsdB : Submodule ℝ (W2B ℝ Ω) :=
  ((⊥ : Submodule ℝ (L2F ℝ Ω (Fin 3))).prod (tsd Ω)).comap
    (WithLp.linearEquiv 2 ℝ (L2F ℝ Ω (Fin 3) × L2F ℝ Ω Ix)).toLinearMap

theorem mem_tsdB {w : W2B ℝ Ω} : w ∈ tsdB Ω ↔ (WithLp.ofLp w).1 = 0 ∧ (WithLp.ofLp w).2 ∈ tsd
    Ω := by
  simp [tsdB, Submodule.mem_prod]

theorem isClosed_tsdB : IsClosed (tsdB Ω : Set (W2B ℝ Ω)) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix)
  have h : (tsdB Ω : Set (W2B ℝ Ω)) = e ⁻¹' ({0} ×ˢ (tsd Ω : Set (L2F ℝ Ω Ix))) := by
    ext w
    simp only [SetLike.mem_coe, mem_tsdB, mem_preimage, mem_prod, mem_singleton_iff]
    rfl
  rw [h]
  exact (isClosed_singleton.prod isClosed_tsd).preimage e.continuous

instance : (tsdB Ω).HasOrthogonalProjection := by
  have : CompleteSpace (tsdB Ω) := isClosed_tsdB.completeSpace_coe
  infer_instance

/-- The projection `(M, B) ↦ B`. -/
def sndB : W2B ℝ Ω →L[ℝ] L2F ℝ Ω Ix :=
  (ContinuousLinearMap.snd ℝ (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix)).toContinuousLinearMap

theorem sndB_apply (w : W2B ℝ Ω) : sndB w = (WithLp.ofLp w).2 := rfl

section Generic

variable {W₀ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]

/-- **`B` loses symmetry, for every complex with second operator contained in `(S₁, curl)` on
`H̊(curl, M)`** (any first operator). From `(0, E₀, (m, β))`, any `E₀`, `m`: every strong
solution on `[0, T]`, `T > 0`, has `B(t)` non-symmetric for some `t ∈ [0, T]`. -/
theorem B_not_symm (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (W2B ℝ Ω)) (hd₁ : S.d₁ ≤ (bggComplex ℝ hΩ).d₁)
    (m : L2F ℝ Ω (Fin 3)) :
    ∀ T > 0, ∀ U : ℝ → PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (W2B ℝ Ω)),
      Evolution.IsStrongSolution S.wave (Icc 0 T) 0 U → (U 0 0 : W₀) = 0 →
        (U 0 2 : W2B ℝ Ω) = betaPair hΩ hb m →
          ∃ t ∈ Icc 0 T, (WithLp.ofLp (U t 2 : W2B ℝ Ω)).2 ∉ symSub ℝ Ω := by
  obtain ⟨h, -, e⟩ := adjoint_betaPair hΩ hb S hd₁ m
  intro T hT U hU h0 h2
  exact not_symm_of_adjoint hΩ hb S (ContinuousLinearMap.id ℝ _) sndB
    (fun u => by
      have hu : S.d₁ u = (bggComplex ℝ hΩ).d₁ ⟨u, hd₁.1 u.2⟩ := hd₁.2 rfl
      rw [ContinuousLinearMap.id_apply, sndB_apply, hu]
      exact (bggComplex_d₁_apply hΩ ⟨u, hd₁.1 u.2⟩).1) ⟨_, h⟩
    (by rw [ContinuousLinearMap.id_apply, e]; have := volume_real_pos hΩ hb hne; linarith)
    T hT U hU h0 h2

/-- **`u` leaves `L²(TSD)`, for every complex with second operator contained in `(S₁, curl)` on
`H̊(curl, M)`** (any first operator). From `(0, E₀, (m, β))`, any `E₀`, `m`: every strong
solution has `u(t) ∉ L²(TSD)` for some `t ∈ [0, T]`, on every `[0, T]`, `T > 0`. -/
theorem not_propagates (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (W2B ℝ Ω)) (hd₁ : S.d₁ ≤ (bggComplex ℝ hΩ).d₁)
    (m : L2F ℝ Ω (Fin 3)) :
    ∀ T > 0, ∀ U : ℝ → PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (W2B ℝ Ω)),
      Evolution.IsStrongSolution S.wave (Icc 0 T) 0 U → (U 0 0 : W₀) = 0 →
        (U 0 2 : W2B ℝ Ω) = betaPair hΩ hb m →
          ∃ t ∈ Icc 0 T, (U t 1 : L2F ℝ Ω Ix) ∉ tsd Ω := by
  obtain ⟨h, -, e⟩ := adjoint_betaPair hΩ hb S hd₁ m
  intro T hT U hU h0 h2
  exact E_not_tsd_of_adjoint hΩ hb S (ContinuousLinearMap.id ℝ _)
    (fun u hu => by
      rw [ContinuousLinearMap.id_apply, ← bggComplex_d₁_domain hΩ]
      exact hd₁.1 hu) ⟨_, h⟩ (constField_mem_orthogonal_tsd₀ hΩ hb diagA)
    (by rw [ContinuousLinearMap.id_apply, e]; have := volume_real_pos hΩ hb hne; linarith)
    T hT U hU h0 h2

end Generic

/-- **Ch. 6 on bounded domains: `B` loses symmetry.** For the BGG complex (5.1) on any nonempty
bounded open `Ω`, from `(0, E₀, (m, β))` with any `E₀`, `m`: every strong solution of the Hodge
wave equation (equivalently of (6.1), `Feec.Models.BoundedDomain.bggComplex_weakEqs_of_isStrongSolution`) on `[0, T]`,
`T > 0`, has `B(t)` non-symmetric for some `t`, although `β` is symmetric.
[QuennevilleBelair2015], §6.3 -/
theorem bggComplex_B_not_symm (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (m : L2F ℝ Ω (Fin 3)) :
    ∀ T > 0, ∀ U : ℝ → PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ Ω) (L2F ℝ Ω Ix) (W2B ℝ Ω)),
      Evolution.IsStrongSolution (bggComplex ℝ hΩ).wave (Icc 0 T) 0 U → (U 0 0 : L2 ℝ Ω) = 0 →
        (U 0 2 : W2B ℝ Ω) = betaPair hΩ hb m →
          ∃ t ∈ Icc 0 T, (WithLp.ofLp (U t 2 : W2B ℝ Ω)).2 ∉ symSub ℝ Ω :=
  B_not_symm hΩ hb hne _ le_rfl m

/-- **Ch. 6 on bounded domains: `u` leaves `L²(TSD)`.** In the setting of
`bggComplex_B_not_symm`, every strong solution has `u(t) ∉ L²(TSD)` for some `t ∈ [0, T]`.
[QuennevilleBelair2015], §6.3 -/
theorem bggComplex_not_propagate (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (m : L2F ℝ Ω (Fin 3)) :
    ∀ T > 0, ∀ U : ℝ → PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ Ω) (L2F ℝ Ω Ix) (W2B ℝ Ω)),
      Evolution.IsStrongSolution (bggComplex ℝ hΩ).wave (Icc 0 T) 0 U → (U 0 0 : L2 ℝ Ω) = 0 →
        (U 0 2 : W2B ℝ Ω) = betaPair hΩ hb m →
          ∃ t ∈ Icc 0 T, (U t 1 : L2F ℝ Ω Ix) ∉ tsd Ω :=
  not_propagates hΩ hb hne _ le_rfl m

/-- **Verdict for Ch. 6 on bounded domains** (unconditional). For the BGG weak-symmetry system
(5.1)/(6.1) with the thesis' boundary conditions on any nonempty bounded open `Ω ⊆ ℝ³`, the TSD
datum `(σ, u, (M, B))(0) = (0, 0, (0, β))` lies in `D(L)` and in
`K = {0} × L²(TSD) × ({0} × L²(TSD))`, and for every `T > 0`: the system has a unique strong
solution on `[0, T]`, with `σ ≡ 0`; `u(t) ∉ L²(TSD)` for some `t`; and `B(t)` is not symmetric for
some `t`. The failure is caused by the boundary: on `ℝ³` and on the torus the same system
propagates TSD.

[QuennevilleBelair2015], §6.1, §6.3: imposing the symmetry of `E` weakly does not restore TSD
propagation on bounded domains. -/
theorem bggComplex_verdict (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ShortHilbertComplex.mk3 0 0 (betaPair hΩ hb 0) ∈ (bggComplex ℝ hΩ).wave.domain ∧
      ShortHilbertComplex.mk3 0 0 (betaPair hΩ hb 0) ∈ HilbertComplex.totalSub
        (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω)) (tsd Ω) (tsdB Ω)) ∧
      ∀ T > 0, ∃ U, U 0 = ShortHilbertComplex.mk3 0 0 (betaPair hΩ hb 0) ∧
        Evolution.IsStrongSolution (bggComplex ℝ hΩ).wave (Icc 0 T) 0 U ∧
        (∀ V, V 0 = ShortHilbertComplex.mk3 0 0 (betaPair hΩ hb 0) →
          Evolution.IsStrongSolution (bggComplex ℝ hΩ).wave (Icc 0 T) 0 V → EqOn V U (Icc 0 T)) ∧
        (∀ t ∈ Icc 0 T, (U t 0 : L2 ℝ Ω) = 0) ∧
        (∃ t ∈ Icc 0 T, (U t 1 : L2F ℝ Ω Ix) ∉ tsd Ω) ∧
        ∃ t ∈ Icc 0 T, (WithLp.ofLp (U t 2 : W2B ℝ Ω)).2 ∉ symSub ℝ Ω := by
  obtain ⟨h, -⟩ := adjoint_betaPair hΩ hb (bggComplex ℝ hΩ) le_rfl 0
  have hD : ShortHilbertComplex.mk3 (0 : L2 ℝ Ω) (0 : L2F ℝ Ω Ix) (betaPair hΩ hb 0) ∈
      (bggComplex ℝ hΩ).wave.domain :=
    (bggComplex ℝ hΩ).mem_wave_domain.2 ⟨Submodule.zero_mem _, Submodule.zero_mem _,
      Submodule.zero_mem _, h⟩
  refine ⟨hD, ShortHilbertComplex.mem_totalSub_family3.2 ⟨Submodule.zero_mem _,
    Submodule.zero_mem _, mem_tsdB.2 ⟨rfl, betaL2_mem_tsd hΩ hb⟩⟩, fun T hT => ?_⟩
  obtain ⟨U, hU0, hU, hσ, huniq⟩ := bggComplex_divFree_propagates hΩ hD rfl
    (Submodule.zero_mem _) 0 T
  have h0 : (U 0 0 : L2 ℝ Ω) = 0 := by rw [hU0]; rfl
  have h2 : (U 0 2 : W2B ℝ Ω) = betaPair hΩ hb 0 := by rw [hU0]; rfl
  have hS := (isClassicalSolution_of_realW3 _ hU).toIsStrongSolution
  exact ⟨U, hU0, hS, fun V hV0 hV => huniq V hV0 (isStrongSolution_realW3 _ hV),
    fun t ht => (hσ t ht).1, bggComplex_not_propagate hΩ hb hne 0 T hT U hS h0 h2,
    bggComplex_B_not_symm hΩ hb hne 0 T hT U hS h0 h2⟩

/-- **The invariant core for the Ch. 6 complex** (`K = {0} × L²(TSD) × S₂`): every datum
`U₀ ∈ D(L) ∩ K*` has, on every `[0, T]`, a classical solution, unique among strong solutions;
it stays in `K* ⊆ K`, and its electric and magnetic parts solve the reduced system (4.15).
The content is `S₁* ⊆ L²(TSD₀)` (`invariantCore₁_le_tsd₀`) and `K* ⊊ K`; no non-stationary
element of `K*` is exhibited.
[QuennevilleBelair2015], Prop. 4.17, corrected, for the Ch. 6 complex -/
theorem bggComplex_invariantCore_propagates (hΩ : IsOpen Ω) (S₂ : Submodule ℝ (W2B ℝ Ω))
    [S₂.HasOrthogonalProjection]
    {U₀ : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ Ω) (L2F ℝ Ω Ix) (W2B ℝ Ω))}
    (hU₀ : U₀ ∈ (bggComplex ℝ hΩ).wave.domain) (hK : U₀ ∈ (bggComplex ℝ hΩ).coreSub (tsd Ω) S₂)
    (T : ℝ) :
    ∃ U, U 0 = U₀ ∧ Evolution.IsClassicalSolution (bggComplex ℝ hΩ).wave (Icc 0 T) 0 U ∧
      (∀ t ∈ Icc 0 T, U t ∈ (bggComplex ℝ hΩ).coreSub (tsd Ω) S₂) ∧
      (∀ t ∈ Icc 0 T, U t ∈ HilbertComplex.totalSub
        (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ Ω)) (tsd Ω) S₂)) ∧
      (∀ V, V 0 = U₀ → Evolution.IsStrongSolution (bggComplex ℝ hΩ).wave (Icc 0 T) 0 V →
        EqOn V U (Icc 0 T)) ∧
      (bggComplex ℝ hΩ).IsReducedSolution (Icc 0 T) (fun t => (U t 1 : L2F ℝ Ω Ix))
        (fun t => (U t 2 : W2B ℝ Ω)) := by
  obtain ⟨U, hU0, hU, hKU, huniq⟩ := ShortHilbertComplex.existsUnique_mem_coreSub hU₀ hK 0 T
  obtain ⟨h0, h1, -⟩ := ShortHilbertComplex.mem_coreSub_iff.1 hK
  have hker : (U 0 1 : L2F ℝ Ω Ix) ∈ (bggComplex ℝ hΩ).d₀†.ker := by
    rw [hU0]; exact tsd_le_ker_bgg hΩ (ShortHilbertComplex.invariantCore₁_le h1)
  have hσ : (U 0 0 : L2 ℝ Ω) = 0 := by rw [hU0]; exact h0
  exact ⟨U, hU0, hU, hKU, fun t ht => ShortHilbertComplex.coreSub_le (hKU t ht), huniq,
    ((bggComplex ℝ hΩ).isReducedSolution_of_isStrongSolution
      (isStrongSolution_realW3 _ hU.1) hσ hker).2⟩

end Feec.Counterexamples.BoundedBGG
