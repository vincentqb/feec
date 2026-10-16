module

public import Feec.Ch4.Existence

/-!
# Restriction to invariant subspaces and constraint propagation (Thesis §4.3)

Core formal content of Thesis §4.3:

* `IsReducing` (`Feec.Foundation.Operators`) packages hypotheses (i) `P_K D(L) ⊆ D(L)` and
  (iii) `L (D(L) ∩ K) ⊆ K` of Thm 4.4: `IsSkewAdjoint.isReducing_iff` (and
  `IsSkewSymm.isReducing_iff` for densely defined skew-symmetric `L`).
* `IsSkewAdjoint.restrictTo` — **Thesis Thm 4.4** (skew-adjoint restriction) for a reducing
  subspace, without the redundant hypothesis (ii) and without a density hypothesis on `D(L)`;
  `skewAdjoint_restrict` and `thm_4_4` are the thesis-shaped corollaries.
* `dense_inter_of_proj_mem` — hypothesis (ii) of Thm 4.4 follows from (i) and density of `D(L)`.
* `map_orthogonal_mem`, `commute_proj` — `L(D(L) ∩ Kᗮ) ⊆ Kᗮ` and `L P_K = P_K L` on `D(L)`.
* `strongSolution_unique` — uniqueness half of **Thesis Thm 4.3** by the energy method.
* `constraint_propagation` — the actual content of **Thesis Cor 4.5**: strong solutions with
  data in `K` stay in `K`. Needs only skew-symmetry (no density, no semigroups).
* `IsSkewAdjoint.exists_strongSolution_restrictTo` (restricted form, as in the thesis),
  `WellPosedExistence.exists_mem_of_isReducing` (ambient form),
  `IsSkewAdjoint.exists_classicalSolution_restrictTo` (with the full `C⁰(D(L̃)) ∩ C¹(K)`
  regularity), all for a reducing `K` and without density hypotheses; `cor_4_5`,
  `cor_4_5_ambient`, `cor_4_5_classical` are the thesis-shaped corollaries.
* `constraint_ker`, `WellPosedExistence.exists_mem_ker` — the §4.3 application `K = ker M`,
  with the corrected hypothesis `M` closed; `isClosed_ker` (`Feec.Foundation.Operators`)
  replaces the false claim that kernels of unbounded operators are
  closed (refuted in `Feec.Ch4.Adjoint`, `exists_not_isClosed_ker`).

Existence of solutions (Thesis Thm 4.3, Hille–Yosida/Stone) is not in Mathlib and enters only
as the explicit hypotheses `WellPosedExistence` / `WellPosedClassical`; uniqueness and
constraint propagation are proved. These hypotheses are satisfiable (bounded skew generators,
via `exp(tA)` and Duhamel's formula): see `Feec.Ch4.Existence`, and here
`wellPosedClassical_bddOp` and `cor_4_5_hypotheses_bddOp_ker` (the full hypothesis set of
Cor 4.5 with `K = ker B`, `B` bounded and commuting with `A`). For skew-adjoint generators the
hypotheses are discharged by Stone's theorem (`Feec.Ch4.Stone`): see `thm_4_3_unconditional`,
`cor_4_5_unconditional`, `cor_4_5_classical_unconditional` and `cor_4_5_ambient_unconditional`
(`Feec.Ch4.StoneApplications`) and `constraint_ker_exists_unconditional`
(`Feec.Ch4.Unconditional`).

## Solution notions (critic item 5)

`IsStrongSolution` (Foundation) only asks for `U t ∈ D(L)` and a pointwise derivative in `X`.
Uniqueness statements proved for it are therefore *stronger* than the thesis'. Existence
statements derived from `WellPosedExistence` are *weaker* than Thm 4.3/Cor 4.5, which assert
`U ∈ C⁰([0,T];D(L)) ∩ C¹([0,T];X)`. To recover the thesis' regularity we introduce
`IsClassicalSolution` (adds continuity of `t ↦ L U(t)` and `t ↦ U'(t)`) and the matching
existence hypothesis `WellPosedClassical`; `cor_4_5_classical` transfers it to `K`.

## References

* [QuennevilleBelair2015], §4.3 (Thm 4.3, Thm 4.4, Cor 4.5, constraints `K = ker M`), and
  §§4.9–4.11 (Props 4.16–4.19, where Cor 4.5 is applied)
* [CazenaveHaraux1998], Prop 4.1.6 and Cor 2.4.9 (the Hille–Yosida corollary cited by the
  thesis for Thm 4.3; enters here only as the hypotheses `WellPosedExistence` /
  `WellPosedClassical`)
* [Pazy1983], §1.10 (Stone's theorem) and Ch. 4 (inhomogeneous initial value problems):
  classical background for the existence hypothesis
-/

open scoped RealInnerProductSpace
open Set

@[expose] public noncomputable section

namespace Feec

section Restriction
open LinearPMap

/-! The statements of this section are real-scalar specializations of the `RCLike` API in
`Feec.ForMathlib.LinearPMap.Reducing`, kept with their old statements. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `L̃ x = L x` for the restriction `L̃ = restrictTo L K h3` of Thesis Thm 4.4. -/
@[simp] theorem restrictTo_apply (L : E →ₗ.[ℝ] E) (K : Submodule ℝ E)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K) (x : (restrictTo L K h3).domain) :
    ((restrictTo L K h3 x : K) : E) = L ⟨((x : K) : E), x.2⟩ := rfl

/-- Thesis Thm 4.4, hypothesis (ii) is redundant: if `D` is dense and `P_K D ⊆ D`, then
`D ∩ K` is dense in `K` (`LinearPMap.dense_inter_of_proj_mem`).

See [QuennevilleBelair2015, Thm 4.4 (ii)].

Correction (redundant hypothesis, not a gap): the thesis lists "`D(L) ∩ K` dense in `K`" as
an independent hypothesis; it is implied by (i) and density of `D(L)`. -/
theorem dense_inter_of_proj_mem (D : Submodule ℝ E) (hD : Dense (D : Set E))
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (hPD : ∀ x ∈ D, K.starProjection x ∈ D) :
    ∀ k ∈ K, k ∈ closure ((D : Set E) ∩ K) :=
  LinearPMap.dense_inter_of_proj_mem D hD K hPD

/-- Domain of the restricted operator `L̃` is dense in `K` (consequence of Thesis Thm 4.4 (i)).
See [QuennevilleBelair2015, Thm 4.4]. -/
theorem dense_restrictTo_domain (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E))
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K) :
    Dense ((restrictTo L K h3).domain : Set K) :=
  LinearPMap.dense_restrict_domain L hD K h1 h3

/-- First step of the proof of Thesis Thm 4.4: `L (D(L) ∩ Kᗮ) ⊆ Kᗮ`.
Only skew-symmetry and density of `D(L)` are used. See [QuennevilleBelair2015, proof of Thm 4.4]. -/
theorem map_orthogonal_mem (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E))
    (hL : IsSkewSymm L) (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    (z : L.domain) (hz : (z : E) ∈ Kᗮ) : L z ∈ Kᗮ :=
  LinearPMap.IsSkewSymmetric.map_orthogonal_mem hL hD h1 h3 z hz

/-- Under the hypotheses of Thesis Thm 4.4, `L` commutes with `P_K` on `D(L)`:
`L (P_K x) = P_K (L x)`. See [QuennevilleBelair2015, Thm 4.4]. -/
theorem commute_proj (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E))
    (hL : IsSkewSymm L) (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K) (x : L.domain) :
    L ⟨K.starProjection (x : E), h1 x⟩ = K.starProjection (L x) :=
  LinearPMap.IsSkewSymmetric.commute_proj hL hD h1 h3 x

/-- Abstract fill of the first itemized hypothesis of Props 4.16/4.18 (used with Cor 4.5):
if a closed subspace `M` lies inside `D`, then `P_{Mᗮ} D ⊆ D`.
See [QuennevilleBelair2015, Props 4.16, 4.18]. -/
theorem proj_orth_mem_of_le (D M : Submodule ℝ E) [M.HasOrthogonalProjection]
    (hMD : M ≤ D) : ∀ x ∈ D, Mᗮ.starProjection x ∈ D :=
  LinearPMap.proj_orthogonal_mem_of_le D M hMD

variable [CompleteSpace E]

omit [CompleteSpace E] in
/-- For a densely defined skew-symmetric `L`, hypotheses (i) `P_K D(L) ⊆ D(L)` and (iii)
`L (D(L) ∩ K) ⊆ K` of Thesis Thm 4.4 make `K` reducing (`commute_proj`). -/
theorem IsSkewSymm.isReducing {L : E →ₗ.[ℝ] E} (hL : IsSkewSymm L) (hD : Dense (L.domain : Set E))
    {K : Submodule ℝ E} [K.HasOrthogonalProjection]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K) : IsReducing L K :=
  LinearPMap.IsSkewSymmetric.isReducing hL hD h1 h3

omit [CompleteSpace E] in
/-- For a densely defined skew-symmetric `L`, `K` is reducing iff hypotheses (i) and (iii) of
Thesis Thm 4.4 hold. -/
theorem IsSkewSymm.isReducing_iff {L : E →ₗ.[ℝ] E} (hL : IsSkewSymm L)
    (hD : Dense (L.domain : Set E)) {K : Submodule ℝ E} [K.HasOrthogonalProjection] :
    IsReducing L K ↔ (∀ x : L.domain, K.starProjection (x : E) ∈ L.domain) ∧
      ∀ x : L.domain, (x : E) ∈ K → L x ∈ K :=
  LinearPMap.IsSkewSymmetric.isReducing_iff hL hD

/-- For skew-adjoint `L`, hypotheses (i) and (iii) of Thesis Thm 4.4 make `K` reducing. -/
theorem IsSkewAdjoint.isReducing {L : E →ₗ.[ℝ] E} (hL : IsSkewAdjoint L)
    {K : Submodule ℝ E} [K.HasOrthogonalProjection]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K) : IsReducing L K :=
  LinearPMap.IsSkewAdjoint.isReducing hL h1 h3

/-- For skew-adjoint `L`, `K` is reducing iff hypotheses (i) and (iii) of Thesis Thm 4.4 hold. -/
theorem IsSkewAdjoint.isReducing_iff {L : E →ₗ.[ℝ] E} (hL : IsSkewAdjoint L)
    {K : Submodule ℝ E} [K.HasOrthogonalProjection] :
    IsReducing L K ↔ (∀ x : L.domain, K.starProjection (x : E) ∈ L.domain) ∧
      ∀ x : L.domain, (x : E) ∈ K → L x ∈ K :=
  LinearPMap.IsSkewAdjoint.isReducing_iff hL

/-- **Skew-adjoint restriction** (Thesis Thm 4.4). If `L` is skew-adjoint and `K` reduces `L`,
then `L̃ = L|_{D(L) ∩ K} : K → K` is skew-adjoint. Specialization of
`LinearPMap.IsSkewAdjoint.restrict`.

Correction: hypothesis (ii) (`D(L) ∩ K` dense in `K`) is dropped — it follows from (i)
(`dense_inter_of_proj_mem`), and so is the density of `D(L)` (`IsSkewAdjoint.dense_domain`).

Thesis: Thm 4.4. See [QuennevilleBelair2015, Thm 4.4]. -/
theorem IsSkewAdjoint.restrictTo {L : E →ₗ.[ℝ] E} (hL : IsSkewAdjoint L)
    {K : Submodule ℝ E} [K.HasOrthogonalProjection] [CompleteSpace K] (hK : IsReducing L K) :
    IsSkewAdjoint (Feec.restrictTo L K hK.mapsTo) :=
  LinearPMap.IsSkewAdjoint.restrict hL hK

/-- **Thesis Thm 4.4** (skew-adjoint restriction), with the hypotheses (i), (iii) and the
(redundant) density of `D(L)`. Corollary of `IsSkewAdjoint.restrictTo`.

See [QuennevilleBelair2015, Thm 4.4]. -/
theorem skewAdjoint_restrict (L : E →ₗ.[ℝ] E) (_hD : Dense (L.domain : Set E))
    (hL : IsSkewAdjoint L)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] [CompleteSpace K]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K) :
    IsSkewAdjoint (restrictTo L K h3) :=
  hL.restrictTo (hL.isReducing h1 h3)

/-- **Thesis Thm 4.4**, literal form with all three itemized hypotheses (the second is unused;
see `IsSkewAdjoint.restrictTo` and `dense_inter_of_proj_mem`).
See [QuennevilleBelair2015, Thm 4.4]. -/
theorem thm_4_4 (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E)) (hL : IsSkewAdjoint L)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] [CompleteSpace K]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (_h2 : ∀ k ∈ K, k ∈ closure ((L.domain : Set E) ∩ K))
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K) :
    IsSkewAdjoint (restrictTo L K h3) :=
  skewAdjoint_restrict L hD hL K h1 h3

end Restriction


/-! ## Evolution: energy uniqueness, constraint propagation, Cor 4.5 -/

section Evolution
open LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Energy lemma, with the derivative given pointwise (wrapper around `energy_zero`). -/
theorem energy_zero_of_exists {e : ℝ → E} {T : ℝ} (hcont : ContinuousOn e (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, ∃ e', HasDerivWithinAt e e' (Ici t) t ∧ ⟪e', e t⟫ = 0)
    (h0 : e 0 = 0) : ∀ t ∈ Icc 0 T, e t = 0 := by
  classical
  let e' : ℝ → E := fun t => if h : t ∈ Ico 0 T then (hd t h).choose else 0
  refine energy_zero (e' := e') hcont (fun t ht => ?_) (fun t ht => ?_) h0
  · simp only [e', ht, ↓reduceDIte]; exact (hd t ht).choose_spec.1
  · simp only [e', ht, ↓reduceDIte]; exact (hd t ht).choose_spec.2

variable {L : E →ₗ.[ℝ] E} {T : ℝ} {U₀ : E} {F U : ℝ → E}

/-- Strong solutions are continuous on `[0,T]`. -/
theorem IsStrongSolution.continuousOn (hU : IsStrongSolution L T U₀ F U) :
    ContinuousOn U (Icc 0 T) :=
  fun t ht => (hU.deriv t ht).continuousWithinAt

/-- Right derivative of a strong solution on `[0,T)`. -/
theorem IsStrongSolution.hasDerivWithinAt_Ici (hU : IsStrongSolution L T U₀ F U) {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt U (L ⟨U t, hU.mem t (Ico_subset_Icc_self ht)⟩ + F t) (Ici t) t :=
  (hU.deriv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

/-- Uniqueness half of **Thesis Thm 4.3**: strong solutions of `U' = L U + F`, `U(0) = U₀`
are unique on `[0,T]` for skew-symmetric `L`.

Remark (alternative elementary proof): the thesis obtains uniqueness from Hille–Yosida [16];
here it is proved directly by the energy method (energy identity
`d/dt ‖U - U'‖² = 2⟪L(U - U'), U - U'⟫ = 0`), which needs neither density nor skew-adjointness.
Since `IsStrongSolution` is weaker than the thesis' solution class
`C⁰(D(L)) ∩ C¹(X)`, this uniqueness statement is stronger than the thesis'.

See [QuennevilleBelair2015, Thm 4.3]; cf. [CazenaveHaraux1998], [Pazy1983, §1.10]. -/
theorem strongSolution_unique (L : E →ₗ.[ℝ] E) (hL : IsSkewSymm L) {T : ℝ} {U₀ : E}
    {F U U' : ℝ → E} (h : IsStrongSolution L T U₀ F U) (h' : IsStrongSolution L T U₀ F U') :
    EqOn U U' (Icc 0 T) :=
  h.unique hL.isDissipative h'

/-- **Constraint propagation** (the real content of **Thesis Cor 4.5**): if `U` is a strong
solution of `U' = L U + F` with `U₀ ∈ K` and `F(t) ∈ K`, and `K` satisfies hypotheses (i) and
(iii) of Thm 4.4, then `U(t) ∈ K` for all `t ∈ [0,T]`.

Remark (simpler route, not a gap): the thesis proof of Cor 4.5 obtains this by applying
Thm 4.3 to `L̃` on `K` (via Thm 4.4) and explicitly identifying the resulting `K`-solution with
the unique `X`-solution. Here it is proved directly by the energy method applied to
`V = (I - P_K) U`: only skew-symmetry of `L` and hypotheses (i), (iii) are used — no density of
`D(L)`, no skew-adjointness, no semigroup theory.

See [QuennevilleBelair2015, Cor 4.5]. -/
theorem constraint_propagation (L : E →ₗ.[ℝ] E) (hL : IsSkewSymm L)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    {T : ℝ} {U₀ : E} {F U : ℝ → E} (hU : IsStrongSolution L T U₀ F U)
    (hU₀ : U₀ ∈ K) (hFK : ∀ t ∈ Icc 0 T, F t ∈ K) : ∀ t ∈ Icc 0 T, U t ∈ K :=
  hU.mem_of_invariant hL.isDissipative h1 h3 hU₀ hFK

/-- Existence, constraint propagation and uniqueness for a reducing subspace (ambient form of
Thesis Cor 4.5): under the existence hypothesis `WellPosedExistence` (standing in for Thm 4.3),
for skew-symmetric `L` and `K` reducing `L`, the problem `U' = L U + F`, `U(0) = U₀ ∈ D(L) ∩ K`,
`F(t) ∈ K`, has a strong solution; it stays in `K` and is unique.

Thesis: Cor 4.5. See [QuennevilleBelair2015, Cor 4.5]. -/
theorem WellPosedExistence.exists_mem_of_isReducing {Adm : (ℝ → E) → Prop}
    (hHY : WellPosedExistence L T Adm) (hL : IsSkewSymm L) {K : Submodule ℝ E}
    [K.HasOrthogonalProjection] (hK : IsReducing L K) (hU₀ : U₀ ∈ L.domain ⊓ K) (hF : Adm F)
    (hFK : ∀ t ∈ Icc 0 T, F t ∈ K) :
    ∃ U, IsStrongSolution L T U₀ F U ∧ (∀ t ∈ Icc 0 T, U t ∈ K) ∧
      ∀ U', IsStrongSolution L T U₀ F U' → EqOn U U' (Icc 0 T) := by
  obtain ⟨U, hU⟩ := hHY U₀ hU₀.1 F hF
  exact ⟨U, hU, constraint_propagation L hL K hK.proj_mem hK.mapsTo hU hU₀.2 hFK,
    fun U' hU' => strongSolution_unique L hL hU hU'⟩

/-- **Thesis Cor 4.5**, ambient form: under the hypotheses of Thm 4.4 and the existence
hypothesis `WellPosedExistence` (standing in for Thm 4.3, Hille–Yosida/Stone, absent from
Mathlib), the problem `U' = L U + F`, `U(0) = U₀ ∈ D(L) ∩ K`, `F(t) ∈ K`, has a strong solution;
it stays in `K` and is unique. Corollary of `WellPosedExistence.exists_mem_of_isReducing`.
Without the existence hypothesis (forcing in `ForcingThm43`):
`Feec.cor_4_5_ambient_unconditional`.

Remark: the thesis states Cor 4.5 for the `K`-valued problem (see `cor_4_5`); this is the
equivalent ambient reformulation, with `U(t) ∈ K` as a conclusion. Hypothesis (ii) of Thm 4.4
is dropped (redundant, `dense_inter_of_proj_mem`). Weaker than the thesis: the existence conclusion is for
`IsStrongSolution` (no `C⁰(D(L)) ∩ C¹` regularity); see `cor_4_5_classical`.

See [QuennevilleBelair2015, Cor 4.5]. -/
theorem cor_4_5_ambient [CompleteSpace E] (L : E →ₗ.[ℝ] E) (_hD : Dense (L.domain : Set E))
    (hL : IsSkewAdjoint L) (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    {T : ℝ} {Adm : (ℝ → E) → Prop} (hHY : WellPosedExistence L T Adm)
    {U₀ : E} (hU₀ : U₀ ∈ L.domain ⊓ K) {F : ℝ → E} (hF : Adm F)
    (hFK : ∀ t ∈ Icc 0 T, F t ∈ K) :
    ∃ U, IsStrongSolution L T U₀ F U ∧ (∀ t ∈ Icc 0 T, U t ∈ K) ∧
      ∀ U', IsStrongSolution L T U₀ F U' → EqOn U U' (Icc 0 T) :=
  hHY.exists_mem_of_isReducing hL.isSkewSymmetric (hL.isReducing h1 h3) hU₀ hF hFK

/-- A `K`-valued strong solution of the restricted problem is an `X`-valued strong solution. -/
theorem IsStrongSolution.coe_restrictTo {K : Submodule ℝ E}
    {h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K} {U₀ : K} {F V : ℝ → K}
    (hV : IsStrongSolution (restrictTo L K h3) T U₀ F V) :
    IsStrongSolution L T U₀ (fun t => F t) (fun t => V t) where
  mem t ht := hV.mem t ht
  deriv t ht := by
    exact K.subtypeL.hasFDerivAt.comp_hasDerivWithinAt t (hV.deriv t ht)
  init := by simp [hV.init]

/-- An `X`-valued strong solution with values in `K` and `K`-valued forcing gives a strong
solution of the restricted problem in `K`. -/
theorem IsStrongSolution.restrictTo {K : Submodule ℝ E} [K.HasOrthogonalProjection]
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K) {U₀ : K} {F : ℝ → K}
    (hU : IsStrongSolution L T U₀ (fun t => F t) U) (hUK : ∀ t ∈ Icc 0 T, U t ∈ K) :
    IsStrongSolution (restrictTo L K h3) T U₀ F (fun t => K.orthogonalProjectionOnto (U t)) := by
  have hcoe : ∀ t ∈ Icc 0 T, ((K.orthogonalProjectionOnto (U t) : K) : E) = U t := fun t ht => by
    rw [← Submodule.starProjection_apply, (K.starProjection_eq_self_iff).2 (hUK t ht)]
  have hmem : ∀ t ∈ Icc 0 T,
      K.orthogonalProjectionOnto (U t) ∈ (Feec.restrictTo L K h3).domain := fun t ht => by
    change ((K.orthogonalProjectionOnto (U t) : K) : E) ∈ L.domain
    rw [hcoe t ht]; exact hU.mem t ht
  refine ⟨hmem, fun t ht => ?_, ?_⟩
  · refine (K.orthogonalProjectionOnto.hasFDerivAt.comp_hasDerivWithinAt t
      (hU.deriv t ht)).congr_deriv (Subtype.ext ?_)
    have hK : L ⟨U t, hU.mem t ht⟩ ∈ K := h3 ⟨U t, hU.mem t ht⟩ (hUK t ht)
    have hK' : L ⟨U t, hU.mem t ht⟩ + (F t : E) ∈ K := K.add_mem hK (F t).2
    simp only [Submodule.coe_add, restrictTo_apply]
    rw [← Submodule.starProjection_apply, (K.starProjection_eq_self_iff).2 hK']
    congr 1
    exact congrArg L (Subtype.ext (hcoe t ht).symm)
  · apply Subtype.ext
    rw [← Submodule.starProjection_apply, hU.init, (K.starProjection_eq_self_iff).2 U₀.2]

/-- Restricted form of Thesis Cor 4.5: for skew-adjoint `L` and `K` reducing `L`,
`L̃ = L|_{D(L) ∩ K}` is skew-adjoint on `K`, and, under the existence hypothesis
`WellPosedExistence`, for `U₀ ∈ D(L̃)` and `K`-valued admissible forcing `F` the restricted
problem `U' = L̃ U + F`, `U(0) = U₀` has a strong solution in `K`, unique among `K`-valued
strong solutions, which coincides on `[0,T]` with every `X`-valued strong solution.

Thesis: Cor 4.5. See [QuennevilleBelair2015, Cor 4.5]. -/
theorem IsSkewAdjoint.exists_strongSolution_restrictTo [CompleteSpace E] (hL : IsSkewAdjoint L)
    {K : Submodule ℝ E} [K.HasOrthogonalProjection] [CompleteSpace K] (hK : IsReducing L K)
    {Adm : (ℝ → E) → Prop} (hHY : WellPosedExistence L T Adm)
    (U₀ : K) (hU₀ : (U₀ : E) ∈ L.domain) (F : ℝ → K) (hF : Adm fun t => (F t : E)) :
    IsSkewAdjoint (Feec.restrictTo L K hK.mapsTo) ∧
    ∃ Ut : ℝ → K, IsStrongSolution (Feec.restrictTo L K hK.mapsTo) T U₀ F Ut ∧
      (∀ V, IsStrongSolution (Feec.restrictTo L K hK.mapsTo) T U₀ F V → EqOn V Ut (Icc 0 T)) ∧
      ∀ U, IsStrongSolution L T U₀ (fun t => F t) U → ∀ t ∈ Icc 0 T, (Ut t : E) = U t := by
  have skew := hL.isSkewSymmetric
  obtain ⟨U, hU⟩ := hHY U₀ hU₀ _ hF
  have hUK := constraint_propagation L skew K hK.proj_mem hK.mapsTo hU U₀.2
    (fun t _ => (F t).2)
  have hUt := hU.restrictTo hK.mapsTo hUK
  refine ⟨hL.restrictTo hK, _, hUt, fun V hV t ht => ?_, fun U' hU' t ht => ?_⟩
  · exact Subtype.ext (strongSolution_unique L skew hV.coe_restrictTo hUt.coe_restrictTo ht)
  · exact strongSolution_unique L skew hUt.coe_restrictTo hU' ht

/-- **Thesis Cor 4.5** (restricted form, as stated in the thesis). Under the hypotheses of
Thm 4.4, `L̃ = L|_{D(L) ∩ K}` is skew-adjoint on `K`, and for `U₀ ∈ D(L̃)` and `K`-valued
admissible forcing `F` the restricted problem `U' = L̃ U + F`, `U(0) = U₀` has a strong solution
in `K`, unique among `K`-valued strong solutions, which coincides on `[0,T]` with every
`X`-valued strong solution of `U' = L U + F`.

Remark (simpler route, not a gap): the thesis proof applies Thm 4.3 to `L̃` on `K` and then
observes that the `K`-solution also solves the `X`-problem. Here existence is taken from the
hypothesis `WellPosedExistence` on `X` (standing in for Thm 4.3; Hille–Yosida is not in Mathlib) and
transferred to `K` by `constraint_propagation`; Thm 4.3 on `K` is not needed. Weaker than the
thesis: the solution class is `IsStrongSolution`; the full regularity is `cor_4_5_classical`.
Corollary of `IsSkewAdjoint.exists_strongSolution_restrictTo`.

See [QuennevilleBelair2015, Cor 4.5 and its proof]. -/
theorem cor_4_5 [CompleteSpace E] (L : E →ₗ.[ℝ] E) (_hD : Dense (L.domain : Set E))
    (hL : IsSkewAdjoint L) (K : Submodule ℝ E) [K.HasOrthogonalProjection] [CompleteSpace K]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    {T : ℝ} {Adm : (ℝ → E) → Prop} (hHY : WellPosedExistence L T Adm)
    (U₀ : K) (hU₀ : (U₀ : E) ∈ L.domain) (F : ℝ → K) (hF : Adm fun t => (F t : E)) :
    IsSkewAdjoint (Feec.restrictTo L K h3) ∧
    ∃ Ut : ℝ → K, IsStrongSolution (Feec.restrictTo L K h3) T U₀ F Ut ∧
      (∀ V, IsStrongSolution (Feec.restrictTo L K h3) T U₀ F V → EqOn V Ut (Icc 0 T)) ∧
      ∀ U, IsStrongSolution L T U₀ (fun t => F t) U → ∀ t ∈ Icc 0 T, (Ut t : E) = U t :=
  hL.exists_strongSolution_restrictTo (hL.isReducing h1 h3) hHY U₀ hU₀ F hF

/-! ### Classical solutions (critic item 5) -/

/-- Solution in the thesis' class `C⁰([0,T]; D(L)) ∩ C¹([0,T]; X)` (Thesis Thm 4.3):
a strong solution with `t ↦ L U(t)` (hence `U` in the graph norm) and `t ↦ U'(t)` continuous on
`[0,T]`. The dependent maps are represented by continuous functions agreeing with them.
See [QuennevilleBelair2015, Thm 4.3]; cf. [Pazy1983, Ch. 4]. -/
structure IsClassicalSolution (L : E →ₗ.[ℝ] E) (T : ℝ) (U₀ : E) (F U : ℝ → E) : Prop
    extends IsStrongSolution L T U₀ F U where
  /-- `U ∈ C⁰([0,T]; D(L))`: `t ↦ L U(t)` is continuous. -/
  graph : ∃ G : ℝ → E, ContinuousOn G (Icc 0 T) ∧ ∀ t (ht : t ∈ Icc 0 T), L ⟨U t, mem t ht⟩ = G t
  /-- `U ∈ C¹([0,T]; X)`: `t ↦ U'(t) = L U(t) + F(t)` is continuous. -/
  c1 : ∃ G : ℝ → E, ContinuousOn G (Icc 0 T) ∧
    ∀ t (ht : t ∈ Icc 0 T), L ⟨U t, mem t ht⟩ + F t = G t

/-- A classical solution in the sense of `Feec.Evolution.IsClassicalSolution` (graph form,
time set `Icc 0 T`). -/
theorem IsClassicalSolution.toEvolution (hU : IsClassicalSolution L T U₀ F U) :
    Evolution.IsClassicalSolution L (Icc 0 T) F U :=
  let ⟨G, hGc, hG⟩ := hU.graph
  Evolution.IsClassicalSolution.iff.2 ⟨hU.mem, hU.deriv, G, hGc, hG⟩

theorem IsClassicalSolution.of_evolution (hU : Evolution.IsClassicalSolution L (Icc 0 T) F U)
    (h0 : U 0 = U₀) (hF : ContinuousOn F (Icc 0 T)) : IsClassicalSolution L T U₀ F U := by
  obtain ⟨hm, hd, G, hGc, hG⟩ := Evolution.IsClassicalSolution.iff.1 hU
  exact ⟨⟨hm, hd, h0⟩, ⟨G, hGc, hG⟩, ⟨G + F, hGc.add hF, fun t ht => by rw [hG t ht]; rfl⟩⟩

/-- `Feec.IsClassicalSolution` is `Feec.Evolution.IsClassicalSolution` on `[0,T]` plus the
initial value, for continuous forcing. -/
theorem isClassicalSolution_iff_evolution (hF : ContinuousOn F (Icc 0 T)) :
    IsClassicalSolution L T U₀ F U ↔ Evolution.IsClassicalSolution L (Icc 0 T) F U ∧ U 0 = U₀ :=
  ⟨fun h => ⟨h.toEvolution, h.init⟩, fun h => .of_evolution h.1 h.2 hF⟩

/-- **Explicit hypothesis standing in for Thesis Thm 4.3** with the thesis' full regularity:
classical solutions exist for initial data in `D(L)` and admissible forcing.
See [QuennevilleBelair2015, Thm 4.3], which cites [CazenaveHaraux1998, Prop 4.1.6, Cor 2.4.9];
cf. [Pazy1983, §1.10, Ch. 4]. -/
def WellPosedClassical (L : E →ₗ.[ℝ] E) (T : ℝ) (Adm : (ℝ → E) → Prop) : Prop :=
  ∀ U₀ ∈ L.domain, ∀ F, Adm F → ∃ U, IsClassicalSolution L T U₀ F U

/-- Classical existence implies strong existence. -/
theorem WellPosedClassical.wellPosedExistence {Adm : (ℝ → E) → Prop}
    (h : WellPosedClassical L T Adm) : WellPosedExistence L T Adm :=
  fun U₀ hU₀ F hF => (h U₀ hU₀ F hF).imp fun _ hU => hU.toIsStrongSolution

/-- Restricted form of Thesis Cor 4.5 with the thesis' regularity: for skew-adjoint `L` and `K`
reducing `L`, if the existence hypothesis provides classical solutions on `X`, the restricted
solution is classical in `K`, i.e. `U ∈ C⁰([0,T]; D(L̃)) ∩ C¹([0,T]; K)`; it is unique and
coincides with the `X`-solution.

Thesis: Cor 4.5. See [QuennevilleBelair2015, Cor 4.5]. -/
theorem IsSkewAdjoint.exists_classicalSolution_restrictTo [CompleteSpace E]
    (hL : IsSkewAdjoint L) {K : Submodule ℝ E} [K.HasOrthogonalProjection] [CompleteSpace K]
    (hK : IsReducing L K) {Adm : (ℝ → E) → Prop} (hHY : WellPosedClassical L T Adm)
    (U₀ : K) (hU₀ : (U₀ : E) ∈ L.domain) (F : ℝ → K) (hF : Adm fun t => (F t : E)) :
    IsSkewAdjoint (Feec.restrictTo L K hK.mapsTo) ∧
    ∃ Ut : ℝ → K, IsClassicalSolution (Feec.restrictTo L K hK.mapsTo) T U₀ F Ut ∧
      (∀ V, IsStrongSolution (Feec.restrictTo L K hK.mapsTo) T U₀ F V → EqOn V Ut (Icc 0 T)) ∧
      ∀ U, IsStrongSolution L T U₀ (fun t => F t) U → ∀ t ∈ Icc 0 T, (Ut t : E) = U t := by
  have skew := hL.isSkewSymmetric
  obtain ⟨U, hU⟩ := hHY U₀ hU₀ _ hF
  have hUK := constraint_propagation L skew K hK.proj_mem hK.mapsTo hU.toIsStrongSolution
    U₀.2 (fun t _ => (F t).2)
  have hUt := hU.toIsStrongSolution.restrictTo hK.mapsTo hUK
  have hcoe : ∀ t ∈ Icc 0 T, ((K.orthogonalProjectionOnto (U t) : K) : E) = U t := fun t ht => by
    rw [← Submodule.starProjection_apply, (K.starProjection_eq_self_iff).2 (hUK t ht)]
  -- `L̃ Ũ(t)` is `P_K (L U(t))`, continuous in `K`
  have hLt : ∀ t (ht : t ∈ Icc 0 T), ((Feec.restrictTo L K hK.mapsTo ⟨_, hUt.mem t ht⟩ : K) : E)
      = L ⟨U t, hU.mem t ht⟩ := fun t ht => congrArg L (Subtype.ext (hcoe t ht))
  obtain ⟨G, hGc, hG⟩ := hU.graph
  obtain ⟨G', hG'c, hG'⟩ := hU.c1
  have hGK : ∀ t (ht : t ∈ Icc 0 T), G t ∈ K := fun t ht =>
    hG t ht ▸ hK.mapsTo ⟨U t, hU.mem t ht⟩ (hUK t ht)
  have hG'K : ∀ t (ht : t ∈ Icc 0 T), G' t ∈ K := fun t ht =>
    hG' t ht ▸ K.add_mem (hK.mapsTo ⟨U t, hU.mem t ht⟩ (hUK t ht)) (F t).2
  refine ⟨hL.restrictTo hK, _,
    ⟨hUt, ⟨fun t => K.orthogonalProjectionOnto (G t),
      K.orthogonalProjectionOnto.continuous.comp_continuousOn hGc, fun t ht => ?_⟩,
      ⟨fun t => K.orthogonalProjectionOnto (G' t),
      K.orthogonalProjectionOnto.continuous.comp_continuousOn hG'c, fun t ht => ?_⟩⟩,
    fun V hV t ht => ?_, fun U' hU' t ht => ?_⟩
  · apply Subtype.ext
    rw [hLt t ht, ← Submodule.starProjection_apply, (K.starProjection_eq_self_iff).2 (hGK t ht),
      hG t ht]
  · apply Subtype.ext
    rw [Submodule.coe_add, hLt t ht, ← Submodule.starProjection_apply,
      (K.starProjection_eq_self_iff).2 (hG'K t ht), hG' t ht]
  · exact Subtype.ext (strongSolution_unique L skew hV.coe_restrictTo hUt.coe_restrictTo ht)
  · exact strongSolution_unique L skew hUt.coe_restrictTo hU' ht


/-- **Thesis Cor 4.5** with the thesis' regularity: if the existence hypothesis provides
classical solutions on `X`, the restricted solution is classical in `K`, i.e.
`U ∈ C⁰([0,T]; D(L̃)) ∩ C¹([0,T]; K)`; it is unique and coincides with the `X`-solution.
Corollary of `IsSkewAdjoint.exists_classicalSolution_restrictTo`.
See [QuennevilleBelair2015, Cor 4.5]. -/
theorem cor_4_5_classical [CompleteSpace E] (L : E →ₗ.[ℝ] E) (_hD : Dense (L.domain : Set E))
    (hL : IsSkewAdjoint L) (K : Submodule ℝ E) [K.HasOrthogonalProjection] [CompleteSpace K]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    {T : ℝ} {Adm : (ℝ → E) → Prop} (hHY : WellPosedClassical L T Adm)
    (U₀ : K) (hU₀ : (U₀ : E) ∈ L.domain) (F : ℝ → K) (hF : Adm fun t => (F t : E)) :
    IsSkewAdjoint (Feec.restrictTo L K h3) ∧
    ∃ Ut : ℝ → K, IsClassicalSolution (Feec.restrictTo L K h3) T U₀ F Ut ∧
      (∀ V, IsStrongSolution (Feec.restrictTo L K h3) T U₀ F V → EqOn V Ut (Icc 0 T)) ∧
      ∀ U, IsStrongSolution L T U₀ (fun t => F t) U → ∀ t ∈ Icc 0 T, (Ut t : E) = U t :=
  hL.exists_classicalSolution_restrictTo (hL.isReducing h1 h3) hHY U₀ hU₀ F hF

end Evolution

/-! ## §4.3 application: constraints `K = ker M` -/

section Kernel
open LinearPMap

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The kernel of a **closed** (possibly unbounded) operator is closed:
`ker M = {x | (x, 0) ∈ Γ(M)}`. Explicit-argument form of `Feec.isClosed_ker`.

Correction (Thesis §4.3): the thesis asserts that the kernel of any not-necessarily-bounded
operator is closed, which is false (zero operator on a dense non-closed domain, see
`Feec.exists_not_isClosed_ker` in `Feec.Ch4.Adjoint`); closedness of `M` is required.
See [QuennevilleBelair2015, §4.3]. -/
theorem isClosed_ker_of_isClosed (M : E →ₗ.[ℝ] Y) (hM : M.IsClosed) :
    IsClosed (M.ker : Set E) :=
  isClosed_ker hM

/-- For closed `M` on a Hilbert space, `ker M` admits an orthogonal projection. -/
theorem hasOrthogonalProjection_ker [CompleteSpace E] (M : E →ₗ.[ℝ] Y) (hM : M.IsClosed) :
    M.ker.HasOrthogonalProjection :=
  LinearPMap.hasOrthogonalProjection_ker M hM

/-- **Constraint propagation for `K = ker M`** (Thesis §4.3, after Cor 4.5): if `M` is closed,
`P_{ker M} D(L) ⊆ D(L)`, `L (D(L) ∩ ker M) ⊆ ker M`, `M U₀ = 0` and `M F(t) = 0`, then every
strong solution satisfies `U(t) ∈ D(M)` and `M U(t) = 0` on `[0,T]`.

Correction: `M` closed is added (the thesis' "kernels of unbounded operators are closed" is
false); the hypotheses on the data, implicit in the thesis, are made explicit. Only
skew-symmetry of `L` is needed. See [QuennevilleBelair2015, §4.3, after Cor 4.5]. -/
theorem constraint_ker [CompleteSpace E] (L : E →ₗ.[ℝ] E) (hL : IsSkewSymm L)
    (M : E →ₗ.[ℝ] Y) (hM : M.IsClosed)
    (h1 : haveI := hasOrthogonalProjection_ker M hM
      ∀ x : L.domain, M.ker.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ M.ker → L x ∈ M.ker)
    {T : ℝ} {U₀ : E} {F U : ℝ → E} (hU : IsStrongSolution L T U₀ F U)
    (hU₀ : U₀ ∈ M.ker) (hFK : ∀ t ∈ Icc 0 T, F t ∈ M.ker) :
    ∀ t ∈ Icc 0 T, ∃ h : U t ∈ M.domain, M ⟨U t, h⟩ = 0 := by
  have := hasOrthogonalProjection_ker M hM
  intro t ht
  obtain ⟨y, hy, hy0⟩ :=
    LinearPMap.mem_ker_iff.1 (constraint_propagation L hL _ h1 h3 hU hU₀ hFK t ht)
  refine ⟨by rw [hy]; exact y.2, ?_⟩
  rw [show (⟨U t, _⟩ : M.domain) = y from Subtype.ext hy]
  exact hy0

/-- Constraint propagation into `ker M` with existence: for skew-symmetric `L`, closed `M`, the
hypotheses (i) and (iii) of Thesis Thm 4.4 for `K = ker M`, and the existence hypothesis
standing in for Thm 4.3, the unique strong solution satisfies `M U(t) = 0` on `[0,T]`.

Thesis: §4.3. See [QuennevilleBelair2015, §4.3, Thm 4.3, Cor 4.5]. -/
theorem WellPosedExistence.exists_mem_ker [CompleteSpace E] {L : E →ₗ.[ℝ] E} {T : ℝ}
    {Adm : (ℝ → E) → Prop} (hHY : WellPosedExistence L T Adm) (hL : IsSkewSymm L)
    (M : E →ₗ.[ℝ] Y) (hM : M.IsClosed)
    (h1 : haveI := hasOrthogonalProjection_ker M hM
      ∀ x : L.domain, M.ker.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ M.ker → L x ∈ M.ker)
    {U₀ : E} (hU₀ : U₀ ∈ L.domain ⊓ M.ker) {F : ℝ → E} (hF : Adm F)
    (hFK : ∀ t ∈ Icc 0 T, F t ∈ M.ker) :
    ∃ U, IsStrongSolution L T U₀ F U ∧ (∀ t ∈ Icc 0 T, ∃ h : U t ∈ M.domain, M ⟨U t, h⟩ = 0) ∧
      ∀ U', IsStrongSolution L T U₀ F U' → EqOn U U' (Icc 0 T) := by
  obtain ⟨U, hU⟩ := hHY U₀ hU₀.1 F hF
  exact ⟨U, hU, constraint_ker L hL M hM h1 h3 hU hU₀.2 hFK,
    fun U' hU' => strongSolution_unique L hL hU hU'⟩

/-- **Thesis §4.3** with existence: under the hypotheses of Thm 4.4 for `K = ker M` (`M` closed)
and the existence hypothesis standing in for Thm 4.3, the unique strong solution satisfies the
constraint `M U(t) = 0` on `[0,T]`. Corollary of `WellPosedExistence.exists_mem_ker`.
See [QuennevilleBelair2015, §4.3, Thm 4.3, Cor 4.5]. -/
theorem constraint_ker_exists [CompleteSpace E] (L : E →ₗ.[ℝ] E)
    (_hD : Dense (L.domain : Set E)) (hL : IsSkewAdjoint L)
    (M : E →ₗ.[ℝ] Y) (hM : M.IsClosed)
    (h1 : haveI := hasOrthogonalProjection_ker M hM
      ∀ x : L.domain, M.ker.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ M.ker → L x ∈ M.ker)
    {T : ℝ} {Adm : (ℝ → E) → Prop} (hHY : WellPosedExistence L T Adm)
    {U₀ : E} (hU₀ : U₀ ∈ L.domain ⊓ M.ker) {F : ℝ → E} (hF : Adm F)
    (hFK : ∀ t ∈ Icc 0 T, F t ∈ M.ker) :
    ∃ U, IsStrongSolution L T U₀ F U ∧ (∀ t ∈ Icc 0 T, ∃ h : U t ∈ M.domain, M ⟨U t, h⟩ = 0) ∧
      ∀ U', IsStrongSolution L T U₀ F U' → EqOn U U' (Icc 0 T) :=
  hHY.exists_mem_ker hL.isSkewSymmetric M hM h1 h3 hU₀ hF hFK

end Kernel

/-! ## Non-vacuity of the Cor 4.5 hypotheses (bounded generators) -/

section Witness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Non-vacuity of `WellPosedClassical`** (the hypothesis of `cor_4_5_classical`, standing in
for Thesis Thm 4.3 with its `C⁰(D(L)) ∩ C¹(X)` regularity): for every bounded `A` it holds with
the admissible class `C([0,T]; E)`. Built from the Duhamel solutions of
`Feec.exists_classical_solution_bddOp`. Cf. [QuennevilleBelair2015, Thm 4.3]; for bounded
generators this is the uniformly continuous case of [Pazy1983, §1.1]. -/
theorem wellPosedClassical_bddOp [CompleteSpace E] (A : E →L[ℝ] E) (T : ℝ) :
    WellPosedClassical (bddOp A) T (fun F => ContinuousOn F (Icc 0 T)) := by
  intro U₀ _ F hF
  by_cases hT : 0 ≤ T
  · obtain ⟨U, hU, -, hAU⟩ := exists_classical_solution_bddOp A hT U₀ hF
    exact ⟨U, hU, ⟨fun t => A (U t), hAU.continuousOn, fun _ _ => rfl⟩,
      ⟨fun t => A (U t) + F t, hAU.continuousOn.add hF, fun _ _ => rfl⟩⟩
  · have hE : Icc (0 : ℝ) T = ∅ := Icc_eq_empty (by linarith)
    exact ⟨fun _ => U₀, ⟨fun t ht => by simp [hE] at ht, fun t ht => by simp [hE] at ht, rfl⟩,
      ⟨0, by simp [hE], fun t ht => by simp [hE] at ht⟩,
      ⟨0, by simp [hE], fun t ht => by simp [hE] at ht⟩⟩

/-- **Non-vacuity of the full hypothesis set of Thesis Cor 4.5** (for `cor_4_5_ambient`,
`cor_4_5`, `cor_4_5_classical`): for a bounded skew `A` and a bounded `B` commuting with `A`,
the constraint space `K = ker B` (closed, so it has an orthogonal projection) satisfies (i) and
(iii) of Thm 4.4, `bddOp A` is densely defined and skew-adjoint, and `WellPosedClassical` holds
with admissible class `C([0,T]; E)`. `K` is nontrivial whenever `B` is neither `0` nor injective
(e.g. `B = A` when `A` has a nontrivial kernel). Cf. [QuennevilleBelair2015, Thm 4.4, Cor 4.5]. -/
theorem cor_4_5_hypotheses_bddOp_ker [CompleteSpace E] (A B : E →L[ℝ] E)
    (hA : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) (hAB : A.comp B = B.comp A) (T : ℝ) :
    ∃ _ : (LinearMap.ker (B : E →ₗ[ℝ] E)).HasOrthogonalProjection,
      Dense ((bddOp A).domain : Set E) ∧ IsSkewAdjoint (bddOp A) ∧
      (∀ x : (bddOp A).domain, (LinearMap.ker (B : E →ₗ[ℝ] E)).starProjection (x : E) ∈ (bddOp A).domain) ∧
      (∀ x : (bddOp A).domain, (x : E) ∈ LinearMap.ker (B : E →ₗ[ℝ] E) → bddOp A x ∈ LinearMap.ker (B : E →ₗ[ℝ] E)) ∧
      WellPosedClassical (bddOp A) T (fun F => ContinuousOn F (Icc 0 T)) := by
  have hc : IsClosed (LinearMap.ker (B : E →ₗ[ℝ] E) : Set E) := B.isClosed_ker
  have : CompleteSpace (LinearMap.ker (B : E →ₗ[ℝ] E)) := hc.completeSpace_coe
  refine ⟨inferInstance, dense_bddOp_domain A, isSkewAdjoint_bddOp A hA, fun _ => trivial,
    fun x hx => ?_, wellPosedClassical_bddOp A T⟩
  rw [LinearMap.mem_ker] at hx ⊢
  have := congrArg (fun C : E →L[ℝ] E => C (x : E)) hAB
  simp only [ContinuousLinearMap.comp_apply] at this
  change B (A (x : E)) = 0
  rw [← this, show B (x : E) = 0 from hx, map_zero]

end Witness

end Feec
