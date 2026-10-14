module

public import Feec.Ch4.Existence

/-!
# Restriction to invariant subspaces and constraint propagation (Thesis §4.3)

Core formal content of Thesis §4.3:

* `skewAdjoint_restrict` — **Thesis Thm 4.4** (skew-adjoint restriction), without the
  redundant density hypothesis (ii); `thm_4_4` is the literal statement.
* `dense_inter_of_proj_mem` — hypothesis (ii) of Thm 4.4 follows from (i) and density of `D(L)`.
* `map_orthogonal_mem`, `commute_proj` — `L(D(L) ∩ Kᗮ) ⊆ Kᗮ` and `L P_K = P_K L` on `D(L)`.
* `strongSolution_unique` — uniqueness half of **Thesis Thm 4.3** by the energy method.
* `constraint_propagation` — the actual content of **Thesis Cor 4.5**: strong solutions with
  data in `K` stay in `K`. Needs only skew-symmetry (no density, no semigroups).
* `cor_4_5` (restricted form, as in the thesis), `cor_4_5_ambient` (ambient form),
  `cor_4_5_classical` (with the full `C⁰(D(L̃)) ∩ C¹(K)` regularity).
* `constraint_ker` — the §4.3 application `K = ker M`, with the corrected hypothesis `M` closed;
  `isClosed_ker_of_isClosed` replaces the false claim that kernels of unbounded operators are
  closed (refuted in `Feec.Ch4.Adjoint`, `exists_not_isClosed_ker`).

Existence of solutions (Thesis Thm 4.3, Hille–Yosida/Stone) is not in Mathlib and enters only
as the explicit hypotheses `WellPosedExistence` / `WellPosedClassical`; uniqueness and
constraint propagation are proved. These hypotheses are satisfiable (bounded skew generators,
via `exp(tA)` and Duhamel's formula): see `Feec.Ch4.Existence`, and here
`wellPosedClassical_bddOp` and `cor_4_5_hypotheses_bddOp_ker` (the full hypothesis set of
Cor 4.5 with `K = ker B`, `B` bounded and commuting with `A`).

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `L̃ x = L x` for the restriction `L̃ = restrictTo L K h3` of Thesis Thm 4.4. -/
@[simp] theorem restrictTo_apply (L : E →ₗ.[ℝ] E) (K : Submodule ℝ E)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K) (x : (restrictTo L K h3).domain) :
    ((restrictTo L K h3 x : K) : E) = L ⟨((x : K) : E), x.2⟩ := rfl

/-- Thesis Thm 4.4, hypothesis (ii) is redundant: if `D` is dense and `P_K D ⊆ D`, then
`D ∩ K` is dense in `K`.

See [QuennevilleBelair2015, Thm 4.4 (ii)].

Correction (redundant hypothesis, not a gap): the thesis lists "`D(L) ∩ K` dense in `K`" as
an independent hypothesis; it is implied by (i) and density of `D(L)`. -/
theorem dense_inter_of_proj_mem (D : Submodule ℝ E) (hD : Dense (D : Set E))
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (hPD : ∀ x ∈ D, K.starProjection x ∈ D) :
    ∀ k ∈ K, k ∈ closure ((D : Set E) ∩ K) := by
  intro k hk
  have hcont : Continuous K.starProjection := K.starProjection.continuous
  have : K.starProjection k ∈ closure (K.starProjection '' (D : Set E)) :=
    map_mem_closure hcont (hD k) (fun x hx => mem_image_of_mem _ hx)
  rw [(K.starProjection_eq_self_iff).2 hk] at this
  refine closure_mono ?_ this
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨hPD x hx, K.starProjection_apply_mem x⟩

/-- Domain of the restricted operator `L̃` is dense in `K` (consequence of Thesis Thm 4.4 (i)).
See [QuennevilleBelair2015, Thm 4.4]. -/
theorem dense_restrictTo_domain (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E))
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K) :
    Dense ((restrictTo L K h3).domain : Set K) := by
  have hd : Dense ((K.orthogonalProjectionOnto) '' (L.domain : Set E)) :=
    (Function.Surjective.denseRange (f := (K.orthogonalProjectionOnto : E → K))
      (fun k : K => ⟨(k : E), K.orthogonalProjectionOnto_mem_subspace_eq_self k⟩)).dense_image
      (K.orthogonalProjectionOnto).continuous hD
  refine hd.mono ?_
  rintro _ ⟨x, hx, rfl⟩
  change ((K.orthogonalProjectionOnto x : K) : E) ∈ L.domain
  rw [← Submodule.starProjection_apply]
  exact h1 ⟨x, hx⟩

/-- First step of the proof of Thesis Thm 4.4: `L (D(L) ∩ Kᗮ) ⊆ Kᗮ`.
Only skew-symmetry and density of `D(L)` are used. See [QuennevilleBelair2015, proof of Thm 4.4]. -/
theorem map_orthogonal_mem (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E))
    (hL : IsSkewSymm L) (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    (z : L.domain) (hz : (z : E) ∈ Kᗮ) : L z ∈ Kᗮ := by
  have hDt := dense_restrictTo_domain L hD K h1 h3
  have hf : Continuous (fun k : K => ⟪(k : E), L z⟫) :=
    continuous_subtype_val.inner continuous_const
  have := Continuous.ext_on hDt hf continuous_const (fun v hv => by
    have hv' : ((v : K) : E) ∈ L.domain := hv
    have hLv : L ⟨v, hv'⟩ ∈ K := h3 ⟨v, hv'⟩ v.2
    have e := hL z ⟨v, hv'⟩
    have e0 : ⟪(z : E), L ⟨v, hv'⟩⟫ = 0 := by
      rw [real_inner_comm]; exact Submodule.inner_right_of_mem_orthogonal hLv hz
    change ⟪((v : K) : E), L z⟫ = 0
    rw [real_inner_comm, e, e0, neg_zero])
  exact (Submodule.mem_orthogonal' K _).2 fun k hk => by
    rw [real_inner_comm]; exact congrFun this ⟨k, hk⟩

/-- Under the hypotheses of Thesis Thm 4.4, `L` commutes with `P_K` on `D(L)`:
`L (P_K x) = P_K (L x)`. (Stated in the audit's corrected Thm 4.4; uses skew-symmetry and
density of `D(L)`.) See [QuennevilleBelair2015, Thm 4.4]. -/
theorem commute_proj (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E))
    (hL : IsSkewSymm L) (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K) (x : L.domain) :
    L ⟨K.starProjection (x : E), h1 x⟩ = K.starProjection (L x) := by
  have hz : (x : E) - K.starProjection x ∈ L.domain := L.domain.sub_mem x.2 (h1 x)
  have hsplit : L x = L ⟨_, h1 x⟩ + L ⟨_, hz⟩ := by
    rw [← LinearPMap.map_add]; congr 1; ext; simp
  have hK : L ⟨_, h1 x⟩ ∈ K := h3 ⟨_, h1 x⟩ (K.starProjection_apply_mem _)
  have hKp : L ⟨_, hz⟩ ∈ Kᗮ :=
    map_orthogonal_mem L hD hL K h1 h3 ⟨_, hz⟩ (K.sub_starProjection_mem_orthogonal _)
  rw [hsplit, _root_.map_add, (K.starProjection_eq_self_iff).2 hK,
    (Submodule.starProjection_apply_eq_zero_iff K).2 hKp, add_zero]

/-- Abstract fill of the first itemized hypothesis of Props 4.16/4.18 (used with Cor 4.5):
if a closed subspace `M` lies inside `D`, then `P_{Mᗮ} D ⊆ D`.
See [QuennevilleBelair2015, Props 4.16, 4.18]. -/
theorem proj_orth_mem_of_le (D M : Submodule ℝ E) [M.HasOrthogonalProjection]
    (hMD : M ≤ D) : ∀ x ∈ D, Mᗮ.starProjection x ∈ D := by
  intro x hx
  have h : Mᗮ.starProjection x = x - M.starProjection x :=
    eq_sub_of_add_eq' (M.starProjection_add_starProjection_orthogonal x)
  rw [h]; exact D.sub_mem hx (hMD (M.starProjection_apply_mem x))

variable [CompleteSpace E]

/-- **Thesis Thm 4.4** (skew-adjoint restriction). Let `L` be skew-adjoint with dense domain and
`K` a closed subspace with (i) `P_K D(L) ⊆ D(L)` and (iii) `L (D(L) ∩ K) ⊆ K`. Then
`L̃ = L|_{D(L) ∩ K} : K → K` is skew-adjoint.

Correction: hypothesis (ii) (`D(L) ∩ K` dense in `K`) is dropped — it follows from (i)
(`dense_inter_of_proj_mem`). The step-3 estimate `|⟨u, L w⟩| ≤ C‖P_K w‖` is replaced by the exact
identity `⟨L̃* u, w⟩ = ⟨u, L w⟩` for `w ∈ D(L)`, giving `u ∈ D(L*) = D(L)` with explicit witness.

See [QuennevilleBelair2015, Thm 4.4]. -/
theorem skewAdjoint_restrict (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E))
    (hL : IsSkewAdjoint L)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] [CompleteSpace K]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K) :
    IsSkewAdjoint (restrictTo L K h3) := by
  set Lt := restrictTo L K h3 with hLt
  have skew := hL.isSkewSymm hD
  have hDt : Dense (Lt.domain : Set K) := dense_restrictTo_domain L hD K h1 h3
  have hform : Lt.IsFormalAdjoint (-Lt) := by
    intro x y
    rw [LinearPMap.neg_apply, Submodule.coe_inner, Submodule.coe_inner, Submodule.coe_neg,
      inner_neg_right]
    exact skew ⟨_, x.2⟩ ⟨_, y.2⟩
  have hle : -Lt ≤ Lt† := hform.le_adjoint hDt
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 ?_)).symm
  intro u hu
  have key : ∀ x : L.domain, ⟪((Lt† ⟨u, hu⟩ : K) : E), (x : E)⟫ = ⟪(u : E), L x⟫ := by
    intro x
    set px : Lt.domain := ⟨K.orthogonalProjectionOnto x, by
      change ((K.orthogonalProjectionOnto x : K) : E) ∈ L.domain
      rw [← Submodule.starProjection_apply]; exact h1 x⟩
    have hadj := LinearPMap.adjoint_isFormalAdjoint hDt ⟨u, hu⟩ px
    have hz : (x : E) - K.starProjection x ∈ L.domain := L.domain.sub_mem x.2 (h1 x)
    have hzK : (x : E) - K.starProjection x ∈ Kᗮ := K.sub_starProjection_mem_orthogonal _
    have hsplit : L x = L ⟨_, h1 x⟩ + L ⟨_, hz⟩ := by
      rw [← LinearPMap.map_add]; congr 1; ext; simp
    have e1 : ⟪(u : E), L ⟨_, hz⟩⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal u.2
        (map_orthogonal_mem L hD skew K h1 h3 ⟨_, hz⟩ hzK)
    have e2 : ⟪((Lt† ⟨u, hu⟩ : K) : E), (x : E)⟫
        = ⟪((Lt† ⟨u, hu⟩ : K) : E), K.starProjection (x : E)⟫ := by
      rw [← sub_eq_zero, ← inner_sub_right]
      exact Submodule.inner_right_of_mem_orthogonal (Lt† ⟨u, hu⟩).2 hzK
    rw [e2, hsplit, inner_add_right, e1, add_zero]
    have := hadj
    simp only [Submodule.coe_inner] at this
    convert this using 2 <;> rfl
  have hmem : (u : E) ∈ L†.domain := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  rw [hL] at hmem
  exact hmem

/-- **Thesis Thm 4.4**, literal form with all three itemized hypotheses (the second is unused;
see `skewAdjoint_restrict` and `dense_inter_of_proj_mem`). See [QuennevilleBelair2015, Thm 4.4]. -/
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

/-- Skew-symmetry gives `⟪L x, x⟫ = 0` (the energy identity). -/
theorem IsSkewSymm.inner_self {L : E →ₗ.[ℝ] E} (hL : IsSkewSymm L) (x : L.domain) :
    ⟪L x, (x : E)⟫ = 0 := by
  have h := hL x x
  have h2 : ⟪(x : E), L x⟫ = ⟪L x, (x : E)⟫ := real_inner_comm _ _
  linarith

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
    EqOn U U' (Icc 0 T) := by
  have hd : ∀ t ∈ Ico 0 T, ∃ e', HasDerivWithinAt (fun t => U t - U' t) e' (Ici t) t ∧
      ⟪e', U t - U' t⟫ = 0 := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    have hm : U t - U' t ∈ L.domain := L.domain.sub_mem (h.mem t ht') (h'.mem t ht')
    refine ⟨L ⟨U t - U' t, hm⟩, ?_, hL.inner_self ⟨_, hm⟩⟩
    have hsub : (⟨U t - U' t, hm⟩ : L.domain) = ⟨U t, h.mem t ht'⟩ - ⟨U' t, h'.mem t ht'⟩ := rfl
    rw [hsub, LinearPMap.map_sub]
    convert (h.hasDerivWithinAt_Ici ht).sub (h'.hasDerivWithinAt_Ici ht) using 1
    abel
  intro t ht
  exact sub_eq_zero.1 (energy_zero_of_exists (h.continuousOn.sub h'.continuousOn) hd
    (by simp [h.init, h'.init]) t ht)

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
    (hU₀ : U₀ ∈ K) (hFK : ∀ t ∈ Icc 0 T, F t ∈ K) : ∀ t ∈ Icc 0 T, U t ∈ K := by
  set P := K.starProjection
  have hd : ∀ t ∈ Ico 0 T, ∃ e', HasDerivWithinAt (fun t => U t - P (U t)) e' (Ici t) t ∧
      ⟪e', U t - P (U t)⟫ = 0 := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    have hD := hU.hasDerivWithinAt_Ici ht
    refine ⟨_, hD.sub (P.hasFDerivAt.comp_hasDerivWithinAt t hD), ?_⟩
    have hVperp : U t - P (U t) ∈ Kᗮ := K.sub_starProjection_mem_orthogonal _
    have hPu : P (U t) ∈ L.domain := h1 ⟨U t, hU.mem t ht'⟩
    have hVt : U t - P (U t) ∈ L.domain := L.domain.sub_mem (hU.mem t ht') hPu
    have hsplit : L ⟨U t, hU.mem t ht'⟩ = L ⟨P (U t), hPu⟩ + L ⟨U t - P (U t), hVt⟩ := by
      rw [← LinearPMap.map_add]; congr 1; ext; simp
    have e1 : ⟪P (L ⟨U t, hU.mem t ht'⟩ + F t), U t - P (U t)⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (K.starProjection_apply_mem _) hVperp
    have e2 : ⟪L ⟨P (U t), hPu⟩, U t - P (U t)⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (h3 _ (K.starProjection_apply_mem _)) hVperp
    have e3 : ⟪F t, U t - P (U t)⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hFK t ht') hVperp
    have e4 : ⟪L ⟨U t - P (U t), hVt⟩, U t - P (U t)⟫ = 0 := hL.inner_self ⟨_, hVt⟩
    rw [inner_sub_left, e1, sub_zero, inner_add_left, e3, add_zero, hsplit, inner_add_left,
      e2, e4, add_zero]
  have hV := energy_zero_of_exists
    (hU.continuousOn.sub (P.continuous.comp_continuousOn hU.continuousOn)) hd
    (by simp [P, hU.init, (K.starProjection_eq_self_iff).2 hU₀])
  intro t ht
  rw [sub_eq_zero.1 (hV t ht)]
  exact K.starProjection_apply_mem _

/-- **Thesis Cor 4.5**, ambient form: under the hypotheses of Thm 4.4 and the existence
hypothesis `WellPosedExistence` (standing in for Thm 4.3, Hille–Yosida/Stone, absent from
Mathlib), the problem `U' = L U + F`, `U(0) = U₀ ∈ D(L) ∩ K`, `F(t) ∈ K`, has a strong solution;
it stays in `K` and is unique.

Remark: the thesis states Cor 4.5 for the `K`-valued problem (see `cor_4_5`); this is the
equivalent ambient reformulation, with `U(t) ∈ K` as a conclusion. Hypothesis (ii) of Thm 4.4
is dropped (redundant, `dense_inter_of_proj_mem`). Weaker than the thesis: the existence conclusion is for
`IsStrongSolution` (no `C⁰(D(L)) ∩ C¹` regularity); see `cor_4_5_classical`.

See [QuennevilleBelair2015, Cor 4.5]. -/
theorem cor_4_5_ambient [CompleteSpace E] (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E))
    (hL : IsSkewAdjoint L) (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    {T : ℝ} {Adm : (ℝ → E) → Prop} (hHY : WellPosedExistence L T Adm)
    {U₀ : E} (hU₀ : U₀ ∈ L.domain ⊓ K) {F : ℝ → E} (hF : Adm F)
    (hFK : ∀ t ∈ Icc 0 T, F t ∈ K) :
    ∃ U, IsStrongSolution L T U₀ F U ∧ (∀ t ∈ Icc 0 T, U t ∈ K) ∧
      ∀ U', IsStrongSolution L T U₀ F U' → EqOn U U' (Icc 0 T) := by
  have skew := hL.isSkewSymm hD
  obtain ⟨U, hU⟩ := hHY U₀ hU₀.1 F hF
  exact ⟨U, hU, constraint_propagation L skew K h1 h3 hU hU₀.2 hFK,
    fun U' hU' => strongSolution_unique L skew hU hU'⟩

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

See [QuennevilleBelair2015, Cor 4.5 and its proof]. -/
theorem cor_4_5 [CompleteSpace E] (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E))
    (hL : IsSkewAdjoint L) (K : Submodule ℝ E) [K.HasOrthogonalProjection] [CompleteSpace K]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    {T : ℝ} {Adm : (ℝ → E) → Prop} (hHY : WellPosedExistence L T Adm)
    (U₀ : K) (hU₀ : (U₀ : E) ∈ L.domain) (F : ℝ → K) (hF : Adm fun t => (F t : E)) :
    IsSkewAdjoint (Feec.restrictTo L K h3) ∧
    ∃ Ut : ℝ → K, IsStrongSolution (Feec.restrictTo L K h3) T U₀ F Ut ∧
      (∀ V, IsStrongSolution (Feec.restrictTo L K h3) T U₀ F V → EqOn V Ut (Icc 0 T)) ∧
      ∀ U, IsStrongSolution L T U₀ (fun t => F t) U → ∀ t ∈ Icc 0 T, (Ut t : E) = U t := by
  have skew := hL.isSkewSymm hD
  obtain ⟨U, hU⟩ := hHY U₀ hU₀ _ hF
  have hUK := constraint_propagation L skew K h1 h3 hU U₀.2 (fun t _ => (F t).2)
  have hUt := hU.restrictTo h3 hUK
  refine ⟨skewAdjoint_restrict L hD hL K h1 h3, _, hUt, fun V hV t ht => ?_, fun U' hU' t ht => ?_⟩
  · exact Subtype.ext (strongSolution_unique L skew hV.coe_restrictTo hUt.coe_restrictTo ht)
  · exact strongSolution_unique L skew hUt.coe_restrictTo hU' ht

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

/-- **Thesis Cor 4.5** with the thesis' regularity: if the existence hypothesis provides
classical solutions on `X`, the restricted solution is classical in `K`, i.e.
`U ∈ C⁰([0,T]; D(L̃)) ∩ C¹([0,T]; K)`; it is unique and coincides with the `X`-solution.
See [QuennevilleBelair2015, Cor 4.5]. -/
theorem cor_4_5_classical [CompleteSpace E] (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E))
    (hL : IsSkewAdjoint L) (K : Submodule ℝ E) [K.HasOrthogonalProjection] [CompleteSpace K]
    (h1 : ∀ x : L.domain, K.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K)
    {T : ℝ} {Adm : (ℝ → E) → Prop} (hHY : WellPosedClassical L T Adm)
    (U₀ : K) (hU₀ : (U₀ : E) ∈ L.domain) (F : ℝ → K) (hF : Adm fun t => (F t : E)) :
    IsSkewAdjoint (Feec.restrictTo L K h3) ∧
    ∃ Ut : ℝ → K, IsClassicalSolution (Feec.restrictTo L K h3) T U₀ F Ut ∧
      (∀ V, IsStrongSolution (Feec.restrictTo L K h3) T U₀ F V → EqOn V Ut (Icc 0 T)) ∧
      ∀ U, IsStrongSolution L T U₀ (fun t => F t) U → ∀ t ∈ Icc 0 T, (Ut t : E) = U t := by
  have skew := hL.isSkewSymm hD
  obtain ⟨U, hU⟩ := hHY U₀ hU₀ _ hF
  have hUK := constraint_propagation L skew K h1 h3 hU.toIsStrongSolution U₀.2
    (fun t _ => (F t).2)
  have hUt := hU.toIsStrongSolution.restrictTo h3 hUK
  have hcoe : ∀ t ∈ Icc 0 T, ((K.orthogonalProjectionOnto (U t) : K) : E) = U t := fun t ht => by
    rw [← Submodule.starProjection_apply, (K.starProjection_eq_self_iff).2 (hUK t ht)]
  -- `L̃ Ũ(t)` is `P_K (L U(t))`, continuous in `K`
  have hLt : ∀ t (ht : t ∈ Icc 0 T), ((Feec.restrictTo L K h3 ⟨_, hUt.mem t ht⟩ : K) : E)
      = L ⟨U t, hU.mem t ht⟩ := fun t ht => congrArg L (Subtype.ext (hcoe t ht))
  obtain ⟨G, hGc, hG⟩ := hU.graph
  obtain ⟨G', hG'c, hG'⟩ := hU.c1
  have hGK : ∀ t (ht : t ∈ Icc 0 T), G t ∈ K := fun t ht =>
    hG t ht ▸ h3 ⟨U t, hU.mem t ht⟩ (hUK t ht)
  have hG'K : ∀ t (ht : t ∈ Icc 0 T), G' t ∈ K := fun t ht =>
    hG' t ht ▸ K.add_mem (h3 ⟨U t, hU.mem t ht⟩ (hUK t ht)) (F t).2
  refine ⟨skewAdjoint_restrict L hD hL K h1 h3, _,
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

end Evolution

/-! ## §4.3 application: constraints `K = ker M` -/

section Kernel
open LinearPMap

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The kernel of a **closed** (possibly unbounded) operator is closed:
`ker M = {x | (x, 0) ∈ Γ(M)}`.

Correction (Thesis §4.3): the thesis asserts that the kernel of any not-necessarily-bounded
operator is closed, which is false (zero operator on a dense non-closed domain, see
`Feec.exists_not_isClosed_ker` in `Feec.Ch4.Adjoint`); closedness of `M` is required.
See [QuennevilleBelair2015, §4.3]. -/
theorem isClosed_ker_of_isClosed (M : E →ₗ.[ℝ] Y) (hM : M.IsClosed) :
    IsClosed (M.ker : Set E) := by
  have : (M.ker : Set E) = (fun x => (x, (0 : Y))) ⁻¹' (M.graph : Set (E × Y)) := by
    ext x
    simp only [SetLike.mem_coe, LinearPMap.mem_ker_iff, mem_preimage, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨y, rfl, hy⟩; exact ⟨y, rfl, hy⟩
    · rintro ⟨y, hy, hy0⟩; exact ⟨y, hy.symm, hy0⟩
  rw [this]
  exact IsClosed.preimage (continuous_id.prodMk continuous_const) hM

/-- For closed `M` on a Hilbert space, `ker M` admits an orthogonal projection. -/
theorem hasOrthogonalProjection_ker [CompleteSpace E] (M : E →ₗ.[ℝ] Y) (hM : M.IsClosed) :
    M.ker.HasOrthogonalProjection := by
  have : CompleteSpace M.ker := (isClosed_ker_of_isClosed M hM).completeSpace_coe
  infer_instance

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

/-- **Thesis §4.3** with existence: under the hypotheses of Thm 4.4 for `K = ker M` (`M` closed)
and the existence hypothesis standing in for Thm 4.3, the unique strong solution satisfies the
constraint `M U(t) = 0` on `[0,T]`. See [QuennevilleBelair2015, §4.3, Thm 4.3, Cor 4.5]. -/
theorem constraint_ker_exists [CompleteSpace E] (L : E →ₗ.[ℝ] E)
    (hD : Dense (L.domain : Set E)) (hL : IsSkewAdjoint L)
    (M : E →ₗ.[ℝ] Y) (hM : M.IsClosed)
    (h1 : haveI := hasOrthogonalProjection_ker M hM
      ∀ x : L.domain, M.ker.starProjection (x : E) ∈ L.domain)
    (h3 : ∀ x : L.domain, (x : E) ∈ M.ker → L x ∈ M.ker)
    {T : ℝ} {Adm : (ℝ → E) → Prop} (hHY : WellPosedExistence L T Adm)
    {U₀ : E} (hU₀ : U₀ ∈ L.domain ⊓ M.ker) {F : ℝ → E} (hF : Adm F)
    (hFK : ∀ t ∈ Icc 0 T, F t ∈ M.ker) :
    ∃ U, IsStrongSolution L T U₀ F U ∧ (∀ t ∈ Icc 0 T, ∃ h : U t ∈ M.domain, M ⟨U t, h⟩ = 0) ∧
      ∀ U', IsStrongSolution L T U₀ F U' → EqOn U U' (Icc 0 T) := by
  obtain ⟨U, hU⟩ := hHY U₀ hU₀.1 F hF
  exact ⟨U, hU, constraint_ker L (hL.isSkewSymm hD) M hM h1 h3 hU hU₀.2 hFK,
    fun U' hU' => strongSolution_unique L (hL.isSkewSymm hD) hU hU'⟩

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
