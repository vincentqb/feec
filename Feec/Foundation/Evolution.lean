module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Feec.Foundation.Operators

/-!
# Feec foundation §B: evolution problems

Strong solutions of `U' = L U + F`, the explicit well-posedness hypotheses standing in for
Thm 4.3 (Hille–Yosida / Stone, which Mathlib lacks), and the energy lemma behind every
uniqueness statement.

## Main results

* `norm_le_norm_zero_of_inner_deriv_nonpos`: the energy inequality `‖e t‖ ≤ ‖e 0‖` when
  `⟪e', e⟫ ≤ 0`; `energy_zero` is its equality case.
* `IsDissipative A`: `⟪A x, x⟫ ≤ 0` on `D(A)`; skew-symmetric operators are dissipative.
* `IsStrongSolution.norm_sub_le`, `IsStrongSolution.unique`: strong solutions for a dissipative
  generator depend `1`-Lipschitz on the initial datum, hence are unique. This is the only
  uniqueness argument; every other uniqueness statement is a corollary.
* `IsStrongSolution.mem_of_invariant`, `IsStrongSolution.mem_of_isReducing`: constraint
  propagation. If `P_K D(A) ⊆ D(A)` and `A (D(A) ∩ K) ⊆ K` (in particular if `K` reduces `A`),
  a strong solution with datum and forcing in `K` stays in `K`, for any dissipative `A`.
* `WellPosedExistence.mono`: the existence hypothesis is antitone in the forcing class. No `axiom`: existence enters only as an explicit hypothesis. For
skew-adjoint generators the hypotheses are discharged downstream by Stone's theorem
(`Feec.stoneGroup` in `Feec.Ch4.Stone`; `Feec.IsSkewAdjoint.wellPosedHom` and
`Feec.IsSkewAdjoint.wellPosedExistence_thm43` in `Feec.Ch4.StoneApplications`).

## References

* [QuennevilleBelair2015], §4.3 (Thm 4.3), §4.4 (strong solutions, Thm 4.6, uniqueness by energy)
* [CazenaveHaraux1998], Prop 4.1.6 and Cor 2.4.9 (the Hille–Yosida corollary the thesis cites for
  Thm 4.3; here only the hypothesis `WellPosedExistence`)
* [Pazy1983], §1.10 (Stone's theorem) and Ch. 4 (inhomogeneous problems): classical background
  for the existence hypothesis
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace
open Set

namespace Feec

/-! ## §B. Evolution problems: solutions and the well-posedness hypothesis -/

section Evolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strong solution of `U' = L U + F` on `[0,T]` with `U 0 = U₀`.
Derivatives are within `Icc 0 T` (one-sided at the endpoints). Continuity of `U` in `E`
follows from `deriv`; graph-norm continuity is NOT part of the predicate (no module needs it).
See [QuennevilleBelair2015, Thm 4.3] and the definition of strong solution in §4.4. -/
structure IsStrongSolution (L : E →ₗ.[ℝ] E) (T : ℝ) (U₀ : E) (F U : ℝ → E) : Prop where
  mem : ∀ t ∈ Icc 0 T, U t ∈ L.domain
  deriv : ∀ t (ht : t ∈ Icc 0 T), HasDerivWithinAt U (L ⟨U t, mem t ht⟩ + F t) (Icc 0 T) t
  init : U 0 = U₀

/-- **Explicit hypothesis standing in for Thm 4.3 (Hille–Yosida / Stone), which Mathlib lacks.**
For every initial datum in `D(L)` and every admissible forcing there is a strong solution.
`Adm` abstracts the class "`C([0,T];X) ∩ (W^{1,1}(0,T;X) ∪ L¹(0,T;D(L)))`".
Never assumed as an `axiom`; always a theorem hypothesis. Uniqueness is *proved* (energy).
For skew-adjoint `L` it is a theorem, `Feec.IsSkewAdjoint.wellPosedExistence_thm43` (Stone),
with the forcing class `ForcingThm43`.
See [QuennevilleBelair2015, Thm 4.3]; cf. [CazenaveHaraux1998, Prop 4.1.6, Cor 2.4.9] and
[Pazy1983, §1.10, Ch. 4]. -/
def WellPosedExistence (L : E →ₗ.[ℝ] E) (T : ℝ) (Adm : (ℝ → E) → Prop) : Prop :=
  ∀ U₀ ∈ L.domain, ∀ F, Adm F → ∃ U, IsStrongSolution L T U₀ F U

/-- Homogeneous version (`F = 0`), the form used in Thm 4.6.
See [QuennevilleBelair2015, Thm 4.6]. -/
def WellPosedHom (L : E →ₗ.[ℝ] E) (T : ℝ) : Prop :=
  ∀ U₀ ∈ L.domain, ∃ U, IsStrongSolution L T U₀ 0 U

/-- `WellPosedExistence` is antitone in the forcing class. -/
theorem WellPosedExistence.mono {L : E →ₗ.[ℝ] E} {T : ℝ} {Adm Adm' : (ℝ → E) → Prop}
    (h : WellPosedExistence L T Adm) (hle : ∀ F, Adm' F → Adm F) : WellPosedExistence L T Adm' :=
  fun U₀ hU₀ F hF => h U₀ hU₀ F (hle F hF)

/-! ### The energy inequality -/

/-- **Energy inequality**: if `e` is continuous on `[0,T]` with right derivative `e'` on `[0,T)`
and `⟪e', e⟫ ≤ 0`, then `‖e t‖ ≤ ‖e 0‖` on `[0,T]` (`‖e‖²` is non-increasing).
The engine behind every uniqueness and propagation statement (Thm 4.3/4.6/4.7, Cor 4.5, Ch 6).
Abstracts the energy argument of [QuennevilleBelair2015, §4.4]. -/
theorem norm_le_norm_zero_of_inner_deriv_nonpos {e e' : ℝ → E} {T : ℝ}
    (hcont : ContinuousOn e (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt e (e' t) (Ici t) t)
    (hneg : ∀ t ∈ Ico 0 T, ⟪e' t, e t⟫ ≤ 0) : ∀ t ∈ Icc 0 T, ‖e t‖ ≤ ‖e 0‖ := by
  have h := image_le_of_deriv_right_le_deriv_boundary (f := fun t => ‖e t‖ ^ 2)
    (f' := fun t => 2 * ⟪e t, e' t⟫) (B := fun _ => ‖e 0‖ ^ 2) (B' := fun _ => 0)
    (hcont.norm.pow 2) (fun t ht => (hd t ht).norm_sq) le_rfl continuousOn_const
    (fun t _ => hasDerivWithinAt_const _ _ _) (fun t ht => by
      have := hneg t ht
      rw [real_inner_comm] at this
      linarith)
  intro t ht
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (h ht)

/-- Energy lemma: if `⟪e', e⟫ = 0` on `[0,T)` then `e(0) = 0` forces `e ≡ 0` on `[0,T]`.
The equality case of `norm_le_norm_zero_of_inner_deriv_nonpos`.
Abstracts the energy argument for uniqueness of weak solutions in [QuennevilleBelair2015, §4.4]. -/
theorem energy_zero {e e' : ℝ → E} {T : ℝ}
    (hcont : ContinuousOn e (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt e (e' t) (Ici t) t)
    (horth : ∀ t ∈ Ico 0 T, ⟪e' t, e t⟫ = 0) (h0 : e 0 = 0) :
    ∀ t ∈ Icc 0 T, e t = 0 := by
  intro t ht
  have := norm_le_norm_zero_of_inner_deriv_nonpos hcont hd (fun s hs => (horth s hs).le) t ht
  rw [h0, norm_zero] at this
  exact norm_le_zero_iff.1 this

/-! ### Dissipative generators: uniqueness and constraint propagation -/

/-- `A` is **dissipative**: `⟪A x, x⟫ ≤ 0` for every `x ∈ D(A)`. Skew-symmetric operators
(`IsSkewSymm.isDissipative`), in particular skew-adjoint ones, are dissipative. -/
def IsDissipative (A : E →ₗ.[ℝ] E) : Prop := ∀ x : A.domain, ⟪A x, (x : E)⟫ ≤ 0

/-- A skew-symmetric operator is dissipative (`⟪A x, x⟫ = 0`). -/
theorem IsSkewSymm.isDissipative {A : E →ₗ.[ℝ] E} (hA : IsSkewSymm A) : IsDissipative A :=
  fun x => (hA.inner_self x).le

/-- A strong solution has a right derivative on `[0,T)` (auxiliary). -/
private theorem IsStrongSolution.hasDerivWithinAt_Ici' {A : E →ₗ.[ℝ] E} {T : ℝ} {U₀ : E}
    {F U : ℝ → E} (hU : IsStrongSolution A T U₀ F U) {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt U (A ⟨U t, hU.mem t (Ico_subset_Icc_self ht)⟩ + F t) (Ici t) t :=
  (hU.deriv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

/-- **Stability of strong solutions** for a dissipative generator: two strong solutions of
`U' = A U + F` with the same forcing satisfy `‖U(t) - V(t)‖ ≤ ‖U(0) - V(0)‖` on `[0,T]`.
Energy method; no density, closedness, skew-adjointness or semigroup is needed.
See [QuennevilleBelair2015, Thm 4.3] (uniqueness half); cf. [Pazy1983, §1.4]. -/
theorem IsStrongSolution.norm_sub_le {A : E →ₗ.[ℝ] E} (hA : IsDissipative A) {T : ℝ}
    {U₀ V₀ : E} {F U V : ℝ → E} (hU : IsStrongSolution A T U₀ F U)
    (hV : IsStrongSolution A T V₀ F V) : ∀ t ∈ Icc 0 T, ‖U t - V t‖ ≤ ‖U₀ - V₀‖ := by
  classical
  have hc : ∀ {W₀ : E} {W : ℝ → E}, IsStrongSolution A T W₀ F W → ContinuousOn W (Icc 0 T) :=
    fun h t ht => (h.deriv t ht).continuousWithinAt
  have hm : ∀ t (ht : t ∈ Icc 0 T), U t - V t ∈ A.domain := fun t ht =>
    A.domain.sub_mem (hU.mem t ht) (hV.mem t ht)
  intro t ht
  have key := norm_le_norm_zero_of_inner_deriv_nonpos (e := fun t => U t - V t)
    (e' := fun t => if h : t ∈ Icc 0 T then A ⟨U t - V t, hm t h⟩ else 0)
    ((hc hU).sub (hc hV)) (fun s hs => ?_) (fun s hs => ?_) t ht
  · simpa [hU.init, hV.init] using key
  · have hs' := Ico_subset_Icc_self hs
    rw [dite_eq_left hs']
    have hsub : (⟨U s - V s, hm s hs'⟩ : A.domain) = ⟨U s, hU.mem s hs'⟩ - ⟨V s, hV.mem s hs'⟩ :=
      rfl
    rw [hsub, LinearPMap.map_sub]
    convert (hU.hasDerivWithinAt_Ici' hs).sub (hV.hasDerivWithinAt_Ici' hs) using 1
    abel
  · simp only [dite_eq_left (Ico_subset_Icc_self hs)]
    exact hA _

/-- **Uniqueness of strong solutions** for a dissipative generator: strong solutions of
`U' = A U + F`, `U(0) = U₀` agree on `[0,T]`. Corollary of `IsStrongSolution.norm_sub_le`.
See [QuennevilleBelair2015, Thm 4.3, Thm 4.6] (uniqueness). -/
theorem IsStrongSolution.unique {A : E →ₗ.[ℝ] E} (hA : IsDissipative A) {T : ℝ} {U₀ : E}
    {F U V : ℝ → E} (hU : IsStrongSolution A T U₀ F U) (hV : IsStrongSolution A T U₀ F V) :
    EqOn U V (Icc 0 T) := fun t ht => by
  have := hU.norm_sub_le hA hV t ht
  rwa [sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] at this

/-- **Constraint propagation** for a dissipative generator: if `P_K D(A) ⊆ D(A)` and
`A (D(A) ∩ K) ⊆ K`, every strong solution of `U' = A U + F` with `U(0) ∈ K` and `K`-valued
forcing stays in `K` on `[0,T]`.

Energy method on `V = (I - P_K) U`: `d/dt ‖V‖² = 2⟪A V, V⟫ ≤ 0`. No density, skew-adjointness or
semigroup is needed, and the two hypotheses are weaker than `K` reducing `A`
(`IsStrongSolution.mem_of_isReducing`). Generalizes [QuennevilleBelair2015, Thm 4.4, Cor 4.5]
(stated there for skew-adjoint `A` via the restricted semigroup). -/
theorem IsStrongSolution.mem_of_invariant {A : E →ₗ.[ℝ] E} (hA : IsDissipative A)
    {K : Submodule ℝ E} [K.HasOrthogonalProjection]
    (hP : ∀ x : A.domain, K.starProjection (x : E) ∈ A.domain)
    (hAK : ∀ x : A.domain, (x : E) ∈ K → A x ∈ K) {T : ℝ} {U₀ : E} {F U : ℝ → E}
    (hU : IsStrongSolution A T U₀ F U) (hU₀ : U₀ ∈ K) (hF : ∀ t ∈ Icc 0 T, F t ∈ K) :
    ∀ t ∈ Icc 0 T, U t ∈ K := by
  classical
  set P := K.starProjection
  have hc : ContinuousOn U (Icc 0 T) := fun t ht => (hU.deriv t ht).continuousWithinAt
  have key := norm_le_norm_zero_of_inner_deriv_nonpos (e := fun t => U t - P (U t))
    (e' := fun t => if h : t ∈ Icc 0 T then
      (A ⟨U t, hU.mem t h⟩ + F t) - P (A ⟨U t, hU.mem t h⟩ + F t) else 0)
    (hc.sub (P.continuous.comp_continuousOn hc)) (fun t ht => ?_) (fun t ht => ?_)
  · intro t ht
    have h0 : U 0 - P (U 0) = 0 := by
      rw [hU.init, (K.starProjection_eq_self_iff).2 hU₀, sub_self]
    have := key t ht
    rw [h0, norm_zero, norm_le_zero_iff, sub_eq_zero] at this
    rw [this]
    exact K.starProjection_apply_mem _
  · rw [dite_eq_left (Ico_subset_Icc_self ht)]
    have hD := hU.hasDerivWithinAt_Ici' ht
    exact hD.sub (P.hasFDerivAt.comp_hasDerivWithinAt t hD)
  · have ht' := Ico_subset_Icc_self ht
    simp only [dite_eq_left ht']
    have hVperp : U t - P (U t) ∈ Kᗮ := K.sub_starProjection_mem_orthogonal _
    have hPu : P (U t) ∈ A.domain := hP ⟨U t, hU.mem t ht'⟩
    have hVt : U t - P (U t) ∈ A.domain := A.domain.sub_mem (hU.mem t ht') hPu
    have hsplit : A ⟨U t, hU.mem t ht'⟩ = A ⟨P (U t), hPu⟩ + A ⟨U t - P (U t), hVt⟩ := by
      rw [← LinearPMap.map_add]; congr 1; ext; simp
    have e1 : ⟪P (A ⟨U t, hU.mem t ht'⟩ + F t), U t - P (U t)⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (K.starProjection_apply_mem _) hVperp
    have e2 : ⟪A ⟨P (U t), hPu⟩, U t - P (U t)⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hAK _ (K.starProjection_apply_mem _)) hVperp
    have e3 : ⟪F t, U t - P (U t)⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hF t ht') hVperp
    rw [inner_sub_left, e1, sub_zero, inner_add_left, e3, add_zero, hsplit, inner_add_left, e2,
      zero_add]
    exact hA ⟨_, hVt⟩

/-- **Constraint propagation through a reducing subspace**: if `K` reduces the dissipative
generator `A`, every strong solution of `U' = A U + F` with `U(0) ∈ K` and `K`-valued forcing
stays in `K`. Thesis: Thm 4.4 and Cor 4.5 (generalized from skew-adjoint to dissipative `A`,
with no density hypothesis). -/
theorem IsStrongSolution.mem_of_isReducing {A : E →ₗ.[ℝ] E} (hA : IsDissipative A)
    {K : Submodule ℝ E} [K.HasOrthogonalProjection] (hK : IsReducing A K) {T : ℝ} {U₀ : E}
    {F U : ℝ → E} (hU : IsStrongSolution A T U₀ F U) (hU₀ : U₀ ∈ K)
    (hF : ∀ t ∈ Icc 0 T, F t ∈ K) : ∀ t ∈ Icc 0 T, U t ∈ K :=
  hU.mem_of_invariant hA hK.proj_mem hK.mapsTo hU₀ hF

end Evolution

end Feec

/-! Sanity check that the API elaborates. -/
section Checks
open Feec
example {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : E →ₗ.[ℝ] E) (T : ℝ) :
    WellPosedHom L T ↔ ∀ U₀ ∈ L.domain, ∃ U, IsStrongSolution L T U₀ 0 U := Iff.rfl
end Checks
