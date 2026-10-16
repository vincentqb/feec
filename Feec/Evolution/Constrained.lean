module

public import Feec.Evolution.Energy
public import Feec.ForMathlib.LinearPMap.Reducing

/-!
# Constraint propagation for `U' = A U + F`

A closed subspace `K` *propagates* under `U' = A U + F` if every strong solution with initial
value and forcing in `K` stays in `K`. For a dissipative generator this holds as soon as
`P_K D(A) ⊆ D(A)` and `A (D(A) ∩ K) ⊆ K`, in particular when `K` reduces `A`.

## Main results

* `IsStrongSolution.mem_of_invariant`: energy method on `V = (1 - P_K) U`:
  `d/dt ‖V‖² = 2 re ⟪A V, V⟫ ≤ 0`. No density, closedness, skew-adjointness or semigroup is
  needed.
* `IsStrongSolution.mem_of_isReducing`: the same for a reducing subspace `K`
  (`LinearPMap.IsReducing`). Thesis: Thm 4.4, Cor 4.5 (generalized from skew-adjoint to
  dissipative `A`, with no density hypothesis).
* `IsStrongSolution.mem_of_isReducing_of_ordConnected`: the same forward in time on any interval.
* `IsStrongSolution.mem_orthogonal_of_isReducing`: for skew-symmetric `A` the orthogonal
  complement `Kᗮ` propagates too, so the `K`- and `Kᗮ`-components evolve independently.

## References

* [QuennevilleBelair2015], §4.3 (Thm 4.4, Cor 4.5)
-/

open Set Filter

@[expose] public noncomputable section

namespace Feec.Evolution.IsStrongSolution

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {A : E →ₗ.[𝕜] E} {I : Set ℝ} {F U : ℝ → E}
  {a b : ℝ}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- **Constraint propagation** for a dissipative generator: if `P_K D(A) ⊆ D(A)` and
`A (D(A) ∩ K) ⊆ K`, every strong solution of `U' = A U + F` on `[a,b]` with `U a ∈ K` and
`K`-valued forcing stays in `K`.

Energy method on `V = (1 - P_K) U`: `d/dt ‖V‖² = 2 re ⟪A V, V⟫ ≤ 0`. The two hypotheses are
weaker than `K` reducing `A` (`IsStrongSolution.mem_of_isReducing`). -/
theorem mem_of_invariant (hA : A.IsDissipative) {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    (hP : ∀ x : A.domain, K.starProjection (x : E) ∈ A.domain)
    (hAK : ∀ x : A.domain, (x : E) ∈ K → A x ∈ K) (hU : IsStrongSolution A (Icc a b) F U)
    (h0 : U a ∈ K) (hF : ∀ t ∈ Icc a b, F t ∈ K) : ∀ t ∈ Icc a b, U t ∈ K := by
  classical
  set P := K.starProjection
  have hPℝ : ∀ {y : E} {s : Set ℝ} {t : ℝ} {e : ℝ → E}, HasDerivWithinAt e y s t →
      HasDerivWithinAt (fun r => P (e r)) (P y) s t := fun h =>
    ((P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt _ h)
  have key := Energy.norm_le_of_re_inner_deriv_nonpos (𝕜 := 𝕜) (e := fun t => U t - P (U t))
    (e' := fun t => if h : t ∈ Icc a b then
      (A ⟨U t, hU.mem_domain h⟩ + F t) - P (A ⟨U t, hU.mem_domain h⟩ + F t) else 0)
    (hU.continuousOn.sub (P.continuous.comp_continuousOn hU.continuousOn)) (fun t ht => ?_)
    (fun t ht => ?_)
  · intro t ht
    have h00 : U a - P (U a) = 0 := by
      rw [(K.starProjection_eq_self_iff).2 h0, sub_self]
    have := key t ht
    rw [h00, norm_zero, norm_le_zero_iff, sub_eq_zero] at this
    rw [this]
    exact K.starProjection_apply_mem _
  · rw [dite_eq_left (Ico_subset_Icc_self ht)]
    have hD := hU.hasDerivWithinAt_Ici ht
    exact hD.sub (hPℝ hD)
  · have ht' := Ico_subset_Icc_self ht
    simp only [dite_eq_left ht']
    have hVperp : U t - P (U t) ∈ Kᗮ := K.sub_starProjection_mem_orthogonal _
    have hPu : P (U t) ∈ A.domain := hP ⟨U t, hU.mem_domain ht'⟩
    have hVt : U t - P (U t) ∈ A.domain := A.domain.sub_mem (hU.mem_domain ht') hPu
    have hsplit : A ⟨U t, hU.mem_domain ht'⟩ = A ⟨P (U t), hPu⟩ + A ⟨U t - P (U t), hVt⟩ := by
      rw [← LinearPMap.map_add]; congr 1; ext; simp
    have e1 : ⟪P (A ⟨U t, hU.mem_domain ht'⟩ + F t), U t - P (U t)⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (K.starProjection_apply_mem _) hVperp
    have e2 : ⟪A ⟨P (U t), hPu⟩, U t - P (U t)⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hAK _ (K.starProjection_apply_mem _)) hVperp
    have e3 : ⟪F t, U t - P (U t)⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hF t ht') hVperp
    rw [inner_sub_left, e1, sub_zero, inner_add_left, e3, add_zero, hsplit, inner_add_left, e2,
      zero_add]
    exact hA ⟨_, hVt⟩

/-- **Constraint propagation through a reducing subspace**: if `K` reduces the dissipative
generator `A`, every strong solution of `U' = A U + F` on `[a,b]` with `U a ∈ K` and `K`-valued
forcing stays in `K`. Thesis: Thm 4.4 and Cor 4.5 (generalized from skew-adjoint to dissipative
`A`, with no density hypothesis). -/
theorem mem_of_isReducing (hA : A.IsDissipative) {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    (hK : A.IsReducing K) (hU : IsStrongSolution A (Icc a b) F U) (h0 : U a ∈ K)
    (hF : ∀ t ∈ Icc a b, F t ∈ K) : ∀ t ∈ Icc a b, U t ∈ K :=
  hU.mem_of_invariant hA hK.proj_mem hK.mapsTo h0 hF

/-- **Constraint propagation on any interval**, forward in time from `a ∈ I`. -/
theorem mem_of_isReducing_of_ordConnected (hA : A.IsDissipative) {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] (hK : A.IsReducing K) (hI : I.OrdConnected)
    (hU : IsStrongSolution A I F U) (ha : a ∈ I) (h0 : U a ∈ K) (hF : ∀ t ∈ I, F t ∈ K) :
    ∀ t ∈ I ∩ Ici a, U t ∈ K := fun t ⟨ht, hat⟩ => by
  have hsub : Icc a t ⊆ I := hI.out ha ht
  exact (hU.mono hsub).mem_of_isReducing hA hK h0 (fun s hs => hF s (hsub hs)) t ⟨hat, le_rfl⟩

/-- For a skew-symmetric generator, a reducing subspace `K` and its orthogonal complement both
propagate: the `Kᗮ`-component of a solution with `Kᗮ`-valued data stays in `Kᗮ`. -/
theorem mem_orthogonal_of_isReducing (hA : A.IsSkewSymmetric) {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] (hK : A.IsReducing K) (hU : IsStrongSolution A (Icc a b) F U)
    (h0 : U a ∈ Kᗮ) (hF : ∀ t ∈ Icc a b, F t ∈ Kᗮ) : ∀ t ∈ Icc a b, U t ∈ Kᗮ :=
  hU.mem_of_isReducing hA.isDissipative hK.orthogonal h0 hF

end Feec.Evolution.IsStrongSolution
