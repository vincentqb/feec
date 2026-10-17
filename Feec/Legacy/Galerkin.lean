module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Feec.Variational.SaddlePoint
public import Feec.Counterexamples.Ell2

/-!
# Galerkin theory: Lax–Milgram, Babuška–Nečas, quasi-optimality, Brezzi (thesis §4.5)

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use.
Most of the original module was re-derived in the general layers (see
`docs/migration/map.tsv`); what remains is listed below.

## Contents

* `Galerkin.infSup_restrict_of_forall`: The attained inf-sup condition on `K` is `Feec.Variational.InfSup` of the restriction.
* `Galerkin.quasi_opt`: **Thesis Thm 4.10** (quasi-optimality, Céa/Babuška), abstract core: under a discrete inf-sup condition on a subspace `K` and Galerkin orthogonality, `‖u - uₕ‖ ≤ (1 + ‖B‖/γ) ‖u - w‖` for every `w ∈ K`.
* `Galerkin.discrete_existsUnique`: Thesis Thm 4.10, discrete well-posedness: on a finite-dimensional subspace `K` (the space `Xₕ`), the discrete inf-sup condition alone gives a unique Galerkin solution `uₕ ∈ K`.

## References

* [QuennevilleBelair2015], §4.5 (Thm 4.8 Lax–Milgram, the inf-sup and dense range conditions,
  Thm 4.9, Thm 4.10 quasi-optimality, Thm 4.11 Brezzi); used in §4.6 and Ch. 5
* [Babuska1971] (inf-sup condition, generalized Lax–Milgram, quasi-optimality of Galerkin
  approximations)
* [Brezzi1974] (existence, uniqueness and stability for saddle point problems; Thm 4.11)
* [BoffiBrezziFortin2013], Ch. 4 (saddle point problems in Hilbert spaces)
* [Arnold2018] (abstract well-posedness and Galerkin stability framework of FEEC)
* [AFW2010] (stability of Galerkin and mixed methods via inf-sup conditions in FEEC)
-/

open scoped RealInnerProductSpace
open InnerProductSpace

@[expose] public noncomputable section

namespace Feec.Legacy.Galerkin

/-! ## Inf-sup and dense range conditions -/

section InfSup

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- The Riesz operator of a bilinear form: `⟪B♯ u, v⟫ = B u v`. -/
local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

end InfSup

/-! ## Quasi-optimality (Thm 4.10) -/

section QuasiOpt

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The attained inf-sup condition on `K` is `Feec.Variational.InfSup` of the restriction. -/
theorem infSup_restrict_of_forall (B : X →L[ℝ] X →L[ℝ] ℝ) (K : Submodule ℝ X) {γ : ℝ}
    (hγ : 0 < γ) (hinf : ∀ w ∈ K, ∃ v ∈ K, ‖v‖ ≤ 1 ∧ γ * ‖w‖ ≤ B w v) :
    Variational.InfSup (Variational.restrict B K K) γ :=
  Variational.InfSup.of_forall_exists_norm_le_one hγ fun w => by
    obtain ⟨v, hv, hv1, h⟩ := hinf w w.2
    exact ⟨⟨v, hv⟩, hv1, h.trans (Real.le_norm_self _)⟩

/-- **Thesis Thm 4.10** (quasi-optimality, Céa/Babuška), abstract core: under a discrete inf-sup
condition on a subspace `K` and Galerkin orthogonality, `‖u - uₕ‖ ≤ (1 + ‖B‖/γ) ‖u - w‖` for
every `w ∈ K`.

Correction: the theorem statement restates boundedness of `a` only on `Xₕ × Xₕ`, while the
proof needs the standing hypothesis (thesis, paragraph before Thm 4.10) that `a` is bounded on
`X × X`; here `‖B‖` is the norm on all of `X`. Neither completeness, finite dimension nor the
orthogonal projection `rₕ` is needed.

See [QuennevilleBelair2015, Thm 4.10]; cf. [Babuska1971]. -/
theorem quasi_opt (B : X →L[ℝ] X →L[ℝ] ℝ) (K : Submodule ℝ X) {γ : ℝ} (hγ : 0 < γ)
    (hinf : ∀ w ∈ K, ∃ v ∈ K, ‖v‖ ≤ 1 ∧ γ * ‖w‖ ≤ B w v)
    {u uh : X} (huh : uh ∈ K) (horth : ∀ v ∈ K, B (u - uh) v = 0) :
    ∀ w ∈ K, ‖u - uh‖ ≤ (1 + ‖B‖ / γ) * ‖u - w‖ := fun _ hw =>
  (infSup_restrict_of_forall B K hγ hinf).norm_sub_le_of_orthogonal huh horth hw

/-- Thesis Thm 4.10, discrete well-posedness: on a finite-dimensional subspace `K` (the space
`Xₕ`), the discrete inf-sup condition alone gives a unique Galerkin solution `uₕ ∈ K`.

Thesis gap: existence and uniqueness of `uₕ` are used but not argued (Thm 4.9 on `Xₕ` would also
need dense range on `Xₕ`, which holds here by rank–nullity).

See [QuennevilleBelair2015, Thm 4.10]. -/
theorem discrete_existsUnique (B : X →L[ℝ] X →L[ℝ] ℝ) (K : Submodule ℝ X)
    [FiniteDimensional ℝ K] {γ : ℝ} (hγ : 0 < γ)
    (hinf : ∀ w ∈ K, ∃ v ∈ K, ‖v‖ ≤ 1 ∧ γ * ‖w‖ ≤ B w v) (F : StrongDual ℝ X) :
    ∃! uh, uh ∈ K ∧ ∀ v ∈ K, B uh v = F v :=
  Variational.existsUnique_galerkin rfl (infSup_restrict_of_forall B K hγ hinf) F

end QuasiOpt

/-! ## Brezzi (Thm 4.11) -/

section Brezzi

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

local notation "adj" => ContinuousLinearMap.adjoint

end Brezzi

end Feec.Legacy.Galerkin
