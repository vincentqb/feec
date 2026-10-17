module

public import Feec.Counterexamples.Fredholm
public import Feec.HilbertComplex.Approximation.SemidiscreteWave
public import Feec.HilbertComplex.HodgeWave
public import Feec.HilbertComplex.Reducing

/-!
# The semi-discrete error estimate needs `C¹` regularity in the graph space

The semi-discrete error estimate for the Hodge wave equation (thesis Thm 4.14,
`Feec.HodgeWave.norm_sub_le_of_semidiscrete`) assumes the exact solution to be `C¹` with values in
the graph space `Γ(𝐝)` of the total differential, i.e. `ξ ∈ C¹([0,T]; V)`. For data in `D(L)`
(the class of the thesis' existence theorem, Thm 4.6) this can fail at `t = 0`:

* `apply_add_mem_domain_of_lift`: if a strong solution of `U' = A U + F` on `[0, T]`, `T > 0`, is
  the `E`-trace of a map into `Γ(S)` that is right-differentiable at `0` in `Γ(S)`, then
  `A U(0) + F(0) ∈ D(S)`;
* on the short complex `ℓ² --A⁻¹--> ℓ² → 0`, `A⁻¹ = diag(n+1)`
  (`Feec.Counterexamples.Fredholm.invComplex`), the datum `U₀ = (0, A h, 0)`,
  `h = (1/(n+1))ₙ`, lies in `D(L)`, but `L U₀ = (-h, 0, 0) ∉ D(𝐝)` (`h ∉ R(A) = D(A⁻¹)`), so no
  strong solution from `U₀` is `C¹` into `Γ(𝐝)` at `0`, on any interval `[0, T]`, `T > 0`
  (`not_C1_graphSpace`). In particular `U₀ ∉ D(L²)`.

## References

* [QuennevilleBelair2015], §4.4 (Thm 4.6), §4.6 (Thm 4.14 and the remark after it)
* [Pazy1983], §1.2 (regularity of orbits)
-/

open scoped InnerProductSpace LinearPMap
open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Counterexamples.ClassicalRegularity

/-! ### Right-differentiability in the graph space forces `A U(0) + F(0) ∈ D(S)` -/

section General

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- If a strong solution `U` of `U' = A U + F` on `[0, T]`, `T > 0`, is the first component of a
map `ξ` into the graph space `Γ(S)` that is right-differentiable at `0` in `Γ(S)`, then
`A U(0) + F(0) = ξ'(0)` lies in `D(S)`. -/
theorem apply_add_mem_domain_of_lift {A S : E →ₗ.[𝕜] E} {F U : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hU : Evolution.IsStrongSolution A (Icc 0 T) F U) {ξ : ℝ → S.GraphSpace} {ξ' : S.GraphSpace}
    (hξ : ∀ t ∈ Icc 0 T, S.graphFst (ξ t) = U t) (hd : HasDerivWithinAt ξ ξ' (Ici 0) 0) :
    ∃ h : U 0 ∈ A.domain, A ⟨U 0, h⟩ + F 0 ∈ S.domain := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  obtain ⟨v, hv, hdU⟩ := hU.deriv 0 h0
  obtain ⟨hdom, hval⟩ := Evolution.mem_graph_iff_exists.1 hv
  have hfst : HasDerivWithinAt (fun t => S.graphFst (ξ t)) (S.graphFst ξ') (Icc 0 T) 0 :=
    ((S.graphFst.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt 0 hd).mono
      Icc_subset_Ici_self
  have hfst' : HasDerivWithinAt U (S.graphFst ξ') (Icc 0 T) 0 :=
    hfst.congr (fun t ht => (hξ t ht).symm) (hξ 0 h0).symm
  have heq : v + F 0 = S.graphFst ξ' :=
    (uniqueDiffOn_Icc hT 0 h0).eq_deriv _ hdU hfst'
  refine ⟨hdom, ?_⟩
  rw [hval, heq]
  exact LinearPMap.mem_domain_of_mem_graph ξ'.2

end General

/-! ### The datum `(0, A h, 0)` on `ℓ² --A⁻¹--> ℓ² → 0` -/

open Fredholm
open Ell2 (L2)
open ShortHilbertComplex (W3)

variable {𝕜 : Type*} [RCLike 𝕜]

variable (𝕜) in
/-- The short complex `ℓ² --A⁻¹--> ℓ² → 0`. -/
abbrev invShort : ShortHilbertComplex 𝕜 (L2 𝕜) (L2 𝕜) PUnit :=
  ShortHilbertComplex.ofOp (invDiag 𝕜) dense_invDiag_domain invDiag_isClosed

theorem invShort_toHilbertComplex : (invShort 𝕜).toHilbertComplex = invComplex 𝕜 := rfl

theorem diag_harm_mem_domain : diag 𝕜 harm ∈ (invDiag 𝕜).domain :=
  (invDiag_domain (𝕜 := 𝕜)) ▸ ⟨harm, rfl⟩

variable (𝕜) in
/-- The datum `U₀ = (0, A h, 0)`, `h = (1/(n+1))ₙ`. -/
def datum : PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit) :=
  WithLp.toLp 2 fun i => match i with
    | 0 => (0 : L2 𝕜)
    | 1 => diag 𝕜 harm
    | 2 => PUnit.unit

theorem datum_mem : datum 𝕜 ∈ (invShort 𝕜).wave.domain := by
  rw [ShortHilbertComplex.mem_wave_domain]
  refine ⟨Submodule.zero_mem _, trivial, ?_, ?_⟩
  · change diag 𝕜 harm ∈ ((invDiag 𝕜)†).domain
    rw [adjoint_invDiag]
    exact diag_harm_mem_domain
  · rw [show (invShort 𝕜).d₁ = 0 from rfl, LinearPMap.adjoint_zero]
    trivial

/-- `(L U₀)₀ = -A⁻¹ (A h) = -h`. -/
theorem wave_datum_zero :
    (((invShort 𝕜).wave ⟨datum 𝕜, datum_mem⟩ : PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit)) 0 : L2 𝕜) =
      -harm := by
  rw [ShortHilbertComplex.wave_apply_zero]
  congr 1
  have key : ∀ T : L2 𝕜 →ₗ.[𝕜] L2 𝕜, T = invDiag 𝕜 → ∀ (h : diag 𝕜 harm ∈ T.domain),
      T ⟨diag 𝕜 harm, h⟩ = harm := by
    rintro _ rfl h
    exact invDiag_diag harm h
  exact key _ adjoint_invDiag _

/-- `L U₀ ∉ D(𝐝)`: its first component `-h` is not in `R(A) = D(A⁻¹)`. -/
theorem wave_datum_not_mem :
    ((invShort 𝕜).wave ⟨datum 𝕜, datum_mem⟩ : PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit)) ∉
      (invComplex 𝕜).totalD.domain := by
  intro h
  have h0 := (invComplex 𝕜).mem_totalDomain.1 h 0 1
  change (((invShort 𝕜).wave ⟨datum 𝕜, datum_mem⟩ : PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit)) 0 : L2 𝕜) ∈
    (invDiag 𝕜).domain at h0
  rw [wave_datum_zero, invDiag_domain] at h0
  have := (LinearMap.range (diag 𝕜 : L2 𝕜 →ₗ[𝕜] L2 𝕜)).neg_mem h0
  rw [neg_neg] at this
  exact harm_not_mem_range this

/-- **No strong solution from `U₀ ∈ D(L)` is `C¹` into the graph space at `t = 0`**: on
`ℓ² --A⁻¹--> ℓ² → 0`, for every `T > 0` and every strong solution `U` of `U' = L U` on `[0, T]`
with `U(0) = U₀`, no lift `ξ` of `U` to `Γ(𝐝)` is right-differentiable at `0`. Hence the
regularity hypothesis of the semi-discrete error estimate fails for this datum.
Thesis: Thm 4.14 (refuted for `D(L)` data) -/
theorem not_C1_graphSpace {T : ℝ} (hT : 0 < T) {U : ℝ → PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit)}
    (hU0 : U 0 = datum 𝕜) (hU : Evolution.IsStrongSolution (invShort 𝕜).wave (Icc 0 T) 0 U) :
    ¬ ∃ (ξ : ℝ → (invComplex 𝕜).totalD.GraphSpace) (ξ' : (invComplex 𝕜).totalD.GraphSpace),
      (∀ t ∈ Icc 0 T, (invComplex 𝕜).totalD.graphFst (ξ t) = U t) ∧
        HasDerivWithinAt ξ ξ' (Ici 0) 0 := by
  rintro ⟨ξ, ξ', hξ, hd⟩
  obtain ⟨h, hmem⟩ := apply_add_mem_domain_of_lift hT hU hξ hd
  rw [Pi.zero_apply, add_zero] at hmem
  have e : ((invShort 𝕜).wave ⟨U 0, h⟩ : PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit)) =
      (invShort 𝕜).wave ⟨datum 𝕜, datum_mem⟩ := by
    congr 2
  exact wave_datum_not_mem (e ▸ hmem)

/-- `U₀ ∈ D(L) \ D(L²)`. -/
theorem datum_not_mem_domain_sq :
    ((invShort 𝕜).wave ⟨datum 𝕜, datum_mem⟩ : PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit)) ∉
      (invShort 𝕜).wave.domain := fun h => wave_datum_not_mem h.1

/-- **Thm 4.14's regularity hypothesis fails for some `D(L)` data** (headline): on
`ℓ² --A⁻¹--> ℓ² → 0` there is `U₀ ∈ D(L) \ D(L²)` whose Hodge wave equation has a classical
solution on every `[0, T]` (Thm 4.6), while no strong solution from `U₀` on `[0, T]`, `T > 0`,
lifts to a map into `Γ(𝐝)` that is right-differentiable at `0`. Thesis: Thm 4.14 (refuted for
`D(L)` data) -/
theorem exists_datum_not_C1 :
    ∃ (U₀ : PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit)) (h : U₀ ∈ (invShort 𝕜).wave.domain),
      ((invShort 𝕜).wave ⟨U₀, h⟩ : PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit)) ∉ (invShort 𝕜).wave.domain ∧
      (∀ T : ℝ, ∃ U, U 0 = U₀ ∧ Evolution.IsClassicalSolution (invShort 𝕜).wave (Icc 0 T) 0 U) ∧
      ∀ T > 0, ∀ U : ℝ → PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit), U 0 = U₀ →
        Evolution.IsStrongSolution (invShort 𝕜).wave (Icc 0 T) 0 U →
        ¬ ∃ (ξ : ℝ → (invComplex 𝕜).totalD.GraphSpace) (ξ' : (invComplex 𝕜).totalD.GraphSpace),
          (∀ t ∈ Icc 0 T, (invComplex 𝕜).totalD.graphFst (ξ t) = U t) ∧
            HasDerivWithinAt ξ ξ' (Ici 0) 0 := by
  refine ⟨datum 𝕜, datum_mem, datum_not_mem_domain_sq, fun T => ?_,
    fun T hT U hU0 hU => not_C1_graphSpace hT hU0 hU⟩
  obtain ⟨U, h0, hU, -⟩ :=
    HilbertComplex.HodgeWave.existsUnique_hom (invShort 𝕜).toHilbertComplex datum_mem 0 T
  exact ⟨U, h0, hU⟩

end Feec.Counterexamples.ClassicalRegularity
