module

public import Feec.Counterexamples.Fredholm
public import Feec.HilbertComplex.Approximation.SemidiscreteWave
public import Feec.HilbertComplex.HodgeWave
public import Feec.HilbertComplex.Reducing
public import Feec.HilbertComplex.ReducedSystem
public import Feec.HilbertComplex.Approximation.Convergence

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
* the coordinate truncations `span{e₀, …, e_{N-1}}` form a dense family of subcomplexes
  (`truncSub`, `eventually_exists_mem_graphSub`), and the semi-discrete solutions for this datum
  converge anyway (`tendstoUniformlyOn_truncSub_datum`): convergence holds for `D(L)` data
  without the regularity Thm 4.14 needs.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4 (Thm 4.6), §4.6 (Thm 4.14 and the remark after it)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.2 (regularity of orbits)

Bibliography: [references.bib](../../docs/references.bib)
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
  obtain ⟨hdom, hval⟩ := LinearPMap.mem_graph_iff_exists.1 hv
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
[QuennevilleBelair2015], Thm 4.14 (refuted for `D(L)` data) -/
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
lifts to a map into `Γ(𝐝)` that is right-differentiable at `0`. [QuennevilleBelair2015], Thm 4.14 (refuted for
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

/-! ### Coordinate truncations: convergence without `C¹` regularity -/

section Truncation

variable (𝕜) in
/-- `span{e₀, …, e_{N-1}}` in `ℓ²`. -/
def trunc (N : ℕ) : Submodule 𝕜 (L2 𝕜) where
  carrier := {x | ∀ n, N ≤ n → x n = 0}
  add_mem' hx hy n hn := by simp [hx n hn, hy n hn]
  zero_mem' _ _ := rfl
  smul_mem' c x hx n hn := by simp [hx n hn]

variable (𝕜) in
/-- The truncation `P_N x = Σ_{n<N} x_n e_n`. -/
def truncSum (N : ℕ) (x : L2 𝕜) : L2 𝕜 := ∑ n ∈ Finset.range N, lp.single 2 n (x n)

theorem truncSum_apply (N : ℕ) (x : L2 𝕜) (m : ℕ) :
    truncSum 𝕜 N x m = if m < N then x m else 0 := by
  rw [truncSum, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb.symm]
    · intro hm; exact absurd (Finset.mem_range.2 h) hm
  · refine Finset.sum_eq_zero fun b hb => ?_
    have : m ≠ b := fun e => h (e ▸ Finset.mem_range.1 hb)
    simp [Pi.single_eq_of_ne this]

theorem truncSum_mem (N : ℕ) (x : L2 𝕜) : truncSum 𝕜 N x ∈ trunc 𝕜 N := fun n hn => by
  rw [truncSum_apply]; simp [not_lt.2 hn]

theorem truncSum_eq_self {N : ℕ} {x : L2 𝕜} (hx : x ∈ trunc 𝕜 N) : truncSum 𝕜 N x = x :=
  lp.ext <| funext fun m => by
    rw [truncSum_apply]
    split_ifs with h
    · rfl
    · exact (hx m (not_lt.1 h)).symm

/-- `P_N x → x` in `ℓ²`. -/
theorem tendsto_truncSum (x : L2 𝕜) : Tendsto (fun N => truncSum 𝕜 N x) atTop (𝓝 x) :=
  (lp.hasSum_single (by norm_num) x).tendsto_sum_nat

instance (N : ℕ) : FiniteDimensional 𝕜 (trunc 𝕜 N) := by
  have := FiniteDimensional.span_of_finite 𝕜
    (Set.finite_range fun n : Fin N => (lp.single 2 (n : ℕ) (1 : 𝕜) : L2 𝕜))
  refine Submodule.finiteDimensional_of_le
    (S₂ := Submodule.span 𝕜 (Set.range fun n : Fin N => (lp.single 2 (n : ℕ) (1 : 𝕜) : L2 𝕜)))
    fun x hx => ?_
  rw [← truncSum_eq_self hx]
  refine Submodule.sum_mem _ fun n hn => ?_
  have e : (lp.single 2 n (x n) : L2 𝕜) = x n • lp.single 2 n (1 : 𝕜) :=
    lp.ext <| funext fun m => by
      by_cases h : m = n
      · subst h; simp
      · simp [lp.single_apply, Pi.single_eq_of_ne h]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨n, Finset.mem_range.1 hn⟩, rfl⟩)

/-- `A` preserves `trunc N`. -/
theorem diag_mem_trunc {N : ℕ} {x : L2 𝕜} (hx : x ∈ trunc 𝕜 N) : diag 𝕜 x ∈ trunc 𝕜 N :=
  fun n hn => by rw [diag_apply, hx n hn, zero_div]

/-- `trunc N ⊆ D(A⁻¹) = R(A)`. -/
theorem trunc_le_domain (N : ℕ) : trunc 𝕜 N ≤ (invDiag 𝕜).domain := by
  intro x hx
  rw [invDiag_domain]
  refine ⟨(∑ n ∈ Finset.range N, lp.single 2 n (((n : 𝕜) + 1) * x n) : L2 𝕜), ?_⟩
  refine lp.ext <| funext fun m => ?_
  change diag 𝕜 _ m = x m
  rw [diag_apply, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply]
  by_cases h : m < N
  · rw [Finset.sum_eq_single m]
    · simp only [Pi.single_eq_same]
      field_simp [natCast_add_one_ne_zero (𝕜 := 𝕜) m]
    · intro b _ hb; simp [Pi.single_eq_of_ne hb.symm]
    · intro hm; exact absurd (Finset.mem_range.2 h) hm
  · rw [Finset.sum_eq_zero fun b hb => ?_, zero_div, hx m (not_lt.1 h)]
    have : m ≠ b := fun e => h (e ▸ Finset.mem_range.1 hb)
    simp [Pi.single_eq_of_ne this]

/-- `A⁻¹` preserves `trunc N`. -/
theorem invDiag_mem_trunc {N : ℕ} (u : (invDiag 𝕜).domain) (hu : (u : L2 𝕜) ∈ trunc 𝕜 N) :
    invDiag 𝕜 u ∈ trunc 𝕜 N := fun n hn => by
  have h := congrArg (fun y : L2 𝕜 => y n) (diag_invDiag u)
  simp only [diag_apply] at h
  rw [hu n hn] at h
  simpa [div_eq_zero_iff, natCast_add_one_ne_zero (𝕜 := 𝕜) n] using h

variable (𝕜) in
/-- The truncation spaces of `ℓ² --A⁻¹--> ℓ² → 0`. -/
def truncFamily (N : ℕ) : ∀ i : Fin 3, Submodule 𝕜 (W3 (L2 𝕜) (L2 𝕜) PUnit i)
  | 0 => trunc 𝕜 N
  | 1 => trunc 𝕜 N
  | 2 => (⊤ : Submodule 𝕜 PUnit)

variable (𝕜) in
/-- **The truncation subcomplexes** `span{e₀, …, e_{N-1}}` in both copies of `ℓ²` (the spectral
Galerkin spaces of `A⁻¹ = diag(n+1)`). -/
def truncSub (N : ℕ) : (invShort 𝕜).toHilbertComplex.Subcomplex where
  V := truncFamily 𝕜 N
  le_domain i j := by
    fin_cases i <;> fin_cases j <;>
      first
        | exact trunc_le_domain N
        | exact fun _ _ => trivial
  mapsTo i j x hx := by
    fin_cases i <;> fin_cases j <;>
      first
        | exact invDiag_mem_trunc ⟨x, trunc_le_domain N hx⟩ hx
        | exact trivial
        | exact Submodule.zero_mem (truncFamily 𝕜 N _)

instance (N : ℕ) (i : Fin 3) : FiniteDimensional 𝕜 ((truncSub 𝕜 N).V i) := by
  fin_cases i
  · exact inferInstanceAs (FiniteDimensional 𝕜 (trunc 𝕜 N))
  · exact inferInstanceAs (FiniteDimensional 𝕜 (trunc 𝕜 N))
  · exact inferInstanceAs (FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 PUnit))

/-- The first component of a point of `D(𝐝)`, as a point of `D(A⁻¹)`. -/
def fstDomain (x : (invShort 𝕜).toHilbertComplex.totalD.domain) : (invDiag 𝕜).domain :=
  ⟨((x : PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit)) 0 : L2 𝕜), x.2 0 1⟩

theorem totalD_invShort_apply_zero (x : (invShort 𝕜).toHilbertComplex.totalD.domain) :
    (((invShort 𝕜).toHilbertComplex.totalD x : PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit)) 0 : L2 𝕜) = 0 := by
  rw [HilbertComplex.totalD_apply, Fin.sum_univ_three]
  simp only [LinearPMap.apply_eq_zero_of_eq_zero
      (show (invShort 𝕜).toHilbertComplex.d 0 0 = 0 from rfl),
    LinearPMap.apply_eq_zero_of_eq_zero (show (invShort 𝕜).toHilbertComplex.d 1 0 = 0 from rfl),
    LinearPMap.apply_eq_zero_of_eq_zero (show (invShort 𝕜).toHilbertComplex.d 2 0 = 0 from rfl)]
  simp

theorem totalD_invShort_apply_one (x : (invShort 𝕜).toHilbertComplex.totalD.domain) :
    (((invShort 𝕜).toHilbertComplex.totalD x : PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit)) 1 : L2 𝕜) =
      invDiag 𝕜 (fstDomain x) := by
  rw [HilbertComplex.totalD_apply, Fin.sum_univ_three]
  simp only [LinearPMap.apply_eq_zero_of_eq_zero
      (show (invShort 𝕜).toHilbertComplex.d 1 1 = 0 from rfl),
    LinearPMap.apply_eq_zero_of_eq_zero (show (invShort 𝕜).toHilbertComplex.d 2 1 = 0 from rfl)]
  simp only [add_zero]
  rfl

/-- The total differential of `ℓ² --A⁻¹--> ℓ² → 0`: `𝐝 (x₀, x₁, x₂) = (0, A⁻¹ x₀, 0)`. -/
theorem totalD_invShort_apply (x : (invShort 𝕜).toHilbertComplex.totalD.domain) :
    ((invShort 𝕜).toHilbertComplex.totalD x : PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit)) =
      ShortHilbertComplex.mk3 0 (invDiag 𝕜 (fstDomain x)) PUnit.unit := by
  refine PiLp.ext fun j => ?_
  fin_cases j
  · exact totalD_invShort_apply_zero x
  · exact totalD_invShort_apply_one x
  · exact Subsingleton.elim (α := PUnit) _ _

/-- **The truncation subcomplexes are dense** in the graph space of the total differential: for
`ζ = (x, 𝐝 x)` the approximant `(A P_N A⁻¹ x₀, P_N x₁, x₂)` converges to `ζ` in `Γ(𝐝)`. -/
theorem eventually_exists_mem_graphSub (ζ : (invShort 𝕜).toHilbertComplex.totalD.GraphSpace)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N in atTop, ∃ w ∈ (truncSub 𝕜 N).graphSub, ‖ζ - w‖ < δ := by
  obtain ⟨x, rfl, -, -⟩ := (invShort 𝕜).toHilbertComplex.totalD.exists_toGraphSpace_eq ζ
  set f : L2 𝕜 := invDiag 𝕜 (fstDomain x)
  set x1 : L2 𝕜 := (x : PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit)) 1
  have hx0 : diag 𝕜 f = (fstDomain x : L2 𝕜) := diag_invDiag _
  have hδ' : 0 < δ / 2 := half_pos hδ
  filter_upwards [Metric.tendsto_nhds.1 (tendsto_truncSum f) _ hδ',
    Metric.tendsto_nhds.1 (tendsto_truncSum x1) _ hδ'] with N hf h1
  rw [dist_eq_norm, norm_sub_rev] at hf h1
  set y : PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit) := ShortHilbertComplex.mk3 (diag 𝕜 (truncSum 𝕜 N f))
    (truncSum 𝕜 N x1) PUnit.unit
  have hy0 : diag 𝕜 (truncSum 𝕜 N f) ∈ trunc 𝕜 N := diag_mem_trunc (truncSum_mem N f)
  have hy : y ∈ (invShort 𝕜).toHilbertComplex.totalD.domain := fun i j => by
    fin_cases i <;> fin_cases j <;>
      first
        | exact trunc_le_domain N hy0
        | exact trivial
  refine ⟨(invShort 𝕜).toHilbertComplex.totalD.toGraphSpace ⟨y, hy⟩, fun i => ?_, ?_⟩
  · fin_cases i
    · exact hy0
    · exact truncSum_mem N x1
    · exact trivial
  have hTy : invDiag 𝕜 (fstDomain ⟨y, hy⟩) = truncSum 𝕜 N f := invDiag_diag _ _
  have hsq := HodgeWave.norm_sq_graphSpace ((invShort 𝕜).toHilbertComplex.totalD.toGraphSpace x -
    (invShort 𝕜).toHilbertComplex.totalD.toGraphSpace ⟨y, hy⟩)
  rw [(invShort 𝕜).toHilbertComplex.totalD.graphFst.map_sub,
    (invShort 𝕜).toHilbertComplex.totalD.graphSnd.map_sub, LinearPMap.graphFst_toGraphSpace,
    LinearPMap.graphFst_toGraphSpace, LinearPMap.graphSnd_toGraphSpace,
    LinearPMap.graphSnd_toGraphSpace, totalD_invShort_apply, totalD_invShort_apply, hTy] at hsq
  have hxy : (x : PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit)) - y =
      ShortHilbertComplex.mk3 (diag 𝕜 (f - truncSum 𝕜 N f)) (x1 - truncSum 𝕜 N x1) 0 := by
    refine PiLp.ext fun i => ?_
    fin_cases i
    · change (fstDomain x : L2 𝕜) - diag 𝕜 (truncSum 𝕜 N f) = diag 𝕜 (f - truncSum 𝕜 N f)
      rw [_root_.map_sub, hx0]
    · rfl
    · exact Subsingleton.elim (α := PUnit) _ _
  have hd : (ShortHilbertComplex.mk3 (0 : L2 𝕜) f PUnit.unit : PiLp 2 (W3 (L2 𝕜) (L2 𝕜) PUnit)) -
      ShortHilbertComplex.mk3 0 (truncSum 𝕜 N f) PUnit.unit =
      ShortHilbertComplex.mk3 0 (f - truncSum 𝕜 N f) 0 := by
    refine PiLp.ext fun i => ?_
    fin_cases i
    · change (0 : L2 𝕜) - 0 = 0
      rw [sub_zero]
    · rfl
    · exact Subsingleton.elim (α := PUnit) _ _
  rw [hxy, hd, ShortHilbertComplex.norm_sq_mk3 (𝕜 := 𝕜),
    ShortHilbertComplex.norm_sq_mk3 (𝕜 := 𝕜)] at hsq
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    zero_add] at hsq
  have hdg := norm_diag_apply_le (f - truncSum 𝕜 N f)
  have hn : ‖(invShort 𝕜).toHilbertComplex.totalD.toGraphSpace x -
      (invShort 𝕜).toHilbertComplex.totalD.toGraphSpace ⟨y, hy⟩‖ ^ 2 < δ ^ 2 := by
    rw [hsq]
    nlinarith [norm_nonneg (diag 𝕜 (f - truncSum 𝕜 N f)), norm_nonneg (f - truncSum 𝕜 N f),
      norm_nonneg (x1 - truncSum 𝕜 N x1)]
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hδ.le two_ne_zero).1 hn

/-- **Convergence without `C¹` regularity** (a concrete, infinite-dimensional instance of the
thesis' convergence remark outside the reach of Thm 4.14): on `ℓ² --A⁻¹--> ℓ² → 0` the datum
`U₀ = (0, A h, 0) ∈ D(L) \ D(L²)` has no strong solution that is `C¹` into `Γ(𝐝)` at `0`, yet the
semi-discrete solutions in the truncation subcomplexes with `ξ_N(0) = P_N U₀` converge to the
solution `e^{tL} U₀`, uniformly on every `[0, T]`.
See [QuennevilleBelair2015], Thm 4.14 and the remark after it. -/
theorem tendstoUniformlyOn_truncSub_datum (T : ℝ) :
    ∃ ξh ξh' : ℕ → ℝ → (invShort 𝕜).toHilbertComplex.totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (truncSub 𝕜 N).graphSub (Icc 0 T) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N 0 = HodgeWave.ellipticProjection (truncSub 𝕜 N).graphSub
        ((invShort 𝕜).toHilbertComplex.totalD.toGraphSpace
          ⟨datum 𝕜, ((invShort 𝕜).toHilbertComplex.mem_wave_domain.1 datum_mem).1⟩)) ∧
      TendstoUniformlyOn (fun N t => (invShort 𝕜).toHilbertComplex.totalD.graphFst (ξh N t))
        (fun t => (invShort 𝕜).toHilbertComplex.waveGroup.S t (datum 𝕜)) atTop (Icc 0 T) := by
  have hK : HodgeWave.IsApproximating atTop fun N => (truncSub 𝕜 N).graphSub :=
    HilbertComplex.Subcomplex.isApproximating fun ζ δ hδ => eventually_exists_mem_graphSub ζ hδ
  obtain ⟨ξh, ξh', hξh, hinit, hconv⟩ :=
    HilbertComplex.HodgeWave.exists_tendstoUniformlyOn_ellipticProjection
      (invShort 𝕜).toHilbertComplex hK 0 T ⟨datum 𝕜, datum_mem⟩
  refine ⟨ξh, ξh', hξh, hinit, hconv.congr_right fun t _ => ?_⟩
  simp only [sub_zero]

end Truncation

end Feec.Counterexamples.ClassicalRegularity
