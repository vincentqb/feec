module

public import Feec.Fourier.Torus
public import Feec.Fourier.BGGSymbol

/-!
# The BGG weak-symmetry complex on `𝕋³`: TSD constraints propagate

The complex (5.1) of the weakly symmetric formulation of Thesis Ch. 6 (`S₀ = I`, `S₁ = 2 vskw`),
`H²(𝕋³) --grad grad--> H(curl; 𝕋³, ℂ³ˣ³) --(S₁, curl)--> L²(𝕋³; ℂ³) × L²(𝕋³; ℂ³ˣ³)`, on the Fourier
side: the torus instance of the symbol theory with `Feec.Fourier.BGG.bggFamily`. On every bounded
domain with the thesis' boundary conditions its Hodge wave equation does not propagate the TSD
constraint; on the torus it does.

## Main results

* `BGG.complex`, `BGG.constraint = {0} × L²(TSD) × ({0} × L²(TSD))` and **`reducingSubcomplex`**.
* **`tsd_propagates`**, `tsd_propagates_neg`, **`tsd_existsUnique`**, `waveGroup_mem`: TSD data
  stay TSD, the multiplier `M` stays `0`, and `B` stays TSD, with existence and uniqueness.
* **`closedRangeAt`**, `dual_closedRangeAt'`, **`hodge`**: closed range at every index (Poincaré
  constant `4`) and the Hodge decomposition without closures.
* **`verdict`**: for TSD data `(0, E₀, (0, B₀))` in `D(L)` the Hodge wave equation of (5.1) has a
  unique classical solution, with `σ ≡ 0`, `u(t)` TSD, `(M, B)(t) = (0, B(t))` with `B(t)` TSD
  (`mem_constraint_two_iff`), and `(u, (M, B))` solves the reduced system (4.15),
  `u' = -(S₁, curl)* (M, B)`, `(M, B)' = (S₁, curl) u`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 5 (§5.1, (5.1)), Ch. 6 (§6.1, §6.3), §3.4 (Lemma 3.5)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory LinearPMap Set Feec.Fourier Feec.Fourier.GradCurl Feec.Fourier.SymCurl
  Feec.Fourier.BGG Feec.ShortHilbertComplex

namespace Feec.Models.Torus.BGG

/-- The spaces `ℓ²(ℤ³; ℂ)`, `ℓ²(ℤ³; ℂ³ˣ³)`, `ℓ²(ℤ³; ℂ³ × ℂ³ˣ³)` of Fourier coefficients. -/
abbrev Space (i : Fin 3) : Type :=
  Lp (W3 ℂ Mat VM i) 2 (Measure.count : Measure (Fin 3 → ℤ))

/-- **The periodic BGG weak-symmetry complex** (5.1) (Fourier side). -/
abbrev complex : HilbertComplex ℂ ComplexShape.fin3 Space :=
  Fourier.Torus.complex bggFamily

/-- **The constraint space** `K = {0} × L²(TSD ∩ S) × L²(TSD ∩ T)`. -/
abbrev constraint (i : Fin 3) : Submodule ℂ (Space i) :=
  Operator.fibreSub Measure.count fun k => bggK i (Fourier.Torus.freq k)

/-- The fibrewise reducing family on the torus. -/
theorem fibreReducing :
    FibreReducing (Fourier.Torus.symbolComplex bggFamily)
      fun i k => bggK i (Fourier.Torus.freq k) :=
  Fourier.Torus.fibreReducing isFibreReducing

instance (i : Fin 3) : (constraint i).HasOrthogonalProjection :=
  fibreReducing.hasOrthogonalProjection i

/-- **`K` is a reducing subcomplex** (the projection hypothesis, proved).
[QuennevilleBelair2015], §6.3 -/
theorem reducingSubcomplex : complex.ReducingSubcomplex constraint :=
  fibreReducing.toReducingSubcomplex

/-- **TSD propagation for the BGG system on `𝕋³`**: strong solutions of `U' = L U + F` with data and forcing in
`K` stay in `K`. [QuennevilleBelair2015], §6.3 -/
theorem tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates hU h0 hF

/-- TSD propagation for the sign convention `U' = -L U + F` of Thesis (4.4). [QuennevilleBelair2015], §6.3 -/
theorem tsd_propagates_neg {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution (-complex.wave) (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates_neg hU h0 hF

/-- **TSD propagation on `𝕋³` with existence**: for `U₀ ∈ D(L) ∩ K` and admissible forcing in `K`, the
Hodge wave equation has a classical solution, unique among strong solutions, staying in `K`.
[QuennevilleBelair2015], §6.3 -/
theorem tsd_existsUnique {U₀ : PiLp 2 Space} (hU₀ : U₀ ∈ complex.wave.domain)
    (hU₀K : U₀ ∈ HilbertComplex.totalSub constraint) {F : ℝ → PiLp 2 Space} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complex.wave a b F)
    (hFK : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complex.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complex.wave (Icc a b) F V →
        EqOn V U (Icc a b) :=
  fibreReducing.existsUnique_mem hU₀ hU₀K hF hFK

/-- The wave group of the periodic complex preserves `K` for all times (forward and backward).
[QuennevilleBelair2015], §6.3 -/
theorem waveGroup_mem (t : ℝ) {x : PiLp 2 Space} (hx : x ∈ HilbertComplex.totalSub constraint) :
    complex.waveGroup.S t x ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.waveGroup_mem t hx

/-! ### Closed range and the Hodge decomposition -/

theorem freq_cases (k : Fin 3 → ℤ) :
    Fourier.Torus.freq k = 0 ∨ 2 * Real.pi ≤ ‖Fourier.Torus.freq k‖ := by
  by_cases hk : k = 0
  · exact Or.inl (Fourier.Torus.freq_eq_zero_iff.2 hk)
  · exact Or.inr (Fourier.Torus.two_pi_le_norm_freq hk)

/-- **The periodic BGG complex has closed range** at every index (Poincaré constant `4`): at
`ξ = 0` the zeroth-order part `S₁` is still present, and controls the skew part
(`Feec.Fourier.BGG.bggFamily_gap`). [QuennevilleBelair2015], §6.3 -/
theorem closedRangeAt (i : Fin 3) : complex.ClosedRangeAt i :=
  (Fourier.Torus.symbolComplex bggFamily).closedRangeAt_of_gap (C := 4)
    (Filter.Eventually.of_forall fun k => bggFamily_gap _ _ (freq_cases k))

theorem dual_closedRangeAt {i j : Fin 3} (hij : ComplexShape.fin3.Rel i j) :
    complex.dual.ClosedRangeAt i :=
  (Fourier.Torus.symbolComplex bggFamily).dual_closedRangeAt_of_gap hij (C := 4)
    (Filter.Eventually.of_forall fun k => bggFamily_gap _ _ (freq_cases k))

theorem dual_closedRangeAt_two : complex.dual.ClosedRangeAt 2 := by
  have hn : ComplexShape.fin3.next 2 = 2 := ComplexShape.fin3.next_eq_self' 2 fun k h => by
    have : (2 : Fin 3).val + 1 = k.val := h
    have := k.isLt; omega
  have h0 : complex.d 2 (ComplexShape.fin3.next 2) = 0 := complex.shape _ _ (by
    rw [hn]; intro h; have : (2 : Fin 3).val + 1 = (2 : Fin 3).val := h; omega)
  rw [HilbertComplex.ClosedRangeAt, HilbertComplex.boundaries_dual, h0, LinearPMap.adjoint_zero]
  convert (isClosed_singleton (x := (0 : Space 2))) using 1
  ext y; constructor
  · rintro ⟨x, rfl⟩; rfl
  · rintro rfl; exact ⟨0, rfl⟩

theorem dual_closedRangeAt' (i : Fin 3) : complex.dual.ClosedRangeAt i := by
  fin_cases i
  · exact dual_closedRangeAt (j := 1) rfl
  · exact dual_closedRangeAt (j := 2) rfl
  · exact dual_closedRangeAt_two

/-- **Hodge decomposition without closures** for the periodic BGG complex at every index,
pairwise orthogonal. [QuennevilleBelair2015], §6.3 -/
theorem hodge (i : Fin 3) :
    complex.boundaries i ⊔ complex.harmonic i ⊔ complex.dual.boundaries i = ⊤ ∧
      complex.boundaries i ⟂ complex.harmonic i ∧
      complex.harmonic i ⟂ complex.dual.boundaries i ∧
      complex.boundaries i ⟂ complex.dual.boundaries i :=
  complex.hodge_of_closedRangeAt (closedRangeAt i) (dual_closedRangeAt' i)

/-! ### The verdict: the BGG system propagates TSD on `𝕋³` -/

/-- `(L x)₀ = -d₀† x₁`. -/
theorem wave_apply_zero (x : complex.wave.domain) :
    (complex.wave x) 0 = -(complex.d 0 1)† ⟨(x : PiLp 2 Space) 1, x.2.2 1 0⟩ := by
  rw [HilbertComplex.wave_apply, Fin.sum_univ_three, Fin.sum_univ_three,
    complex.apply_eq_zero_of_not_rel (i := 0) (j := 0) (by simp),
    complex.apply_eq_zero_of_not_rel (i := 1) (j := 0) (by simp),
    complex.apply_eq_zero_of_not_rel (i := 2) (j := 0) (by simp),
    adjoint_apply_eq_zero_of_eq_zero (complex.shape 0 0 (by simp)),
    adjoint_apply_eq_zero_of_eq_zero (complex.shape 0 2 (by simp))]
  simp

/-- `(L x)₁ = d₀ x₀ - d₁† x₂`. -/
theorem wave_apply_one (x : complex.wave.domain) :
    (complex.wave x) 1 = complex.d 0 1 ⟨(x : PiLp 2 Space) 0, x.2.1 0 1⟩ -
      (complex.d 1 2)† ⟨(x : PiLp 2 Space) 2, x.2.2 2 1⟩ := by
  rw [HilbertComplex.wave_apply, Fin.sum_univ_three, Fin.sum_univ_three,
    complex.apply_eq_zero_of_not_rel (i := 1) (j := 1) (by simp),
    complex.apply_eq_zero_of_not_rel (i := 2) (j := 1) (by simp),
    adjoint_apply_eq_zero_of_eq_zero (complex.shape 1 0 (by simp)),
    adjoint_apply_eq_zero_of_eq_zero (complex.shape 1 1 (by simp))]
  simp

/-- `(L x)₂ = d₁ x₁`. -/
theorem wave_apply_two (x : complex.wave.domain) :
    (complex.wave x) 2 = complex.d 1 2 ⟨(x : PiLp 2 Space) 1, x.2.1 1 2⟩ := by
  rw [HilbertComplex.wave_apply, Fin.sum_univ_three, Fin.sum_univ_three,
    complex.apply_eq_zero_of_not_rel (i := 0) (j := 2) (by simp),
    complex.apply_eq_zero_of_not_rel (i := 2) (j := 2) (by simp),
    adjoint_apply_eq_zero_of_eq_zero (complex.shape 2 0 (by simp)),
    adjoint_apply_eq_zero_of_eq_zero (complex.shape 2 1 (by simp)),
    adjoint_apply_eq_zero_of_eq_zero (complex.shape 2 2 (by simp))]
  simp

/-- The scalar slot of the constraint is `{0}`. -/
theorem mem_constraint_zero_iff {u : Space 0} : u ∈ constraint 0 ↔ u = 0 := by
  refine ⟨fun h => Lp.ext_count fun k => ?_, fun h => h ▸ Submodule.zero_mem _⟩
  rw [Measure.ae_count_iff.1 (Lp.coeFn_zero (W3 ℂ Mat VM 0) 2 Measure.count) k]
  exact (Submodule.mem_bot ℂ).1 (Measure.ae_count_iff.1 (Operator.mem_fibreSub.1 h) k)

/-- **The third slot of the constraint**: `(M, B) ∈ L²({0} × TSD)` iff `M ≡ 0` and `B` is TSD
(fibrewise: `M̂(k) = 0`, `B̂(k) ∈ tsd (2πk)`). -/
theorem mem_constraint_two_iff {ρ : Space 2} : ρ ∈ constraint 2 ↔
    ∀ k, (WithLp.ofLp ((ρ : (Fin 3 → ℤ) → VM) k)).1 = 0 ∧
      (WithLp.ofLp ((ρ : (Fin 3 → ℤ) → VM) k)).2 ∈ tsd (Fourier.Torus.freq k) := by
  rw [Operator.mem_fibreSub, Measure.ae_count_iff]
  exact forall_congr' fun k => mem_tsdB

/-- **TSD fields are divergence-free**: `L²(TSD) ⊆ ker (grad grad)† = ker div div`. -/
theorem constraint_le_ker_adjoint : constraint 1 ≤ ((complex.d 0 1)†).ker := by
  intro u hu
  change u ∈ ((Fourier.Torus.symbolComplex bggFamily).toHilbertComplex.d 0 1)†.ker
  rw [(Fourier.Torus.symbolComplex bggFamily).adjoint_d 0 1]
  refine Operator.mem_ker_mulOp.2 ?_
  filter_upwards [Operator.mem_fibreSub.1 hu] with k hk
  exact (Submodule.mem_bot ℂ).1 (fibreReducing.map_adj 0 1 k ⟨_, hk, rfl⟩)

theorem mem_domain_adjoint_of_mem_constraint {u : Space 1} (hu : u ∈ constraint 1) :
    u ∈ ((complex.d 0 1)†).domain :=
  LinearPMap.ker_le_domain (constraint_le_ker_adjoint hu)

/-- **TSD data with `E₀ ∈ H(curl)` and `(0, B₀) ∈ D((S₁, curl)†)` lie in `D(L)`.** -/
theorem mem_wave_domain_of {U₀ : PiLp 2 Space} (h0 : U₀ 0 = 0) (hE₀ : U₀ 1 ∈ constraint 1)
    (hE : U₀ 1 ∈ (complex.d 1 2).domain) (hB : U₀ 2 ∈ ((complex.d 1 2)†).domain) :
    U₀ ∈ complex.wave.domain := by
  have htop : ∀ {i j : Fin 3}, ¬ ComplexShape.fin3.Rel i j → ∀ v, v ∈ (complex.d i j).domain :=
    fun h v => complex.domain_eq_top_of_not_rel h ▸ Submodule.mem_top
  have htop' : ∀ {i j : Fin 3}, ¬ ComplexShape.fin3.Rel i j → ∀ v, v ∈ ((complex.d i j)†).domain :=
    fun h v => by rw [complex.shape _ _ h, adjoint_zero]; exact Submodule.mem_top
  refine complex.mem_wave_domain.2 ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact htop (by simp) _
    · change U₀ 0 ∈ (complex.d 0 1).domain; rw [h0]; exact Submodule.zero_mem _
    · exact htop (by simp) _
    · exact htop (by simp) _
    · exact htop (by simp) _
    · exact hE
    · exact htop (by simp) _
    · exact htop (by simp) _
    · exact htop (by simp) _
  · fin_cases i <;> fin_cases j
    · exact htop' (by simp) _
    · exact mem_domain_adjoint_of_mem_constraint hE₀
    · exact htop' (by simp) _
    · exact htop' (by simp) _
    · exact htop' (by simp) _
    · exact hB
    · exact htop' (by simp) _
    · exact htop' (by simp) _
    · exact htop' (by simp) _

/-- **The BGG system propagates TSD on `𝕋³`.** For data `U₀ = (0, E₀, (0, B₀))` in `D(L)` with
`E₀`, `B₀` TSD, the Hodge wave equation `U' = L U` of the complex (5.1) has a classical solution
on `[a, b]` (Stone), unique among strong solutions, and for every `t`:
`σ(t) = 0`, `u(t) = E(t)` is TSD (the weakly imposed symmetry holds strongly), the multiplier
`M(t)` vanishes and `B(t)` is TSD (`mem_constraint_two_iff`), and `(E, (M, B))` solves the
reduced system (4.15): `E' = -(S₁, curl)* (M, B)`, `(M, B)' = (S₁, curl) E`. Periodic counterpart
of the whole-space verdict.
See [QuennevilleBelair2015], §6.3, Eq. (4.15) (§4.10). -/
theorem verdict {U₀ : PiLp 2 Space} (hU₀ : U₀ ∈ complex.wave.domain) (h0 : U₀ 0 = 0)
    (hE₀ : U₀ 1 ∈ constraint 1) (hB₀ : U₀ 2 ∈ constraint 2) (a b : ℝ) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complex.wave (Icc a b) 0 U ∧
      (∀ V, V a = U₀ → Evolution.IsStrongSolution complex.wave (Icc a b) 0 V →
        EqOn V U (Icc a b)) ∧
      ∀ t ∈ Icc a b, U t 0 = 0 ∧ U t 1 ∈ constraint 1 ∧ U t 2 ∈ constraint 2 ∧
        ∃ (hE : U t 1 ∈ (complex.d 1 2).domain) (hB : U t 2 ∈ ((complex.d 1 2)†).domain),
          HasDerivWithinAt (fun s => U s 1) (-(complex.d 1 2)† ⟨U t 2, hB⟩) (Icc a b) t ∧
          HasDerivWithinAt (fun s => U s 2) (complex.d 1 2 ⟨U t 1, hE⟩) (Icc a b) t := by
  have hK : U₀ ∈ HilbertComplex.totalSub constraint := by
    intro i
    fin_cases i
    · exact mem_constraint_zero_iff.2 h0
    · exact hE₀
    · exact hB₀
  have hF : Evolution.ForcingClass.admissible complex.wave a b 0 :=
    Evolution.ForcingClass.admissible_of_C1 (F' := 0) continuous_zero.continuousOn
      continuous_zero.continuousOn fun t _ => hasDerivAt_const t (0 : PiLp 2 Space)
  obtain ⟨U, hU0, hU, hUK, huniq⟩ :=
    reducingSubcomplex.existsUnique_mem hU₀ hK hF fun _ _ => Submodule.zero_mem _
  refine ⟨U, hU0, hU, huniq, fun t ht => ?_⟩
  have hσ : U t 0 = 0 := mem_constraint_zero_iff.1 (hUK t ht 0)
  have hdom := hU.toIsStrongSolution.mem_domain ht
  have hd := hU.toIsStrongSolution.hasDerivWithinAt ht
  refine ⟨hσ, hUK t ht 1, hUK t ht 2, hdom.1 1 2, hdom.2 2 1, ?_, ?_⟩
  · have h1 : HasDerivWithinAt (fun s => U s 1)
        ((complex.wave ⟨U t, hdom⟩ + (0 : ℝ → PiLp 2 Space) t) 1) (Icc a b) t :=
      (PiLp.proj (𝕜 := ℝ) 2 Space 1).hasFDerivAt.comp_hasDerivWithinAt t hd
    refine h1.congr_deriv ?_
    rw [Pi.zero_apply, add_zero, wave_apply_one,
      LinearPMap.apply_mk_eq_zero _ _ hσ, zero_sub]
  · have h2 : HasDerivWithinAt (fun s => U s 2)
        ((complex.wave ⟨U t, hdom⟩ + (0 : ℝ → PiLp 2 Space) t) 2) (Icc a b) t :=
      (PiLp.proj (𝕜 := ℝ) 2 Space 2).hasFDerivAt.comp_hasDerivWithinAt t hd
    refine h2.congr_deriv ?_
    rw [Pi.zero_apply, add_zero, wave_apply_two]

end Feec.Models.Torus.BGG
