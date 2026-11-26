module

public import Feec.Fourier.Torus
public import Feec.Fourier.BGGSymbol

/-!
# The BGG weak-symmetry complex on `𝕋³`: TSD constraints propagate

The complex (5.1) of the weakly symmetric formulation of [QuennevilleBelair2015], Ch. 6 on `𝕋³`,
on the Fourier side: it has closed range, and `K = {0} × L²(TSD) × ({0} × L²(TSD))` is a
reducing subcomplex, so TSD data stay TSD.

## Main results

* `tsd_existsUnique`: TSD propagation, with existence and uniqueness.
* `closedRangeAt`, `hodge`: closed range and the Hodge decomposition without closures.
* `verdict`: TSD solutions solve the reduced system (4.15).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

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

/-- The periodic BGG weak-symmetry complex (5.1), on the Fourier side. -/
abbrev complex : HilbertComplex ℂ ComplexShape.fin3 Space :=
  Fourier.Torus.complex bggFamily

/-- The constraint space `K = {0} × L²(TSD) × ({0} × L²(TSD))`. -/
abbrev constraint (i : Fin 3) : Submodule ℂ (Space i) :=
  Operator.fibreSub Measure.count fun k => bggK i (Fourier.Torus.freq k)

theorem fibreReducing :
    FibreReducing (Fourier.Torus.symbolComplex bggFamily)
      fun i k => bggK i (Fourier.Torus.freq k) :=
  Fourier.Torus.fibreReducing isFibreReducing

instance (i : Fin 3) : (constraint i).HasOrthogonalProjection :=
  fibreReducing.hasOrthogonalProjection i

theorem reducingSubcomplex : complex.ReducingSubcomplex constraint :=
  fibreReducing.toReducingSubcomplex

theorem tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates hU h0 hF

theorem tsd_propagates_neg {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution (-complex.wave) (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub constraint)
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.propagates_neg hU h0 hF

/-- Data in `K ∩ D(L)` and admissible forcing in `K` give a classical solution, unique among strong
solutions, that stays in `K`. [QuennevilleBelair2015], §6.3 -/
theorem tsd_existsUnique {U₀ : PiLp 2 Space} (hU₀ : U₀ ∈ complex.wave.domain)
    (hU₀K : U₀ ∈ HilbertComplex.totalSub constraint) {F : ℝ → PiLp 2 Space} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complex.wave a b F)
    (hFK : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub constraint) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complex.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub constraint) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complex.wave (Icc a b) F V →
        EqOn V U (Icc a b) :=
  fibreReducing.existsUnique_mem hU₀ hU₀K hF hFK

theorem waveGroup_mem (t : ℝ) {x : PiLp 2 Space} (hx : x ∈ HilbertComplex.totalSub constraint) :
    complex.waveGroup.S t x ∈ HilbertComplex.totalSub constraint :=
  fibreReducing.waveGroup_mem t hx

theorem freq_cases (k : Fin 3 → ℤ) :
    Fourier.Torus.freq k = 0 ∨ 2 * Real.pi ≤ ‖Fourier.Torus.freq k‖ := by
  by_cases hk : k = 0
  · exact Or.inl (Fourier.Torus.freq_eq_zero_iff.2 hk)
  · exact Or.inr (Fourier.Torus.two_pi_le_norm_freq hk)

/-- The periodic BGG complex has closed range at every index. -/
theorem closedRangeAt (i : Fin 3) : complex.ClosedRangeAt i :=
  (Fourier.Torus.symbolComplex bggFamily).closedRangeAt_of_gap (C := 4)
    (Filter.Eventually.of_forall fun k => bggFamily_gap _ _ (freq_cases k))

theorem dual_closedRangeAt {i j : Fin 3} (hij : ComplexShape.fin3.Rel i j) :
    complex.dual.ClosedRangeAt i :=
  (Fourier.Torus.symbolComplex bggFamily).dual_closedRangeAt_of_gap hij (C := 4)
    (Filter.Eventually.of_forall fun k => bggFamily_gap _ _ (freq_cases k))

theorem dual_closedRangeAt' (i : Fin 3) : complex.dual.ClosedRangeAt i := by
  fin_cases i
  · exact dual_closedRangeAt (j := 1) rfl
  · exact dual_closedRangeAt (j := 2) rfl
  · exact complex.dual_closedRangeAt_of_forall_not_rel fun k h => by
      have : (2 : Fin 3).val + 1 = k.val := h
      have := k.isLt; omega

/-- The Hodge decomposition without closures of the periodic BGG complex at every index. -/
theorem hodge (i : Fin 3) :
    complex.boundaries i ⊔ complex.harmonic i ⊔ complex.dual.boundaries i = ⊤ ∧
      complex.boundaries i ⟂ complex.harmonic i ∧
      complex.harmonic i ⟂ complex.dual.boundaries i ∧
      complex.boundaries i ⟂ complex.dual.boundaries i :=
  complex.hodge_of_closedRangeAt (closedRangeAt i) (dual_closedRangeAt' i)

theorem wave_apply_zero (x : complex.wave.domain) :
    (complex.wave x) 0 = -(complex.d 0 1)† ⟨(x : PiLp 2 Space) 1, x.2.2 1 0⟩ := by
  rw [HilbertComplex.wave_apply, Fin.sum_univ_three, Fin.sum_univ_three,
    complex.apply_eq_zero_of_not_rel (i := 0) (j := 0) (by simp),
    complex.apply_eq_zero_of_not_rel (i := 1) (j := 0) (by simp),
    complex.apply_eq_zero_of_not_rel (i := 2) (j := 0) (by simp),
    adjoint_apply_eq_zero_of_eq_zero (complex.shape 0 0 (by simp)),
    adjoint_apply_eq_zero_of_eq_zero (complex.shape 0 2 (by simp))]
  simp

theorem wave_apply_one (x : complex.wave.domain) :
    (complex.wave x) 1 = complex.d 0 1 ⟨(x : PiLp 2 Space) 0, x.2.1 0 1⟩ -
      (complex.d 1 2)† ⟨(x : PiLp 2 Space) 2, x.2.2 2 1⟩ := by
  rw [HilbertComplex.wave_apply, Fin.sum_univ_three, Fin.sum_univ_three,
    complex.apply_eq_zero_of_not_rel (i := 1) (j := 1) (by simp),
    complex.apply_eq_zero_of_not_rel (i := 2) (j := 1) (by simp),
    adjoint_apply_eq_zero_of_eq_zero (complex.shape 1 0 (by simp)),
    adjoint_apply_eq_zero_of_eq_zero (complex.shape 1 1 (by simp))]
  simp

theorem wave_apply_two (x : complex.wave.domain) :
    (complex.wave x) 2 = complex.d 1 2 ⟨(x : PiLp 2 Space) 1, x.2.1 1 2⟩ := by
  rw [HilbertComplex.wave_apply, Fin.sum_univ_three, Fin.sum_univ_three,
    complex.apply_eq_zero_of_not_rel (i := 0) (j := 2) (by simp),
    complex.apply_eq_zero_of_not_rel (i := 2) (j := 2) (by simp),
    adjoint_apply_eq_zero_of_eq_zero (complex.shape 2 0 (by simp)),
    adjoint_apply_eq_zero_of_eq_zero (complex.shape 2 1 (by simp)),
    adjoint_apply_eq_zero_of_eq_zero (complex.shape 2 2 (by simp))]
  simp

theorem mem_constraint_zero_iff {u : Space 0} : u ∈ constraint 0 ↔ u = 0 := by
  refine ⟨fun h => Lp.ext_count fun k => ?_, fun h => h ▸ Submodule.zero_mem _⟩
  rw [Measure.ae_count_iff.1 (Lp.coeFn_zero (W3 ℂ Mat VM 0) 2 Measure.count) k]
  exact (Submodule.mem_bot ℂ).1 (Measure.ae_count_iff.1 (Operator.mem_fibreSub.1 h) k)

theorem mem_constraint_two_iff {ρ : Space 2} : ρ ∈ constraint 2 ↔
    ∀ k, (WithLp.ofLp ((ρ : (Fin 3 → ℤ) → VM) k)).1 = 0 ∧
      (WithLp.ofLp ((ρ : (Fin 3 → ℤ) → VM) k)).2 ∈ tsd (Fourier.Torus.freq k) := by
  rw [Operator.mem_fibreSub, Measure.ae_count_iff]
  exact forall_congr' fun k => mem_tsdB

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

/-- For TSD data `(0, E₀, (0, B₀)) ∈ D(L)`, the unique solution stays TSD, with multiplier `0`, and
solves the reduced system (4.15). [QuennevilleBelair2015], §6.3 -/
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
