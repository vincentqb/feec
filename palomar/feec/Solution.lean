module

public import Solution.Rates
public import Solution.Existence
public import Solution.Witness

/-!
# Finite element exterior calculus for Hilbert complexes (solution)

The compared theorems of `Challenge.lean`: `FEEC.feec` from the static verdict
(`HilbertComplex.SubcomplexFamily.exists_staticVerdict`, through
`Feec.HilbertComplex.SubcomplexFamily.staticFEEC` and the bridge `Solution.Bridge`) and the wave
and heat verdicts (`HilbertComplex.SubcomplexFamily.waveVerdict`, `heatVerdict`, through
`Feec.HilbertComplex.approxFEEC`, `Feec.HilbertComplex.dissipFEEC_fullyDiscrete`,
`Feec.HilbertComplex.ConstrainedFEEC.heatFEEC` and `Solution.Dynamic`); `FEEC.feec_rated` from
them (`Solution.Rates`); `FEEC.staticFEEC_uniform` from the explicit constants of `Feec`;
`FEEC.exists_cochainProjection` and `FEEC.exists_subcomplexFamily_iff` from
`Feec.HilbertComplex.Subcomplex.exists_cochainProjection` and
`Feec.HilbertComplex.Subcomplex.exists_isGraphBounded_iff` (`Solution.Existence`);
`FEEC.crimeFEEC` from `Feec.HilbertComplex.ApproxComplexCrime.Family.staticFEEC`, the cochain case
of `Feec.HilbertComplex.Approximation.StaticCochain` and
`Feec.HilbertComplex.ApproxComplexCrime.HeatFamily.heatFEEC` (`Solution.Crime`); and
`FEEC.crime_nonvacuous` from the witness `Solution.Witness`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.3–§3.4, Thm 3.7
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015], Ch. 4
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012], §3
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology

universe u v w

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

/-- **Bounded cochain projections from discrete stability** ([AFW2010], Thm 3.7). -/
theorem exists_cochainProjection {H : HilbertComplex 𝕜 W} (S : H.Subcomplex)
    [∀ i, FiniteDimensional 𝕜 (S.V i)] {c₁ c₂ : ℤ → ℝ} (hc₁ : ∀ i, 0 ≤ c₁ i)
    (hc₂ : ∀ i, 0 ≤ c₂ i) (hP : ∀ i, S.PoincareBy i (c₁ i))
    (hH : ∀ i, S.HarmonicBoundBy i (c₂ i)) :
    ∃ P : S.CochainProjection, ∀ i (x : (H.d i (i + 1)).domain),
      H.graphNorm i (i + 1) ⟨P.π i x, S.le_domain i (i + 1) (P.π i x).2⟩ ≤
        (1 + c₁ i) * (1 + c₂ i) * H.graphNorm i (i + 1) x := by
  obtain ⟨P, hP'⟩ := S.toFeec.exists_cochainProjection hc₁ hc₂ (fun i => (hP i).toFeec)
    fun i => HilbertComplex.Subcomplex.harmonicBound_iff.2 (hH i)
  exact ⟨HilbertComplex.Subcomplex.CochainProjection.ofFeec P, fun i x =>
    HilbertComplex.Subcomplex.CochainProjection.graphNorm_ofFeec_le P
      (mul_nonneg (by linarith [hc₁ i]) (by linarith [hc₂ i])) (hP' i) x⟩

/-- **Uniformly bounded cochain projections exist iff discrete stability holds uniformly**
([AFW2010], Thms 3.6, 3.7 and (30)). -/
theorem exists_subcomplexFamily_iff {κ : Type*} {H : HilbertComplex 𝕜 W} (l : Filter κ)
    (V : κ → H.Subcomplex) [∀ h i, FiniteDimensional 𝕜 ((V h).V i)]
    (hcr : ∀ i, IsClosed (H.boundaries i : Set (W i))) :
    (∃ F : H.SubcomplexFamily κ, F.l = l ∧ F.V = V ∧ ∀ i, F.IsGraphBounded i) ↔
      ∀ i, ∃ c₁ c₂ : ℝ, ∀ h, (V h).PoincareBy i c₁ ∧ (V h).HarmonicBoundBy i c₂ := by
  have key := Feec.HilbertComplex.Subcomplex.exists_isGraphBounded_iff (fun h => (V h).toFeec)
    fun i => (H.closedRangeAt_iff i).2 (hcr i)
  refine ⟨?_, fun hV => ?_⟩
  · rintro ⟨F, rfl, rfl, hF⟩ i
    obtain ⟨c₁, c₂, hc⟩ := key.1 ⟨fun h => (F.π h).toFeec,
      fun i => HilbertComplex.SubcomplexFamily.isGraphBounded_toFeec (hF i)⟩ i
    exact ⟨|c₁|, c₂, fun h => ⟨HilbertComplex.Subcomplex.poincareBy_of_feec (hc h).1,
      HilbertComplex.Subcomplex.harmonicBound_iff.1 (hc h).2⟩⟩
  · obtain ⟨π, hπ⟩ := key.2 fun i => by
      obtain ⟨c₁, c₂, hc⟩ := hV i
      exact ⟨c₁, c₂, fun h =>
        ⟨(hc h).1.toFeec, HilbertComplex.Subcomplex.harmonicBound_iff.2 (hc h).2⟩⟩
    refine ⟨⟨l, V, fun h => HilbertComplex.Subcomplex.CochainProjection.ofFeec (π h)⟩, rfl, rfl,
      fun i => ?_⟩
    obtain ⟨C, hC⟩ := hπ i
    exact ⟨|C|, fun h x => HilbertComplex.Subcomplex.CochainProjection.graphNorm_ofFeec_le (π h)
      (abs_nonneg C) (fun y => (hC h y).trans_eq (by rw [sq_abs])) x⟩

/-- **The constants of the static FEEC theorem** depend only on the bound `c` of the cochain
projections and the Poincaré constant `c_P` ([AFW2010], §3.3–§3.4): one function `Φ` serves every
Hilbert complex, family of subcomplexes and degree. -/
theorem staticFEEC_uniform : ∃ Φ : ℝ → ℝ → ℝ, ∀ {𝕜 : Type u} [RCLike 𝕜] {W : ℤ → Type v}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
    {κ : Type w} {H : HilbertComplex 𝕜 W} (F : H.SubcomplexFamily κ) (j : ℤ) {c cP : ℝ},
    F.IsGraphBoundedBy (j - 1) c → F.IsGraphBoundedBy j c →
    H.PoincareBy (j - 1) cP → H.PoincareBy j cP → F.StaticVerdict j (Φ c cP) :=
  ⟨fun c cP => HilbertComplex.staticConst (max c 1) cP, fun F j _ _ hπ hπ' hP hP' =>
    F.staticVerdict_of j (le_max_right _ _) (hπ.mono (le_max_left _ _)) (hπ'.mono (le_max_left _ _))
      hP hP'⟩

variable [∀ i, NormedSpace ℝ (W i)]

/-- **The FEEC theorem with rates** ([AFW2010], Thm 3.9, §3.5; [QuennevilleBelair2015],
Thm 4.14; [BrennerThomee1979]): for every Jackson estimate `J` of `F`, the static error is
`O(L hᵒʳᵈ⁽ˢ⁾)` and, on every window `F` approximates, the fully discrete wave error
`O(L hᵒʳᵈ⁽ˢ⁾ + τᵖ ‖Lₕ^{p+1} v‖)` (`HilbertComplex.SubcomplexFamily.Rated`). -/
theorem feec_rated {κ ρ : Type*} {H : HilbertComplex 𝕜 W} (F : H.SubcomplexFamily κ)
    (J : F.Jackson ρ) : F.Rated J :=
  F.rated J

/-- **The FEEC theorem** ([AFW2010], Thms 3.4–3.6, 3.8, 3.9; [QuennevilleBelair2015], Thms 4.6,
4.7, 4.14, Props 4.13, 4.16, 4.17; [GilletteHolstZhu2017]; [BrennerThomee1979]). Every family
of subcomplexes satisfies the static, wave and heat verdicts under their hypotheses
(`HilbertComplex.SubcomplexFamily.Verdict`). -/
theorem feec {κ : Type*} {H : HilbertComplex 𝕜 W} (F : H.SubcomplexFamily κ) : F.Verdict :=
  have : ∀ i, IsScalarTower ℝ 𝕜 (W i) := fun _ => isScalarTower_of_normedSpace
  ⟨fun a m => by
    rw [HilbertComplex.wave_eq]; exact (H.toFeec.window a m).isSkewAdjoint_wave,
    fun j hπ hπ' hj hj' => F.exists_staticVerdict j hπ hπ' hj hj', fun a m ha =>
    ⟨F.waveVerdict a m (F.approximates_window a m ha.1 ha.2), fun hπ hπ' hcr =>
      F.heatVerdict a m (F.approximates_window a m ha.1 ha.2) hπ hπ' hcr⟩⟩

/-- **The FEEC theorem with variational crimes** ([HolstStern2012], §3; [AFW2010], Thm 3.8):
on a window with closed ranges (degrees `a + 1, …, a + m - 1`), every approximating family of
discrete differential spaces satisfies the static, cochain and heat verdicts with crimes under
their hypotheses (`HilbertComplex.CrimeFamily.Verdict`). -/
theorem crimeFEEC {κ : Type*} {H : HilbertComplex 𝕜 W} {a : ℤ} {m : ℕ} (S : H.CrimeFamily a m κ)
    (hcr : ∀ i : Fin m, 0 < (i : ℕ) →
      IsClosed (H.boundaries (a + (i : ℕ)) : Set (W (a + (i : ℕ))))) : S.Verdict :=
  have : ∀ i, IsScalarTower ℝ 𝕜 (W i) := fun _ => isScalarTower_of_normedSpace
  ⟨fun hP => S.staticVerdict hcr hP, fun hi _ P => S.cochainVerdict hcr hi P,
    fun hP hJ hconv => S.heatVerdict hcr hP hJ hconv⟩

/-- **Non-vacuity of the crimes** ([HolstStern2012], §3): on the complex `ℝ` in every degree with
`d⁰ = id` and all other differentials `0`, on the window `ℝ --id--> ℝ --0--> ℝ` (harmonic forms
`ℝ (0, 0, 1) ≠ 0`), a family of cochain reading maps `iₙ` with cochain projections `πₙ`,
`iₙ πₙ = 1`, satisfies the hypotheses of the cochain verdict: closed ranges, `iₙ* iₙ ≠ 1` (not
isometric) but `‖1 - iₙ* iₙ‖ → 0`; some discrete harmonic form is read off `ℌ`, and the error at
some datum is positive at every level. -/
theorem crime_nonvacuous : ∃ (H : HilbertComplex ℝ fun _ : ℤ => ℝ)
    (S : H.CrimeFamily.{0} 0 3 ℕ) (P : S.CochainProj 2),
    (∀ i : Fin 3, 0 < (i : ℕ) → IsClosed (H.boundaries (0 + (i : ℕ)) : Set ℝ)) ∧
    S.l = atTop ∧ S.IsCochain ∧ (∀ n, (S.incl n).adjoint ∘L S.incl n ≠ 1) ∧
    Tendsto (fun n => ‖1 - (S.incl n).adjoint ∘L S.incl n‖) atTop (𝓝 0) ∧
    (∀ n (x : (H.totalD 0 3).domain), S.incl n (P.π n x) = x) ∧
    (∃ q ∈ H.totalHarmonic 0 3, q ≠ 0) ∧
    (∀ n, ∃ q ∈ S.harmonic n, S.incl n q ∉ H.totalHarmonic 0 3) ∧
    ∃ f, ∀ σ u p, H.IsTotalMixedSolution 0 3 f σ u p → ∀ n σh uh ph,
      S.IsMixedSolution n f σh uh ph → 0 < S.readError n σ u p σh uh ph := by
  have hcr : ∀ i : Fin 3, 0 < (i : ℕ) →
      IsClosed (Witness.complex.boundaries (0 + (i : ℕ)) : Set ℝ) :=
    fun _ _ => Submodule.closed_of_finiteDimensional _
  have hcr' := Witness.complex.closedRangeAt_win 0 3 hcr
  refine ⟨Witness.complex, Witness.family, Witness.proj, hcr, rfl, Witness.isCochain,
    Witness.J_ne_one, Witness.tendsto_one_sub_J, fun n x => Witness.incl_projL n x,
    ⟨Witness.e2, Witness.mem_totalHarmonic_e2, fun h0 => by
      have := congrArg (fun y : Witness.T3 => y 2) h0
      exact one_ne_zero this⟩,
    fun n => ⟨Witness.e2, Witness.mem_harmonic_e2 n, Witness.incl_e2_not_mem n⟩,
    Witness.e2, fun σ u p hs n σh uh ph hsh => ?_⟩
  obtain ⟨-, -, hp⟩ := Witness.complex.eq_totalSol 0 3 hcr' hs
  obtain ⟨-, -, hp'⟩ := Witness.complex.eq_totalSol 0 3 hcr' Witness.isTotalMixedSolution_e2
  obtain ⟨-, -, hph⟩ := Witness.family.eq_mixedSol hsh
  obtain ⟨-, -, hph'⟩ := Witness.family.eq_mixedSol (Witness.isMixedSolution_e2 n)
  have e1 : p = Witness.e2 := hp.trans hp'.symm
  have e2 : ph = Witness.e2 := hph.trans hph'.symm
  have hpos : 0 < ‖p - Witness.family.incl n ph‖ := by
    rw [e1, e2]
    refine norm_pos_iff.2 fun h0 => ?_
    have h1 := congrArg (fun y : Witness.T3 => y 1) h0
    change Witness.e2 1 - Witness.incl n Witness.e2 1 = 0 at h1
    rw [Witness.incl_e2] at h1
    change (0 : ℝ) - Witness.mesh n = 0 at h1
    linarith [Witness.mesh_pos n]
  unfold HilbertComplex.CrimeFamily.readError
  positivity

end FEEC
