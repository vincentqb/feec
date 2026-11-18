module

public import Solution.Cube
public import Solution.Convert
public import Solution.Existence
public import Solution.Witness

/-!
# Galerkin approximation of Hilbert complexes (solution)

The four theorems of `Challenge.lean` and their witnesses. Theorem 1 (`FEEC.projectionFEEC`)
from `Feec.HilbertComplex.Subcomplex.exists_cochainProjection` and
`Feec.HilbertComplex.Subcomplex.exists_isGraphBounded_iff`; Theorem 2 (`FEEC.staticFEEC`) from
the static verdict with explicit constants (`HilbertComplex.SubcomplexFamily.staticVerdict_of`,
through `Feec.HilbertComplex.SubcomplexFamily.staticFEEC` and `Solution.Bridge`) and the rates of
`Solution.Rates`; Theorem 3 (`FEEC.evolutionFEEC`) from the wave and heat verdicts
(`HilbertComplex.SubcomplexFamily.waveVerdict`, `heatVerdict`, through
`Feec.HilbertComplex.approxFEEC`, `Feec.HilbertComplex.ConstrainedFEEC.heatFEEC` and
`Solution.Dynamic`) and `Solution.Rates`; Theorem 4 (`FEEC.crimeFEEC`) from `Solution.Crime`. The
witnesses: `FEEC.crime_nonvacuous` from `Solution.Witness`, `FEEC.feec_cube` from `Solution.Cube`
(the Whitney forms on the Freudenthal meshes of the cube, `Feec.Models.StarShaped.CubeWitness`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996]
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace LinearPMap
open Filter Topology Set MeasureTheory

universe u v w

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

/-- **Bounded cochain projections from discrete stability** ([AFW2010], Thm 3.7), for one
subcomplex. -/
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

/-- **Theorem 1: bounded cochain projections ⇔ uniform discrete stability** ([AFW2010], Thm 3.7
and its converse, Thm 3.6 and (30)): the projections of `FEEC.exists_cochainProjection` for every
`h`, and `Feec.HilbertComplex.Subcomplex.exists_isGraphBounded_iff` under closed ranges. -/
theorem projectionFEEC {κ : Type*} {H : HilbertComplex 𝕜 W} (l : Filter κ)
    (V : κ → H.Subcomplex) [∀ h i, FiniteDimensional 𝕜 ((V h).V i)] :
    (∀ c₁ c₂ : ℤ → ℝ, (∀ i, 0 ≤ c₁ i) → (∀ i, 0 ≤ c₂ i) →
      (∀ h i, (V h).PoincareBy i (c₁ i) ∧ (V h).HarmonicBoundBy i (c₂ i)) →
      ∃ F : H.SubcomplexFamily κ, F.l = l ∧ F.V = V ∧
        ∀ i, F.IsGraphBoundedBy i ((1 + c₁ i) * (1 + c₂ i))) ∧
    ((∀ i, IsClosed (H.boundaries i : Set (W i))) →
      ((∃ F : H.SubcomplexFamily κ, F.l = l ∧ F.V = V ∧ ∀ i, F.IsGraphBounded i) ↔
        ∀ i, ∃ c₁ c₂ : ℝ, ∀ h, (V h).PoincareBy i c₁ ∧ (V h).HarmonicBoundBy i c₂)) := by
  refine ⟨fun c₁ c₂ hc₁ hc₂ hV => ?_, fun hcr => ?_⟩
  · choose P hP using fun h => exists_cochainProjection (V h) hc₁ hc₂ (fun i => (hV h i).1)
      fun i => (hV h i).2
    exact ⟨⟨l, V, P⟩, rfl, rfl, fun i h x => hP h i x⟩
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

/-- **Theorem 2: the static theory** ([AFW2010], Thms 3.4–3.6, 3.8, 3.9, §3.3–§3.5): closed range
is the Poincaré inequality (`HilbertComplex.closedRange_iff_poincareBy`); the static verdict with
the constant `HilbertComplex.staticConst (max c 1) c_P`
(`HilbertComplex.SubcomplexFamily.staticVerdict_of`) and the rates of
`HilbertComplex.SubcomplexFamily.rated`. -/
theorem staticFEEC : ∃ Φ : ℝ → ℝ → ℝ, ∀ {𝕜 : Type u} [RCLike 𝕜] {W : ℤ → Type v}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
    {H : HilbertComplex 𝕜 W},
    (∀ i, IsClosed (H.boundaries (i + 1) : Set (W (i + 1))) ↔ ∃ c, H.PoincareBy i c) ∧
    ∀ {κ : Type w} (F : H.SubcomplexFamily κ) (j : ℤ) {c cP : ℝ},
      F.IsGraphBoundedBy (j - 1) c → F.IsGraphBoundedBy j c →
      H.PoincareBy (j - 1) cP → H.PoincareBy j cP →
      F.StaticVerdict j (Φ c cP) ∧ ∀ {ρ : Type*} (J : F.Jackson ρ) (s : ρ),
        F.HasRate j (J.Reg s) fun h => J.meshSize h ^ J.ord s :=
  ⟨fun c cP => HilbertComplex.staticConst (max c 1) cP, fun {_ _ _ _ _ _ H} =>
    ⟨H.closedRange_iff_poincareBy, fun F j c _ hπ hπ' hP hP' =>
      ⟨(F.staticVerdict_of j (le_max_right _ _) (hπ.mono (le_max_left _ _))
        (hπ'.mono (le_max_left _ _)) hP hP').toStaticVerdict, fun J s =>
        (F.rated J).hasRate j ⟨c, hπ⟩ ⟨c, hπ'⟩
          ((H.closedRange_iff_poincareBy_of_eq (sub_add_cancel j 1)).2 ⟨_, hP⟩)
          ((H.closedRange_iff_poincareBy j).2 ⟨_, hP'⟩) s⟩⟩⟩

variable [∀ i, NormedSpace ℝ (W i)]

/-- **Theorem 3: the evolution equations** ([QuennevilleBelair2015], Thms 4.6, 4.7, 4.14,
Prop 4.13; [GilletteHolstZhu2017]; [BrennerThomee1979]): the skew-adjointness of `Feec`'s window,
the wave verdict (`HilbertComplex.SubcomplexFamily.waveVerdict`) with its rates
(`HilbertComplex.SubcomplexFamily.WaveVerdict.hasWaveRate`) and the heat verdict
(`HilbertComplex.SubcomplexFamily.heatVerdict`). -/
theorem evolutionFEEC {κ : Type*} {H : HilbertComplex 𝕜 W} (F : H.SubcomplexFamily κ) (a : ℤ)
    (m : ℕ) : (H.wave a m)† = -H.wave a m ∧
    (F.ApproximatesOn a m → ∃ S, F.WaveVerdict a m S ∧ ∀ {ρ : Type*} (J : F.Jackson ρ) (s : ρ),
      F.HasWaveRate a m S (J.Reg s) fun h => J.meshSize h ^ J.ord s) ∧
    (F.ApproximatesOn a m → (∀ i : Fin m, (i : ℕ) + 1 < m → F.IsGraphBounded (a + (i : ℕ))) →
      (∀ i : Fin m, (i : ℕ) + 1 = m → ∃ C : ℝ, ∀ (h : κ)
        (x : (H.d (a + (i : ℕ)) (a + (i : ℕ) + 1)).domain),
          ‖((F.π h).π _ x : W (a + (i : ℕ)))‖ ≤ C * ‖(x : W (a + (i : ℕ)))‖) →
      (∀ i : Fin m, 0 < (i : ℕ) →
        IsClosed (H.boundaries (a + (i : ℕ)) : Set (W (a + (i : ℕ))))) →
      ∃ S, EvolutionVerdict (sq (H.wave a m)) F.l (fun h => F.Xh a m h)
        (fun h => (F.Xh a m h).subtypeL) (fun h => F.Lh a m h ^ 2) S) :=
  have : ∀ i, IsScalarTower ℝ 𝕜 (W i) := fun _ => RCLike.isScalarTower_of_normedSpace
  ⟨by rw [HilbertComplex.wave_eq]; exact (H.toFeec.window a m).isSkewAdjoint_wave,
    fun ha => (F.waveVerdict a m (F.approximates_window a m ha.1 ha.2)).imp fun _ hS =>
      ⟨hS, fun J s => hS.hasWaveRate J s⟩,
    fun ha hπ hπ' hcr => F.heatVerdict a m (F.approximates_window a m ha.1 ha.2) hπ hπ' hcr⟩

/-- **Theorem 4: variational crimes** ([HolstStern2012], §3; [AFW2010], Thm 3.8): on a window with
closed ranges (degrees `a + 1, …, a + m - 1`), the static, cochain and heat verdicts of
`Solution.Crime` (`HilbertComplex.CrimeFamily.staticVerdict`, `cochainVerdict`, `heatVerdict`). -/
theorem crimeFEEC {κ : Type*} {H : HilbertComplex 𝕜 W} {a : ℤ} {m : ℕ} (S : H.CrimeFamily a m κ)
    (hcr : ∀ i : Fin m, 0 < (i : ℕ) →
      IsClosed (H.boundaries (a + (i : ℕ)) : Set (W (a + (i : ℕ))))) :
    (∀ {cP : ℝ}, S.IsPoincare cP → ∃ C, S.StaticVerdict C) ∧
    (S.IsCochain → ∀ {Cπ : ℝ} (P : S.CochainProj Cπ), S.CochainVerdict P) ∧
    ∀ {cP : ℝ}, S.IsPoincare cP → Tendsto S.defect S.l (𝓝 0) → (∀ f, S.ConvergesAt f) →
      ∃ U, EvolutionVerdict (sq (H.wave a m)) S.l S.X S.incl
        (fun h => (S.D h - (S.D h).adjoint) ^ 2) U :=
  have : ∀ i, IsScalarTower ℝ 𝕜 (W i) := fun _ => RCLike.isScalarTower_of_normedSpace
  ⟨fun hP => (S.staticVerdict hcr hP).imp fun _ V => V.toStaticVerdict,
    fun hi _ P => (S.cochainVerdict hcr hi P).toCochainVerdict,
    fun hP hJ hconv => S.heatVerdict hcr hP hJ hconv⟩

/-- **Non-vacuity of Theorem 4** ([HolstStern2012], §3): on the complex `ℝ` in every degree with
`d⁰ = id` and all other differentials `0`, on the window `ℝ --id--> ℝ --0--> ℝ` (harmonic forms
`ℝ (0, 0, 1) ≠ 0`), a family of cochain reading maps `iₙ` with cochain projections `πₙ`,
`iₙ πₙ = 1`, satisfies the hypotheses of the cochain verdict: closed ranges, `iₙ* iₙ ≠ 1` (not
isometric) but `‖1 - iₙ* iₙ‖ → 0`; some discrete harmonic form is read off `ℌ`, and the error at
some datum is positive at every level. -/
theorem crime_nonvacuous : ∃ (H : HilbertComplex ℝ fun _ : ℤ => ℝ)
    (S : H.CrimeFamily.{0} 0 3 ℕ) (P : S.CochainProj 2),
    (∀ i : Fin 3, 0 < (i : ℕ) → IsClosed (H.boundaries (0 + (i : ℕ)) : Set ℝ)) ∧
    S.l = atTop ∧ S.IsCochain ∧ (∀ n, (S.incl n).adjoint ∘L S.incl n ≠ 1) ∧
    Tendsto S.defect atTop (𝓝 0) ∧
    (∀ n (x : (H.totalD 0 3).domain), S.incl n (P.π n x) = x) ∧
    (∃ q ∈ H.totalHarmonic 0 3, q ≠ 0) ∧
    (∀ n, ∃ q ∈ S.harmonic n, S.incl n q ∉ H.totalHarmonic 0 3) ∧
    ∃ f, ∀ x, IsMixedSolution (H.totalMixedSpace 0 3) f x → ∀ n xh,
      S.IsSolution n f xh → 0 < S.readError n x xh := by
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
    Witness.e2, fun ⟨σ, u, p⟩ hs n ⟨σh, uh, ph⟩ hsh => ?_⟩
  replace hs := HilbertComplex.isMixedSolution_total_iff.1 hs
  replace hsh := (Witness.family.isSolution_iff).1 hsh
  rw [HilbertComplex.CrimeFamily.readError_eq₀]
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
  unfold HilbertComplex.CrimeFamily.readError₀
  positivity


open Feec.Domain Feec.FiniteElement Feec.Models.StarShaped Feec.Models.Cube HilbertComplex in
/-- **A finite element family meets the hypotheses of Theorems 2 and 3: Whitney forms on the
cube.** -/
theorem feec_cube (n : ℕ) [NeZero n] :
    ∃ (H : HilbertComplex ℝ (L2Form (cube n))) (F : H.SubcomplexFamily ℕ),
      (∀ k, H.d k (k + 1) = dMax (cube n) k) ∧ F.l = atTop ∧
      (∀ N k, ∀ u ∈ (F.V N).V k, ∀ (z : Fin n → Fin (N + 1)) (σ : Equiv.Perm (Fin n)),
        ∃ (a : Finset (Fin n) → ℝ) (A : Finset (Fin n) → Fin n → ℝ), ∀ s : FormIdx n k,
          ⇑(u s) =ᵐ[volume.restrict (cube n ∩ convexHull ℝ (range fun (j : Fin (n + 1)) i =>
            ((z i : ℝ) + if (σ.symm i : ℕ) < j then 1 else 0) / (2 * (N + 1))))]
            fun x => a s.1 + ∑ i, A s.1 i * x i) ∧
      (∃ C : ℝ, ∀ N i (x : (H.d i (i + 1)).domain),
        ‖((F.π N).π i x : L2Form (cube n) i)‖ ≤ C * ‖(x : L2Form (cube n) i)‖) ∧
      (∀ i, F.IsGraphBounded i) ∧ (∀ i, F.Approximates i) ∧
      (∀ i, IsClosed (H.boundaries i : Set (L2Form (cube n) i))) ∧
      ∀ j, F.HasRate j (IsCsForm (cube n) 0) fun N => 1 / (N + 1) := by
  set D := CubeWitness.starDomain n
  set Fm := CubeWitness.meshFamily n
  obtain ⟨K, hK1, hK⟩ := Fm.exists_uniform_polyProj whitney
  choose π hπ1 hπ2 using hK
  let H : HilbertComplex ℝ (L2Form (cube n)) := HilbertComplex.ofFeec D.complex
  let F : H.SubcomplexFamily ℕ :=
    { l := atTop
      V := fun N => Subcomplex.ofFeec (Fm.poly whitney N)
      finiteDimensional := fun N i =>
        inferInstanceAs (FiniteDimensional ℝ ((Fm.poly whitney N).V i))
      π := fun N => CochainProjection.ofFeec (π N) }
  have hA : ∀ i, F.Approximates i := fun i =>
    H.approximates_of_eventually F i fun x ε hε =>
      Fm.eventually_exists_poly_graph whitney i x.1 x.2 hε
  have hB : ∀ i, F.IsGraphBounded i := fun i =>
    ⟨K, fun N x => H.graphNorm_le_of_sq (by linarith) (hπ2 N i (i + 1) x)⟩
  have hcr : ∀ i, IsClosed (H.boundaries i : Set (L2Form (cube n) i)) := fun i =>
    (H.closedRangeAt_iff i).1 ((Feec.HilbertComplex.closedRangeAt_iff_poincare_of_rel _
      (rel_sub_one i)).2 ⟨_, CubeWitness.hasPoincare n (i - 1) i (rel_sub_one i)⟩)
  let J : F.Jackson Unit :=
    { meshSize := fun N => (Fm.mesh N).meshSize
      meshSize_nonneg := fun N => (Fm.meshSize_pos N).le
      tendsto_meshSize := Fm.tendsto_meshSize
      Reg := fun _ j L x => IsCsForm (cube n) 0 j L x
      ord := fun _ => 1
      B := fun _ => Fm.polyInterpBound whitney
      jackson := fun _ N i L x hL hx => by
        obtain ⟨v, hv, h1, h2⟩ := Fm.exists_mem_poly_le_of_isCsForm whitney
          (whitney_polyOrderAt i) ((isCsForm_cube 0 i L x).1 hx) hL N
        have e : Fm.polyInterpBound whitney i * L * (Fm.mesh N).meshSize ^ (0 + 1) =
            Fm.polyInterpBound whitney i * (L * (Fm.mesh N).meshSize ^ (1 : ℝ)) := by
          rw [Real.rpow_one]; ring
        exact ⟨v, hv, e ▸ h1, fun j hxj => e ▸ h2 j hxj⟩ }
  refine ⟨H, F, fun k => dMax_cube k, rfl, fun N k u hu z σ => ?_,
    ⟨K, fun N i x => hπ1 N i x.1⟩, hB, hA, hcr, fun j => ?_⟩
  · obtain ⟨T, hT, hpts⟩ := FEM.exists_mem_simplices_points_eq N z σ
    obtain ⟨w, hw, hae⟩ := PolySeq.exists_piece_of_mem_subcomplex (FEM.mesh n N) (Fm.domain_eq N)
      (Fm.isOpen_domain N) D.isOpen whitney hu hT
    obtain ⟨a, A, haff⟩ := exists_affine_of_mem_polySpace_one
      (polyMinusSpace_le_polySpace (r := 1) (k := k.toNat) hw)
    refine ⟨a, A, fun s => ?_⟩
    have hset : convexHull ℝ (range fun (j : Fin (n + 1)) i =>
        ((z i : ℝ) + if (σ.symm i : ℕ) < j then 1 else 0) / (2 * (N + 1))) = T.closedInterior := by
      rw [← Affine.Simplex.convexHull_eq_closedInterior]
      congr 2
      funext j i
      exact (hpts j i).symm
    rw [hset]
    filter_upwards [hae s] with x hx
    exact hx.trans (haff _ _)
  · obtain ⟨C, hC⟩ := (F.rated J).hasRate j (hB _) (hB _) (hcr _) (hcr _) ()
    refine ⟨C / 2, fun {f x} hs {L} hL h1 h2 h3 h4 N xh hsh => ?_⟩
    have h := hC hs hL h1 h2 h3 h4 N hsh
    have hm : J.meshSize N ^ J.ord () = 1 / 2 / (N + 1) := by
      change (FEM.mesh n N).meshSize ^ (1 : ℝ) = _
      rw [Real.rpow_one, FEM.meshSize_mesh, FEM.hN_eq_meshSize, FEM.meshSize]
    change _ ≤ C * L * (J.meshSize N ^ J.ord ()) at h
    rw [hm] at h
    refine h.trans_eq ?_
    ring

end FEEC
