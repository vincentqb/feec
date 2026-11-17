module

public import Solution.Cube
public import Solution.Existence
public import Solution.Witness
public import Solution.BGGBridge

/-!
# Finite element exterior calculus: Hilbert complexes, Whitney forms and BGG complexes (solution)

The compared theorems of `Challenge.lean`. `FEEC.feec` from the full static verdict
(`HilbertComplex.SubcomplexFamily.exists_staticVerdict`, through
`Feec.HilbertComplex.SubcomplexFamily.staticFEEC` and `Solution.Bridge`) and the full wave verdict
(`HilbertComplex.SubcomplexFamily.waveVerdict`, through `Feec.HilbertComplex.approxFEEC` and
`Solution.Dynamic`), projected to the compared fields. `FEEC.feec_cube` from `Solution.Cube` (the
Whitney forms on the Freudenthal meshes of the cube, `Feec.Models.StarShaped.CubeWitness`) and the
static rate of `Solution.Rates`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021]
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996]
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012]
* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set MeasureTheory

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


open Feec.Domain Feec.FiniteElement Feec.Models.StarShaped Feec.Models.Cube HilbertComplex in
/-- **A finite element family meets the hypotheses of `FEEC.feec`: Whitney forms on the
cube.** -/
theorem feec_cube (n : ℕ) [NeZero n] :
    ∃ (H : HilbertComplex ℝ (L2Form (cube n))) (F : H.SubcomplexFamily ℕ),
      (∀ k, H.d k (k + 1) = dMax (cube n) k) ∧ F.l = atTop ∧
      (∀ N k, ∀ u ∈ (F.V N).V k, ∀ (z : Fin n → Fin (N + 1)) (σ : Equiv.Perm (Fin n)),
        ∃ (a : Finset (Fin n) → ℝ) (A : Finset (Fin n) → Fin n → ℝ), ∀ s : FormIdx n k,
          ⇑(u s) =ᵐ[volume.restrict (cube n ∩ convexHull ℝ (range fun (j : Fin (n + 1)) i =>
            ((z i : ℝ) + if (σ.symm i : ℕ) < j then 1 else 0) / (2 * (N + 1))))]
            fun x => a s.1 + ∑ i, A s.1 i * x i) ∧
      (∀ i, F.IsGraphBounded i) ∧ (∀ i, F.Approximates i) ∧
      (∀ i, IsClosed (H.boundaries i : Set (L2Form (cube n) i))) ∧
      ∀ j, ∃ C, ∀ {f : L2Form (cube n) j} {σ : (H.d (j - 1) j).domain}
        {u : (H.d j (j + 1)).domain} {p : L2Form (cube n) j},
        H.IsMixedSolution j ⊤ ⊤ (H.harmonic j) f σ u p → ∀ {L : ℝ}, 0 ≤ L →
        IsCsForm (cube n) 0 (j - 1) L σ → IsCsForm (cube n) 0 j L u → IsCsForm (cube n) 0 j L p →
        IsCsForm (cube n) 0 j L ((H.boundaries j).topologicalClosure.starProjection u) →
        ∀ (N : ℕ) {σh : (H.d (j - 1) j).domain} {uh : (H.d j (j + 1)).domain} {ph},
          H.IsMixedSolution j ((F.V N).V (j - 1)) ((F.V N).V j) ((F.V N).harmonic j) f σh uh ph →
          H.mixedError j σ σh u uh p ph ≤ C * L / (N + 1) := by
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
  have hR := F.rated J
  refine ⟨H, F, fun k => dMax_cube k, rfl, fun N k u hu z σ => ?_, hB, hA, hcr, fun j => ?_⟩
  · obtain ⟨T, hT, hpts⟩ := exists_kuhn N z σ
    obtain ⟨w, hw, hae⟩ := exists_piece_of_mem_poly (FEM.mesh n N) (Fm.domain_eq N)
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
  · obtain ⟨C, hC⟩ := hR.static j (hB _) (hB _) (hcr _) (hcr _) ()
    refine ⟨C / 2, fun {f σ u p} hs {L} hL h1 h2 h3 h4 N σh uh ph hsh => ?_⟩
    have h := hC hs hL h1 h2 h3 h4 N hsh
    have hm : J.meshSize N ^ J.ord () = 1 / 2 / (N + 1) := by
      change (FEM.mesh n N).meshSize ^ (1 : ℝ) = _
      rw [Real.rpow_one, FEM.meshSize_mesh, FEM.hN_eq_meshSize, FEM.meshSize]
    rw [hm] at h
    refine h.trans_eq ?_
    field_simp

section BGGSection

open CategoryTheory

/-- **The BGG construction** ([ArnoldHu2021], §5.2). For a stacked diagram `S : Ṽ ⟶ V⟦1⟧` of
cochain complexes of modules over any ring, with `Sⁱ` injective for `i < J` and onto modulo `d`
for `i ≥ J` (`R(dⁱ) + R(Sⁱ) = Vⁱ⁺¹`; in particular when `Sⁱ` is surjective, [ArnoldHu2021], (23)),
the inclusion `Γ → T` and the projection `Γ → Γ / Δ` are quasi-isomorphisms: the BGG complex has
the cohomology of the twisted complex. -/
theorem bggCohomology {R : Type u} [Ring R] {V Vt : CochainComplex (ModuleCat.{v} R) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (J : ℤ) (hinj : ∀ i < J, Function.Injective (S.f i))
    (hsurj : ∀ i, J ≤ i →
      LinearMap.range (V.d i (i + 1)).hom ⊔ LinearMap.range (BGG.conn S i (i + 1)) = ⊤) :
    QuasiIso (BGG.bggΓι S J) ∧ QuasiIso (BGG.bggπ S J) := by
  have h := BGG.eliminates_toData S hinj hsurj
  exact ⟨BGG.quasiIso_bggΓι h, BGG.quasiIso_bggπ h⟩

/-- **The cohomology of the BGG complex** ([ArnoldHu2021], Theorem 6). Over a field, under the
hypotheses of `FEEC.bggCohomology`, if both rows have finite-dimensional cohomology in degree `i`,
so does the BGG complex, `dim Hⁱ(Γ / Δ) ≤ dim Hⁱ(V) + dim Hⁱ(Ṽ)`, with equality if and only if
`Sⁱ⁻¹` and `Sⁱ` induce the zero maps on cohomology ([ArnoldHu2021], (27)). -/
theorem bggFinrank {K : Type u} [Field K] {V Vt : CochainComplex (ModuleCat.{v} K) ℤ}
    (S : Vt ⟶ V⟦(1 : ℤ)⟧) (J : ℤ) (hinj : ∀ i < J, Function.Injective (S.f i))
    (hsurj : ∀ i, J ≤ i →
      LinearMap.range (V.d i (i + 1)).hom ⊔ LinearMap.range (BGG.conn S i (i + 1)) = ⊤) (i : ℤ)
    [FiniteDimensional K (V.homology i)] [FiniteDimensional K (Vt.homology i)] :
    FiniteDimensional K ((BGG.bgg S J).homology i) ∧
      Module.finrank K ((BGG.bgg S J).homology i) ≤
        Module.finrank K (V.homology i) + Module.finrank K (Vt.homology i) ∧
      (Module.finrank K ((BGG.bgg S J).homology i) =
          Module.finrank K (V.homology i) + Module.finrank K (Vt.homology i) ↔
        BGG.InducesZero S (i - 1) ∧ BGG.InducesZero S i) :=
  BGG.finiteDimensional_and_finrank_le hinj hsurj i

/-- **The BGG complex of bounded Hilbert complexes is a bounded Hilbert complex with closed
ranges** ([ArnoldHu2021], Theorem 6 and the remark after it). For complexes `d`, `d̃` of bounded
operators on Hilbert spaces and bounded `s`, `d s = -s d̃`, bounded below for `i < J` and onto
modulo `d` for `i ≥ J`: `Γⁱ`, `Δⁱ` are closed; `y ↦ [y]` is an isometry of `Γⁱ ∩ (Δⁱ)ᗮ` onto
`Γⁱ / Δⁱ` with the quotient norm of the `ℓ²` norm (a Hilbert norm); the differentials
`[(σ, φ)] ↦ [(dσ - sφ, d̃φ)]` are bounded; and the differential into `Γⁱ⁺¹ / Δⁱ⁺¹` has closed range
where both rows have finite-dimensional cohomology in degree `i + 1`. -/
theorem bggHilbert {𝕜 : Type u} [RCLike 𝕜] {H Ht : ℤ → Type v}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace 𝕜 (H i)] [∀ i, CompleteSpace (H i)]
    [∀ i, NormedAddCommGroup (Ht i)] [∀ i, InnerProductSpace 𝕜 (Ht i)]
    [∀ i, CompleteSpace (Ht i)]
    (d : ∀ i, H i →L[𝕜] H (i + 1)) (hd : ∀ i x, d (i + 1) (d i x) = 0)
    (dt : ∀ i, Ht i →L[𝕜] Ht (i + 1)) (hdt : ∀ i x, dt (i + 1) (dt i x) = 0)
    (s : ∀ i, Ht i →L[𝕜] H (i + 1)) (hs : ∀ i x, d (i + 1) (s i x) = -s (i + 1) (dt i x))
    (J : ℤ) (hinj : ∀ i < J, ∃ C, AntilipschitzWith C (s i))
    (hsurj : ∀ i, J ≤ i → LinearMap.range (d i : H i →ₗ[𝕜] H (i + 1)) ⊔
      LinearMap.range (s i : Ht i →ₗ[𝕜] H (i + 1)) = ⊤) :
    let S := BGG.ofBoundedHom (hd := hd) (hdt := hdt) s hs
    let ΓL := BGG.ΓL (hd := hd) (hdt := hdt) s hs J
    let ΔL := BGG.ΔL (hd := hd) (hdt := hdt) s hs J
    let Q := BGG.QuotL (hd := hd) (hdt := hdt) s hs J
    (∀ i, IsClosed (BGG.Γ S J i : Set (H i × Ht i)) ∧ IsClosed (BGG.Δ S J i : Set (H i × Ht i))) ∧
      (∀ i, ∃ e : ↥(ΓL i ⊓ (ΔL i)ᗮ) ≃ₗᵢ[𝕜] Q i, ∀ y, e y = Submodule.Quotient.mk ⟨y, y.2.1⟩) ∧
      ∃ D : ∀ i, Q i →L[𝕜] Q (i + 1),
        (∀ i (x : ΓL i) (x' : ΓL (i + 1)), (x' : WithLp 2 (H (i + 1) × Ht (i + 1))).ofLp =
          BGG.twist S i (i + 1) (x : WithLp 2 (H i × Ht i)).ofLp →
            D i (Submodule.Quotient.mk x) = Submodule.Quotient.mk x') ∧
        ∀ i, [FiniteDimensional 𝕜 ((BGG.ofBounded d hd).homology (i + 1))] →
          [FiniteDimensional 𝕜 ((BGG.ofBounded dt hdt).homology (i + 1))] →
          IsClosed (Set.range (D i)) :=
  BGG.hilbert s hs J hinj hsurj

end BGGSection

end FEEC
