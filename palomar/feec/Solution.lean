module

public import Solution.Convert
public import Solution.Existence
public import Solution.Torus

/-!
# Galerkin approximation of Hilbert complexes (solution)

The three theorems of `Challenge.lean`. Theorem 1 (`FEEC.projectionFEEC`) from
`Feec.HilbertComplex.Subcomplex.exists_cochainProjection` and
`Feec.HilbertComplex.Subcomplex.exists_isGraphBounded_iff`; Theorem 2 (`FEEC.staticFEEC`) from
the static verdict with explicit constants (`HilbertComplex.SubcomplexFamily.staticVerdict_of`,
through `Feec.HilbertComplex.SubcomplexFamily.staticFEEC` and `Solution.Bridge`) and the rates of
`Solution.Rates`; Theorem 3 (`FEEC.evolutionFEEC`) from the wave and heat verdicts
(`HilbertComplex.SubcomplexFamily.waveVerdict`, `heatVerdict`, through
`Feec.HilbertComplex.approxFEEC`, `Feec.HilbertComplex.ConstrainedFEEC.heatFEEC` and
`Solution.Dynamic`) and `Solution.Rates`. The witness `FEEC.spectral_nonvacuous` from the
spectral Galerkin family of the torus and its `Hˢ` Jackson estimate (`Solution.Torus`), the
hypotheses of Theorem 1 through Theorem 1 itself.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996]
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

/-- **Non-vacuity of Theorems 1–3: spectral Galerkin for the de Rham complex of the torus**: the
band subcomplexes of `Feec.Models.Torus.DeRhamGalerkin` with the Fourier truncations, through
`Solution.Torus`; the harmonic forms are the constant forms
(`Feec.Models.Torus.DeRham.finrank_harmonic`); the discrete Poincaré inequality and the harmonic
bound from Theorem 1, under closed ranges, since the truncations are bounded in the graph norm;
the Jackson estimate of the truncations on the `Hˢ` classes (`Torus.jackson`, from
`Feec.Fourier.Torus.norm_sub_starProjection_band_le`). -/
theorem spectral_nonvacuous (n : ℕ) [NeZero n] :
    ∃ (H : HilbertComplex ℂ (TorusForm n)) (F : H.SubcomplexFamily ℕ) (J : F.Jackson NNReal),
      (∀ k (u : TorusForm n k) (w : TorusForm n (k + 1)), (u, w) ∈ (H.d k (k + 1)).graph ↔
        ∀ ξ (s : {s : Finset (Fin n) // (s.card : ℤ) = k + 1}), w ξ s = torusD u ξ s.1) ∧
      F.l = atTop ∧
      (∀ N k (u : TorusForm n k), u ∈ (F.V N).V k ↔ ∀ ξ, (∃ j, (N : ℤ) < |ξ j|) → u ξ = 0) ∧
      (∀ N k (x : (H.d k (k + 1)).domain) ξ, ((F.π N).π k x : TorusForm n k) ξ =
        if ∀ j, |ξ j| ≤ N then (x : TorusForm n k) ξ else 0) ∧
      (∀ k, FiniteDimensional ℂ (H.harmonic k)) ∧
      (∀ k : ℕ, Module.finrank ℂ (H.harmonic k) = n.choose k) ∧
      (∀ k : ℤ, 0 ≤ k → k ≤ n → ∀ N, (F.V N).V k ≠ ⊤) ∧
      (∀ k, IsClosed (H.boundaries k : Set (TorusForm n k))) ∧
      (∀ k, H.PoincareBy k (√(1 + (2 * Real.pi)⁻¹ ^ 2))) ∧
      (∀ k, ∃ c₁ c₂ : ℝ, ∀ N, (F.V N).PoincareBy k c₁ ∧ (F.V N).HarmonicBoundBy k c₂) ∧
      (∀ k, F.IsGraphBoundedBy k 1) ∧
      (∀ N k (x : (H.d k (k + 1)).domain),
        ‖((F.π N).π k x : TorusForm n k)‖ ≤ ‖(x : TorusForm n k)‖) ∧
      (∀ k, F.Approximates k) ∧ (∀ a m, F.ApproximatesOn a m) ∧
      (∀ N k (q : H.harmonic k), (F.π N).harmonicError q = 0) ∧
      (∀ N, J.meshSize N = (2 * Real.pi * (N + 1))⁻¹) ∧ (∀ s, J.ord s = s) ∧
      (∀ s k, J.B s k = 1) ∧ ∀ s k L (x : TorusForm n k), J.Reg s k L x ↔
        IsTorusSobolev s L x ∧
          ∀ hx : x ∈ (H.d k (k + 1)).domain, IsTorusSobolev s L (H.d k (k + 1) ⟨x, hx⟩) :=
  ⟨Torus.complexC n, Torus.family n, Torus.jackson n, Torus.mem_graph_iff, rfl, Torus.mem_V_iff,
    Torus.π_apply, fun _ => inferInstance, Torus.finrank_harmonic, fun _ => Torus.V_ne_top,
    Torus.isClosed_boundaries, Torus.poincareBy,
    ((projectionFEEC atTop (Torus.family n).V).2 Torus.isClosed_boundaries).1
      ⟨Torus.family n, rfl, rfl, fun k => ⟨1, Torus.isGraphBoundedBy k⟩⟩,
    Torus.isGraphBoundedBy, Torus.norm_π_le, Torus.approximates, Torus.approximatesOn,
    fun N _ q => Torus.harmonicError_eq_zero N q, fun _ => rfl, fun _ => rfl, fun _ _ => rfl,
    fun _ _ _ _ => Iff.rfl⟩

end FEEC
