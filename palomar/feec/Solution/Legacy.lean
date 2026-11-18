module

public import Solution.Defs

/-!
# The definitions of the challenge before its redesign

The challenge states the mixed problems with one Galerkin space (`FEEC.IsMixedSolution`) and the
crime problems on triples; the proofs of `Solution.Bridge` and `Solution.Crime` were written for
the earlier, componentwise forms, kept here (`HilbertComplex.IsMixedSolution`, the three equations;
`SubcomplexFamily.StaticVerdict₀`, `SubcomplexFamily.Rated₀`, `IsTotalMixedSolution`,
`CrimeFamily.StaticVerdict₀`, `CrimeFamily.CochainVerdict₀`, `CrimeFamily.Verdict₀`).
`Solution.Convert` proves the challenge's verdicts from these.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

universe u

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex

variable (H : HilbertComplex 𝕜 W)

/-! ### The mixed Hodge Laplacian -/

/-- `(σ, u, p) ∈ A × B × Q` solves the **mixed Hodge Laplacian** in degree `j` with data `f`,
Galerkin in `A ⊆ Wʲ⁻¹`, `B ⊆ Wʲ` and `Q ⊆ Wʲ` (the harmonic forms for the exact problem):
`⟪τ, σ⟫ - ⟪dτ, u⟫ = 0`, `⟪v, dσ⟫ + ⟪dv, du⟫ + ⟪v, p⟫ = ⟪v, f⟫`, `⟪q, u⟫ = 0`. -/
structure IsMixedSolution (j : ℤ) (A : Submodule 𝕜 (W (j - 1))) (B Q : Submodule 𝕜 (W j))
    (f : W j) (σ : (H.d (j - 1) j).domain) (u : (H.d j (j + 1)).domain) (p : W j) : Prop where
  mem : (σ : W (j - 1)) ∈ A ∧ (u : W j) ∈ B ∧ p ∈ Q
  fst : ∀ τ : (H.d (j - 1) j).domain, (τ : W (j - 1)) ∈ A →
    ⟪(τ : W (j - 1)), (σ : W (j - 1))⟫_𝕜 - ⟪H.d (j - 1) j τ, (u : W j)⟫_𝕜 = 0
  snd : ∀ v : (H.d j (j + 1)).domain, (v : W j) ∈ B →
    ⟪(v : W j), H.d (j - 1) j σ⟫_𝕜 + ⟪H.d j (j + 1) v, H.d j (j + 1) u⟫_𝕜 + ⟪(v : W j), p⟫_𝕜 =
      ⟪(v : W j), f⟫_𝕜
  harm : ∀ q ∈ Q, ⟪q, (u : W j)⟫_𝕜 = 0

/-- The **mixed form** `B(σ, u, p; τ, v, q) = ⟪τ, σ⟫ - ⟪dτ, u⟫ + ⟪v, dσ⟫ + ⟪dv, du⟫ + ⟪v, p⟫ -
⟪q, u⟫` of the mixed Hodge Laplacian in degree `j`. -/
def mixedForm (j : ℤ) (σ : (H.d (j - 1) j).domain) (u : (H.d j (j + 1)).domain) (p : W j)
    (τ : (H.d (j - 1) j).domain) (v : (H.d j (j + 1)).domain) (q : W j) : 𝕜 :=
  ⟪(τ : W (j - 1)), (σ : W (j - 1))⟫_𝕜 - ⟪H.d (j - 1) j τ, (u : W j)⟫_𝕜 +
    ⟪(v : W j), H.d (j - 1) j σ⟫_𝕜 + ⟪H.d j (j + 1) v, H.d j (j + 1) u⟫_𝕜 + ⟪(v : W j), p⟫_𝕜 -
    ⟪q, (u : W j)⟫_𝕜

/-- The norm `‖σ‖_V + ‖u‖_V + ‖p‖` of the mixed space `Vʲ⁻¹ × Vʲ × Wʲ`. -/
def mixedNorm₃ (j : ℤ) (σ : (H.d (j - 1) j).domain) (u : (H.d j (j + 1)).domain) (p : W j) : ℝ :=
  H.graphNorm (j - 1) j σ + H.graphNorm j (j + 1) u + ‖p‖

/-- The error `‖σ - σ'‖_V + ‖u - u'‖_V + ‖p - p'‖`. -/
def mixedError (j : ℤ) (σ σ' : (H.d (j - 1) j).domain) (u u' : (H.d j (j + 1)).domain)
    (p p' : W j) : ℝ :=
  H.mixedNorm₃ j (σ - σ') (u - u') (p - p')


variable {H} {κ : Type*}

/-- **The conclusions of the static FEEC theorem** in degree `j` for the family of subcomplexes
`F`, with the constant `C` (independent of `h`) in every bound. -/
structure SubcomplexFamily.StaticVerdict₀ (F : H.SubcomplexFamily κ) (j : ℤ) (C : ℝ) : Prop where
  /-- the gap from `ℌʲ` to `ℌₕʲ`: `dist(q, ℌₕʲ) ≤ ‖q - πₕ q‖` -/
  harmonicDist (h : κ) (q : W j) (hq : q ∈ H.harmonic j) :
    Metric.infDist q ((F.V h).harmonic j) ≤ ‖q - (F.π h).π j ⟨q, H.harmonic_le_domain j hq⟩‖
  /-- the gap from `ℌₕʲ` to `ℌʲ`: `‖q - P_ℌ q‖ ≤ ‖P_ℌ q - πₕ P_ℌ q‖` -/
  discreteHarmonicDist (h : κ) (q : W j) (hq : q ∈ (F.V h).harmonic j) :
    ‖q - (H.harmonic j).starProjection q‖ ≤ ‖(H.harmonic j).starProjection q -
      (F.π h).π j ⟨_, H.harmonic_le_domain j (Submodule.starProjection_apply_mem _ q)⟩‖
  /-- `πₕ` induces a left inverse of the map induced by the inclusion -/
  cohomologyMap_comp_incl (h : κ) :
    (F.π h).cohomologyMap j ∘ₗ (F.V h).cohomologyIncl j = LinearMap.id
  /-- where `‖q - πₕ q‖ < ‖q‖` on `ℌʲ \ 0`, both are isomorphisms `Hʲ ≅ Hʲ(Vₕ)` -/
  cohomology_of_lt (h : κ)
    (hgap : ∀ (q : W j) (hq : q ∈ H.harmonic j), q ≠ 0 →
      ‖q - (F.π h).π j ⟨q, H.harmonic_le_domain j hq⟩‖ < ‖q‖) :
    Function.Bijective ((F.π h).cohomologyMap j) ∧ Function.Bijective ((F.V h).cohomologyIncl j)
  /-- where `F` approximates in degree `j` and `ℌʲ` is finite-dimensional, the harmonic gap tends
  to `0` -/
  harmonicGap (ha : F.Approximates j) [FiniteDimensional 𝕜 (H.harmonic j)] :
    Tendsto (fun h => (F.π h).harmonicGap j) F.l (𝓝 0)
  /-- and both maps are eventually isomorphisms `Hʲ ≅ Hʲ(Vₕ)` -/
  cohomology (ha : F.Approximates j) [FiniteDimensional 𝕜 (H.harmonic j)] :
    ∀ᶠ h in F.l, Function.Bijective ((F.π h).cohomologyMap j) ∧
      Function.Bijective ((F.V h).cohomologyIncl j)
  /-- the uniform discrete Poincaré inequality `‖v‖_V ≤ C ‖d v‖` on `Vₕʲ ⊥ 𝔷ₕʲ` -/
  poincare (h : κ) : (F.V h).PoincareBy j C
  /-- the mixed problem is uniquely solvable -/
  existsUnique (f : W j) : ∃! x : (H.d (j - 1) j).domain × (H.d j (j + 1)).domain × W j,
    H.IsMixedSolution j ⊤ ⊤ (H.harmonic j) f x.1 x.2.1 x.2.2
  /-- and so is its Galerkin discretization in `Vₕ` -/
  existsUnique_discrete (h : κ) (f : W j) :
    ∃! x : (H.d (j - 1) j).domain × (H.d j (j + 1)).domain × W j,
      H.IsMixedSolution j ((F.V h).V (j - 1)) ((F.V h).V j) ((F.V h).harmonic j) f x.1 x.2.1 x.2.2
  /-- the uniform discrete inf-sup condition: every `x = (σ, u, p) ∈ Vₕʲ⁻¹ × Vₕʲ × ℌₕʲ` has a
  `y = (τ, v, q)` there with `‖y‖ ≤ ‖x‖` and `‖x‖² ≤ C |B(x; y)|` (inf-sup constant `1 / C`) -/
  infSup : ∀ (h : κ) (σ : (H.d (j - 1) j).domain) (u : (H.d j (j + 1)).domain) (p : W j),
    (σ : W (j - 1)) ∈ (F.V h).V (j - 1) → (u : W j) ∈ (F.V h).V j → p ∈ (F.V h).harmonic j →
    ∃ (τ : (H.d (j - 1) j).domain) (v : (H.d j (j + 1)).domain) (q : W j),
      (τ : W (j - 1)) ∈ (F.V h).V (j - 1) ∧ (v : W j) ∈ (F.V h).V j ∧ q ∈ (F.V h).harmonic j ∧
      H.mixedNorm₃ j τ v q ≤ H.mixedNorm₃ j σ u p ∧
      H.mixedNorm₃ j σ u p ^ 2 ≤ C * ‖H.mixedForm j σ u p τ v q‖
  /-- the discrete solutions are stable: `‖σₕ‖_V + ‖uₕ‖_V + ‖pₕ‖ ≤ C ‖f‖` -/
  stable : ∀ (h : κ) {f : W j} {σh : (H.d (j - 1) j).domain}
    {uh : (H.d j (j + 1)).domain} {ph : W j},
    H.IsMixedSolution j ((F.V h).V (j - 1)) ((F.V h).V j) ((F.V h).harmonic j) f σh uh ph →
      H.mixedNorm₃ j σh uh ph ≤ C * ‖f‖
  /-- the discrete solutions are quasi-optimal in the graph norm, `P_𝔅` the orthogonal
  projection onto the closure of `𝔅ʲ` -/
  quasiOptimal : ∀ {f : W j} {σ : (H.d (j - 1) j).domain} {u : (H.d j (j + 1)).domain}
    {p : W j} (hs : H.IsMixedSolution j ⊤ ⊤ (H.harmonic j) f σ u p)
    (h : κ) {σh : (H.d (j - 1) j).domain} {uh : (H.d j (j + 1)).domain} {ph : W j},
    H.IsMixedSolution j ((F.V h).V (j - 1)) ((F.V h).V j) ((F.V h).harmonic j) f σh uh ph →
    H.mixedError j σ σh u uh p ph ≤ C * ((F.V h).graphDist (j - 1) j σ +
      (F.V h).graphDist j (j + 1) u +
      (F.V h).graphDist j (j + 1) ⟨p, H.harmonic_le_domain j hs.mem.2.2⟩ +
      (F.π h).harmonicGap j * (F.V h).graphDist j (j + 1)
        ⟨_, H.topologicalClosure_boundaries_le_domain j
          (Submodule.starProjection_apply_mem (H.boundaries j).topologicalClosure (u : W j))⟩)
  /-- where `F` approximates in degrees `j - 1` and `j`, the discrete solutions converge in the
  graph norm -/
  converges (ha : F.Approximates (j - 1)) (ha' : F.Approximates j) {f : W j}
    {σ : (H.d (j - 1) j).domain} {u : (H.d j (j + 1)).domain} {p : W j}
    (hs : H.IsMixedSolution j ⊤ ⊤ (H.harmonic j) f σ u p)
    {σh : κ → (H.d (j - 1) j).domain} {uh : κ → (H.d j (j + 1)).domain} {ph : κ → W j}
    (hsh : ∀ h, H.IsMixedSolution j ((F.V h).V (j - 1)) ((F.V h).V j) ((F.V h).harmonic j) f
      (σh h) (uh h) (ph h)) :
    Tendsto (fun h => H.mixedError j σ (σh h) u (uh h) p (ph h)) F.l (𝓝 0)

namespace SubcomplexFamily

variable {H : HilbertComplex 𝕜 W} {κ : Type*} (F : H.SubcomplexFamily κ) [∀ i, NormedSpace ℝ (W i)]

/-- **The rates of a Jackson estimate** `J` of `F`, constants independent of `h`, `τ`, `n`, `L`
and the data. -/
structure Rated₀ {ρ : Type*} (J : F.Jackson ρ) : Prop where
  /-- the mixed method in degree `j` is `O(L hᵒʳᵈ⁽ˢ⁾)` when `σ`, `u`, `p`, `P_𝔅 u` are `s`-regular
  with bound `L` ([AFW2010], Thm 3.9, §3.5) -/
  static (j : ℤ) (hπ : F.IsGraphBounded (j - 1)) (hπ' : F.IsGraphBounded j)
    (hj : IsClosed (H.boundaries j : Set (W j)))
    (hj' : IsClosed (H.boundaries (j + 1) : Set (W (j + 1)))) (s : ρ) :
    ∃ C, ∀ {f : W j} {σ : (H.d (j - 1) j).domain} {u : (H.d j (j + 1)).domain} {p : W j},
      H.IsMixedSolution j ⊤ ⊤ (H.harmonic j) f σ u p → ∀ {L : ℝ}, 0 ≤ L →
      J.Reg s (j - 1) L σ → J.Reg s j L u → J.Reg s j L p →
      J.Reg s j L ((H.boundaries j).topologicalClosure.starProjection (u : W j)) →
      ∀ (h : κ) {σh : (H.d (j - 1) j).domain} {uh : (H.d j (j + 1)).domain} {ph : W j},
      H.IsMixedSolution j ((F.V h).V (j - 1)) ((F.V h).V j) ((F.V h).harmonic j) f σh uh ph →
      H.mixedError j σ σh u uh p ph ≤ C * L * J.meshSize h ^ J.ord s
  /-- on a window `F` approximates, with its group `S`, the iterates `r(τ Lₕ)ⁿ v` of an A-stable
  rational scheme of order `p` have the error
  `‖v - x‖ + C (1 + nτ) L hᵒʳᵈ⁽ˢ⁾ + K nτ τᵖ ‖Lₕ^{p+1} v‖` when the components of `S(t) x`,
  `S(t) L x` are `s`-regular with bound `L` on `[0, nτ]` ([QuennevilleBelair2015], Thm 4.14;
  [BrennerThomee1979]) -/
  wave (a : ℤ) (m : ℕ) (ha : F.ApproximatesOn a m) (P Q : Polynomial ℝ) (hr : IsAStable P Q)
    {p : ℕ} (hp : HasOrder P Q p) (s : ρ) : ∃ S, F.WaveVerdict a m S ∧ ∃ C K : ℝ,
      ∀ (x : Total W a m) (hx : x ∈ (H.wave a m).domain),
      H.wave a m ⟨x, hx⟩ ∈ (H.wave a m).domain → ∀ {L : ℝ}, 0 ≤ L → ∀ (h : κ) {τ : ℝ}, 0 ≤ τ →
      ∀ (n : ℕ) (v : F.Xh a m h), (∀ t ∈ Icc 0 (n * τ), ∀ i : Fin m,
        J.Reg s (a + (i : ℕ)) L (S t x i) ∧ J.Reg s (a + (i : ℕ)) L (S t (H.wave a m ⟨x, hx⟩) i)) →
      ‖S (n * τ) x - ((rationalApply P Q ((τ : 𝕜) • F.Lh a m h) ^ n) v : Total W a m)‖ ≤
        ‖(v : Total W a m) - x‖ + C * (1 + n * τ) * L * J.meshSize h ^ J.ord s +
          K * (n * τ) * τ ^ p * ‖(F.Lh a m h ^ (p + 1)) v‖


end SubcomplexFamily


/-- `(σ, u, p)` solves the **mixed Hodge Laplacian of the window** with data `f`: `p ∈ ℌ`, and
`⟪τ, σ⟫ - ⟪𝐝τ, u⟫ = 0`, `⟪v, 𝐝σ⟫ + ⟪𝐝v, 𝐝u⟫ + ⟪v, p⟫ = ⟪v, f⟫` for `τ, v ∈ D(𝐝)`, `u ⊥ ℌ`. -/
structure IsTotalMixedSolution (H : HilbertComplex 𝕜 W) (a : ℤ) (m : ℕ) (f : Total W a m)
    (σ u : (H.totalD a m).domain) (p : Total W a m) : Prop where
  mem : p ∈ H.totalHarmonic a m
  fst : ∀ τ : (H.totalD a m).domain,
    ⟪(τ : Total W a m), (σ : Total W a m)⟫_𝕜 - ⟪H.totalD a m τ, (u : Total W a m)⟫_𝕜 = 0
  snd : ∀ v : (H.totalD a m).domain, ⟪(v : Total W a m), H.totalD a m σ⟫_𝕜 +
    ⟪H.totalD a m v, H.totalD a m u⟫_𝕜 + ⟪(v : Total W a m), p⟫_𝕜 = ⟪(v : Total W a m), f⟫_𝕜
  harm : ∀ q ∈ H.totalHarmonic a m, ⟪q, (u : Total W a m)⟫_𝕜 = 0

namespace CrimeFamily

variable {H : HilbertComplex 𝕜 W} {a : ℤ} {m : ℕ} {κ : Type*} (S : H.CrimeFamily a m κ)

/-- The residual `B(σ, u, p; τ, v, q) - ⟪iₕ v, f⟫` of `(σ, u, p)` in the discrete mixed problem
with the load `iₕ* f`, at the test function `(τ, v, q)`. -/
def residual₀ (h : κ) (f : Total W a m) (σ u p τ v q : S.X h) : 𝕜 :=
  ⟪τ, σ⟫_𝕜 - ⟪S.D h τ, u⟫_𝕜 + ⟪v, S.D h σ⟫_𝕜 + ⟪S.D h v, S.D h u⟫_𝕜 + ⟪v, p⟫_𝕜 - ⟪q, u⟫_𝕜 -
    ⟪S.incl h v, f⟫_𝕜

/-- `(σₕ, uₕ, pₕ)` solves the **discrete mixed problem** with the load `iₕ* f`: `pₕ ∈ ℌₕ` and the
residual vanishes at every test function `(τ, v, q) ∈ Xₕ × Xₕ × ℌₕ`. -/
def IsMixedSolution (h : κ) (f : Total W a m) (σ u p : S.X h) : Prop :=
  p ∈ S.harmonic h ∧ ∀ τ v q, q ∈ S.harmonic h → S.residual₀ h f σ u p τ v q = 0

/-- The **read error** `‖σ - iₕ σ̃‖ + ‖𝐝σ - iₕ 𝐝ₕ σ̃‖ + ‖u - iₕ ũ‖ + ‖𝐝u - iₕ 𝐝ₕ ũ‖ + ‖p - iₕ p̃‖`
of a discrete triple against a continuous one. -/
def readError₀ (h : κ) (σ u : (H.totalD a m).domain) (p : Total W a m) (σ' u' p' : S.X h) : ℝ :=
  ‖(σ : Total W a m) - S.incl h σ'‖ + ‖H.totalD a m σ - S.incl h (S.D h σ')‖ +
    ‖(u : Total W a m) - S.incl h u'‖ + ‖H.totalD a m u - S.incl h (S.D h u')‖ +
    ‖p - S.incl h p'‖

/-- **Consistent approximation** at the data `f`: discrete triples whose read error against the
solution and whose residual (in the dual graph norm) tend to `0`. -/
def IsConsistentAt₀ (f : Total W a m) : Prop :=
  ∀ σ u p, H.IsTotalMixedSolution a m f σ u p → ∀ ε > 0, ∀ᶠ h in S.l,
    ∃ σ' u' p' : S.X h, p' ∈ S.harmonic h ∧ S.readError₀ h σ u p σ' u' p' ≤ ε ∧
      ∀ τ v q, q ∈ S.harmonic h → ‖S.residual₀ h f σ' u' p' τ v q‖ ≤
        ε * (‖τ‖ + ‖S.D h τ‖ + ‖v‖ + ‖S.D h v‖ + ‖q‖)

/-- **The static FEEC theorem with variational crimes**, constant `C`: unique solvability,
stability, the Strang lemma (error at most the read error of any discrete triple plus `C` times
its residual), and convergence for every datum from consistency on a dense set. -/
structure StaticVerdict₀ (C : ℝ) : Prop where
  /-- the mixed problem of the window is uniquely solvable -/
  existsUnique (f : Total W a m) : ∃! x : (H.totalD a m).domain × (H.totalD a m).domain ×
    Total W a m, H.IsTotalMixedSolution a m f x.1 x.2.1 x.2.2
  /-- and so is the discrete one -/
  existsUnique_discrete (h : κ) (f : Total W a m) :
    ∃! x : S.X h × S.X h × S.X h, S.IsMixedSolution h f x.1 x.2.1 x.2.2
  /-- uniformly stable in the discrete graph norm -/
  stable (h : κ) {f : Total W a m} {σ u p : S.X h} (hs : S.IsMixedSolution h f σ u p) :
    ‖σ‖ + ‖S.D h σ‖ + ‖u‖ + ‖S.D h u‖ + ‖p‖ ≤ C * ‖f‖
  /-- the Strang lemma: best read approximation plus residual -/
  strang (h : κ) {f : Total W a m} {σ u : (H.totalD a m).domain} {p : Total W a m}
    (hs : H.IsTotalMixedSolution a m f σ u p) {σh uh ph : S.X h}
    (hsh : S.IsMixedSolution h f σh uh ph) (σ' u' p' : S.X h) (hp' : p' ∈ S.harmonic h) {ε : ℝ}
    (hε : 0 ≤ ε) (hres : ∀ τ v q, q ∈ S.harmonic h → ‖S.residual₀ h f σ' u' p' τ v q‖ ≤
      ε * (‖τ‖ + ‖S.D h τ‖ + ‖v‖ + ‖S.D h v‖ + ‖q‖)) :
    S.readError₀ h σ u p σh uh ph ≤ S.readError₀ h σ u p σ' u' p' + C * ε
  /-- convergence for every datum from consistency on a dense set -/
  converges {D : Set (Total W a m)} (hD : Dense D) (hc : ∀ g ∈ D, S.IsConsistentAt₀ g)
    {f : Total W a m} {σ u : (H.totalD a m).domain} {p : Total W a m}
    (hs : H.IsTotalMixedSolution a m f σ u p) {σh uh ph : ∀ h, S.X h}
    (hsh : ∀ h, S.IsMixedSolution h f (σh h) (uh h) (ph h)) :
    Tendsto (fun h => S.readError₀ h σ u p (σh h) (uh h) (ph h)) S.l (𝓝 0)

/-- **The static FEEC theorem with cochain reading maps** and the cochain projections `P`
([HolstStern2012], Thms 3.3, 3.5, 3.10, Cors 3.4, 3.11). -/
structure CochainVerdict₀ {Cπ : ℝ} (P : S.CochainProj Cπ) : Prop where
  /-- the uniform discrete Poincaré inequality -/
  poincare : ∃ cP, S.IsPoincare cP
  /-- convergence for every datum when `‖1 - iₕ* iₕ‖ → 0` and `iₕ πₕ → 1` on `D(𝐝)` -/
  converges (hJ : Tendsto (fun h => ‖1 - (S.incl h).adjoint ∘L S.incl h‖) S.l (𝓝 0))
    (hπ : ∀ x : (H.totalD a m).domain,
      Tendsto (fun h => ‖(x : Total W a m) - S.incl h (P.π h x)‖) S.l (𝓝 0))
    {f : Total W a m} {σ u : (H.totalD a m).domain} {p : Total W a m}
    (hs : H.IsTotalMixedSolution a m f σ u p) {σh uh ph : ∀ h, S.X h}
    (hsh : ∀ h, S.IsMixedSolution h f (σh h) (uh h) (ph h)) :
    Tendsto (fun h => S.readError₀ h σ u p (σh h) (uh h) (ph h)) S.l (𝓝 0)
  /-- eventually `[z] ↦ [πₕ z]` is an isomorphism `H(𝐝) ≅ H(𝐝ₕ)`: onto (every discrete cycle is
  `πₕ` of a cycle up to a discrete boundary) and one-to-one (a cycle `z` with `πₕ z` a discrete
  boundary is a boundary) -/
  cohomology [FiniteDimensional 𝕜 (H.totalHarmonic a m)]
    (hπ : ∀ q ∈ H.totalHarmonic a m, Tendsto (fun h => ‖q - S.incl h (P.π h q)‖) S.l (𝓝 0)) :
    ∀ᶠ h in S.l, (∀ w : S.X h, S.D h w = 0 → ∃ z : (H.totalD a m).domain,
        H.totalD a m z = 0 ∧ ∃ y, w - P.π h z = S.D h y) ∧
      ∀ z : (H.totalD a m).domain, H.totalD a m z = 0 → (∃ y, P.π h z = S.D h y) →
        ∃ y : (H.totalD a m).domain, (z : Total W a m) = H.totalD a m y
  /-- the error is at most `K ε` when `σ, u, p` and `P_𝔅 u` are within `ε` of `iₕ Xₕ` in the graph
  norm and `‖1 - iₕ* iₕ‖ (‖σ‖ + ‖𝐝σ‖ + ‖u‖ + ‖𝐝u‖ + ‖p‖) ≤ ε` -/
  rate : ∃ K : ℝ, ∀ (h : κ) {f : Total W a m} {σ u : (H.totalD a m).domain} {p : Total W a m},
    H.IsTotalMixedSolution a m f σ u p → ∀ {σh uh ph : S.X h}, S.IsMixedSolution h f σh uh ph →
    ∀ {ε : ℝ}, (∃ v, ‖(σ : Total W a m) - S.incl h v‖ +
        ‖H.totalD a m σ - S.incl h (S.D h v)‖ ≤ ε) →
      (∃ v, ‖(u : Total W a m) - S.incl h v‖ + ‖H.totalD a m u - S.incl h (S.D h v)‖ ≤ ε) →
      (∃ v, ‖p - S.incl h v‖ + ‖S.incl h (S.D h v)‖ ≤ ε) →
      (∃ v, ‖(LinearMap.range (H.totalD a m).toFun).topologicalClosure.starProjection
        (u : Total W a m) - S.incl h v‖ + ‖S.incl h (S.D h v)‖ ≤ ε) →
      ‖1 - (S.incl h).adjoint ∘L S.incl h‖ * (‖(σ : Total W a m)‖ + ‖H.totalD a m σ‖ +
        ‖(u : Total W a m)‖ + ‖H.totalD a m u‖ + ‖p‖) ≤ ε →
      S.readError₀ h σ u p σh uh ph ≤ K * ε

variable [∀ i, NormedSpace ℝ (W i)]

/-- **The conclusions of the FEEC theorem with variational crimes** for `S`: the static verdict
under the uniform discrete Poincaré inequality, the cochain verdict for cochain reading maps. -/
structure Verdict₀ : Prop where
  static {cP : ℝ} (hP : S.IsPoincare cP) : ∃ C, S.StaticVerdict₀ C
  cochain (hi : S.IsCochain) {Cπ : ℝ} (P : S.CochainProj Cπ) : S.CochainVerdict₀ P
  /-- the heat equation `u' = L² u`, `-Δₕ = -(𝐝ₕ 𝐝ₕ* + 𝐝ₕ* 𝐝ₕ)`, when the static method converges
  for every datum and `‖1 - iₕ* iₕ‖ → 0`: well posed, and `iₕ exp(-t Δₕ) vₕ → U(t) x` uniformly on
  `[0, T]` for every family with `iₕ vₕ → x` -/
  heat {cP : ℝ} (hP : S.IsPoincare cP)
    (hJ : Tendsto (fun h => ‖1 - (S.incl h).adjoint ∘L S.incl h‖) S.l (𝓝 0))
    (hconv : ∀ f σ u p, H.IsTotalMixedSolution a m f σ u p → ∀ σh uh ph : ∀ h, S.X h,
      (∀ h, S.IsMixedSolution h f (σh h) (uh h) (ph h)) →
        Tendsto (fun h => S.readError₀ h σ u p (σh h) (uh h) (ph h)) S.l (𝓝 0)) :
    ∃ U : ℝ → Total W a m →L[𝕜] Total W a m,
      (∀ x ∈ (sq (H.wave a m)).domain, ∀ T,
        IsStrongSolution (sq (H.wave a m)).graph (Icc 0 T) fun t => U t x) ∧
      (∀ x ∈ (sq (H.wave a m)).domain, ∀ T (y : ℝ → Total W a m), y 0 = x →
        IsStrongSolution (sq (H.wave a m)).graph (Icc 0 T) y → EqOn y (fun t => U t x) (Icc 0 T)) ∧
      (∀ x, U 0 x = x) ∧ (∀ x t, 0 ≤ t → ‖U t x‖ ≤ ‖x‖) ∧
      ∀ (x : Total W a m) (v : ∀ h, S.X h), Tendsto (fun h => S.incl h (v h)) S.l (𝓝 x) →
        ∀ T, TendstoUniformlyOn (fun h (t : ℝ) => S.incl h (semiflow
          (-(S.D h ∘L (S.D h).adjoint + (S.D h).adjoint ∘L S.D h)) t (v h)))
          (fun t => U t x) S.l (Icc 0 T)


end CrimeFamily

end HilbertComplex

/-! ### The redesigned forms are the earlier ones -/

section Galerkin

variable {E₀ E₁ E₂ : Type*} [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  {d₀ : E₀ →ₗ.[𝕜] E₁} {d₁ : E₁ →ₗ.[𝕜] E₂}

theorem mem_galerkin {A : Submodule 𝕜 E₀} {B Q : Submodule 𝕜 E₁} {x : MixedSpace d₀ d₁} :
    x ∈ galerkin d₀ d₁ A B Q ↔ (x.1 : E₀) ∈ A ∧ (x.2.1 : E₁) ∈ B ∧ x.2.2 ∈ Q := Iff.rfl

/-- **The one-equation mixed problem on a Galerkin space is the three equations.** -/
theorem isMixedSolution_galerkin_iff {A : Submodule 𝕜 E₀} {B Q : Submodule 𝕜 E₁} {f : E₁}
    {x : MixedSpace d₀ d₁} : IsMixedSolution (galerkin d₀ d₁ A B Q) f x ↔
      ((x.1 : E₀) ∈ A ∧ (x.2.1 : E₁) ∈ B ∧ x.2.2 ∈ Q) ∧
      (∀ τ : d₀.domain, (τ : E₀) ∈ A → ⟪(τ : E₀), (x.1 : E₀)⟫_𝕜 - ⟪d₀ τ, (x.2.1 : E₁)⟫_𝕜 = 0) ∧
      (∀ v : d₁.domain, (v : E₁) ∈ B → ⟪(v : E₁), d₀ x.1⟫_𝕜 + ⟪d₁ v, d₁ x.2.1⟫_𝕜 +
        ⟪(v : E₁), x.2.2⟫_𝕜 = ⟪(v : E₁), f⟫_𝕜) ∧
      (∀ q ∈ Q, ⟪q, (x.2.1 : E₁)⟫_𝕜 = 0) := by
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨hx, fun τ hτ => ?_, fun v hv => ?_, fun q hq => ?_⟩
    · simpa [mixedForm] using hy (τ, 0, 0) ⟨hτ, zero_mem _, zero_mem _⟩
    · simpa [mixedForm] using hy (0, v, 0) ⟨zero_mem _, hv, zero_mem _⟩
    · simpa [mixedForm] using hy (0, 0, q) ⟨zero_mem _, zero_mem _, hq⟩
  · rintro ⟨hx, h1, h2, h3⟩
    refine ⟨hx, fun y hy => ?_⟩
    have e1 := h1 y.1 hy.1
    have e2 := h2 y.2.1 hy.2.1
    have e3 := h3 y.2.2 hy.2.2
    unfold mixedForm
    linear_combination e1 + e2 - e3

end Galerkin

namespace HilbertComplex

variable {H : HilbertComplex 𝕜 W}

theorem isMixedSolution_iff {j : ℤ} {A : Submodule 𝕜 (W (j - 1))} {B Q : Submodule 𝕜 (W j)}
    {f : W j} {x : H.Mixed j} :
    FEEC.IsMixedSolution (galerkin _ _ A B Q) f x ↔ H.IsMixedSolution j A B Q f x.1 x.2.1 x.2.2 :=
  isMixedSolution_galerkin_iff.trans
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun h => ⟨h.mem, h.fst, h.snd, h.harm⟩⟩

theorem isMixedSolution_total_iff {a : ℤ} {m : ℕ} {f : Total W a m}
    {x : MixedSpace (H.totalD a m) (H.totalD a m)} :
    FEEC.IsMixedSolution (H.totalMixedSpace a m) f x ↔ H.IsTotalMixedSolution a m f x.1 x.2.1 x.2.2 :=
  isMixedSolution_galerkin_iff.trans
    ⟨fun ⟨a, b, c, d⟩ => ⟨a.2.2, fun τ => b τ trivial, fun v => c v trivial, d⟩,
      fun h => ⟨⟨trivial, trivial, h.mem⟩, fun τ _ => h.fst τ, fun v _ => h.snd v, h.harm⟩⟩

namespace CrimeFamily

variable {a : ℤ} {m : ℕ} {κ : Type*} (S : H.CrimeFamily a m κ)

theorem isSolution_iff {h : κ} {f : Total W a m} {x : S.X h × S.X h × S.X h} :
    S.IsSolution h f x ↔ S.IsMixedSolution h f x.1 x.2.1 x.2.2 :=
  and_congr Iff.rfl ⟨fun H τ v q hq => H (τ, v, q) hq, fun H y hy => H y.1 y.2.1 y.2.2 hy⟩

theorem readError_eq₀ (h : κ) (x : MixedSpace (H.totalD a m) (H.totalD a m))
    (x' : S.X h × S.X h × S.X h) :
    S.readError h x x' = S.readError₀ h x.1 x.2.1 x.2.2 x'.1 x'.2.1 x'.2.2 := by
  unfold readError readError₀ readGap
  ring

theorem convergesAt_iff {f : Total W a m} : S.ConvergesAt f ↔
    ∀ σ u p, H.IsTotalMixedSolution a m f σ u p → ∀ σh uh ph : ∀ h, S.X h,
      (∀ h, S.IsMixedSolution h f (σh h) (uh h) (ph h)) →
        Tendsto (fun h => S.readError₀ h σ u p (σh h) (uh h) (ph h)) S.l (𝓝 0) := by
  constructor
  · intro hc σ u p hs σh uh ph hsh
    simpa only [readError_eq₀] using hc (σ, u, p) (HilbertComplex.isMixedSolution_total_iff.2 hs)
      (fun h => (σh h, uh h, ph h)) fun h => (S.isSolution_iff).2 (hsh h)
  · intro hc x hx xh hxh
    simpa only [readError_eq₀] using hc x.1 x.2.1 x.2.2 (HilbertComplex.isMixedSolution_total_iff.1 hx)
      (fun h => (xh h).1) (fun h => (xh h).2.1) (fun h => (xh h).2.2)
      fun h => (S.isSolution_iff).1 (hxh h)

end CrimeFamily

end HilbertComplex

end FEEC
