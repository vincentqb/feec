module

public import Solution.Defs

/-!
# The definitions of the challenge before its redesign

The challenge states the mixed problems with one Galerkin space (`FEEC.IsMixedSolution`); the
proofs of `Solution.Bridge` were written for the earlier, componentwise forms, kept here
(`HilbertComplex.IsMixedSolution`, the three equations; `SubcomplexFamily.StaticVerdict₀`,
`SubcomplexFamily.Rated₀`). `Solution.Convert` proves the challenge's verdicts from these.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
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

variable {H : HilbertComplex 𝕜 W} {κ : Type*} (F : H.SubcomplexFamily κ)

/-- **The static rates of a Jackson estimate** `J` of `F`, constants independent of `h`, `L` and
the data. -/
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

end SubcomplexFamily

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

end HilbertComplex

end FEEC
