module

public import Solution.Defs

/-!
# The definitions of the challenge before its redesign

The challenge states the mixed problems with one Galerkin space (`FEEC.IsMixedSolution`) and the
crime problems on triples; the proofs of `Solution.Crime` were written for the earlier,
componentwise forms, kept here (`IsTotalMixedSolution`, the three equations of the mixed Hodge
Laplacian of a window; `CrimeFamily.StaticVerdict₀`, `CrimeFamily.CochainVerdict₀`).
`Solution.Convert` proves the challenge's verdicts from these.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex

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
