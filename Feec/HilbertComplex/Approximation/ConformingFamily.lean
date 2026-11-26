module

public import Feec.HilbertComplex.Approximation.CochainProjection
public import Feec.HilbertComplex.Window

/-!
# Conforming families of subcomplexes

Families of finite-dimensional subcomplexes of a Hilbert complex with commuting cochain
projections, refined along a filter, and their windows.

## Main definitions

* `SubcomplexFamily`: subcomplexes with cochain projections, with no bound.
* `ConformingFamily`: projections bounded in `W` and the approximation property in `W`.
* `SubcomplexFamily.Jackson`: a Jackson estimate of a family of subcomplexes.
-/

open Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.HilbertComplex

theorem tendsto_infDist_submodule_iff {𝕜 E κ : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup E] [Module 𝕜 E] {l : Filter κ} (V : κ → Submodule 𝕜 E) (y : E) :
    Tendsto (fun h => infDist y (V h : Set E)) l (𝓝 0) ↔
      ∀ ε > 0, ∀ᶠ h in l, ∃ v ∈ V h, ‖y - v‖ < ε := by
  refine ⟨fun hy ε hε => ?_, fun hy => tendsto_order.2 ⟨fun a ha =>
    Eventually.of_forall fun _ => ha.trans_le infDist_nonneg, fun a ha => ?_⟩⟩
  · filter_upwards [(tendsto_order.1 hy).2 ε hε] with h hh
    obtain ⟨v, hv, hd⟩ := (infDist_lt_iff ⟨0, (V h).zero_mem⟩).1 hh
    exact ⟨v, hv, by rwa [← dist_eq_norm]⟩
  · filter_upwards [hy a ha] with h ⟨v, hv, hlt⟩
    exact (infDist_le_dist_of_mem hv).trans_lt (by rwa [dist_eq_norm])

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

/-- A **family of subcomplexes**: finite-dimensional subcomplexes with cochain projections. -/
structure SubcomplexFamily (H : HilbertComplex 𝕜 c W) (κ : Type*) where
  /-- the filter of refinement -/
  l : Filter κ
  /-- the discrete subcomplexes -/
  V : κ → H.Subcomplex
  [finiteDimensional : ∀ h i, FiniteDimensional 𝕜 ((V h).V i)]
  /-- the commuting cochain projections -/
  π : ∀ h, (V h).CochainProjection

attribute [instance] SubcomplexFamily.finiteDimensional

/-- A **conforming family**: projections bounded in `W` uniformly in `h`, and `dist(w, Vₕⁱ) → 0`. -/
structure ConformingFamily (H : HilbertComplex 𝕜 c W) (κ : Type*) extends SubcomplexFamily H κ where
  bound_π : ∃ C, ∀ h i x, ‖(π h).π i x‖ ≤ C * ‖x‖
  /-- the approximation property -/
  approx : ∀ i (w : W i), Tendsto (fun h => infDist w ((V h).V i : Set (W i))) l (𝓝 0)

namespace SubcomplexFamily

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (G : SubcomplexFamily H κ)

/-- A **Jackson estimate**: classes `Reg s` approximated in the graph norm at order `hₕ^{ord s}`. -/
structure Jackson (ρ : Type*) where
  /-- the mesh size -/
  meshSize : κ → ℝ
  meshSize_nonneg : ∀ h, 0 ≤ meshSize h
  tendsto_meshSize : Tendsto meshSize G.l (𝓝 0)
  /-- `Reg s i L x`: `x` is `s`-regular with bound `L` -/
  Reg : ρ → ∀ i, ℝ → W i → Prop
  /-- the order of the class `s` -/
  ord : ρ → ℝ
  /-- the constants -/
  B : ρ → ι → ℝ
  B_nonneg : ∀ s i, 0 ≤ B s i
  jackson : ∀ s h i {L : ℝ} (x : W i), 0 ≤ L → Reg s i L x → ∃ v, ∃ hv : v ∈ (G.V h).V i,
    ‖x - v‖ ≤ B s i * (L * meshSize h ^ ord s) ∧ ∀ j (hx : x ∈ (H.d i j).domain),
      ‖H.d i j ⟨x - v, Submodule.sub_mem _ hx ((G.V h).le_domain i j hv)⟩‖ ≤
        B s i * (L * meshSize h ^ ord s)

end SubcomplexFamily

namespace ConformingFamily

variable {H : HilbertComplex 𝕜 c W} {κ : Type*}

/-- A conforming family from the existence of uniformly bounded cochain projections. -/
def ofExists (l : Filter κ) (V : κ → H.Subcomplex) [∀ h i, FiniteDimensional 𝕜 ((V h).V i)]
    (hπ : ∃ (C : ℝ) (π : ∀ h, (V h).CochainProjection), ∀ h i x, ‖(π h).π i x‖ ≤ C * ‖x‖)
    (happrox : ∀ i (w : W i), Tendsto (fun h => infDist w ((V h).V i : Set (W i))) l (𝓝 0)) :
    ConformingFamily H κ where
  l := l
  V := V
  π := hπ.choose_spec.choose
  bound_π := ⟨hπ.choose, hπ.choose_spec.choose_spec⟩
  approx := happrox

variable (F : ConformingFamily H κ)

theorem eventually_exists_lt (i : ι) (w : W i) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in F.l, ∃ v ∈ (F.V h).V i, ‖w - v‖ < ε :=
  (tendsto_infDist_submodule_iff (fun h => (F.V h).V i) w).1 (F.approx i w) ε hε

/-- A uniform bound `C ≥ 1` of the cochain projections in `W`. -/
def projBound : ℝ := max F.bound_π.choose 1

theorem one_le_projBound : 1 ≤ F.projBound := le_max_right _ _

theorem norm_π_le (h : κ) (i : ι) (x : W i) : ‖(F.π h).π i x‖ ≤ F.projBound * ‖x‖ :=
  (F.bound_π.choose_spec h i x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

end ConformingFamily

/-! ### Windows -/

section Window

variable {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α] [CharZero α] {V : α → Type*}
  [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, CompleteSpace (V i)]
  {H : HilbertComplex 𝕜 (ComplexShape.up α) V}

/-- The window `Vₕᵃ → ⋯ → Vₕ^{a + m - 1}` of a subcomplex, a subcomplex of `H.window a m`. -/
abbrev Subcomplex.window (S : H.Subcomplex) (a : α) (m : ℕ) : (H.window a m).Subcomplex where
  V i := S.V (a + i)
  le_domain _ _ := S.le_domain _ _
  mapsTo _ _ := S.mapsTo _ _

/-- The window of a cochain projection. -/
def Subcomplex.CochainProjection.window {S : H.Subcomplex} (P : S.CochainProjection) (a : α)
    (m : ℕ) : (S.window a m).CochainProjection where
  π i := P.π (a + i)
  mem _ x := P.mem _ x
  proj _ x hx := P.proj _ x hx
  comm _ _ x := P.comm _ _ x

variable {κ : Type*}

/-- The window of a family of subcomplexes, a family of subcomplexes of `H.window a m`. -/
def SubcomplexFamily.window (G : SubcomplexFamily H κ) (a : α) (m : ℕ) :
    SubcomplexFamily (H.window a m) κ where
  l := G.l
  V h := (G.V h).window a m
  finiteDimensional h i := inferInstanceAs (FiniteDimensional 𝕜 ((G.V h).V (a + i)))
  π h := (G.π h).window a m

/-- The window of a conforming family, a conforming family of `H.window a m`. -/
def ConformingFamily.window (F : ConformingFamily H κ) (a : α) (m : ℕ) :
    ConformingFamily (H.window a m) κ where
  toSubcomplexFamily := F.toSubcomplexFamily.window a m
  bound_π := by
    obtain ⟨C, hC⟩ := F.bound_π
    exact ⟨C, fun h i x => hC h _ x⟩
  approx i w := F.approx (a + i) w

/-- The window of a Jackson estimate, a Jackson estimate of `G.window a m`. -/
def SubcomplexFamily.Jackson.window {G : SubcomplexFamily H κ} {ρ : Type*} (J : G.Jackson ρ)
    (a : α) (m : ℕ) : (G.window a m).Jackson ρ where
  meshSize := J.meshSize
  meshSize_nonneg := J.meshSize_nonneg
  tendsto_meshSize := J.tendsto_meshSize
  Reg s i := J.Reg s (a + i)
  ord := J.ord
  B s i := J.B s (a + i)
  B_nonneg s i := J.B_nonneg s (a + i)
  jackson s h i _ x hL hx := by
    obtain ⟨v, hv, h1, h2⟩ := J.jackson s h (a + i) x hL hx
    exact ⟨v, hv, h1, fun j hxj => h2 (a + j) hxj⟩

end Window

end Feec.HilbertComplex
