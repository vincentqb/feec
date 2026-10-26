module

public import Feec.HilbertComplex.Approximation.DiscreteCohomology
public import Feec.HilbertComplex.Approximation.GraphApprox
public import Feec.HilbertComplex.Approximation.ImprovedEstimate

/-!
# The static FEEC theorem

The approximation theory of [AFW2010], §3.3–§3.4 for the mixed Hodge Laplacian, for a conforming
family `F` (`Feec.HilbertComplex.ConformingFamily`: finite-dimensional subcomplexes `Vₕ` along a
filter, commuting cochain projections `πₕ` bounded in `W` uniformly in `h`, the approximation
property) of a Hilbert complex on any scalar field `𝕜` (`RCLike`) and any `ComplexShape`.

**The static FEEC theorem** `ConformingFamily.staticFEEC` (statement
`ConformingFamily.StaticVerdict F j`, a structure whose fields are the conclusions): if `H` has
closed range and `ℌʲ` is finite-dimensional, then at the degree `j` (and its neighbours
`i → j → k`), with constants independent of `h`,

* `poincare`: the uniform discrete Poincaré inequality `‖v‖ ≤ c ‖dₕ v‖` on `Vₕʲ ⊥ 𝔷ₕʲ`
  ([AFW2010], Thm 3.6);
* `wellPosed`: the discrete mixed problem is uniquely solvable, with `‖xₕ‖ ≤ C ‖fₕ‖`
  ([AFW2010], Thm 3.8);
* `harmonicGap`: the harmonic gap `μₕ = sup_{q ∈ ℌ, ‖q‖ ≤ 1} ‖q - πₕ q‖` tends to `0`
  ([AFW2010], Thm 3.5);
* `cohomology`: `πₕ` eventually induces isomorphisms `Hʲ(H) ≅ Hʲ(Vₕ)` ([AFW2010], Thm 3.4);
* `quasiOptimal`: `‖σ - σₕ‖_V + ‖u - uₕ‖_V + ‖p - pₕ‖ ≤ K (E_V(σ) + E_V(u) + E(p) + μₕ E_V(P_𝔅 u))`
  ([AFW2010], Thm 3.9);
* `converges`: the discrete solutions converge to the solution of the mixed problem.

With a Jackson estimate (`ConformingFamily.Jackson`) the error is `O(hᵒʳᵈ)` for regular solutions
(`ConformingFamily.StaticVerdict.rate`), from `quasiOptimal`; with rates of the quantities `η`,
`δ`, `μ` of [AFW2010], §3.5 (elliptic regularity), the `L²` error of `u` is one order better
(`ConformingFamily.rate_static_L2`, from the improved estimates of
`Feec.HilbertComplex.Approximation.ImprovedEstimate`).

The same theory for any family of subcomplexes with uniformly bounded cochain projections and
vanishing harmonic gap, without the approximation property (`Subcomplex.HasUniformProj`, the
hypothesis of the finite element theorems of the models): `HasUniformProj.discretePoincare`,
`HasUniformProj.mixed_wellPosed`, `HasUniformProj.mixed_quasiOptimal`, and the rate for one
projection `Subcomplex.CochainProjection.norm_sub_le_rate`. A conforming family has uniform
projections (`ConformingFamily.hasUniformProj`).

## Main definitions

* `Subcomplex.mixedError`: `‖σ - σₕ‖_V + ‖u - uₕ‖_V + ‖p - pₕ‖`.
* `Subcomplex.HasUniformProj l S`.
* `ConformingFamily.StaticVerdict F j`.

## Main results

* **`ConformingFamily.staticFEEC`**, **`ConformingFamily.StaticVerdict.rate`**;
  `ConformingFamily.rate_static_L2`, the improved `L²` rate of [AFW2010], Thm 3.11, conditional on
  elliptic regularity (rates of `η`, `δ`, `μ`).
* `Subcomplex.CochainProjection.mixedApprox_le`, `Subcomplex.CochainProjection.norm_sub_le_rate`.
* `ConformingFamily.isGraphBounded`, `ConformingFamily.infDist_domainSub_le`,
  `ConformingFamily.tendsto_infDist_domainSub`, `ConformingFamily.hasUniformProj`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (Thm 3.4, 3.5, 3.6), §3.4 (Thm 3.8, 3.9), §3.5 (Thm 3.11)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 5 (Thm 5.3, 5.5), Ch. 7
  (rates for smooth solutions)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W}

namespace Subcomplex

/-! ### The error of the mixed method -/

/-- **The error of the mixed method** `‖σ - σₕ‖_V + ‖u - uₕ‖_V + ‖p - pₕ‖`, for the discrete mixed
solution `(σₕ, uₕ, pₕ)` (`CochainProjection.discreteMixedSolution`) with data `f`. -/
def mixedError (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)] {i j k : ι}
    (hij : c.Rel i j) (hjk : c.Rel j k) (f : W j) (σ : H.domainSpace i) (u : H.domainSpace j)
    (p : H.harmonic j) : ℝ :=
  ‖σ - S.embD i (CochainProjection.discreteMixedSolution S hij hjk f).fst‖ +
    ‖u - S.embD j (CochainProjection.discreteMixedSolution S hij hjk f).snd.fst‖ +
    ‖(p : W j) - (((CochainProjection.discreteMixedSolution S hij hjk f).snd.snd : S.V j) : W j)‖

theorem mixedError_nonneg (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)] {i j k : ι}
    (hij : c.Rel i j) (hjk : c.Rel j k) (f : W j) (σ : H.domainSpace i) (u : H.domainSpace j)
    (p : H.harmonic j) : 0 ≤ S.mixedError hij hjk f σ u p := by
  unfold mixedError; positivity

/-! ### The rate for one cochain projection -/

namespace CochainProjection

variable {S : H.Subcomplex} [∀ i, FiniteDimensional 𝕜 (S.V i)] (P : S.CochainProjection)

/-- **The approximation terms of the quasi-optimal estimate from degreewise approximation**: if
every form of the class `Reg` in degree `l` has a `v ∈ Vₕˡ` with `‖x - v‖, ‖d (x - v)‖ ≤ ε_l`, and
`σ`, `u`, `P_𝔅 u`, `q` are in the class, then for `μ ≤ 1 + C`,
`E_V(σ) + E_V(u) + E(q) + μ E_V(P_𝔅 u) ≤ 2 (ε_i + (3 + 2C) ε_j)` (`E(q)`, the distance to `ℌₕ`,
through `infDist_harmonicW_le`). -/
theorem mixedApprox_le {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) {C : ℝ} (hC : 0 ≤ C)
    (hπ : P.IsGraphBounded j k C) {Reg : ∀ l, W l → Prop} {ε : ι → ℝ}
    (happ : ∀ l (x : W l), Reg l x → ∃ v, ∃ hv : v ∈ S.V l, ‖x - v‖ ≤ ε l ∧
      ∀ j' (hx : x ∈ (H.d l j').domain),
        ‖H.d l j' ⟨x - v, Submodule.sub_mem _ hx (S.le_domain l j' hv)⟩‖ ≤ ε l)
    {σ : H.domainSpace i} {u : H.domainSpace j} {q : H.harmonic j}
    (hσ : Reg i (H.domainIncl i σ)) (hu : Reg j (H.domainIncl j u))
    (hb : Reg j (H.domainIncl j (H.boundaryPart j (H.domainIncl j u)))) (hq : Reg j (q : W j))
    {μ : ℝ} (hμ : μ ≤ 1 + C) :
    infDist σ (S.domainSub i) + infDist u (S.domainSub j) + infDist (q : W j) (S.harmonicW j) +
        μ * infDist (H.boundaryPart j (H.domainIncl j u)) (S.domainSub j) ≤
      2 * (ε i + (3 + 2 * C) * ε j) := by
  have dist_of : ∀ {l l' : ι}, c.Rel l l' → ∀ {τ : H.domainSpace l}, Reg l (H.domainIncl l τ) →
      infDist τ (S.domainSub l) ≤ 2 * ε l := fun {l l'} hl {τ} hτ => by
    obtain ⟨v, hv, h1, h2⟩ := happ _ _ hτ
    exact S.infDist_domainSub_le_two_mul hl τ hv h1 (h2 _)
  have d1 := dist_of hij hσ
  have d2 := dist_of hjk hu
  have d3 := mul_le_mul hμ (dist_of hjk hb) infDist_nonneg (by linarith)
  have d4 := (P.infDist_harmonicW_le hjk hC hπ q.2).trans (mul_le_mul_of_nonneg_left
    (dist_of hjk (τ := cyclesToDomainSpace (H.harmonic_le_cycles j q.2)) hq) (by linarith))
  linarith

/-- **Convergence at the approximation rate** for one cochain projection ([AFW2010], Thm 3.9;
[Arnold2018], Ch. 7): with `π` bounded by `C ≥ 1` in the graph norm and Poincaré constants `c_P`,
if every form of the class `Reg` in degree `l` has a `v ∈ Vₕˡ` with `‖x - v‖, ‖d (x - v)‖ ≤ B_l r`,
and the solution `(σ, u, q)`, the boundary part of `u` and `q` are in the class, then the error of
the discrete mixed solution is `≤ K r`, with `K` depending only on `C`, `c_P` and `B`. -/
theorem norm_sub_le_rate {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) {cP C : ℝ}
    (hC : 1 ≤ C)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (hπi : P.IsGraphBounded i j C) (hπj : P.IsGraphBounded j k C) {Reg : ∀ l, W l → Prop}
    {B : ι → ℝ} (hB : ∀ l, 0 ≤ B l) {r : ℝ} (hr : 0 ≤ r)
    (happ : ∀ l (x : W l), Reg l x → ∃ v, ∃ hv : v ∈ S.V l, ‖x - v‖ ≤ B l * r ∧
      ∀ j' (hx : x ∈ (H.d l j').domain),
        ‖H.d l j' ⟨x - v, Submodule.sub_mem _ hx (S.le_domain l j' hv)⟩‖ ≤ B l * r)
    {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {q : H.harmonic j}
    (hs : H.IsMixedSolution i j k f σ u q) (hσ : Reg i (H.domainIncl i σ))
    (hu : Reg j (H.domainIncl j u))
    (hb : Reg j (H.domainIncl j (H.boundaryPart j (H.domainIncl j u))))
    (hq : Reg j (q : W j)) :
    S.mixedError hij hjk f σ u q ≤
      (1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C) * (2 * (B i + B j) * (3 + 2 * C)) * r := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hK : 0 ≤ (1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C) := by positivity
  refine (P.norm_sub_le_infDist hij hjk hC (by linarith) hPi hPj hπi hπj
    (fun _ hq' => P.norm_sub_π_harmonic_le hjk hC0 hπj hq') hs).trans ?_
  have h := P.mixedApprox_le hij hjk hC0 hπj (ε := fun l => B l * r) happ hσ hu hb hq
    (μ := 1 + C) le_rfl
  have hBi := mul_nonneg (hB i) hr
  have hBj := mul_nonneg (hB j) hr
  have : 2 * (B i * r + (3 + 2 * C) * (B j * r)) ≤ 2 * (B i + B j) * (3 + 2 * C) * r := by
    nlinarith
  calc _ ≤ (1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C) * (2 * (B i + B j) * (3 + 2 * C) * r) :=
        mul_le_mul_of_nonneg_left (h.trans this) hK
    _ = _ := by ring

end CochainProjection

/-! ### Families of subcomplexes with uniformly bounded projections -/

variable {κ : Type*}

/-- **Uniformly bounded cochain projections with vanishing harmonic gap** onto a family of
subcomplexes `S h` along the filter `l`: projections bounded by `C ≥ 1` in `W` and in the graph
norm, with harmonic gaps tending to `0` in every degree. A conforming family has them
(`ConformingFamily.hasUniformProj`). -/
def HasUniformProj (l : Filter κ) (S : κ → H.Subcomplex) : Prop :=
  ∃ (C : ℝ) (π : ∀ h, (S h).CochainProjection), 1 ≤ C ∧ (∀ h i x, ‖(π h).π i x‖ ≤ C * ‖x‖) ∧
    (∀ h i j, (π h).IsGraphBounded i j C) ∧
    ∀ j, Tendsto (fun h => (π h).harmonicGap j) l (𝓝 0)

namespace HasUniformProj

variable {l : Filter κ} {S : κ → H.Subcomplex} {cP : ℝ}
  (hP : ∀ i j, c.Rel i j → ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ →
    ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
include hP

/-- **Uniform discrete Poincaré inequality** ([AFW2010], Thm 3.6). -/
theorem discretePoincare (hU : HasUniformProj l S) : ∃ C : ℝ, ∀ {i j : ι}, c.Rel i j →
    ∀ (h : κ) {x : W i} (hx : x ∈ (S h).V i), (∀ y ∈ (S h).cyclesW i, ⟪y, x⟫_𝕜 = 0) →
      ‖x‖ ≤ C * ‖H.d i j ⟨x, (S h).le_domain i j hx⟩‖ := by
  obtain ⟨C, π, hC, hπ, -, -⟩ := hU
  exact ⟨C * cP, fun {i j} hij h x hx hxo =>
    (π h).norm_le_of_forall_inner_eq_zero hij (hP i j hij) (zero_le_one.trans hC) (hπ h i) hx hxo⟩

/-- **Uniform well-posedness and stability of the discrete mixed Hodge Laplacian** ([AFW2010],
Thm 3.8). -/
theorem mixed_wellPosed [∀ h i, FiniteDimensional 𝕜 ((S h).V i)] (hcP : 1 ≤ cP)
    (hU : HasUniformProj l S) : ∃ C : ℝ, ∀ {i j k : ι}, c.Rel i j → c.Rel j k →
    ∀ (h : κ) (f : (S h).V j),
    (∃! x, (S h).toHilbertComplex.mixedForm i j k x = (S h).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (S h).toHilbertComplex.MixedSpace i j,
      (S h).toHilbertComplex.mixedForm i j k x = (S h).toHilbertComplex.mixedRHS i j f →
        ‖x‖ ≤ C * ‖f‖ := by
  obtain ⟨C, π, hC1, hb, -, -⟩ := hU
  refine ⟨16 * (C * cP) ^ 2, fun {i j k} hij hjk h f => ⟨?_, fun x hx => ?_⟩⟩
  · exact (π h).existsUnique_mixed hij hjk hcP hC1 (hP i j hij) (hP j k hjk) (hb h i) (hb h j) f
  · exact (π h).norm_le_of_mixed hij hjk hcP hC1 (hP i j hij) (hP j k hjk) (hb h i) (hb h j) hx

/-- **Quasi-optimality of the mixed method** ([AFW2010], Thm 3.9) with weights `μ_j(h) → 0`. -/
theorem mixed_quasiOptimal [∀ h i, FiniteDimensional 𝕜 ((S h).V i)] (hU : HasUniformProj l S) :
    ∃ (K : ℝ) (μ : ι → κ → ℝ), (∀ j, Tendsto (μ j) l (𝓝 0)) ∧
    ∀ {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k)
    {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {q : H.harmonic j},
    H.IsMixedSolution i j k f σ u q → ∀ h : κ,
    (S h).mixedError hij hjk f σ u q ≤
      K * (infDist σ ((S h).domainSub i) + infDist u ((S h).domainSub j) +
        infDist (q : W j) ((S h).harmonicW j) +
        μ j h * infDist (H.boundaryPart j (H.domainIncl j u)) ((S h).domainSub j)) := by
  obtain ⟨C, π, hC1, -, hg, hgap⟩ := hU
  exact ⟨(1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C), fun j h => (π h).harmonicGap j, hgap,
    fun {i j k} hij hjk _ _ _ _ hs h => (π h).norm_sub_le_infDist_harmonicGap hij hjk hC1
      (hP i j hij) (hP j k hjk) (hg h i j) (hg h j k) hs⟩

end HasUniformProj

end Subcomplex

/-! ### Conforming families -/

namespace ConformingFamily

variable {κ : Type*} (F : ConformingFamily H κ)

/-- The projections of a conforming family are bounded by `projBound` in the graph norm. -/
theorem isGraphBounded (h : κ) (i j : ι) : (F.π h).IsGraphBounded i j F.projBound :=
  (F.π h).isGraphBounded_of_norm_le (F.norm_π_le h i) (F.norm_π_le h j)

/-- **Distance to `Vₕ` in the graph norm** through the projection:
`dist_V(σ, Vₕⁱ) ≤ (1 + C) (dist(σ, Vₕⁱ) + dist(d σ, Vₕʲ))`, since `d πₕ σ = πₕ d σ`. -/
theorem infDist_domainSub_le (h : κ) {i j : ι} (hij : c.Rel i j) (σ : H.domainSpace i) :
    infDist σ ((F.V h).domainSub i) ≤ (1 + F.projBound) *
      (infDist (H.domainIncl i σ) ((F.V h).V i : Set (W i)) +
        infDist (H.d i j (H.domainCoord i j σ)) ((F.V h).V j : Set (W j))) := by
  have hC := zero_le_one.trans F.one_le_projBound
  refine ((F.V h).infDist_domainSub_le hij σ ((F.π h).mem i (H.domainIncl i σ))).trans ?_
  have e : H.d i j ⟨(F.π h).π i (H.domainIncl i σ), (F.V h).le_domain i j ((F.π h).mem i _)⟩ =
      (F.π h).π j (H.d i j (H.domainCoord i j σ)) := (F.π h).comm i j (H.domainCoord i j σ)
  rw [e, mul_add]
  exact add_le_add ((F.π h).norm_sub_π_le_infDist hC (F.norm_π_le h i) _)
    ((F.π h).norm_sub_π_le_infDist hC (F.norm_π_le h j) _)

/-- **The approximation property in the graph norm**: `dist_V(σ, Vₕⁱ) → 0` for every `σ ∈ Vⁱ`. -/
theorem tendsto_infDist_domainSub {i j : ι} (hij : c.Rel i j) (σ : H.domainSpace i) :
    Tendsto (fun h => infDist σ ((F.V h).domainSub i)) F.l (𝓝 0) := by
  have h0 : Tendsto (fun h => (1 + F.projBound) *
      (infDist (H.domainIncl i σ) ((F.V h).V i : Set (W i)) +
        infDist (H.d i j (H.domainCoord i j σ)) ((F.V h).V j : Set (W j)))) F.l (𝓝 0) := by
    simpa using ((F.approx i _).add (F.approx j _)).const_mul (1 + F.projBound)
  exact squeeze_zero (fun _ => infDist_nonneg) (fun h => F.infDist_domainSub_le h hij σ) h0

/-- **A conforming family has uniformly bounded projections with vanishing harmonic gap**, where
the harmonic forms are finite-dimensional. -/
theorem hasUniformProj [∀ j, FiniteDimensional 𝕜 (H.harmonic j)] :
    Subcomplex.HasUniformProj F.l F.V :=
  ⟨F.projBound, F.π, F.one_le_projBound, F.norm_π_le, F.isGraphBounded,
    fun _ => F.tendsto_harmonicGap⟩

/-! ### The static FEEC theorem -/

/-- **The conclusions of the static FEEC theorem** (`staticFEEC`) for a conforming family `F` at
the degree `j`, with constants independent of `h`. [AFW2010], §3.3–§3.4 -/
structure StaticVerdict (j : ι) : Prop where
  /-- the uniform discrete Poincaré inequality `‖v‖ ≤ C ‖dₕ v‖` on `Vₕʲ ⊥ 𝔷ₕʲ` ([AFW2010],
  Thm 3.6) -/
  poincare {k : ι} (hjk : c.Rel j k) : ∃ C : ℝ, ∀ (h : κ) {x : W j} (hx : x ∈ (F.V h).V j),
    (∀ y ∈ (F.V h).cyclesW j, ⟪y, x⟫_𝕜 = 0) → ‖x‖ ≤ C * ‖H.d j k ⟨x, (F.V h).le_domain j k hx⟩‖
  /-- the discrete mixed problem is uniquely solvable, `‖xₕ‖ ≤ C ‖fₕ‖` ([AFW2010], Thm 3.8) -/
  wellPosed {i k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) : ∃ C : ℝ, ∀ (h : κ) (f : (F.V h).V j),
    (∃! x, (F.V h).toHilbertComplex.mixedForm i j k x = (F.V h).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (F.V h).toHilbertComplex.MixedSpace i j,
      (F.V h).toHilbertComplex.mixedForm i j k x = (F.V h).toHilbertComplex.mixedRHS i j f →
        ‖x‖ ≤ C * ‖f‖
  /-- the harmonic gap `μₕ = sup_{q ∈ ℌʲ, ‖q‖ ≤ 1} ‖q - πₕ q‖` tends to `0` ([AFW2010], Thm 3.5) -/
  harmonicGap : Tendsto (fun h => (F.π h).harmonicGap j) F.l (𝓝 0)
  /-- `πₕ` eventually induces isomorphisms `Hʲ(H) ≅ Hʲ(Vₕ)`, `[z] ↦ [πₕ z]` ([AFW2010],
  Thm 3.4) -/
  cohomology : ∀ᶠ h in F.l, Function.Bijective ((F.π h).cohomologyMap j)
  /-- quasi-optimality: `‖σ - σₕ‖_V + ‖u - uₕ‖_V + ‖p - pₕ‖ ≤
  K (E_V(σ) + E_V(u) + E(p) + μₕ E_V(P_𝔅 u))`, `E` the distances to `Vₕ` and to `ℌₕ`
  ([AFW2010], Thm 3.9) -/
  quasiOptimal {i k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j},
    H.IsMixedSolution i j k f σ u p → ∀ h : κ,
    (F.V h).mixedError hij hjk f σ u p ≤
      K * (infDist σ ((F.V h).domainSub i) + infDist u ((F.V h).domainSub j) +
        infDist (p : W j) ((F.V h).harmonicW j) +
        (F.π h).harmonicGap j * infDist (H.boundaryPart j (H.domainIncl j u)) ((F.V h).domainSub j))
  /-- the discrete solutions converge: the error of the mixed method tends to `0` -/
  converges {i k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) {f : W j} {σ : H.domainSpace i}
    {u : H.domainSpace j} {p : H.harmonic j} (hs : H.IsMixedSolution i j k f σ u p) :
    Tendsto (fun h => (F.V h).mixedError hij hjk f σ u p) F.l (𝓝 0)

variable {F} in
/-- **The rate of the static FEEC theorem** from quasi-optimality and a Jackson estimate
([AFW2010], Thm 3.9; [Arnold2018], Ch. 7): if the solution `(σ, u, p)` of the mixed problem, the
boundary part of `u` and `p` are `s`-regular with bound `L`, the error of the mixed method is
`≤ K L hₕ^{ord s}`, with `K` independent of `h` and of the solution. -/
theorem StaticVerdict.rate {j : ι} (V : F.StaticVerdict j) {ρ : Type*} (J : F.Jackson ρ) (s : ρ)
    {i k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) :
    ∃ K : ℝ, ∀ {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j},
    H.IsMixedSolution i j k f σ u p → ∀ {L : ℝ}, 0 ≤ L →
    J.Reg s i L (H.domainIncl i σ) → J.Reg s j L (H.domainIncl j u) →
    J.Reg s j L (H.domainIncl j (H.boundaryPart j (H.domainIncl j u))) →
    J.Reg s j L (p : W j) → ∀ h : κ,
    (F.V h).mixedError hij hjk f σ u p ≤ K * L * J.meshSize h ^ J.ord s := by
  obtain ⟨K, hK, hqo⟩ := V.quasiOptimal hij hjk
  set C := F.projBound
  have hC : 0 ≤ C := zero_le_one.trans F.one_le_projBound
  refine ⟨K * (2 * (J.B s i + (3 + 2 * C) * J.B s j)),
    fun {f σ u p} hs L hL hσ hu hb hp h => (hqo hs h).trans ?_⟩
  have hgap : (F.π h).harmonicGap j ≤ 1 + C := (F.π h).harmonicGap_le (by linarith)
    fun _ hq => (F.π h).norm_sub_π_harmonic_le hjk hC (F.isGraphBounded h j k) hq
  have hA := (F.π h).mixedApprox_le hij hjk hC (F.isGraphBounded h j k)
    (Reg := fun l x => J.Reg s l L x) (ε := fun l => J.B s l * (L * J.meshSize h ^ J.ord s))
    (fun l x hx => J.jackson s h l x hL hx) hσ hu hb hp hgap
  calc _ ≤ K * (2 * (J.B s i * (L * J.meshSize h ^ J.ord s) +
        (3 + 2 * C) * (J.B s j * (L * J.meshSize h ^ J.ord s)))) :=
        mul_le_mul_of_nonneg_left hA hK
    _ = _ := by ring

/-- **The static FEEC theorem.** For a conforming family `F` of a Hilbert complex `H` with closed
range, and a finite-dimensional `ℌʲ` (`StaticVerdict`), with constants independent of `h`:

1. (**stability**) the uniform discrete Poincaré inequality on `Vₕʲ ⊥ 𝔷ₕʲ` and the uniform
   well-posedness of the discrete mixed Hodge Laplacian, `‖xₕ‖ ≤ C ‖fₕ‖`;
2. (**harmonic forms and cohomology**) the harmonic gap tends to `0` and `πₕ` eventually induces
   isomorphisms `Hʲ(H) ≅ Hʲ(Vₕ)`;
3. (**quasi-optimality**) the error of the mixed method is at most
   `K (E_V(σ) + E_V(u) + E(p) + μₕ E_V(P_𝔅 u))`;
4. (**convergence**) the discrete solutions converge to the solution of the mixed problem; with a
   Jackson estimate, at the rate `hᵒʳᵈ` for regular solutions (`StaticVerdict.rate`).

[AFW2010], Thm 3.4, 3.5, 3.6, 3.8, 3.9; [Arnold2018], Thm 5.3, 5.5 -/
theorem staticFEEC (hcr : ∀ i, H.ClosedRangeAt i) (j : ι) [FiniteDimensional 𝕜 (H.harmonic j)] :
    F.StaticVerdict j := by
  have hC := F.one_le_projBound
  have hgap : Tendsto (fun h => (F.π h).harmonicGap j) F.l (𝓝 0) := F.tendsto_harmonicGap
  have hqo : ∀ {i k : ι} (hij : c.Rel i j) (hjk : c.Rel j k), ∃ K : ℝ, 0 ≤ K ∧
      ∀ {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j},
      H.IsMixedSolution i j k f σ u p → ∀ h : κ,
      (F.V h).mixedError hij hjk f σ u p ≤
        K * (infDist σ ((F.V h).domainSub i) + infDist u ((F.V h).domainSub j) +
          infDist (p : W j) ((F.V h).harmonicW j) + (F.π h).harmonicGap j *
            infDist (H.boundaryPart j (H.domainIncl j u)) ((F.V h).domainSub j)) := by
    intro i k hij hjk
    obtain ⟨cP, -, hPi, hPj⟩ := H.exists_poincare_pair hij hjk (hcr j) (hcr k)
    exact ⟨_, by have := zero_le_one.trans hC; positivity, fun hs h =>
      (F.π h).norm_sub_le_infDist_harmonicGap hij hjk hC hPi hPj (F.isGraphBounded h i j)
        (F.isGraphBounded h j k) hs⟩
  refine ⟨fun {k} hjk => ?_, fun {i k} hij hjk => ?_, hgap,
    F.eventually_bijective_cohomologyMap (hcr j), hqo, fun {i k} hij hjk f σ u p hs => ?_⟩
  · obtain ⟨cP, -, hP⟩ := H.exists_poincare_of_closedRangeAt hjk (hcr k)
    exact ⟨F.projBound * cP, fun h x hx hxo => (F.π h).norm_le_of_forall_inner_eq_zero hjk hP
      (zero_le_one.trans hC) (F.norm_π_le h j) hx hxo⟩
  · obtain ⟨cP, hcP, hPi, hPj⟩ := H.exists_poincare_pair hij hjk (hcr j) (hcr k)
    exact ⟨16 * (F.projBound * cP) ^ 2, fun h f =>
      ⟨(F.π h).existsUnique_mixed hij hjk hcP hC hPi hPj (F.norm_π_le h i) (F.norm_π_le h j) f,
        fun x hx => (F.π h).norm_le_of_mixed hij hjk hcP hC hPi hPj (F.norm_π_le h i)
          (F.norm_π_le h j) hx⟩⟩
  · -- the four distances tend to `0` (the harmonic one through the projections)
    obtain ⟨K, -, hK⟩ := hqo hij hjk
    have hq : Tendsto (fun h => infDist (p : W j) ((F.V h).harmonicW j)) F.l (𝓝 0) := by
      have h0 := (F.tendsto_infDist_domainSub hjk
        (cyclesToDomainSpace (H.harmonic_le_cycles j p.2))).const_mul (1 + F.projBound)
      rw [mul_zero] at h0
      exact squeeze_zero (fun _ => infDist_nonneg) (fun h => (F.π h).infDist_harmonicW_le hjk
        (zero_le_one.trans hC) (F.isGraphBounded h j k) p.2) h0
    have h0 := ((((F.tendsto_infDist_domainSub hij σ).add (F.tendsto_infDist_domainSub hjk u)).add
      hq).add (hgap.mul (F.tendsto_infDist_domainSub hjk
        (H.boundaryPart j (H.domainIncl j u))))).const_mul K
    simp only [add_zero, mul_zero] at h0
    exact squeeze_zero (fun h => (F.V h).mixedError_nonneg hij hjk f σ u p) (fun h => hK hs h) h0

/-! ### The improved `L²` rate, conditional on elliptic regularity -/

/-- **The improved `L²` rate** ([AFW2010], Thm 3.11 and §3.5), conditional on elliptic regularity
in the form it takes there: if `η ≤ a hₕ`, `δ ≤ b hₕ²` and `μ ≤ m hₕ` (the quantities
`improvedEta`, `improvedDelta`, `harmonicGap` of `πₕ`, small by elliptic regularity of the
solution operator) and the `W`-best approximation errors are `E(dσ) + E(p) ≤ e hₕʳ`,
`E(du) + E(σ), E(P_𝔅 u) ≤ e hₕ^{r+1}`, `E(u) ≤ e hₕ^{r+2}`, then
`‖u - uₕ‖ ≤ 4 (1 + C)² (1 + a + a² + b + m) e hₕ^{r+2}`: one order better for `u` in `L²` than the
energy estimate. -/
theorem rate_static_L2 {ρ : Type*} (J : F.Jackson ρ) {i j k : ι} (hij : c.Rel i j)
    (hjk : c.Rel j k) (hj : H.ClosedRangeAt j) (hk : H.ClosedRangeAt k) (h : κ) {a b m e : ℝ}
    {r : ℕ} (ha : 0 ≤ a) (hm : 0 ≤ m)
    (hη : (F.π h).improvedEta hij hjk hj hk ≤ a * J.meshSize h)
    (hδ : (F.π h).improvedDelta hij hjk hj hk ≤ b * J.meshSize h ^ 2)
    (hμ : (F.π h).harmonicGap j ≤ m * J.meshSize h) {f : W j} (X : H.ContinuousSolution i j k f)
    (Y : (F.V h).DiscreteSolution i j k f)
    (hE₀ : (F.V h).bestApprox X.dσ + (F.V h).bestApprox X.p ≤ e * J.meshSize h ^ r)
    (hE₁ : (F.V h).bestApprox X.du + (F.V h).bestApprox (X.σ : W i) ≤ e * J.meshSize h ^ (r + 1))
    (hEb : (F.V h).bestApprox ((H.boundaries j).topologicalClosure.starProjection (X.u : W j)) ≤
      e * J.meshSize h ^ (r + 1))
    (hE₂ : (F.V h).bestApprox (X.u : W j) ≤ e * J.meshSize h ^ (r + 2)) :
    ‖(X.u : W j) - Y.u‖ ≤
      4 * (1 + F.projBound) ^ 2 * (1 + a + a ^ 2 + b + m) * e * J.meshSize h ^ (r + 2) := by
  obtain ⟨cP, hcP, hPi, hPj⟩ := H.exists_poincare_pair hij hjk hj hk
  have hC := zero_le_one.trans F.one_le_projBound
  have hmain := (F.π h).norm_sub_u_le_improved hij hjk hj hk hC (zero_le_one.trans hcP) hPi hPj
    (F.norm_π_le h i) (F.norm_π_le h j) (F.norm_π_le h k) X Y
  set t := J.meshSize h
  have ht := J.meshSize_nonneg h
  have hη0 := (F.π h).improvedEta_nonneg hij hjk hj hk
  have hδ0 := (F.π h).improvedDelta_nonneg hij hjk hj hk
  have hμ0 := (F.π h).harmonicGap_nonneg j
  have hE0 := add_nonneg ((F.V h).bestApprox_nonneg X.dσ) ((F.V h).bestApprox_nonneg X.p)
  have hE1 := add_nonneg ((F.V h).bestApprox_nonneg X.du)
    ((F.V h).bestApprox_nonneg (X.σ : W i))
  have hEb0 := (F.V h).bestApprox_nonneg
    ((H.boundaries j).topologicalClosure.starProjection (X.u : W j))
  have hη2 : (F.π h).improvedEta hij hjk hj hk ^ 2 ≤ a ^ 2 * t ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hη0 hη 2
  have k1 := mul_le_mul hη hE₁ hE1 (mul_nonneg ha ht)
  have k2 := mul_le_mul (add_le_add hη2 hδ) hE₀ hE0 (by nlinarith)
  have k3 := mul_le_mul hμ hEb hEb0 (mul_nonneg hm ht)
  have key : e * t ^ (r + 2) + a * t * (e * t ^ (r + 1)) + (a ^ 2 * t ^ 2 + b * t ^ 2) *
      (e * t ^ r) + m * t * (e * t ^ (r + 1)) = (1 + a + a ^ 2 + b + m) * e * t ^ (r + 2) := by
    ring
  calc _ ≤ _ := hmain
    _ ≤ 4 * (1 + F.projBound) ^ 2 * (e * t ^ (r + 2) + a * t * (e * t ^ (r + 1)) +
        (a ^ 2 * t ^ 2 + b * t ^ 2) * (e * t ^ r) + m * t * (e * t ^ (r + 1))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by rw [key]; ring

end ConformingFamily

end Feec.HilbertComplex
