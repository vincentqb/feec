module

public import Mathlib.Algebra.Homology.ComplexShape
public import Feec.Operator.Adjoint

/-!
# Hilbert complexes over a complex shape

A Hilbert complex over `𝕜 = ℝ` or `ℂ`, indexed by a `ComplexShape c` on an index type `ι`, is a
family of Hilbert spaces `W i` with closed densely defined operators `d i j : W i →ₗ.[𝕜] W j`,
zero unless `c.Rel i j`, such that `R(d i j) ⊆ D(d j k)` and `d j k ∘ d i j = 0`.

The index shape is arbitrary: `ComplexShape.up ℤ` for a complex of any length, a finite window
(`Feec.HilbertComplex.Window`) for the Dirac and wave operators, and `c.symm` for the dual
complex (`Feec.HilbertComplex.Dual`), which then needs no index transport.

## Main definitions

* `Feec.HilbertComplex 𝕜 c W`: the structure.
* `HilbertComplex.ofSucc`: the complex on `ComplexShape.up α` (`α = ℕ, ℤ, …`) built from
  `δ i : W i →ₗ.[𝕜] W (i + 1)`.
* `HilbertComplex.cycles i = N(d i (c.next i))`, `HilbertComplex.boundaries i = R(d (c.prev i) i)`,
  `HilbertComplex.harmonic i = cycles i ⊓ N((d (c.prev i) i)†)`, and
  `HilbertComplex.ClosedRangeAt i` (closed boundaries).

## Main results

* `HilbertComplex.range_le_ker`, `HilbertComplex.boundaries_le_cycles`: `d d = 0` as an inclusion.
* `HilbertComplex.isClosed_ker`, `HilbertComplex.isClosed_cycles`: kernels are closed.
* `HilbertComplex.dense_adjoint_domain`, `HilbertComplex.adjoint_mapsTo`,
  `HilbertComplex.adjoint_comp_eq_zero`: the adjoints form a complex (used by `dual`).
* `HilbertComplex.cycles_eq_iInf`: `cycles i` is the joint kernel of all `d i j`.
* `HilbertComplex.cycles_eq`, `HilbertComplex.boundaries_eq`: at a related pair `i → j`,
  `cycles i = N(d i j)` and `boundaries j = R(d i j)`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.2 (Hilbert complexes)
* [J. Brüning, M. Lesch, *Hilbert complexes*][BruningLesch1992] (Hilbert complexes of closed densely
  defined operators)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
  (the Finite Element Exterior Calculus framework)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 4

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap

@[expose] public noncomputable section

/-- Equal partial maps agree at equal points. -/
theorem LinearPMap.apply_eq_of_eq {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {T T' : E →ₗ.[𝕜] F}
    (hT : T = T') (x : T.domain) (y : T'.domain) (hxy : (x : E) = y) : T x = T' y := by
  subst hT; rw [Subtype.ext hxy]

namespace Feec

/-- A Hilbert complex over `𝕜` with index shape `c`: closed densely defined operators
`d i j : W i →ₗ.[𝕜] W j`, zero off the relation of `c`, with `R(d i j) ⊆ D(d j k)` and
`d j k ∘ d i j = 0`. Closed range is not assumed (`HilbertComplex.ClosedRangeAt`).
[QuennevilleBelair2015], §4.2, following [BruningLesch1992] and [AFW2010], §3.1; this is the
abstract setting of Finite Element Exterior Calculus, [AFW2006], [AFW2010]. -/
structure HilbertComplex (𝕜 : Type*) [RCLike 𝕜] {ι : Type*} (c : ComplexShape ι)
    (W : ι → Type*) [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
    [∀ i, CompleteSpace (W i)] where
  /-- the differentials -/
  d : ∀ i j, W i →ₗ.[𝕜] W j
  shape : ∀ i j, ¬ c.Rel i j → d i j = 0
  dense : ∀ i j, Dense ((d i j).domain : Set (W i))
  closed : ∀ i j, (d i j).IsClosed
  mapsTo : ∀ i j k (x : (d i j).domain), (d i j x : W j) ∈ (d j k).domain
  d_comp_d : ∀ i j k (x : (d i j).domain), d j k ⟨_, mapsTo i j k x⟩ = 0

namespace HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W)

/-! ### Elementary facts -/

/-- Two Hilbert complexes with the same differentials are equal. -/
theorem ext_d {H₁ H₂ : HilbertComplex 𝕜 c W} (h : H₁.d = H₂.d) : H₁ = H₂ := by
  cases H₁; cases H₂; subst h; rfl

/-- A partial map equal to `0` vanishes on its domain. -/
theorem _root_.LinearPMap.apply_eq_zero_of_eq_zero {R E F : Type*} [Ring R] [AddCommGroup E]
    [Module R E] [AddCommGroup F] [Module R F] {T : E →ₗ.[R] F} (hT : T = 0) (x : T.domain) :
    T x = 0 := by
  subst hT; rfl

theorem apply_eq_zero_of_not_rel {i j : ι} (h : ¬ c.Rel i j) (x : (H.d i j).domain) :
    H.d i j x = 0 :=
  apply_eq_zero_of_eq_zero (H.shape i j h) x

theorem domain_eq_top_of_not_rel {i j : ι} (h : ¬ c.Rel i j) : (H.d i j).domain = ⊤ := by
  rw [H.shape i j h]; rfl

/-- The zero partial map (domain `⊤`) is closed. -/
theorem _root_.LinearPMap.isClosed_zero {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] :
    (0 : E →ₗ.[𝕜] F).IsClosed :=
  ContinuousLinearMap.isClosed_toPMap_top (0 : E →L[𝕜] F)

/-- `R(d i j) ⊆ N(d j k)`. -/
theorem range_le_ker (i j k : ι) : LinearMap.range (H.d i j).toFun ≤ (H.d j k).ker :=
  Feec.Operator.range_le_ker (H.mapsTo i j k) (H.d_comp_d i j k)

theorem isClosed_ker (i j : ι) : IsClosed ((H.d i j).ker : Set (W i)) :=
  LinearPMap.isClosed_ker (H.closed i j)

/-- `D((d i j)†)` is dense. -/
theorem dense_adjoint_domain (i j : ι) : Dense (((H.d i j)†).domain : Set (W j)) :=
  LinearPMap.dense_adjoint_domain _ (H.dense i j) (H.closed i j)

/-- `R((d j k)†) ⊆ D((d i j)†)`. -/
theorem adjoint_mapsTo (i j k : ι) (y : ((H.d j k)†).domain) :
    ((H.d j k)† y : W j) ∈ ((H.d i j)†).domain :=
  Feec.Operator.adjoint_mapsTo (H.dense j k) (H.mapsTo i j k) (H.d_comp_d i j k) y

/-- `(d i j)† (d j k)† = 0`. -/
theorem adjoint_comp_eq_zero (i j k : ι) (y : ((H.d j k)†).domain) :
    (H.d i j)† ⟨_, H.adjoint_mapsTo i j k y⟩ = 0 :=
  Feec.Operator.adjoint_comp_eq_zero (H.dense i j) (H.dense j k) (H.mapsTo i j k)
    (H.d_comp_d i j k) y

/-- `N(d j k)ᗮ ⊆ N((d i j)†)` (no closed range needed). -/
theorem orthogonal_ker_le_ker_adjoint (i j k : ι) : (H.d j k).kerᗮ ≤ ((H.d i j)†).ker :=
  Feec.Operator.orthogonal_ker_le_ker_adjoint (H.dense i j) (H.mapsTo i j k) (H.d_comp_d i j k)

/-- `N((d i j)†)ᗮ ⊆ N(d j k)` (no closed range needed). -/
theorem orthogonal_ker_adjoint_le_ker (i j k : ι) : ((H.d i j)†).kerᗮ ≤ (H.d j k).ker :=
  Feec.Operator.orthogonal_ker_adjoint_le_ker (H.dense i j) (H.closed j k) (H.mapsTo i j k)
    (H.d_comp_d i j k)

/-! ### Cycles, boundaries, harmonic forms -/

/-- The cycles `𝔷ⁱ = N(d i (c.next i))`. [QuennevilleBelair2015], §4.2; [BruningLesch1992],
[AFW2010], §3.1 -/
def cycles (i : ι) : Submodule 𝕜 (W i) := (H.d i (c.next i)).ker

/-- The boundaries `𝔅ⁱ = R(d (c.prev i) i)`. [QuennevilleBelair2015], §4.2; [BruningLesch1992],
[AFW2010], §3.1 -/
def boundaries (i : ι) : Submodule 𝕜 (W i) := LinearMap.range (H.d (c.prev i) i).toFun

/-- The harmonic forms `ℌⁱ = 𝔷ⁱ ∩ N((d (c.prev i) i)†)`. [QuennevilleBelair2015], §4.2;
[BruningLesch1992], [AFW2010], §3.1 -/
def harmonic (i : ι) : Submodule 𝕜 (W i) := H.cycles i ⊓ ((H.d (c.prev i) i)†).ker

/-- The complex has closed range at `i`: `𝔅ⁱ` is closed. [QuennevilleBelair2015], §4.2;
[BruningLesch1992], [AFW2010], §3.1 -/
def ClosedRangeAt (i : ι) : Prop := IsClosed (H.boundaries i : Set (W i))

theorem boundaries_le_cycles (i : ι) : H.boundaries i ≤ H.cycles i :=
  H.range_le_ker _ _ _

theorem isClosed_cycles (i : ι) : IsClosed (H.cycles i : Set (W i)) := H.isClosed_ker _ _

theorem isClosed_harmonic (i : ι) : IsClosed (H.harmonic i : Set (W i)) :=
  (H.isClosed_cycles i).inter
    (LinearPMap.isClosed_ker (adjoint_isClosed (H.dense _ _)))

/-- Every `d i j` with `j ≠ c.next i` is zero. -/
theorem d_eq_zero_of_ne_next {i j : ι} (hj : j ≠ c.next i) : H.d i j = 0 :=
  H.shape i j fun h => hj (c.next_eq' h).symm

/-- At a related pair `i → j`, the cycles at `i` are `N(d i j)`. -/
theorem cycles_eq {i j : ι} (h : c.Rel i j) : H.cycles i = (H.d i j).ker := by
  obtain rfl := c.next_eq' h; rfl

/-- At a related pair `i → j`, the boundaries at `j` are `R(d i j)`. -/
theorem boundaries_eq {i j : ι} (h : c.Rel i j) :
    H.boundaries j = LinearMap.range (H.d i j).toFun := by
  obtain rfl := c.prev_eq' h; rfl

/-- The cycles are the joint kernel of all differentials leaving `i`. -/
theorem cycles_eq_iInf (i : ι) : H.cycles i = ⨅ j, (H.d i j).ker := by
  refine le_antisymm (le_iInf fun j => ?_) (iInf_le _ _)
  by_cases hj : j = c.next i
  · subst hj; exact le_rfl
  · rw [H.d_eq_zero_of_ne_next hj]
    intro x _
    exact mem_ker_iff.2 ⟨⟨x, Submodule.mem_top⟩, rfl, rfl⟩

/-! ### Complexes on `ComplexShape.up α` from successive differentials -/

section OfSucc

variable {α : Type*} [Add α] [One α] {V : α → Type*}
  [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]

open Classical in
/-- The differentials `d i j` of `ofSucc`: `δ i` transported along `i + 1 = j`, else `0`. -/
def ofSuccD (δ : ∀ i, V i →ₗ.[𝕜] V (i + 1)) (i j : α) : V i →ₗ.[𝕜] V j :=
  if h : i + 1 = j then h ▸ δ i else 0

theorem ofSuccD_succ (δ : ∀ i, V i →ₗ.[𝕜] V (i + 1)) (i : α) : ofSuccD δ i (i + 1) = δ i := by
  simp [ofSuccD]

theorem ofSuccD_of_ne (δ : ∀ i, V i →ₗ.[𝕜] V (i + 1)) {i j : α} (h : i + 1 ≠ j) :
    ofSuccD δ i j = 0 := by
  simp [ofSuccD, h]

/-- The Hilbert complex `⋯ → V i → V (i + 1) → ⋯` on `ComplexShape.up α` (`α = ℕ, ℤ, …`) built
from closed densely defined `δ i : V i →ₗ.[𝕜] V (i + 1)` with `δ (i + 1) δ i = 0`. -/
def ofSucc [IsRightCancelAdd α] [∀ i, CompleteSpace (V i)] (δ : ∀ i, V i →ₗ.[𝕜] V (i + 1))
    (dense : ∀ i, Dense ((δ i).domain : Set (V i)))
    (closed : ∀ i, (δ i).IsClosed)
    (mapsTo : ∀ i (x : (δ i).domain), (δ i x : V (i + 1)) ∈ (δ (i + 1)).domain)
    (comp : ∀ i (x : (δ i).domain), δ (i + 1) ⟨_, mapsTo i x⟩ = 0) :
    HilbertComplex 𝕜 (ComplexShape.up α) V where
  d := ofSuccD δ
  shape i j h := ofSuccD_of_ne δ h
  dense i j := by
    by_cases h : i + 1 = j
    · subst h; rw [ofSuccD_succ]; exact dense i
    · rw [ofSuccD_of_ne δ h]; simp [zero_domain]
  closed i j := by
    by_cases h : i + 1 = j
    · subst h; rw [ofSuccD_succ]; exact closed i
    · rw [ofSuccD_of_ne δ h]; exact LinearPMap.isClosed_zero
  mapsTo i j k x := by
    by_cases h : i + 1 = j
    · subst h
      have key : ∀ T : V i →ₗ.[𝕜] V (i + 1), T = δ i → ∀ x : T.domain,
          (T x : V (i + 1)) ∈ (ofSuccD δ (i + 1) k).domain := by
        rintro _ rfl x
        by_cases h' : i + 1 + 1 = k
        · subst h'; rw [ofSuccD_succ]; exact mapsTo i x
        · rw [ofSuccD_of_ne δ h']; exact Submodule.mem_top
      exact key _ (ofSuccD_succ δ i) x
    · rw [apply_eq_zero_of_eq_zero (ofSuccD_of_ne δ h) x]; exact Submodule.zero_mem _
  d_comp_d i j k x := by
    by_cases h : i + 1 = j
    · subst h
      by_cases h' : i + 1 + 1 = k
      · subst h'
        have key : ∀ T : V i →ₗ.[𝕜] V (i + 1), T = δ i → ∀ S : V (i + 1) →ₗ.[𝕜] V (i + 1 + 1),
            S = δ (i + 1) → ∀ (x : T.domain) (hx : (T x : V (i + 1)) ∈ S.domain),
            S ⟨_, hx⟩ = 0 := by
          rintro _ rfl _ rfl x hx; exact comp i x
        exact key _ (ofSuccD_succ δ i) _ (ofSuccD_succ δ (i + 1)) x _
      · exact apply_eq_zero_of_eq_zero (ofSuccD_of_ne δ h') _
    · have key : ∀ T : V i →ₗ.[𝕜] V j, T = 0 → ∀ (x : T.domain)
          (hx : (T x : V j) ∈ (ofSuccD δ j k).domain), ofSuccD δ j k ⟨_, hx⟩ = 0 := by
        rintro _ rfl x hx
        exact (ofSuccD δ j k).map_zero
      exact key _ (ofSuccD_of_ne δ h) x _

end OfSucc

end HilbertComplex

end Feec
