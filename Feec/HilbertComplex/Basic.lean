module

public import Mathlib.Algebra.Homology.ComplexShape
public import Feec.Operator.Adjoint

/-!
# Hilbert complexes over a complex shape

Hilbert complexes over `𝕜 = ℝ` or `ℂ` on a `ComplexShape c`: Hilbert spaces `W i` with closed
densely defined `d i j : W i →ₗ.[𝕜] W j`, zero unless `c.Rel i j`, such that `R(d i j) ⊆ D(d j k)`
and `d j k ∘ d i j = 0`; their cycles, boundaries and harmonic forms.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [J. Brüning, M. Lesch, *Hilbert complexes*][BruningLesch1992]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap

@[expose] public noncomputable section

theorem LinearPMap.apply_eq_of_eq {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {T T' : E →ₗ.[𝕜] F}
    (hT : T = T') (x : T.domain) (y : T'.domain) (hxy : (x : E) = y) : T x = T' y := by
  subst hT; rw [Subtype.ext hxy]

namespace Feec

/-- A Hilbert complex over `𝕜` on the shape `c`. [QuennevilleBelair2015], §4.2; [BruningLesch1992];
[AFW2010], §3.1 -/
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

theorem ext_d {H₁ H₂ : HilbertComplex 𝕜 c W} (h : H₁.d = H₂.d) : H₁ = H₂ := by
  cases H₁; cases H₂; subst h; rfl

theorem _root_.LinearPMap.apply_eq_zero_of_eq_zero {R E F : Type*} [Ring R] [AddCommGroup E]
    [Module R E] [AddCommGroup F] [Module R F] {T : E →ₗ.[R] F} (hT : T = 0) (x : T.domain) :
    T x = 0 := by
  subst hT; rfl

theorem _root_.LinearPMap.apply_of_eq_toPMap {R E F : Type*} [Ring R] [AddCommGroup E]
    [Module R E] [AddCommGroup F] [Module R F] {T : E →ₗ.[R] F} {g : E →ₗ[R] F}
    (h : T = g.toPMap ⊤) (x : T.domain) : T x = g x := by
  subst h; rfl

theorem apply_eq_zero_of_not_rel {i j : ι} (h : ¬ c.Rel i j) (x : (H.d i j).domain) :
    H.d i j x = 0 :=
  apply_eq_zero_of_eq_zero (H.shape i j h) x

theorem domain_eq_top_of_not_rel {i j : ι} (h : ¬ c.Rel i j) : (H.d i j).domain = ⊤ := by
  rw [H.shape i j h]; rfl

theorem _root_.LinearPMap.isClosed_zero {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] :
    (0 : E →ₗ.[𝕜] F).IsClosed :=
  ContinuousLinearMap.isClosed_toPMap_top (0 : E →L[𝕜] F)

theorem range_le_ker (i j k : ι) : LinearMap.range (H.d i j).toFun ≤ (H.d j k).ker :=
  Feec.Operator.range_le_ker (H.mapsTo i j k) (H.d_comp_d i j k)

theorem isClosed_ker (i j : ι) : IsClosed ((H.d i j).ker : Set (W i)) :=
  LinearPMap.isClosed_ker (H.closed i j)

theorem dense_adjoint_domain (i j : ι) : Dense (((H.d i j)†).domain : Set (W j)) :=
  LinearPMap.dense_adjoint_domain _ (H.dense i j) (H.closed i j)

theorem adjoint_mapsTo (i j k : ι) (y : ((H.d j k)†).domain) :
    ((H.d j k)† y : W j) ∈ ((H.d i j)†).domain :=
  Feec.Operator.adjoint_mapsTo (H.dense j k) (H.mapsTo i j k) (H.d_comp_d i j k) y

theorem adjoint_comp_eq_zero (i j k : ι) (y : ((H.d j k)†).domain) :
    (H.d i j)† ⟨_, H.adjoint_mapsTo i j k y⟩ = 0 :=
  Feec.Operator.adjoint_comp_eq_zero (H.dense i j) (H.dense j k) (H.mapsTo i j k)
    (H.d_comp_d i j k) y

theorem orthogonal_ker_le_ker_adjoint (i j k : ι) : (H.d j k).kerᗮ ≤ ((H.d i j)†).ker :=
  Feec.Operator.orthogonal_ker_le_ker_adjoint (H.dense i j) (H.mapsTo i j k) (H.d_comp_d i j k)

theorem orthogonal_ker_adjoint_le_ker (i j k : ι) : ((H.d i j)†).kerᗮ ≤ (H.d j k).ker :=
  Feec.Operator.orthogonal_ker_adjoint_le_ker (H.dense i j) (H.closed j k) (H.mapsTo i j k)
    (H.d_comp_d i j k)

/-! ### Cycles, boundaries, harmonic forms -/

/-- The cycles `𝔷ⁱ = N(d i (c.next i))`. -/
def cycles (i : ι) : Submodule 𝕜 (W i) := (H.d i (c.next i)).ker

/-- The boundaries `𝔅ⁱ = R(d (c.prev i) i)`. -/
def boundaries (i : ι) : Submodule 𝕜 (W i) := LinearMap.range (H.d (c.prev i) i).toFun

/-- The harmonic forms `ℌⁱ = 𝔷ⁱ ∩ N((d (c.prev i) i)†)`. -/
def harmonic (i : ι) : Submodule 𝕜 (W i) := H.cycles i ⊓ ((H.d (c.prev i) i)†).ker

/-- The complex has closed range at `i`: `𝔅ⁱ` is closed. -/
def ClosedRangeAt (i : ι) : Prop := IsClosed (H.boundaries i : Set (W i))

theorem boundaries_le_cycles (i : ι) : H.boundaries i ≤ H.cycles i :=
  H.range_le_ker _ _ _

theorem isClosed_cycles (i : ι) : IsClosed (H.cycles i : Set (W i)) := H.isClosed_ker _ _

theorem isClosed_harmonic (i : ι) : IsClosed (H.harmonic i : Set (W i)) :=
  (H.isClosed_cycles i).inter
    (LinearPMap.isClosed_ker (adjoint_isClosed (H.dense _ _)))

theorem d_eq_zero_of_ne_next {i j : ι} (hj : j ≠ c.next i) : H.d i j = 0 :=
  H.shape i j fun h => hj (c.next_eq' h).symm

theorem cycles_eq {i j : ι} (h : c.Rel i j) : H.cycles i = (H.d i j).ker := by
  obtain rfl := c.next_eq' h; rfl

theorem boundaries_eq {i j : ι} (h : c.Rel i j) :
    H.boundaries j = LinearMap.range (H.d i j).toFun := by
  obtain rfl := c.prev_eq' h; rfl

theorem cycles_eq_iInf (i : ι) : H.cycles i = ⨅ j, (H.d i j).ker := by
  refine le_antisymm (le_iInf fun j => ?_) (iInf_le _ _)
  by_cases hj : j = c.next i
  · subst hj; exact le_rfl
  · rw [H.d_eq_zero_of_ne_next hj]
    intro x _
    exact mem_ker_iff.2 ⟨⟨x, Submodule.mem_top⟩, rfl, rfl⟩

/-! ### Cochain maps -/

section CochainMap

variable {H} {𝕜' : Type*} [RCLike 𝕜'] {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)]
  [∀ i, InnerProductSpace 𝕜' (W' i)] [∀ i, CompleteSpace (W' i)] {H' : HilbertComplex 𝕜' c W'}
  {R : Type*} [Semiring R] [∀ i, Module R (W i)] [∀ i, Module R (W' i)] {T : ∀ j, W' j →ₗ[R] W j}

/-- **Cochain maps preserve cycles**: if `T D(d') ⊆ D(d)` and `d T = T d'`, then
`T 𝔷ⁱ(H') ⊆ 𝔷ⁱ(H)`. -/
theorem apply_mem_cycles
    (hT : ∀ j k, c.Rel j k → ∀ x : (H'.d j k).domain,
      ∃ hx : T j x ∈ (H.d j k).domain, H.d j k ⟨_, hx⟩ = T k (H'.d j k x))
    {i : ι} {x : W' i} (hx : x ∈ H'.cycles i) : T i x ∈ H.cycles i := by
  by_cases h : c.Rel i (c.next i)
  · obtain ⟨y, rfl, hy⟩ := LinearPMap.mem_ker_iff.1 hx
    obtain ⟨hTy, e⟩ := hT _ _ h y
    exact LinearPMap.mem_ker_iff.2 ⟨⟨_, hTy⟩, rfl, by rw [e, hy, _root_.map_zero]⟩
  · rw [cycles, H.shape _ _ h]
    exact LinearPMap.mem_ker_iff.2 ⟨⟨T i x, Submodule.mem_top⟩, rfl, rfl⟩

/-- **Cochain maps preserve boundaries**: if `T D(d') ⊆ D(d)` and `d T = T d'`, then
`T 𝔅ⁱ(H') ⊆ 𝔅ⁱ(H)`. -/
theorem apply_mem_boundaries
    (hT : ∀ j k, c.Rel j k → ∀ x : (H'.d j k).domain,
      ∃ hx : T j x ∈ (H.d j k).domain, H.d j k ⟨_, hx⟩ = T k (H'.d j k x))
    {i : ι} {x : W' i} (hx : x ∈ H'.boundaries i) : T i x ∈ H.boundaries i := by
  obtain ⟨y, rfl⟩ := hx
  by_cases h : c.Rel (c.prev i) i
  · obtain ⟨hTy, e⟩ := hT _ _ h y
    exact ⟨⟨_, hTy⟩, e⟩
  · change T i (H'.d (c.prev i) i y) ∈ _
    rw [H'.apply_eq_zero_of_not_rel h, _root_.map_zero]
    exact Submodule.zero_mem _

end CochainMap

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

/-- The Hilbert complex `⋯ → V i → V (i + 1) → ⋯` on `ComplexShape.up α` built from `δ i`. -/
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
