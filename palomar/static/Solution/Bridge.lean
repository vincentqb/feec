module

public import Solution.Defs
public import Feec.HilbertComplex.Approximation.StaticFEEC

/-!
# The bridge from the challenge to `Feec`

The vocabulary of `Challenge.lean` restates over Mathlib the objects of `Feec`: a Hilbert complex
of the challenge is a `Feec.HilbertComplex` on `ComplexShape.up ℤ` (`HilbertComplex.toFeec`, the
same fields), and so are its subcomplexes and cochain projections; a family of subcomplexes is a
`Feec.HilbertComplex.SubcomplexFamily` (`SubcomplexFamily.toFeec`), to which the graph-norm bounds
and the approximation property transfer degree by degree. This module identifies
the challenge's cycles, boundaries, harmonic forms, harmonic gaps, graph-norm distances and mixed
solutions with those of `Feec`, and turns the verdict of `Feec.HilbertComplex.SubcomplexFamily.staticFEEC`
into the conclusions of the challenge (`SubcomplexFamily.staticVerdict`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.3–§3.4

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex

variable (H : HilbertComplex 𝕜 W)

/-! ### The complex, its subcomplexes and cochain projections in `Feec` -/

/-- The complex as a `Feec` Hilbert complex on `ComplexShape.up ℤ`. -/
def toFeec : Feec.HilbertComplex 𝕜 (ComplexShape.up ℤ) W where
  d := H.d
  shape := H.shape
  dense := H.dense
  closed := H.closed
  mapsTo := H.mapsTo
  d_comp_d := H.d_comp_d

theorem rel_add_one (i : ℤ) : (ComplexShape.up ℤ).Rel i (i + 1) := rfl

theorem rel_sub_one (i : ℤ) : (ComplexShape.up ℤ).Rel (i - 1) i := sub_add_cancel i 1

theorem cycles_eq (i : ℤ) : H.toFeec.cycles i = H.cycles i :=
  H.toFeec.cycles_eq (rel_add_one i)

theorem boundaries_eq (i : ℤ) : H.toFeec.boundaries i = H.boundaries i :=
  H.toFeec.boundaries_eq (rel_sub_one i)

theorem harmonic_eq (i : ℤ) : H.toFeec.harmonic i = H.harmonic i := by
  have hp : (ComplexShape.up ℤ).prev i = i - 1 := (ComplexShape.up ℤ).prev_eq' (rel_sub_one i)
  change H.toFeec.cycles i ⊓ ((H.toFeec.d _ i)†).ker = _
  rw [cycles_eq, hp]
  rfl

theorem closedRangeAt_iff (i : ℤ) :
    H.toFeec.ClosedRangeAt i ↔ IsClosed (H.boundaries i : Set (W i)) := by
  rw [Feec.HilbertComplex.ClosedRangeAt, boundaries_eq]

namespace Subcomplex

variable {H} (S : H.Subcomplex)

/-- The subcomplex as a `Feec` subcomplex. -/
def toFeec : H.toFeec.Subcomplex := ⟨S.V, S.le_domain, S.mapsTo⟩

instance [∀ i, FiniteDimensional 𝕜 (S.V i)] (i : ℤ) : FiniteDimensional 𝕜 (S.toFeec.V i) :=
  ‹∀ i, FiniteDimensional 𝕜 (S.V i)› i

/-- The cochain projection as a `Feec` cochain projection. -/
def CochainProjection.toFeec {S : H.Subcomplex} (P : S.CochainProjection) :
    S.toFeec.CochainProjection :=
  ⟨P.π, P.mem, P.proj, P.comm⟩

/-- The harmonic gap is that of `Feec`. -/
theorem CochainProjection.harmonicGap_toFeec {S : H.Subcomplex} (P : S.CochainProjection)
    (j : ℤ) : P.toFeec.harmonicGap j = P.harmonicGap j := by
  unfold Feec.HilbertComplex.Subcomplex.CochainProjection.harmonicGap
    Subcomplex.CochainProjection.harmonicGap
  rw [H.harmonic_eq j]
  rfl

theorem graphDist_nonneg (i j : ℤ) (x : W i) (y : W j) : 0 ≤ S.graphDist i j x y :=
  le_ciInf fun _ => by positivity

/-- The graph-norm distance of `Feec` is at most that of the challenge. -/
theorem infDist_domainSub_le [∀ i, FiniteDimensional 𝕜 (S.V i)] {i j : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (σ : H.toFeec.domainSpace i) :
    Metric.infDist σ (S.toFeec.domainSub i) ≤
      S.graphDist i j (H.toFeec.domainIncl i σ) (H.d i j (H.toFeec.domainCoord i j σ)) :=
  le_ciInf fun v => S.toFeec.infDist_domainSub_le hij σ v.2

/-- For a cycle `b`, the same with `d b = 0`. -/
theorem infDist_cycles_le [∀ i, FiniteDimensional 𝕜 (S.V i)] {j : ℤ} {b : W j}
    (hb : b ∈ H.toFeec.cycles j) :
    Metric.infDist (Feec.HilbertComplex.cyclesToDomainSpace hb) (S.toFeec.domainSub j) ≤
      S.graphDist j (j + 1) b 0 := by
  have := S.infDist_domainSub_le (rel_add_one j) (Feec.HilbertComplex.cyclesToDomainSpace hb)
  rw [Feec.HilbertComplex.domainIncl_cyclesToDomainSpace] at this
  convert this using 2
  exact (Feec.HilbertComplex.d_domainCoord_cyclesToDomainSpace (H := H.toFeec) (j + 1) hb).symm

end Subcomplex

variable {H} {κ : Type*}

/-- The family as a `Feec` family of subcomplexes. -/
def SubcomplexFamily.toFeec (F : H.SubcomplexFamily κ) :
    Feec.HilbertComplex.SubcomplexFamily H.toFeec κ where
  l := F.l
  V h := (F.V h).toFeec
  finiteDimensional h i := F.finiteDimensional h i
  π h := (F.π h).toFeec

/-- **Graph-norm bounds transfer**: `‖π x‖ + ‖d π x‖ ≤ C (‖x‖ + ‖d x‖)` gives
`‖π x‖_V ≤ 2 |C| ‖x‖_V`. -/
theorem SubcomplexFamily.isGraphBounded_toFeec {F : H.SubcomplexFamily κ} {i : ℤ}
    (hπ : F.IsGraphBounded i) : F.toFeec.IsGraphBounded i := by
  obtain ⟨C, hC⟩ := hπ
  refine ⟨2 * |C|, fun h => ?_⟩
  rw [(ComplexShape.up ℤ).next_eq' (rel_add_one i)]
  intro x
  have h1 := (hC h x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  set a := ‖(F.π h).π i x‖
  set b := ‖H.d i (i + 1) ⟨(F.π h).π i x, (F.V h).le_domain i (i + 1) ((F.π h).mem i x)⟩‖
  set r := ‖(x : W i)‖
  set s := ‖H.d i (i + 1) x‖
  change a ^ 2 + b ^ 2 ≤ (2 * |C|) ^ 2 * (r ^ 2 + s ^ 2)
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hr : 0 ≤ r := norm_nonneg _
  have hs : 0 ≤ s := norm_nonneg _
  have hc := abs_nonneg C
  have h2 : (a + b) ^ 2 ≤ (|C| * (r + s)) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  nlinarith [sq_nonneg (r - s)]

/-- **The approximation property transfers**: the graph-norm distance of `Feec` is at most that
of the challenge. -/
theorem SubcomplexFamily.approximates_toFeec {F : H.SubcomplexFamily κ} {i : ℤ}
    (ha : F.Approximates i) : F.toFeec.Approximates i := fun σ =>
  squeeze_zero (fun _ => Metric.infDist_nonneg)
    (fun h => (F.V h).infDist_domainSub_le (rel_add_one i) σ) (ha (H.toFeec.domainCoord i (i + 1) σ))

end HilbertComplex

/-! ### Mixed solutions -/

namespace HilbertComplex

variable (H : HilbertComplex 𝕜 W)

/-- Two solutions with the same data differ by a solution with zero data. -/
theorem IsMixedSolution.sub {j : ℤ} {A : Submodule 𝕜 (W (j - 1))} {B Q : Submodule 𝕜 (W j)}
    {f : W j} {σ σ' : (H.d (j - 1) j).domain} {u u' : (H.d j (j + 1)).domain} {p p' : W j}
    (hs : H.IsMixedSolution j A B Q f σ u p) (hs' : H.IsMixedSolution j A B Q f σ' u' p') :
    H.IsMixedSolution j A B Q 0 (σ - σ') (u - u') (p - p') where
  mem := ⟨A.sub_mem hs.mem.1 hs'.mem.1, B.sub_mem hs.mem.2.1 hs'.mem.2.1,
    Q.sub_mem hs.mem.2.2 hs'.mem.2.2⟩
  fst τ hτ := by
    have h1 := hs.fst τ hτ
    have h2 := hs'.fst τ hτ
    rw [Submodule.coe_sub, Submodule.coe_sub, inner_sub_right, inner_sub_right]
    linear_combination h1 - h2
  snd v hv := by
    have h1 := hs.snd v hv
    have h2 := hs'.snd v hv
    rw [LinearPMap.map_sub, LinearPMap.map_sub, inner_sub_right, inner_sub_right, inner_sub_right,
      inner_zero_right]
    linear_combination h1 - h2
  harm q hq := by
    rw [Submodule.coe_sub, inner_sub_right, hs.harm q hq, hs'.harm q hq, sub_zero]

omit [∀ i, CompleteSpace (W i)] in
theorem eq_zero_of_inner_self_add {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {x : E} {y : F}
    (h : ⟪x, x⟫_𝕜 + ⟪y, y⟫_𝕜 = 0) : x = 0 ∧ y = 0 := by
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
    ← RCLike.ofReal_pow, ← RCLike.ofReal_add, RCLike.ofReal_eq_zero] at h
  have hx : ‖x‖ = 0 := by nlinarith [norm_nonneg x, norm_nonneg y]
  have hy : ‖y‖ = 0 := by nlinarith [norm_nonneg x, norm_nonneg y]
  exact ⟨norm_eq_zero.1 hx, norm_eq_zero.1 hy⟩

/-- **Uniqueness for the mixed problem**: a solution with zero data vanishes when the harmonic
space `Q` is made of cycles of `B` and contains every cycle of `B` orthogonal to `d A`. -/
theorem IsMixedSolution.eq_zero {j : ℤ} {A : Submodule 𝕜 (W (j - 1))} {B Q : Submodule 𝕜 (W j)}
    (hQ : ∀ q ∈ Q, ∃ hq : q ∈ (H.d j (j + 1)).domain, q ∈ B ∧ H.d j (j + 1) ⟨q, hq⟩ = 0)
    (hQ' : ∀ u : (H.d j (j + 1)).domain, (u : W j) ∈ B → H.d j (j + 1) u = 0 →
      (∀ τ : (H.d (j - 1) j).domain, (τ : W (j - 1)) ∈ A → ⟪H.d (j - 1) j τ, (u : W j)⟫_𝕜 = 0) →
        (u : W j) ∈ Q)
    {σ : (H.d (j - 1) j).domain} {u : (H.d j (j + 1)).domain} {p : W j}
    (hs : H.IsMixedSolution j A B Q 0 σ u p) : σ = 0 ∧ u = 0 ∧ p = 0 := by
  obtain ⟨hσ, hu, hp⟩ := hs.mem
  have e1 := hs.fst σ hσ
  have e2 := hs.snd u hu
  have e3 := hs.harm p hp
  rw [inner_zero_right] at e2
  have e3' : ⟪(u : W j), p⟫_𝕜 = 0 := by rw [← inner_conj_symm, e3, _root_.map_zero]
  have e4 : ⟪(u : W j), H.d (j - 1) j σ⟫_𝕜 = ⟪(σ : W (j - 1)), σ⟫_𝕜 := by
    rw [← inner_conj_symm, ← sub_eq_zero.1 e1, inner_conj_symm]
  rw [e3', e4, add_zero] at e2
  obtain ⟨hσ0, hdu⟩ := eq_zero_of_inner_self_add e2
  have hσ0' : σ = 0 := Subtype.ext hσ0
  subst hσ0'
  obtain ⟨hpd, hpB, hdp⟩ := hQ p hp
  have e5 := hs.snd ⟨p, hpd⟩ hpB
  simp only [LinearPMap.map_zero, inner_zero_right, zero_add, hdp, inner_zero_left,
    inner_self_eq_zero] at e5
  subst e5
  have huQ : (u : W j) ∈ Q := hQ' u hu hdu fun τ hτ => by
    have := hs.fst τ hτ
    rwa [ZeroMemClass.coe_zero, inner_zero_right, zero_sub, neg_eq_zero] at this
  have e6 := hs.harm _ huQ
  rw [inner_self_eq_zero] at e6
  exact ⟨rfl, Subtype.ext e6, rfl⟩

/-- **Uniqueness for the mixed problem** with the same data. -/
theorem IsMixedSolution.unique {j : ℤ} {A : Submodule 𝕜 (W (j - 1))} {B Q : Submodule 𝕜 (W j)}
    (hQ : ∀ q ∈ Q, ∃ hq : q ∈ (H.d j (j + 1)).domain, q ∈ B ∧ H.d j (j + 1) ⟨q, hq⟩ = 0)
    (hQ' : ∀ u : (H.d j (j + 1)).domain, (u : W j) ∈ B → H.d j (j + 1) u = 0 →
      (∀ τ : (H.d (j - 1) j).domain, (τ : W (j - 1)) ∈ A → ⟪H.d (j - 1) j τ, (u : W j)⟫_𝕜 = 0) →
        (u : W j) ∈ Q)
    {f : W j} {σ σ' : (H.d (j - 1) j).domain} {u u' : (H.d j (j + 1)).domain} {p p' : W j}
    (hs : H.IsMixedSolution j A B Q f σ u p) (hs' : H.IsMixedSolution j A B Q f σ' u' p') :
    σ = σ' ∧ u = u' ∧ p = p' := by
  obtain ⟨h1, h2, h3⟩ := (hs.sub H hs').eq_zero H hQ hQ'
  exact ⟨sub_eq_zero.1 h1, sub_eq_zero.1 h2, sub_eq_zero.1 h3⟩

/-- The harmonic forms are cycles. -/
theorem harmonic_cond {j : ℤ} : ∀ q ∈ H.harmonic j, ∃ hq : q ∈ (H.d j (j + 1)).domain,
    q ∈ (⊤ : Submodule 𝕜 (W j)) ∧ H.d j (j + 1) ⟨q, hq⟩ = 0 := by
  rintro q ⟨hq, -⟩
  obtain ⟨y, hy, rfl⟩ := hq
  exact ⟨y.2, trivial, hy⟩

/-- A cycle orthogonal to the boundaries is harmonic. -/
theorem harmonic_cond' {j : ℤ} : ∀ u : (H.d j (j + 1)).domain, (u : W j) ∈ (⊤ : Submodule 𝕜 (W j)) →
    H.d j (j + 1) u = 0 → (∀ τ : (H.d (j - 1) j).domain, (τ : W (j - 1)) ∈ (⊤ : Submodule 𝕜 _) →
      ⟪H.d (j - 1) j τ, (u : W j)⟫_𝕜 = 0) → (u : W j) ∈ H.harmonic j := by
  intro u _ hdu hτ
  refine ⟨⟨u, hdu, rfl⟩, ?_⟩
  have hmem : (u : W j) ∈ (H.d (j - 1) j)†.domain :=
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨0, fun τ => by
      rw [inner_zero_left, ← inner_conj_symm, hτ τ trivial, _root_.map_zero]⟩
  refine ⟨⟨_, hmem⟩, ?_, rfl⟩
  exact LinearPMap.adjoint_apply_eq (H.dense _ _) _ fun τ => by
    rw [inner_zero_left, ← inner_conj_symm, hτ τ trivial, _root_.map_zero]

end HilbertComplex

/-! ### Mixed solutions of `Feec` -/

namespace HilbertComplex

variable (H : HilbertComplex 𝕜 W)

/-- A point of `D(d i j)` at a related pair, as a point of the domain space of `Feec`. -/
def toDomainSpace {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (x : (H.d i j).domain) :
    H.toFeec.domainSpace i :=
  (H.toFeec.d i ((ComplexShape.up ℤ).next i)).toGraphSpace
    ⟨x, by rw [(ComplexShape.up ℤ).next_eq' hij]; exact x.2⟩

/-- The mixed solutions of `Feec` are mixed solutions. -/
theorem isMixedSolution_of_feec {j : ℤ} {f : W j} {σ : H.toFeec.domainSpace (j - 1)}
    {u : H.toFeec.domainSpace j} {p : H.toFeec.harmonic j}
    (hs : H.toFeec.IsMixedSolution (j - 1) j (j + 1) f σ u p) :
    H.IsMixedSolution j ⊤ ⊤ (H.harmonic j) f (H.toFeec.domainCoord (j - 1) j σ)
      (H.toFeec.domainCoord j (j + 1) u) p where
  mem := ⟨trivial, trivial, H.harmonic_eq j ▸ p.2⟩
  fst τ _ := hs.fst (H.toDomainSpace (rel_sub_one j) τ)
  snd v _ := hs.snd (H.toDomainSpace (rel_add_one j) v)
  harm q hq := hs.harm q ((H.harmonic_eq j).symm ▸ hq)

namespace Subcomplex

variable {H} (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)]

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
theorem boundaries_eq (i : ℤ) : S.toFeec.boundariesW i = S.boundaries i := by
  have hp : (ComplexShape.up ℤ).prev i = i - 1 := (ComplexShape.up ℤ).prev_eq' (rel_sub_one i)
  change LinearMap.range ((S.V i).subtype ∘ₗ S.toFeec.dLin _ i) = _
  rw [hp]
  rfl

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
theorem harmonic_eq (i : ℤ) : S.toFeec.harmonicW i = S.harmonic i := by
  change S.V i ⊓ H.toFeec.cycles i ⊓ (S.toFeec.boundariesW i)ᗮ = _
  rw [H.cycles_eq, boundaries_eq]
  rfl

/-- A point of `Vⁱ` at a related pair, as a point of the discrete domain space of `Feec`. -/
def toDomainSpace (i : ℤ) (x : S.V i) : S.toFeec.toHilbertComplex.domainSpace i :=
  (S.toFeec.toHilbertComplex.d i ((ComplexShape.up ℤ).next i)).toGraphSpace ⟨x, Submodule.mem_top⟩

/-- The discrete mixed solutions of `Feec`, read in `W`, are discrete mixed solutions. -/
theorem isMixedSolution_of_feec {j : ℤ} {f : W j}
    {σ : S.toFeec.toHilbertComplex.domainSpace (j - 1)}
    {u : S.toFeec.toHilbertComplex.domainSpace j} {p : S.toFeec.toHilbertComplex.harmonic j}
    (hs : S.toFeec.toHilbertComplex.IsMixedSolution (j - 1) j (j + 1)
      ((S.V j).orthogonalProjectionOnto f) σ u p) :
    H.IsMixedSolution j (S.V (j - 1)) (S.V j) (S.harmonic j) f
      (H.toFeec.domainCoord (j - 1) j (S.toFeec.embD (j - 1) σ))
      (H.toFeec.domainCoord j (j + 1) (S.toFeec.embD j u)) ((p : S.toFeec.V j) : W j) where
  mem := ⟨(S.toFeec.toHilbertComplex.domainIncl (j - 1) σ).2,
    (S.toFeec.toHilbertComplex.domainIncl j u).2,
    by rw [← S.harmonic_eq j]; exact S.toFeec.mem_harmonic_iff.1 p.2⟩
  fst τ hτ := hs.fst (S.toDomainSpace (j - 1) ⟨τ, hτ⟩)
  snd v hv := by
    exact (hs.snd (S.toDomainSpace j ⟨v, hv⟩)).trans
      (Feec.HilbertComplex.Subcomplex.CochainProjection.inner_orthogonalProjectionOnto_eq
        S.toFeec f ⟨v, hv⟩)
  harm q hq := by
    have hqV : q ∈ S.V j := hq.1.1
    exact hs.harm ⟨q, hqV⟩ (S.toFeec.mem_harmonic_iff.2 (S.harmonic_eq j ▸ hq))

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- The discrete harmonic forms are cycles of `V`. -/
theorem harmonic_cond {j : ℤ} : ∀ q ∈ S.harmonic j, ∃ hq : q ∈ (H.d j (j + 1)).domain,
    q ∈ S.V j ∧ H.d j (j + 1) ⟨q, hq⟩ = 0 := by
  rintro q ⟨⟨hqV, hq⟩, -⟩
  obtain ⟨y, hy, rfl⟩ := hq
  exact ⟨y.2, hqV, hy⟩

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- A cycle of `V` orthogonal to the discrete boundaries is discrete harmonic. -/
theorem harmonic_cond' {j : ℤ} : ∀ u : (H.d j (j + 1)).domain, (u : W j) ∈ S.V j →
    H.d j (j + 1) u = 0 → (∀ τ : (H.d (j - 1) j).domain, (τ : W (j - 1)) ∈ S.V (j - 1) →
      ⟪H.d (j - 1) j τ, (u : W j)⟫_𝕜 = 0) → (u : W j) ∈ S.harmonic j := by
  intro u hu hdu hτ
  refine ⟨⟨hu, u, hdu, rfl⟩, fun b hb => ?_⟩
  obtain ⟨y, rfl⟩ := hb
  exact hτ ⟨y, S.le_domain _ _ y.2⟩ y.2

end Subcomplex

end HilbertComplex

/-! ### The static verdict -/

namespace HilbertComplex

variable {H : HilbertComplex 𝕜 W}

/-- **The inclusion induces an isomorphism on cohomology** as soon as the map `[z] ↦ [π z]`
induced by a cochain projection is one-to-one (`Feec`'s `cohomologyMap`). -/
theorem Subcomplex.cohomologyIncl_bijective (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)]
    (P : S.CochainProjection) {j : ℤ} (hP : Function.Injective (P.toFeec.cohomologyMap j)) :
    Function.Bijective (S.cohomologyIncl j) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun q hq => ?_, fun q => ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [cohomologyIncl, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    obtain ⟨y, hy⟩ := hq
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨P.π (j - 1) y, P.mem _ _⟩, ?_⟩
    change H.d (j - 1) j ⟨P.π (j - 1) y, _⟩ = (z : W j)
    rw [P.comm, show H.d (j - 1) j y = (z : W j) from hy, P.proj _ _ z.2.1]
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hz : (z : W j) ∈ H.toFeec.cycles j := (H.cycles_eq j).symm ▸ z.2
    have hπz : P.π j z ∈ S.V j ⊓ H.toFeec.cycles j := P.toFeec.mem_cyclesW hz
    have hdiff : (z : W j) - P.π j z ∈ H.toFeec.cycles j := sub_mem hz hπz.2
    have h0 : P.toFeec.cohomologyMap j (Submodule.Quotient.mk ⟨_, hdiff⟩) =
        P.toFeec.cohomologyMap j 0 := by
      rw [_root_.map_zero, Feec.HilbertComplex.Subcomplex.CochainProjection.cohomologyMap, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero]
      have : P.toFeec.cyclesMap j ⟨_, hdiff⟩ = 0 := Subtype.ext (Subtype.ext (by
        rw [Feec.HilbertComplex.Subcomplex.CochainProjection.coe_cyclesMap_apply]
        change P.π j ((z : W j) - P.π j z) = 0
        rw [_root_.map_sub, P.proj _ _ (P.mem _ _), sub_self]))
      rw [this]
      exact zero_mem _
    have hb := Submodule.Quotient.mk_eq_zero _ |>.1 (hP h0)
    rw [Submodule.mem_comap, Submodule.coe_subtype, HilbertComplex.boundaries_eq H j] at hb
    refine ⟨Submodule.Quotient.mk ⟨P.π j z, hπz.1, by have h2 := hπz.2; rwa [H.cycles_eq j] at h2⟩, ?_⟩
    rw [cohomologyIncl, Submodule.mapQ_apply, Submodule.Quotient.eq]
    have := neg_mem hb
    rwa [neg_sub] at this

/-- The graph-norm error of two triples read from `Feec`'s domain spaces is at most twice their
distance there. -/
theorem mixedError_le {j : ℤ} (σ σ' : H.toFeec.domainSpace (j - 1))
    (u u' : H.toFeec.domainSpace j) (p p' : W j) :
    H.mixedError j (H.toFeec.domainCoord (j - 1) j σ) (H.toFeec.domainCoord (j - 1) j σ')
      (H.toFeec.domainCoord j (j + 1) u) (H.toFeec.domainCoord j (j + 1) u') p p' ≤
      2 * (‖σ - σ'‖ + ‖u - u'‖ + ‖p - p'‖) := by
  have h1 : ‖(H.toFeec.domainCoord (j - 1) j σ : W (j - 1)) - H.toFeec.domainCoord (j - 1) j σ'‖
      ≤ ‖σ - σ'‖ := by
    rw [← Submodule.coe_sub, ← _root_.map_sub]; exact H.toFeec.norm_domainIncl_le _ _
  have h2 : ‖H.d (j - 1) j (H.toFeec.domainCoord (j - 1) j σ) -
      H.d (j - 1) j (H.toFeec.domainCoord (j - 1) j σ')‖ ≤ ‖σ - σ'‖ := by
    have := H.toFeec.norm_d_domainCoord_le (j - 1) j (σ - σ')
    rwa [_root_.map_sub, LinearPMap.map_sub] at this
  have h3 : ‖(H.toFeec.domainCoord j (j + 1) u : W j) - H.toFeec.domainCoord j (j + 1) u'‖
      ≤ ‖u - u'‖ := by
    rw [← Submodule.coe_sub, ← _root_.map_sub]; exact H.toFeec.norm_domainIncl_le _ _
  have h4 : ‖H.d j (j + 1) (H.toFeec.domainCoord j (j + 1) u) -
      H.d j (j + 1) (H.toFeec.domainCoord j (j + 1) u')‖ ≤ ‖u - u'‖ := by
    have := H.toFeec.norm_d_domainCoord_le j (j + 1) (u - u')
    rwa [_root_.map_sub, LinearPMap.map_sub] at this
  unfold mixedError
  linarith [norm_nonneg (p - p')]

variable {κ : Type*}

/-- A discrete triple of `Feec`'s mixed space of norm at most `B` has graph-norm size at most
`6 B` in the challenge. -/
theorem Subcomplex.mixedError_le_of_norm_le (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)]
    {j : ℤ} (x : S.toFeec.toHilbertComplex.MixedSpace (j - 1) j) {B : ℝ} (hx : ‖x‖ ≤ B) :
    H.mixedError j (H.toFeec.domainCoord (j - 1) j (S.toFeec.embD (j - 1) (WithLp.fst x))) 0
      (H.toFeec.domainCoord j (j + 1) (S.toFeec.embD j (WithLp.snd x).fst)) 0
      (((WithLp.snd x).snd : S.toFeec.V j) : W j) 0 ≤ 6 * B := by
  have e := mixedError_le (H := H) (j := j) (S.toFeec.embD (j - 1) (WithLp.fst x)) 0
    (S.toFeec.embD j (WithLp.snd x).fst) 0 (((WithLp.snd x).snd : S.toFeec.V j) : W j) 0
  rw [_root_.map_zero, _root_.map_zero] at e
  refine e.trans ?_
  simp only [sub_zero, LinearIsometry.norm_map, Submodule.norm_coe]
  have n1 := WithLp.norm_fst_le (x := x)
  have n2 := WithLp.norm_snd_le (x := x)
  have n3 := WithLp.norm_fst_le (x := WithLp.snd x)
  have n4 := WithLp.norm_snd_le (x := WithLp.snd x)
  linarith

theorem starProjection_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {K K' : Submodule 𝕜 E} (h : K = K') [K.HasOrthogonalProjection] [K'.HasOrthogonalProjection]
    (x : E) : K.starProjection x = K'.starProjection x := by
  subst h; rfl

/-- **The static verdict** from `Feec`'s static FEEC theorem for families of subcomplexes. -/
theorem SubcomplexFamily.staticVerdict (F : H.SubcomplexFamily κ) (j : ℤ)
    (hπ : F.IsGraphBounded (j - 1)) (hπ' : F.IsGraphBounded j)
    (hj : IsClosed (H.boundaries j : Set (W j)))
    (hj' : IsClosed (H.boundaries (j + 1) : Set (W (j + 1)))) : F.StaticVerdict j := by
  set G := F.toFeec
  have hcj := (H.closedRangeAt_iff j).2 hj
  have hck := (H.closedRangeAt_iff (j + 1)).2 hj'
  have hbi : G.IsGraphBounded ((ComplexShape.up ℤ).prev j) := by
    rw [(ComplexShape.up ℤ).prev_eq' (rel_sub_one j)]
    exact SubcomplexFamily.isGraphBounded_toFeec hπ
  have V := G.staticFEEC j hbi (SubcomplexFamily.isGraphBounded_toFeec hπ') hcj fun k hk => by
    obtain rfl : j + 1 = k := hk; exact hck
  have hsol := fun f => H.isMixedSolution_of_feec (H.toFeec.isMixedSolution_mixedSolution
    (rel_sub_one j) (rel_add_one j) hcj hck f)
  have hdsol := fun h f => (F.V h).isMixedSolution_of_feec
    (Feec.HilbertComplex.Subcomplex.CochainProjection.isMixedSolution_discreteMixedSolution
      (F.V h).toFeec (rel_sub_one j) (rel_add_one j) f)
  have uq := fun {f σ σ' u u' p p'} => @IsMixedSolution.unique _ _ _ _ _ _ H j ⊤ ⊤ (H.harmonic j)
    H.harmonic_cond H.harmonic_cond' f σ σ' u u' p p'
  have uqh := fun h {f σ σ' u u' p p'} => @IsMixedSolution.unique _ _ _ _ _ _ H j
    ((F.V h).V (j - 1)) ((F.V h).V j) ((F.V h).harmonic j) (F.V h).harmonic_cond
    (F.V h).harmonic_cond' f σ σ' u u' p p'
  have hgap : ∀ h, (G.π h).harmonicGap j = (F.π h).harmonicGap j := fun h =>
    (F.π h).harmonicGap_toFeec j
  refine ⟨fun h q hq => ?_, fun ha _ => ?_, fun ha _ => ?_, ?_,
    fun f => ⟨(_, _, _), hsol f, fun x hx => ?_⟩, fun h f => ⟨(_, _, _), hdsol h f, fun x hx => ?_⟩,
    ?_, ?_, fun ha ha' {f σ u p} hs {σh uh ph} hsh => ?_⟩
  · have hq' : q ∈ H.toFeec.harmonic j := (H.harmonic_eq j).symm ▸ hq
    have hm : ((G.V h).harmonicW j).starProjection q ∈ (F.V h).harmonic j := by
      rw [← (F.V h).harmonic_eq j]; exact Submodule.starProjection_apply_mem _ q
    exact (Metric.infDist_le_dist_of_mem hm).trans
      (by rw [dist_eq_norm]; exact V.harmonicDist h hq')
  · have : FiniteDimensional 𝕜 (H.toFeec.harmonic j) := by rw [H.harmonic_eq]; infer_instance
    have h0 := V.harmonicGap (SubcomplexFamily.approximates_toFeec ha)
    simp only [hgap] at h0
    exact h0
  · have : FiniteDimensional 𝕜 (H.toFeec.harmonic j) := by rw [H.harmonic_eq]; infer_instance
    filter_upwards [V.cohomology (SubcomplexFamily.approximates_toFeec ha)] with h hh
    exact (F.V h).cohomologyIncl_bijective (F.π h) hh.1
  · obtain ⟨C, hC⟩ := V.poincare (rel_add_one j)
    refine ⟨C, fun h v hv hz => hC h hv fun y hy => hz y ⟨hy.1, ?_⟩⟩
    rw [← H.cycles_eq]; exact hy.2
  · obtain ⟨h1, h2, h3⟩ := uq hx (hsol f)
    exact Prod.ext h1 (Prod.ext h2 h3)
  · obtain ⟨h1, h2, h3⟩ := uqh h hx (hdsol h f)
    exact Prod.ext h1 (Prod.ext h2 h3)
  · -- stability, from `Feec`'s uniform stability for the data `P_{Vₕ} f`
    obtain ⟨C, hC⟩ := V.wellPosed (rel_sub_one j) (rel_add_one j)
    refine ⟨6 * max C 0, fun h {f σh uh ph} hsh => ?_⟩
    obtain ⟨h1, h2, h3⟩ := uqh h hsh (hdsol h f)
    rw [h1, h2, h3]
    have hx := (hC h (((F.V h).toFeec.V j).orthogonalProjectionOnto f)).2 _
      ((F.V h).toFeec.toHilbertComplex.mixedForm_mixedSolution (rel_sub_one j) (rel_add_one j)
        ((F.V h).toFeec.closedRangeAt _) ((F.V h).toFeec.closedRangeAt _)
        (((F.V h).toFeec.V j).orthogonalProjectionOnto f))
    have hPf : ‖((F.V h).toFeec.V j).orthogonalProjectionOnto f‖ ≤ ‖f‖ :=
      ((F.V h).toFeec.V j).norm_orthogonalProjectionOnto_apply_le f
    exact ((F.V h).mixedError_le_of_norm_le
      (Feec.HilbertComplex.Subcomplex.CochainProjection.discreteMixedSolution (F.V h).toFeec
        (rel_sub_one j) (rel_add_one j) f) (hx.trans
      ((mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hPf (le_max_right C 0))))).trans_eq (mul_assoc _ _ _).symm
  · obtain ⟨K, hK0, hK⟩ := V.quasiOptimal (rel_sub_one j) (rel_add_one j)
    obtain ⟨Cb, hCb, -, hCbj⟩ := hbi.exists_bound (SubcomplexFamily.isGraphBounded_toFeec hπ')
    have hC0 : 0 ≤ Cb := zero_le_one.trans hCb
    refine ⟨2 * (K * (1 + Cb)), fun {f σ u p} hs h {σh uh ph} hsh => ?_⟩
    obtain ⟨rfl, rfl, rfl⟩ := uq hs (hsol f)
    obtain ⟨h1, h2, h3⟩ := uqh h hsh (hdsol h f)
    rw [h1, h2, h3]
    set X := H.toFeec.mixedSolution (rel_sub_one j) (rel_add_one j) hcj hck f
    have e := hK (H.toFeec.isMixedSolution_mixedSolution (rel_sub_one j) (rel_add_one j) hcj hck f) h
    have a1 := (F.V h).infDist_domainSub_le (rel_sub_one j) X.fst
    have a2 := (F.V h).infDist_domainSub_le (rel_add_one j) X.snd.fst
    have a3 := ((G.π h).infDist_harmonicW_le (rel_add_one j) hC0 ((hCbj h).of_next (rel_add_one j))
      X.snd.snd.2).trans (mul_le_mul_of_nonneg_left
        ((F.V h).infDist_cycles_le (H.toFeec.harmonic_le_cycles j X.snd.snd.2)) (by linarith))
    have hBc := congrArg Submodule.topologicalClosure (H.boundaries_eq j)
    have hbz : (H.boundaries j).topologicalClosure.starProjection
        (H.toFeec.domainIncl j X.snd.fst) ∈ H.toFeec.cycles j := by
      rw [← starProjection_congr hBc]
      exact H.toFeec.closure_boundaries_le_cycles j (Submodule.starProjection_apply_mem _ _)
    have eb : H.toFeec.boundaryPart j (H.toFeec.domainIncl j X.snd.fst) =
        Feec.HilbertComplex.cyclesToDomainSpace hbz :=
      H.toFeec.domainIncl_injective j (by
        rw [Feec.HilbertComplex.domainIncl_cyclesToDomainSpace]
        exact starProjection_congr hBc _)
    have a4 := (F.V h).infDist_cycles_le hbz
    rw [eb] at e
    have hμ := (G.π h).harmonicGap_nonneg j
    rw [hgap h] at e hμ
    have g1 := (F.V h).graphDist_nonneg (j - 1) j (H.toFeec.domainIncl (j - 1) X.fst)
      (H.d (j - 1) j (H.toFeec.domainCoord (j - 1) j X.fst))
    have g2 := (F.V h).graphDist_nonneg j (j + 1) (H.toFeec.domainIncl j X.snd.fst)
      (H.d j (j + 1) (H.toFeec.domainCoord j (j + 1) X.snd.fst))
    have g3 := (F.V h).graphDist_nonneg j (j + 1) (X.snd.snd : W j) 0
    have g4 := (F.V h).graphDist_nonneg j (j + 1)
      ((H.boundaries j).topologicalClosure.starProjection (H.toFeec.domainIncl j X.snd.fst)) 0
    refine (mixedError_le _ _ _ _ _ _).trans ?_
    refine (mul_le_mul_of_nonneg_left e zero_le_two).trans ?_
    rw [mul_assoc 2]
    refine mul_le_mul_of_nonneg_left ?_ zero_le_two
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hK0
    have key : ∀ {a b c d A B P D μ C' : ℝ}, a ≤ A → b ≤ B → c ≤ (1 + C') * P → d ≤ D →
        0 ≤ μ → 0 ≤ C' → 0 ≤ A → 0 ≤ B → 0 ≤ D →
        a + b + c + μ * d ≤ (1 + C') * (A + B + P + μ * D) := by
      intro a b c d A B P D μ C' h1 h2 h3 h4 h5 h6 h7 h8 h9
      nlinarith [mul_le_mul_of_nonneg_left h4 h5, mul_nonneg h6 h7, mul_nonneg h6 h8,
        mul_nonneg h6 (mul_nonneg h5 h9)]
    exact key a1 a2 a3 a4 hμ hC0 g1 g2 g4
  · obtain ⟨rfl, rfl, rfl⟩ := uq hs (hsol f)
    have hT := (V.converges (rel_sub_one j) (rel_add_one j)
      (SubcomplexFamily.approximates_toFeec ha) (SubcomplexFamily.approximates_toFeec ha')
      (H.toFeec.isMixedSolution_mixedSolution (rel_sub_one j) (rel_add_one j) hcj hck f)).const_mul 2
    rw [mul_zero] at hT
    refine squeeze_zero (fun _ => by unfold mixedError; positivity) (fun h => ?_) hT
    obtain ⟨h1, h2, h3⟩ := uqh h (hsh h) (hdsol h f)
    rw [h1, h2, h3]
    exact mixedError_le _ _ _ _ _ _

end HilbertComplex

end FEEC
