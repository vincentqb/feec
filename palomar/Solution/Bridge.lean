module

public import Solution.Defs
public import Feec.HilbertComplex.Approximation.Crown

/-!
# The bridge from the challenge to `Feec`

The vocabulary of `Challenge.lean` restates over Mathlib the objects of `Feec`: a Hilbert complex
of the challenge is a `Feec.HilbertComplex` on `ComplexShape.up ℤ` (`HilbertComplex.toFeec`, the
same fields), and so are its subcomplexes, cochain projections and conforming families. This
module identifies the challenge's cycles, boundaries, harmonic forms, mixed solutions, window
operators and discrete operators with those of `Feec`, and turns the verdicts of
`Feec.HilbertComplex.ConformingFamily.feec` into the conclusions of the challenge.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.3–§3.4

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex

variable (H : HilbertComplex 𝕜 W)

/-! ### The complex, its subcomplexes and conforming families in `Feec` -/

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

end Subcomplex

variable {H} {κ : Type*}

/-- The conforming family as a `Feec` conforming family. -/
def ConformingFamily.toFeec (F : H.ConformingFamily κ) :
    Feec.HilbertComplex.ConformingFamily H.toFeec κ where
  l := F.l
  V h := (F.V h).toFeec
  finiteDimensional h i := F.finiteDimensional h i
  π h := (F.π h).toFeec
  bound_π := F.bound_π
  approx := F.approx

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

/-- **The static verdict** from `Feec`'s static FEEC theorem. -/
theorem ConformingFamily.staticVerdict (F : H.ConformingFamily κ)
    (hcr : ∀ i, IsClosed (H.boundaries i : Set (W i))) (j : ℤ)
    [FiniteDimensional 𝕜 (H.harmonic j)] : F.StaticVerdict j := by
  have hcr' : ∀ i, H.toFeec.ClosedRangeAt i := fun i => (H.closedRangeAt_iff i).2 (hcr i)
  have : FiniteDimensional 𝕜 (H.toFeec.harmonic j) := by rw [H.harmonic_eq]; infer_instance
  have V := F.toFeec.staticFEEC hcr' j
  have hsol := fun f => H.isMixedSolution_of_feec (H.toFeec.isMixedSolution_mixedSolution
    (rel_sub_one j) (rel_add_one j) (hcr' j) (hcr' (j + 1)) f)
  have hdsol := fun h f => (F.V h).isMixedSolution_of_feec
    (Feec.HilbertComplex.Subcomplex.CochainProjection.isMixedSolution_discreteMixedSolution
      (F.V h).toFeec (rel_sub_one j) (rel_add_one j) f)
  have uq := fun {f σ σ' u u' p p'} => @IsMixedSolution.unique _ _ _ _ _ _ H j ⊤ ⊤ (H.harmonic j)
    H.harmonic_cond H.harmonic_cond' f σ σ' u u' p p'
  have uqh := fun h {f σ σ' u u' p p'} => @IsMixedSolution.unique _ _ _ _ _ _ H j
    ((F.V h).V (j - 1)) ((F.V h).V j) ((F.V h).harmonic j) (F.V h).harmonic_cond
    (F.V h).harmonic_cond' f σ σ' u u' p p'
  refine ⟨?_, fun f => ⟨(_, _, _), hsol f, fun x hx => ?_⟩, fun h f => ⟨(_, _, _), hdsol h f, fun x hx => ?_⟩,
    fun {f σ u p} hs {σh uh ph} hsh => ?_⟩
  · filter_upwards [V.cohomology] with h hh
    exact (F.V h).cohomologyIncl_bijective (F.π h) hh.1
  · obtain ⟨h1, h2, h3⟩ := uq hx (hsol f)
    exact Prod.ext h1 (Prod.ext h2 h3)
  · obtain ⟨h1, h2, h3⟩ := uqh h hx (hdsol h f)
    exact Prod.ext h1 (Prod.ext h2 h3)
  · obtain ⟨rfl, rfl, rfl⟩ := uq hs (hsol f)
    have hT := (V.converges (rel_sub_one j) (rel_add_one j)
      (H.toFeec.isMixedSolution_mixedSolution (rel_sub_one j) (rel_add_one j) (hcr' j)
        (hcr' (j + 1)) f)).const_mul 2
    rw [mul_zero] at hT
    refine squeeze_zero (fun _ => by unfold mixedError; positivity) (fun h => ?_) hT
    obtain ⟨h1, h2, h3⟩ := uqh h (hsh h) (hdsol h f)
    rw [h1, h2, h3]
    exact mixedError_le _ _ _ _ _ _

end HilbertComplex

/-! ### Evolutions -/

section Evolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {κ : Type*}

omit [CompleteSpace E] [IsScalarTower ℝ 𝕜 E] in
theorem IsStrongSolution.congr {A : E →ₗ.[𝕜] E} {I : Set ℝ} {u v : ℝ → E}
    (hu : IsStrongSolution A I u) (h : EqOn v u I) : IsStrongSolution A I v :=
  ⟨hu.1.congr h, fun t ht => by
    obtain ⟨w, hw, hd⟩ := hu.2 t ht
    exact ⟨w, h ht ▸ hw, hd.congr h (h ht)⟩⟩

omit [CompleteSpace E] [IsScalarTower ℝ 𝕜 E] in
theorem isStrongSolution_iff {A : E →ₗ.[𝕜] E} {I : Set ℝ} {u : ℝ → E} :
    IsStrongSolution A I u ↔ Feec.Evolution.IsStrongSolution A I 0 u := by
  refine ⟨fun h => ⟨h.1, fun t ht => ?_⟩, fun h => ⟨h.continuousOn, fun t ht => ?_⟩⟩
  · obtain ⟨v, hv, hd⟩ := h.2 t ht
    exact ⟨v, hv, by simpa using hd⟩
  · obtain ⟨v, hv, hd⟩ := h.deriv t ht
    exact ⟨v, hv, by simpa using hd⟩

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- A dissipative `B` has no nonzero `z = c B z` with `c ≥ 0`. -/
theorem eq_zero_of_eq_smul {B : E →L[𝕜] E} (hB : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ 0) {c : ℝ}
    (hc : 0 ≤ c) {z : E} (hz : z = (c : 𝕜) • B z) : z = 0 := by
  have h : ⟪z, z⟫_𝕜 = ⟪(c : 𝕜) • B z, z⟫_𝕜 := by rw [← hz]
  rw [inner_smul_left, RCLike.conj_ofReal] at h
  have h' := congrArg RCLike.re h
  rw [RCLike.re_ofReal_mul, inner_self_eq_norm_sq] at h'
  have : ‖z‖ ^ 2 ≤ 0 := h' ▸ mul_nonpos_of_nonneg_of_nonpos hc (hB z)
  exact norm_eq_zero.1 (by nlinarith [norm_nonneg z])

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- **The θ-iterates are the powers of the θ-step** `r_θ(τ B)` for a dissipative `B`. -/
theorem theta_eq_pow {B : E →L[𝕜] E} (hB : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ 0) {θ τ : ℝ}
    (hθ : 1 / 2 ≤ θ) (hτ : 0 < τ) {w : ℕ → E}
    (hw : ∀ n, w (n + 1) - w n = (τ : 𝕜) • B ((θ : 𝕜) • w (n + 1) + (1 - (θ : 𝕜)) • w n))
    (n : ℕ) :
    w n = (Feec.TimeStepping.thetaStep ((B : E →ₗ[𝕜] E).toPMap ⊤) (θ : 𝕜) τ ^ n) (w 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, ← ih]
    set u' := Feec.TimeStepping.thetaStep ((B : E →ₗ[𝕜] E).toPMap ⊤) (θ : 𝕜) τ (w n)
    obtain ⟨_, hu'⟩ := Feec.TimeStepping.isThetaStep_thetaStep_of_isMDissipative
      (θ := (θ : 𝕜)) (B.isMDissipative_toPMap_top hB) (by rw [RCLike.ofReal_re]; linarith) hτ (w n)
    change u' - w n = (τ : 𝕜) • B ((θ : 𝕜) • u' + (1 - (θ : 𝕜)) • w n) at hu'
    refine sub_eq_zero.1 (eq_zero_of_eq_smul hB (mul_nonneg hτ.le (by linarith : (0 : ℝ) ≤ θ)) ?_)
    calc w (n + 1) - u' = (w (n + 1) - w n) - (u' - w n) := by abel
      _ = (τ : 𝕜) • (B ((θ : 𝕜) • w (n + 1) + (1 - (θ : 𝕜)) • w n) -
          B ((θ : 𝕜) • u' + (1 - (θ : 𝕜)) • w n)) := by rw [hw n, hu', smul_sub]
      _ = (τ : 𝕜) • B ((θ : 𝕜) • (w (n + 1) - u')) := by
        rw [← _root_.map_sub, smul_sub]; congr 2; abel
      _ = ((τ * θ : ℝ) : 𝕜) • B (w (n + 1) - u') := by
        rw [_root_.map_smul, smul_smul, RCLike.ofReal_mul]

omit [IsScalarTower ℝ 𝕜 E] in
/-- **The evolution verdict from `Feec`'s**: the conclusions of the dissipative and fully discrete
FEEC theorems, restated. -/
theorem evolutionVerdict_of {A : E →ₗ.[𝕜] E} {l : Filter κ} {X : κ → Submodule 𝕜 E}
    [∀ h, CompleteSpace (X h)] {B : ∀ h, X h →L[𝕜] X h} {S S' : ℝ → E →L[𝕜] E} (hSS' : ∀ t, 0 ≤ t → S t = S' t)
    (hA : A.IsMDissipative)
    (hB : ∀ h x, RCLike.re ⟪B h x, x⟫_𝕜 ≤ 0)
    (hsol : ∀ (x : A.domain) (T : ℝ),
      Feec.Evolution.IsClassicalSolution A (Icc 0 T) 0 fun t => S' t x)
    (huniq : ∀ (x : A.domain) (T : ℝ) (U : ℝ → E), U 0 = x →
      Feec.Evolution.IsStrongSolution A (Icc 0 T) 0 U → EqOn U (fun t => S' t x) (Icc 0 T))
    (hanti : ∀ x, AntitoneOn (fun t => ‖S' t x‖) (Ici 0)) (hS0 : ∀ x, S' 0 x = x)
    (hconv : ∀ (x : E) (v : ∀ h, X h), Tendsto (fun h => (v h : E)) l (𝓝 x) → ∀ T : ℝ,
      TendstoUniformlyOn (fun h t => ((Feec.C0Group.ofBounded (B h)).S t (v h) : E))
        (fun t => S' t x) l (Icc 0 T))
    (htheta : ∀ (θ : ℝ) (_ : 1 / 2 ≤ θ) (τ : κ → ℝ) (_ : ∀ h, 0 < τ h), Tendsto τ l (𝓝 0) →
      ∀ (x : E) (v : ∀ h, X h), Tendsto (fun h => (v h : E)) l (𝓝 x) → ∀ (T ε : ℝ), 0 < ε →
        ∀ᶠ h in l, ∀ n : ℕ, (n : ℝ) * τ h ∈ Icc 0 T →
          ‖S' (n * τ h) x - ((Feec.TimeStepping.thetaStep ((B h : X h →ₗ[𝕜] X h).toPMap ⊤)
            (θ : 𝕜) (τ h) ^ n) (v h) : E)‖ < ε) :
    EvolutionVerdict A l X B S where
  dense := hA.dense_domain
  solution x hx T := (isStrongSolution_iff.2 (hsol ⟨x, hx⟩ T).toIsStrongSolution).congr
    fun t ht => by simp only [hSS' t ht.1]
  unique x hx T u hu0 hu := fun t ht => by
    simp only [hSS' t ht.1]; exact huniq ⟨x, hx⟩ T u hu0 (isStrongSolution_iff.1 hu) ht
  contraction x t ht := by
    have := hanti x (Set.mem_Ici.2 le_rfl) ht ht
    dsimp only at this
    rwa [hS0, ← hSS' t ht] at this
  semidiscrete x v hv T := by
    simpa only [Feec.C0Group.ofBounded_S] using
      (hconv x v hv T).congr_right fun t ht => by simp only [hSS' t ht.1]
  theta θ hθ τ hτ hτ0 x w hw hw0 T ε hε := by
    filter_upwards [htheta θ hθ τ hτ hτ0 x (fun h => w h 0) hw0 T ε hε] with h hh n hn
    rw [theta_eq_pow (hB h) hθ (hτ h) (hw h) n, hSS' _ hn.1]
    exact hh n hn

end Evolution

/-! ### Windows -/

namespace HilbertComplex

section Window

variable (H : HilbertComplex 𝕜 W) (a : ℤ) (m : ℕ)

theorem totalD_eq : H.totalD a m = (H.toFeec.window a m).totalD := by
  refine LinearPMap.ext rfl fun x hx hy => ?_
  ext j
  rw [Feec.HilbertComplex.totalD_apply]
  rfl

theorem wave_eq : H.wave a m = (H.toFeec.window a m).wave := by
  rw [wave, totalD_eq, Feec.HilbertComplex.wave_eq]

omit [∀ i, CompleteSpace (W i)] in
theorem sq_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : sq A = A.sq := by
  have hd : (sq A).domain = A.sq.domain := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hx⟩
      exact ⟨hx, hy⟩
    · rintro ⟨hx, hAx⟩
      exact ⟨Submodule.mem_map.2 ⟨⟨x, hx⟩, hAx, rfl⟩, hx⟩
  exact LinearPMap.ext hd fun x hx hy => rfl

theorem heat_eq : sq (H.wave a m) = -(H.toFeec.window a m).hodgeLaplacian := by
  rw [sq_eq, wave_eq, Feec.HilbertComplex.hodgeLaplacian, neg_neg]

/-- Closed ranges of `H` give closed ranges of every window. -/
theorem closedRangeAt_window (hcr : ∀ i, IsClosed (H.boundaries i : Set (W i))) (i : Fin m) :
    (H.toFeec.window a m).ClosedRangeAt i := by
  by_cases hi : (ComplexShape.window m).Rel ((ComplexShape.window m).prev i) i
  · rw [Feec.HilbertComplex.ClosedRangeAt, Feec.HilbertComplex.boundaries_eq _ hi]
    have hrel : (ComplexShape.up ℤ).Rel (a + (((ComplexShape.window m).prev i : Fin m) : ℕ))
        (a + ((i : ℕ) : ℤ)) := by
      change _ + 1 = _
      rw [ComplexShape.window_rel] at hi
      omega
    have := (H.closedRangeAt_iff _).2 (hcr (a + ((i : ℕ) : ℤ)))
    rwa [Feec.HilbertComplex.ClosedRangeAt, H.toFeec.boundaries_eq hrel] at this
  · rw [Feec.HilbertComplex.ClosedRangeAt, Feec.HilbertComplex.boundaries_eq_bot_of_not_rel _ hi,
      Submodule.bot_coe]
    exact isClosed_singleton

/-- Finite-dimensional harmonic fields `N(L)` give finite-dimensional harmonic forms of every
degree of the window. -/
theorem finiteDimensional_harmonic_window [FiniteDimensional 𝕜 (H.wave a m).ker] (i : Fin m) :
    FiniteDimensional 𝕜 ((H.toFeec.window a m).harmonic i) := by
  have : FiniteDimensional 𝕜 (H.toFeec.window a m).wave.ker := by
    rw [← wave_eq]; infer_instance
  classical
  let f : (H.toFeec.window a m).harmonic i →ₗ[𝕜] PiLp 2 fun i : Fin m => W (a + ((i : ℕ) : ℤ)) :=
    (WithLp.linearEquiv 2 𝕜 (∀ i : Fin m, W (a + ((i : ℕ) : ℤ)))).symm.toLinearMap ∘ₗ
      LinearMap.single 𝕜 (fun i : Fin m => W (a + ((i : ℕ) : ℤ))) i ∘ₗ
        ((H.toFeec.window a m).harmonic i).subtype
  have hf : Function.Injective f := fun v w hvw => Subtype.ext (by
    simpa [f] using congrFun (congrArg WithLp.ofLp hvw) i)
  refine Module.Finite.of_injective (LinearMap.codRestrict ((H.toFeec.window a m).wave.ker) f
    fun v => (H.toFeec.window a m).mem_ker_wave_iff.2 fun j => ?_) fun v w hvw =>
      hf (congrArg Subtype.val hvw)
  by_cases hj : j = i
  · subst hj
    simp [f]
  · simp [f, hj]

end Window

end HilbertComplex

/-! ### The wave and heat verdicts -/

omit [∀ i, CompleteSpace (W i)] in
theorem isReducing_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    IsReducing A K ↔ A.IsReducing K :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun h x => ⟨h.proj_mem x, h.comm x⟩⟩

namespace HilbertComplex.ConformingFamily

variable {H : HilbertComplex 𝕜 W} {κ : Type*} (F : H.ConformingFamily κ) (a : ℤ) (m : ℕ)
  (K : Submodule 𝕜 (Total W a m)) (hK : IsClosed (K : Set (Total W a m)))

instance (h : κ) : CompleteSpace (F.Xh a m h) := FiniteDimensional.complete 𝕜 _

theorem Dh_eq (h : κ) : F.Dh a m h = (F.toFeec.windowFEEC a m K hK).discreteD h :=
  ContinuousLinearMap.ext fun _ => Subtype.ext (LinearPMap.apply_eq_of_eq (H.totalD_eq a m) _ _ rfl)

theorem Lh_eq (h : κ) : F.Lh a m h = (F.toFeec.windowFEEC a m K hK).discreteWave h := by
  rw [Lh, F.Dh_eq a m K hK]
  rfl

theorem Lh_sq_eq (h : κ) :
    (F.Lh a m h ^ 2 : F.Xh a m h →L[𝕜] F.Xh a m h) = (F.toFeec.windowFEEC a m K hK).heatGen h := by
  set G := F.toFeec.windowFEEC a m K hK
  set D := G.discreteD h
  have hdh : (G.totalSubcomplex h).dh () () = D := ContinuousLinearMap.ext fun _ => rfl
  have hD : D * D = 0 := ContinuousLinearMap.ext fun x => Subtype.ext
    ((H.toFeec.window a m).totalD_comp_totalD ⟨x, G.Xh_mem_domain h x⟩)
  have hD' : D.adjoint * D.adjoint = 0 := by
    rw [ContinuousLinearMap.mul_def, ← ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.mul_def, hD]
    exact LinearIsometryEquiv.map_zero _
  rw [pow_two, F.Lh_eq a m K hK]
  show (G.discreteWave h * G.discreteWave h : G.Xh h →L[𝕜] G.Xh h) = _
  rw [Feec.HilbertComplex.ConstrainedFEEC.discreteWave, sub_mul,
    mul_sub, mul_sub, hD, hD', Feec.HilbertComplex.ConstrainedFEEC.heatGen,
    Feec.HilbertComplex.Subcomplex.laplacian, hdh, ← ContinuousLinearMap.mul_def,
    ← ContinuousLinearMap.mul_def]
  abel

omit [∀ i, CompleteSpace (W i)] in
theorem isClosed_top : IsClosed ((⊤ : Submodule 𝕜 (Total W a m)) : Set (Total W a m)) := by
  rw [Submodule.top_coe]; exact isClosed_univ

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **The wave verdict** from `Feec`'s approximating, skew-adjoint and fully discrete FEEC
theorems on the window. -/
theorem waveVerdict : ∃ S : ℝ → Total W a m →L[𝕜] Total W a m,
    EvolutionVerdict (H.wave a m) F.l (F.Xh a m) (F.Lh a m) S ∧ (∀ t x, ‖S t x‖ = ‖x‖) ∧
    (∀ s t, S (s + t) = S s ∘L S t) ∧
    ∀ (K : Submodule 𝕜 (Total W a m)) [K.HasOrthogonalProjection],
      IsReducing (H.wave a m) K ↔ ∀ t, ∀ x ∈ K, S t x ∈ K := by
  set G := F.toFeec.windowFEEC a m ⊤ (isClosed_top a m)
  have V := F.toFeec.feec.wave a m ⊤ (isClosed_top a m)
  have VF := F.toFeec.feec.full a m ⊤ (isClosed_top a m)
  refine ⟨G.toApprox.U, ?_, V.norm_U, fun s t => G.toApprox.isSkewAdjoint.group.map_add s t,
    fun K _ => ?_⟩
  · have hL : F.Lh a m = fun h => G.discreteWave h := funext (F.Lh_eq a m ⊤ (isClosed_top a m))
    rw [H.wave_eq a m, hL]
    exact evolutionVerdict_of (S' := G.toApprox.S) (fun t ht => (V.S_eq_U ht).symm)
      G.toApprox.isMDissipative G.toApprox.dissipative V.isClassicalSolution V.unique V.antitone
      (fun x => by rw [Feec.HilbertComplex.DissipFEEC.S_def, Feec.C0Semigroup.S_zero_apply])
      (fun x v hv T => V.converges (G.mem_toCore_closure x) hv T)
      (fun θ hθ τ hτ hτ0 x v hv T ε hε =>
        (VF.wave (Feec.HilbertComplex.DissipFEEC.thetaScheme _ θ hθ τ hτ)).converges_iterates
          (G.mem_toCore_closure x) hv hτ0 T hε)
  · have hK : IsClosed (K : Set (Total W a m)) := by
      rw [← K.orthogonal_orthogonal]; exact Kᗮ.isClosed_orthogonal
    have VK := F.toFeec.feec.wave a m K hK
    rw [isReducing_iff, H.wave_eq a m]
    exact VK.isReducing_iff_invariant

/-- **The heat verdict** from `Feec`'s heat and fully discrete FEEC theorems on the window. -/
theorem heatVerdict (hcr : ∀ i, IsClosed (H.boundaries i : Set (W i)))
    [FiniteDimensional 𝕜 (H.wave a m).ker] : ∃ S : ℝ → Total W a m →L[𝕜] Total W a m,
    EvolutionVerdict (sq (H.wave a m)) F.l (F.Xh a m) (fun h => F.Lh a m h ^ 2) S := by
  have hcrw := H.closedRangeAt_window a m hcr
  have := H.finiteDimensional_harmonic_window a m
  set G := F.toFeec.windowFEEC a m ⊤ (isClosed_top a m)
  have V := F.toFeec.feec.heat a m ⊤ (isClosed_top a m) hcrw
  have VF := F.toFeec.feec.full a m ⊤ (isClosed_top a m)
  have hZ : ∀ x, x ∈ (G.heatCore hcrw).Data.topologicalClosure := fun x => by
    rw [G.dense_heatCore_data hcrw]; exact Submodule.mem_top
  refine ⟨G.toHeat.S, ?_⟩
  have hL : (fun h => F.Lh a m h ^ 2) = fun h => G.heatGen h :=
    funext (F.Lh_sq_eq a m ⊤ (isClosed_top a m))
  rw [H.heat_eq a m, hL]
  exact evolutionVerdict_of (S' := G.toHeat.S) (fun _ _ => rfl) G.toHeat.isMDissipative
    G.toHeat.dissipative V.isClassicalSolution V.unique V.antitone
    (fun x => by rw [Feec.HilbertComplex.DissipFEEC.S_def, Feec.C0Semigroup.S_zero_apply])
    (fun x v hv T => V.converges (hZ x) hv T)
    (fun θ hθ τ hτ hτ0 x v hv T ε hε =>
      (VF.heat hcrw (Feec.HilbertComplex.DissipFEEC.thetaScheme _ θ hθ τ hτ)).converges_iterates
        (hZ x) hv hτ0 T hε)

end HilbertComplex.ConformingFamily

end FEEC
