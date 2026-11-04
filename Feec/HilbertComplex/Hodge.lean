module

public import Feec.HilbertComplex.Dual

/-!
# Hodge theory of a Hilbert complex

For a Hilbert complex `H : HilbertComplex 𝕜 c W` on an arbitrary complex shape (any length, any
index, `𝕜 = ℝ` or `ℂ`), at every index `i`:

* harmonic forms are the cycles orthogonal to the boundaries, `ℌⁱ = 𝔷ⁱ ∩ (𝔅ⁱ)ᗮ`, and they are
  also the harmonic forms of the dual complex;
* the **Hodge decomposition** `Wⁱ = cl 𝔅ⁱ ⊕ ℌⁱ ⊕ cl 𝔅*ᵢ` (orthogonal, no closed range
  needed), where `𝔅*ᵢ = R((d i (c.next i))†)` are the boundaries of the dual complex; it holds
  without closures when both ranges are closed;
* the decomposition of the domain `Vⁱ = D(d i (c.next i)) = cl 𝔅ⁱ ⊕ ℌⁱ ⊕ (Vⁱ ∩ (𝔷ⁱ)ᗮ)`;
* the **Poincaré inequality** is equivalent to closed range, `closedRangeAt_iff_poincare`, in
  both the operator and the adjoint form, and closed range transfers to the dual complex;
* cohomology `𝔷ⁱ / 𝔅ⁱ`: harmonic forms always inject, and they represent the cohomology iff the
  range is closed (`harmonicToCohomology_surjective_iff`, `cohomologyEquivHarmonic`); a finite
  dimensional cohomology forces closed range (Brüning–Lesch); finite-dimensional cohomology
  passes along cochain maps `P a`, `R a` with `Σ_a R a P a = 1`.

## Main results

* `HilbertComplex.harmonic_eq`.
* `HilbertComplex.closure_boundaries_sup_harmonic`: `cl 𝔅ⁱ ⊕ ℌⁱ = 𝔷ⁱ`.
* `HilbertComplex.hodge`, `HilbertComplex.hodge_of_closedRangeAt`, `HilbertComplex.hodge_unique`
  (the three components are unique).
* `HilbertComplex.hodge_domain`, `HilbertComplex.hodge_domain_of_closedRangeAt`;
  `HilbertComplex.exists_mem_orthogonal_cycles_inf_domain`: `Vⁱ ∩ (𝔷ⁱ)ᗮ ≠ 0` when `𝔷ⁱ ≠ Wⁱ`.
* `HilbertComplex.closedRangeAt_iff_poincare`, `HilbertComplex.closedRangeAt_iff_poincare_adjoint`,
  `HilbertComplex.dual_closedRangeAt_iff`.
* `HilbertComplex.cohomologyEquivHarmonic`,
  `HilbertComplex.closedRangeAt_of_finiteDimensional_cohomology`,
  `HilbertComplex.exact_iff_harmonic_eq_bot`.
* `HilbertComplex.apply_mem_cycles`, `HilbertComplex.apply_mem_boundaries`,
  `HilbertComplex.finiteDimensional_cohomology_of_sum_eq_id`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.2 (Thm 4.1 Hodge decomposition, Thm 4.2 Poincaré inequality)
* [J. Brüning, M. Lesch, *Hilbert complexes*][BruningLesch1992], Lemma 2.1 (weak and strong Hodge
  decomposition), Thm 2.4
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1.2–§3.1.3
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 4

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap Set

@[expose] public noncomputable section

/-! ### Finite codimension forces closed range -/

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- If the range of a closed operator `T` lies in a closed subspace `Z` with finite-dimensional
algebraic quotient `Z / R(T)`, then `R(T)` is closed. -/
theorem isClosed_range_of_finiteDimensional_quotient {T : E →ₗ.[𝕜] F} (hc : T.IsClosed)
    {Z : Submodule 𝕜 F} (hZ : _root_.IsClosed (Z : Set F)) (hTZ : LinearMap.range T.toFun ≤ Z)
    [FiniteDimensional 𝕜 (Z ⧸ (LinearMap.range T.toFun).comap Z.subtype)] :
    _root_.IsClosed (LinearMap.range T.toFun : Set F) := by
  have : CompleteSpace Z := hZ.completeSpace_coe
  -- the graph of `T` over `N(T)ᗮ`, a complete space on which `snd` is injective
  let G : Submodule 𝕜 (E × F) := T.graph ⊓ T.kerᗮ.comap (LinearMap.fst 𝕜 E F)
  have hG : _root_.IsClosed (G : Set (E × F)) :=
    hc.inter ((Submodule.isClosed_orthogonal _).preimage continuous_fst)
  have : CompleteSpace G := hG.completeSpace_coe
  have hπZ : ∀ p : G, (p : E × F).2 ∈ Z := fun p => by
    obtain ⟨x, -, hx⟩ := (LinearPMap.mem_graph_iff _).1 p.2.1
    exact hTZ ⟨x, hx⟩
  let π : G →L[𝕜] Z :=
    ((ContinuousLinearMap.snd 𝕜 E F).comp G.subtypeL).codRestrict Z hπZ
  have hπ : ∀ p : G, (π p : F) = (p : E × F).2 := fun _ => rfl
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨⟨a, b⟩, hab, ha⟩ hp
    have hb : b = 0 := congrArg Subtype.val hp
    subst hb
    obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff _).1 hab
    have hk : a ∈ T.ker := (LinearPMap.mem_ker_iff).2 ⟨x, hx1.symm, hx2⟩
    have : a ∈ T.ker ⊓ T.kerᗮ := ⟨hk, ha⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
    subst this
    rfl
  have hπrange : ∀ z : Z, z ∈ LinearMap.range (π : G →ₗ[𝕜] Z) ↔ (z : F) ∈ LinearMap.range T.toFun := by
    intro z
    constructor
    · rintro ⟨⟨⟨a, b⟩, hab, -⟩, rfl⟩
      obtain ⟨x, -, hx⟩ := (LinearPMap.mem_graph_iff _).1 hab
      exact ⟨x, hx⟩
    · rintro ⟨x, hx⟩
      obtain ⟨y, hy, hTy⟩ := exists_mem_orthogonal_ker_eq hc x
      exact ⟨⟨((y : E), T y), ⟨T.mem_graph y, by exact hy⟩⟩, Subtype.ext (hTy.trans hx)⟩
  set B' : Submodule 𝕜 Z := (LinearMap.range T.toFun).comap Z.subtype
  have hB' : LinearMap.range (π : G →ₗ[𝕜] Z) = B' := by
    ext z; exact hπrange z
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl B'
  have : FiniteDimensional 𝕜 C :=
    LinearEquiv.finiteDimensional (Submodule.quotientEquivOfIsCompl B' C hC)
  have : CompleteSpace C := FiniteDimensional.complete 𝕜 C
  let Φ : (G × C) →L[𝕜] Z :=
    π.comp (ContinuousLinearMap.fst 𝕜 _ _) + C.subtypeL.comp (ContinuousLinearMap.snd 𝕜 _ _)
  have hΦ : ∀ p, Φ p = π p.1 + (p.2 : Z) := fun _ => rfl
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨g, w⟩ hp
    rw [hΦ] at hp
    have hw : (w : Z) ∈ B' ⊓ C := by
      refine ⟨?_, w.2⟩
      rw [eq_neg_of_add_eq_zero_right hp, ← hB']
      exact neg_mem ⟨g, rfl⟩
    rw [hC.inf_eq_bot, Submodule.mem_bot] at hw
    have hw0 : w = 0 := Subtype.ext hw
    rw [hw, add_zero] at hp
    have hg : g = 0 := hπinj (hp.trans (_root_.map_zero π).symm)
    simp [hg, hw0]
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨b, hb, w, hw, rfl⟩ :=
      Submodule.mem_sup.1 (hC.sup_eq_top ▸ Submodule.mem_top (x := z))
    rw [← hB'] at hb
    obtain ⟨g, rfl⟩ := hb
    exact ⟨(g, ⟨w, hw⟩), rfl⟩
  let e : (G × C) ≃L[𝕜] Z := ContinuousLinearEquiv.ofBijective Φ
    (LinearMap.ker_eq_bot.2 hinj) (LinearMap.range_eq_top.2 hsurj)
  have hS : (B' : Set Z) = e '' {p | p.2 = 0} := by
    ext z
    constructor
    · intro hz
      rw [SetLike.mem_coe, ← hB'] at hz
      obtain ⟨g, rfl⟩ := hz
      exact ⟨(g, 0), rfl, by change Φ (g, 0) = π g; rw [hΦ]; simp⟩
    · rintro ⟨⟨g, w⟩, (hw : w = 0), rfl⟩
      subst hw
      change Φ (g, 0) ∈ B'
      rw [hΦ, ← hB']
      simp
  have hB'c : _root_.IsClosed (B' : Set Z) := by
    rw [hS]
    exact e.toHomeomorph.isClosedMap _ (isClosed_eq continuous_snd continuous_const)
  have hBS : (LinearMap.range T.toFun : Set F) = Subtype.val '' (B' : Set Z) := by
    ext x
    constructor
    · intro hx; exact ⟨⟨x, hTZ hx⟩, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact hy
  rw [hBS]
  exact hZ.isClosedEmbedding_subtypeVal.isClosedMap _ hB'c

end LinearPMap

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W)

instance (i : ι) : (H.cycles i).HasOrthogonalProjection := by
  have : CompleteSpace (H.cycles i) := (H.isClosed_cycles i).completeSpace_coe
  infer_instance

instance (i : ι) : (H.boundaries i).topologicalClosure.HasOrthogonalProjection := by
  have : CompleteSpace (H.boundaries i).topologicalClosure :=
    (H.boundaries i).isClosed_topologicalClosure.completeSpace_coe
  infer_instance

instance (i : ι) : (H.harmonic i).HasOrthogonalProjection := by
  have : CompleteSpace (H.harmonic i) := (H.isClosed_harmonic i).completeSpace_coe
  infer_instance

/-! ### Orthogonal complements of cycles and boundaries -/

/-- `(𝔅ⁱ)ᗮ = N((d (c.prev i) i)†)`, the cycles of the dual complex. [QuennevilleBelair2015], (4.1a) -/
theorem orthogonal_boundaries (i : ι) : (H.boundaries i)ᗮ = H.dual.cycles i := by
  rw [cycles_dual, boundaries, orthogonal_range_eq_ker_adjoint _ (H.dense _ _)]

/-- `(𝔷ⁱ)ᗮ = cl 𝔅*ᵢ`, the closure of the boundaries of the dual complex. [QuennevilleBelair2015], (4.1b) -/
theorem orthogonal_cycles (i : ι) :
    (H.cycles i)ᗮ = (H.dual.boundaries i).topologicalClosure := by
  rw [boundaries_dual, cycles, orthogonal_ker _ (H.dense _ _) (H.closed _ _)]

/-- `(cl 𝔅ⁱ)ᗮ = (𝔅ⁱ)ᗮ`. -/
theorem orthogonal_closure_boundaries (i : ι) :
    (H.boundaries i).topologicalClosureᗮ = (H.boundaries i)ᗮ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.triorthogonal_eq_orthogonal]

theorem closure_boundaries_le_cycles (i : ι) :
    (H.boundaries i).topologicalClosure ≤ H.cycles i :=
  Submodule.topologicalClosure_minimal _ (H.boundaries_le_cycles i) (H.isClosed_cycles i)

/-! ### Harmonic forms -/

/-- `ℌⁱ = 𝔷ⁱ ∩ (𝔅ⁱ)ᗮ`. [QuennevilleBelair2015], §4.2 -/
theorem harmonic_eq (i : ι) : H.harmonic i = H.cycles i ⊓ (H.boundaries i)ᗮ := by
  rw [orthogonal_boundaries, cycles_dual]; rfl

theorem mem_harmonic_iff {i : ι} {x : W i} :
    x ∈ H.harmonic i ↔ x ∈ H.cycles i ∧ x ∈ (H.boundaries i)ᗮ := by
  rw [harmonic_eq]; rfl

/-- `ℌⁱ = 𝔷ⁱ ∩ 𝔷*ᵢ`: the cycles of the complex and of its dual. -/
theorem harmonic_eq_cycles_inf_dual (i : ι) : H.harmonic i = H.cycles i ⊓ H.dual.cycles i := by
  rw [cycles_dual]; rfl

theorem harmonic_le_cycles (i : ι) : H.harmonic i ≤ H.cycles i := inf_le_left

theorem harmonic_le_dual_cycles (i : ι) : H.harmonic i ≤ H.dual.cycles i := by
  rw [harmonic_eq_cycles_inf_dual]; exact inf_le_right

/-- **`𝔷ⁱ = cl 𝔅ⁱ ⊕ ℌⁱ`** (orthogonal; no closed range). [QuennevilleBelair2015], §4.2 -/
theorem closure_boundaries_sup_harmonic (i : ι) :
    (H.boundaries i).topologicalClosure ⊔ H.harmonic i = H.cycles i := by
  rw [harmonic_eq, inf_comm, ← orthogonal_closure_boundaries]
  exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (H.closure_boundaries_le_cycles i)

theorem isOrtho_closure_boundaries_harmonic (i : ι) :
    (H.boundaries i).topologicalClosure ⟂ H.harmonic i := by
  rw [Submodule.isOrtho_comm, Submodule.isOrtho_iff_le, orthogonal_closure_boundaries,
    harmonic_eq]
  exact inf_le_right

theorem isOrtho_cycles_closure_dual_boundaries (i : ι) :
    H.cycles i ⟂ (H.dual.boundaries i).topologicalClosure := by
  rw [Submodule.isOrtho_comm, Submodule.isOrtho_iff_le, ← orthogonal_cycles]

theorem isOrtho_harmonic_closure_dual_boundaries (i : ι) :
    H.harmonic i ⟂ (H.dual.boundaries i).topologicalClosure :=
  (H.isOrtho_cycles_closure_dual_boundaries i).mono_left (H.harmonic_le_cycles i)

theorem isOrtho_closure_boundaries_closure_dual_boundaries (i : ι) :
    (H.boundaries i).topologicalClosure ⟂ (H.dual.boundaries i).topologicalClosure :=
  (H.isOrtho_cycles_closure_dual_boundaries i).mono_left (H.closure_boundaries_le_cycles i)

/-! ### The Hodge decomposition -/

/-- **Hodge decomposition** (weak form, no closed range): `Wⁱ = cl 𝔅ⁱ ⊕ ℌⁱ ⊕ cl 𝔅*ᵢ`, with the
three summands pairwise orthogonal, at every index of every complex. [QuennevilleBelair2015], Thm 4.1;
see [BruningLesch1992], Lemma 2.1 and [AFW2010], §3.1. -/
theorem hodge (i : ι) :
    (H.boundaries i).topologicalClosure ⊔ H.harmonic i ⊔
        (H.dual.boundaries i).topologicalClosure = ⊤ ∧
      (H.boundaries i).topologicalClosure ⟂ H.harmonic i ∧
      H.harmonic i ⟂ (H.dual.boundaries i).topologicalClosure ∧
      (H.boundaries i).topologicalClosure ⟂ (H.dual.boundaries i).topologicalClosure := by
  refine ⟨?_, H.isOrtho_closure_boundaries_harmonic i,
    H.isOrtho_harmonic_closure_dual_boundaries i,
    H.isOrtho_closure_boundaries_closure_dual_boundaries i⟩
  rw [closure_boundaries_sup_harmonic, ← orthogonal_cycles]
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

/-- Under closed range, `𝔷ⁱ = 𝔅ⁱ ⊕ ℌⁱ`. [QuennevilleBelair2015], §4.2 -/
theorem boundaries_sup_harmonic {i : ι} (hi : H.ClosedRangeAt i) :
    H.boundaries i ⊔ H.harmonic i = H.cycles i := by
  have h := H.closure_boundaries_sup_harmonic i
  rwa [IsClosed.submodule_topologicalClosure_eq hi] at h

/-- **Hodge decomposition** (strong form): if `𝔅ⁱ` and `𝔅*ᵢ` are closed, then
`Wⁱ = 𝔅ⁱ ⊕ ℌⁱ ⊕ 𝔅*ᵢ`, pairwise orthogonal. By `dual_closedRangeAt_iff`, closedness of `𝔅*ᵢ` is
closedness of the next boundaries. [QuennevilleBelair2015], Thm 4.1 -/
theorem hodge_of_closedRangeAt {i : ι} (hi : H.ClosedRangeAt i) (hi' : H.dual.ClosedRangeAt i) :
    H.boundaries i ⊔ H.harmonic i ⊔ H.dual.boundaries i = ⊤ ∧
      H.boundaries i ⟂ H.harmonic i ∧ H.harmonic i ⟂ H.dual.boundaries i ∧
      H.boundaries i ⟂ H.dual.boundaries i := by
  have h := H.hodge i
  rwa [IsClosed.submodule_topologicalClosure_eq hi,
    IsClosed.submodule_topologicalClosure_eq hi'] at h

/-- The Hodge decomposition is unique: the components of `x = b + h + b*` are the orthogonal
projections of `x`. -/
theorem hodge_unique {i : ι} {b b' h h' a a' : W i}
    (hb : b ∈ (H.boundaries i).topologicalClosure) (hb' : b' ∈ (H.boundaries i).topologicalClosure)
    (hh : h ∈ H.harmonic i) (hh' : h' ∈ H.harmonic i)
    (ha : a ∈ (H.dual.boundaries i).topologicalClosure)
    (ha' : a' ∈ (H.dual.boundaries i).topologicalClosure)
    (heq : b + h + a = b' + h' + a') : b = b' ∧ h = h' ∧ a = a' := by
  have hz : (b - b') + (h - h') ∈ H.cycles i :=
    add_mem (H.closure_boundaries_le_cycles i (sub_mem hb hb'))
      (H.harmonic_le_cycles i (sub_mem hh hh'))
  have ha'' : a' - a ∈ (H.cycles i)ᗮ := by
    rw [orthogonal_cycles]; exact sub_mem ha' ha
  have e1 : (b - b') + (h - h') = a' - a := by
    rw [← sub_eq_zero, ← sub_eq_zero.2 heq]; abel
  have hzz : a' - a ∈ H.cycles i ⊓ (H.cycles i)ᗮ := ⟨e1 ▸ hz, ha''⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hzz
  rw [hzz] at e1
  have e2 : b - b' = h' - h := by rw [← sub_eq_zero, ← e1]; abel
  have hbb : b - b' ∈ (H.boundaries i).topologicalClosure ⊓
      (H.boundaries i).topologicalClosureᗮ := by
    refine ⟨sub_mem hb hb', ?_⟩
    rw [e2]
    exact (H.isOrtho_closure_boundaries_harmonic i).symm (sub_mem hh' hh)
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hbb
  rw [hbb] at e2
  exact ⟨sub_eq_zero.1 hbb, (sub_eq_zero.1 e2.symm).symm, (sub_eq_zero.1 hzz).symm⟩

/-! ### Decomposition of the domain `Vⁱ = D(d i (c.next i))` -/

theorem cycles_le_domain (i : ι) : H.cycles i ≤ (H.d i (c.next i)).domain :=
  (H.d i (c.next i)).ker_le_domain

/-- `Vⁱ = 𝔷ⁱ ⊕ (Vⁱ ∩ (𝔷ⁱ)ᗮ)`. -/
theorem domain_eq_cycles_sup (i : ι) :
    (H.d i (c.next i)).domain = H.cycles i ⊔ (H.cycles i)ᗮ ⊓ (H.d i (c.next i)).domain :=
  (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (H.cycles_le_domain i)).symm

/-- **`Vⁱ ∩ (𝔷ⁱ)ᗮ ≠ 0` when `𝔷ⁱ ≠ Wⁱ`**: at a related pair `i → j`, if `dⁱ ≠ 0` then some nonzero
`v ∈ D(d i j)` is orthogonal to the cycles (the domain is dense and `𝔷ⁱ` is closed). In degree `1`
of `HΛ(Ω)`: a nonzero `u ∈ H(curl) ∩ (𝔷¹)ᗮ`, so `div u = 0` and `u · ν = 0`. -/
theorem exists_mem_orthogonal_cycles_inf_domain {i j : ι} (hij : c.Rel i j)
    (h : H.cycles i ≠ ⊤) : ∃ v ∈ (H.cycles i)ᗮ ⊓ (H.d i j).domain, v ≠ 0 := by
  obtain rfl := c.next_eq' hij
  by_contra! h0
  have hdom := H.domain_eq_cycles_sup i
  rw [(Submodule.eq_bot_iff _).2 h0, sup_bot_eq] at hdom
  refine h (Submodule.eq_top_iff'.2 fun x => ?_)
  have hx := H.dense i (c.next i) x
  rwa [hdom, (H.isClosed_cycles i).closure_eq] at hx

/-- **Hodge decomposition of the domain** (`V`-level, no closed range):
`Vⁱ = cl 𝔅ⁱ ⊕ ℌⁱ ⊕ (Vⁱ ∩ cl 𝔅*ᵢ)`, pairwise orthogonal in `Wⁱ`; since the first two summands
are cycles, they are also orthogonal in the graph inner product. [QuennevilleBelair2015],
Thm 4.1 -/
theorem hodge_domain (i : ι) :
    (H.d i (c.next i)).domain = (H.boundaries i).topologicalClosure ⊔ H.harmonic i ⊔
      (H.dual.boundaries i).topologicalClosure ⊓ (H.d i (c.next i)).domain := by
  rw [closure_boundaries_sup_harmonic, ← orthogonal_cycles]
  exact H.domain_eq_cycles_sup i

/-- Under closed range, `Vⁱ = 𝔅ⁱ ⊕ ℌⁱ ⊕ (Vⁱ ∩ (𝔷ⁱ)ᗮ)`. [QuennevilleBelair2015], Thm 4.1 -/
theorem hodge_domain_of_closedRangeAt {i : ι} (hi : H.ClosedRangeAt i) :
    (H.d i (c.next i)).domain =
      H.boundaries i ⊔ H.harmonic i ⊔ (H.cycles i)ᗮ ⊓ (H.d i (c.next i)).domain := by
  rw [H.boundaries_sup_harmonic hi]
  exact H.domain_eq_cycles_sup i

/-! ### Closed range: Poincaré inequality and duality -/

/-- **Poincaré inequality ⇔ closed range**, at every index: `𝔅ʲ` is closed iff
`‖x‖ ≤ C ‖d x‖` for `x ∈ D(d (c.prev j) j) ∩ N(d (c.prev j) j)ᗮ`. [QuennevilleBelair2015], Thm 4.2;
see [BruningLesch1992] and [AFW2010], §3.1. -/
theorem closedRangeAt_iff_poincare (j : ι) :
    H.ClosedRangeAt j ↔ ∃ C : ℝ, ∀ x : (H.d (c.prev j) j).domain,
      (x : W (c.prev j)) ∈ (H.d (c.prev j) j).kerᗮ → ‖(x : W (c.prev j))‖ ≤ C * ‖H.d _ j x‖ :=
  isClosed_range_iff_exists_norm_le (H.closed _ _)

/-- **Poincaré inequality ⇔ closed range** at a related pair `i → j`, on the orthogonal
complement of the cycles: `𝔅ʲ` is closed iff `‖x‖ ≤ C ‖d x‖` for `x ∈ Vⁱ ∩ (𝔷ⁱ)ᗮ`.
[QuennevilleBelair2015], Thm 4.2 -/
theorem closedRangeAt_iff_poincare_of_rel {i j : ι} (h : c.Rel i j) :
    H.ClosedRangeAt j ↔ ∃ C : ℝ, ∀ x : (H.d i j).domain,
      (x : W i) ∈ (H.cycles i)ᗮ → ‖(x : W i)‖ ≤ C * ‖H.d i j x‖ := by
  rw [ClosedRangeAt, H.boundaries_eq h, H.cycles_eq h]
  exact isClosed_range_iff_exists_norm_le (H.closed _ _)

/-- **Poincaré inequality for the adjoint ⇔ closed range** at a related pair `i → j`:
`𝔅ʲ` is closed iff `‖y‖ ≤ C ‖d† y‖` for `y ∈ D((d i j)†) ∩ cl 𝔅ʲ`. [QuennevilleBelair2015], Thm 4.2 -/
theorem closedRangeAt_iff_poincare_adjoint {i j : ι} (h : c.Rel i j) :
    H.ClosedRangeAt j ↔ ∃ C : ℝ, ∀ y : ((H.d i j)†).domain,
      (y : W j) ∈ (H.boundaries j).topologicalClosure → ‖(y : W j)‖ ≤ C * ‖(H.d i j)† y‖ := by
  rw [ClosedRangeAt, H.boundaries_eq h, ← isClosed_range_adjoint_iff _ (H.dense i j) (H.closed i j),
    ← orthogonal_ker_adjoint _ (H.dense i j)]
  exact isClosed_range_iff_exists_norm_le (adjoint_isClosed (H.dense i j))

/-- Closed range transfers to the dual complex: at a related pair `i → j`, the dual boundaries
`𝔅*ᵢ = R((d i j)†)` are closed iff `𝔅ʲ` is (closed range theorem). [QuennevilleBelair2015], §4.2 -/
theorem dual_closedRangeAt_iff {i j : ι} (h : c.Rel i j) :
    H.dual.ClosedRangeAt i ↔ H.ClosedRangeAt j := by
  obtain rfl := c.next_eq' h
  rw [ClosedRangeAt, ClosedRangeAt, boundaries_dual, H.boundaries_eq h]
  exact isClosed_range_adjoint_iff _ (H.dense _ _) (H.closed _ _)

/-! ### Cohomology -/

/-- The (algebraic) cohomology `𝔷ⁱ / 𝔅ⁱ`. [QuennevilleBelair2015], §4.2 -/
abbrev cohomology (i : ι) := H.cycles i ⧸ (H.boundaries i).comap (H.cycles i).subtype

/-- The class map `ℌⁱ → 𝔷ⁱ / 𝔅ⁱ`, `h ↦ [h]`. -/
def harmonicToCohomology (i : ι) : H.harmonic i →ₗ[𝕜] H.cohomology i :=
  ((H.boundaries i).comap (H.cycles i).subtype).mkQ ∘ₗ Submodule.inclusion (H.harmonic_le_cycles i)

@[simp] theorem harmonicToCohomology_apply (i : ι) (x : H.harmonic i) :
    H.harmonicToCohomology i x =
      Submodule.Quotient.mk (Submodule.inclusion (H.harmonic_le_cycles i) x) := rfl

/-- `ℌⁱ ∩ 𝔅ⁱ = 0`. -/
theorem boundaries_inf_harmonic (i : ι) : H.boundaries i ⊓ H.harmonic i = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hb, hh⟩
  have : x ∈ H.boundaries i ⊓ (H.boundaries i)ᗮ := ⟨hb, (H.mem_harmonic_iff.1 hh).2⟩
  rwa [Submodule.inf_orthogonal_eq_bot] at this

/-- Harmonic forms inject into cohomology (no closed range). -/
theorem harmonicToCohomology_injective (i : ι) : Function.Injective (H.harmonicToCohomology i) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker, harmonicToCohomology_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap] at hx
  have : (x : W i) ∈ H.boundaries i ⊓ H.harmonic i := ⟨hx, x.2⟩
  rw [boundaries_inf_harmonic, Submodule.mem_bot] at this
  exact (Submodule.mem_bot 𝕜).2 (Subtype.ext this)

/-- Harmonic forms represent all of cohomology **iff** `𝔅ⁱ` is closed. [QuennevilleBelair2015], §4.2 -/
theorem harmonicToCohomology_surjective_iff (i : ι) :
    Function.Surjective (H.harmonicToCohomology i) ↔ H.ClosedRangeAt i := by
  constructor
  · intro hs
    -- every `b ∈ cl 𝔅` is a cycle `b = β + h` with `β ∈ 𝔅`, `h ∈ ℌ ∩ cl 𝔅 = 0`
    have hle : (H.boundaries i).topologicalClosure ≤ H.boundaries i := by
      intro b hb
      obtain ⟨h, hh⟩ := hs (Submodule.Quotient.mk ⟨b, H.closure_boundaries_le_cycles i hb⟩)
      rw [harmonicToCohomology_apply, Submodule.Quotient.eq, Submodule.mem_comap] at hh
      change (h : W i) - b ∈ H.boundaries i at hh
      have hhb : (h : W i) ∈ (H.boundaries i).topologicalClosure := by
        have := add_mem ((H.boundaries i).le_topologicalClosure hh) hb
        rwa [sub_add_cancel] at this
      have h0 : (h : W i) ∈ (H.boundaries i).topologicalClosure ⊓
          (H.boundaries i).topologicalClosureᗮ :=
        ⟨hhb, (H.isOrtho_closure_boundaries_harmonic i).symm h.2⟩
      rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h0
      rw [h0, zero_sub] at hh
      simpa using neg_mem hh
    have heq := le_antisymm hle (H.boundaries i).le_topologicalClosure
    rw [ClosedRangeAt, ← heq]
    exact (H.boundaries i).isClosed_topologicalClosure
  · intro hi q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hz : (z : W i) ∈ H.boundaries i ⊔ H.harmonic i := (H.boundaries_sup_harmonic hi).symm ▸ z.2
    obtain ⟨b, hb, h, hh, hbh⟩ := Submodule.mem_sup.1 hz
    refine ⟨⟨h, hh⟩, ?_⟩
    rw [harmonicToCohomology_apply, Submodule.Quotient.eq, Submodule.mem_comap]
    change h - (z : W i) ∈ H.boundaries i
    rw [← hbh, sub_add_cancel_right]
    exact neg_mem hb

/-- **Harmonic forms represent cohomology**: under closed range, `𝔷ⁱ / 𝔅ⁱ ≃ ℌⁱ`.
[QuennevilleBelair2015], §4.2 -/
def cohomologyEquivHarmonic {i : ι} (hi : H.ClosedRangeAt i) : H.cohomology i ≃ₗ[𝕜] H.harmonic i :=
  (LinearEquiv.ofBijective _
    ⟨H.harmonicToCohomology_injective i, (H.harmonicToCohomology_surjective_iff i).2 hi⟩).symm

/-- **Brüning–Lesch: finite-dimensional cohomology ⇒ closed range.** If `𝔷ⁱ / 𝔅ⁱ` is
finite-dimensional, `𝔅ⁱ` is closed. (With "Fredholm" read as finite-dimensional *harmonic*
forms the implication fails; see `Counterexamples`.) [QuennevilleBelair2015], §4.2 (corrected) -/
theorem closedRangeAt_of_finiteDimensional_cohomology (i : ι)
    [FiniteDimensional 𝕜 (H.cohomology i)] : H.ClosedRangeAt i :=
  have : FiniteDimensional 𝕜 (H.cycles i ⧸
      (LinearMap.range (H.d (c.prev i) i).toFun).comap (H.cycles i).subtype) :=
    ‹FiniteDimensional 𝕜 (H.cohomology i)›
  isClosed_range_of_finiteDimensional_quotient (H.closed _ _) (H.isClosed_cycles i)
    (H.boundaries_le_cycles i)

/-- Under closed range, harmonic forms are finite-dimensional iff cohomology is. -/
theorem finiteDimensional_harmonic_iff {i : ι} (hi : H.ClosedRangeAt i) :
    FiniteDimensional 𝕜 (H.harmonic i) ↔ FiniteDimensional 𝕜 (H.cohomology i) :=
  ⟨fun _ => (H.cohomologyEquivHarmonic hi).symm.finiteDimensional,
    fun _ => (H.cohomologyEquivHarmonic hi).finiteDimensional⟩

/-- `ℌⁱ = 0` iff `𝔅ⁱ` is dense in `𝔷ⁱ` (no closed range needed). -/
theorem harmonic_eq_bot_iff (i : ι) :
    H.harmonic i = ⊥ ↔ (H.boundaries i).topologicalClosure = H.cycles i := by
  constructor
  · intro h
    rw [← H.closure_boundaries_sup_harmonic i, h, sup_bot_eq]
  · intro h
    rw [harmonic_eq, ← h, ← orthogonal_closure_boundaries, Submodule.inf_orthogonal_eq_bot]

/-- Under closed range, the complex is exact at `i` iff `ℌⁱ = 0`. [QuennevilleBelair2015], §4.2 -/
theorem exact_iff_harmonic_eq_bot {i : ι} (hi : H.ClosedRangeAt i) :
    H.boundaries i = H.cycles i ↔ H.harmonic i = ⊥ := by
  rw [harmonic_eq_bot_iff, IsClosed.submodule_topologicalClosure_eq hi]

/-- If `𝔅ⁱ` is not closed it is not all of the closed space `𝔷ⁱ`. -/
theorem boundaries_ne_cycles_of_not_closedRangeAt {i : ι} (h : ¬ H.ClosedRangeAt i) :
    H.boundaries i ≠ H.cycles i := fun he => h (by rw [ClosedRangeAt, he]; exact H.isClosed_cycles i)

/-! ### Cochain maps and finite-dimensional cohomology -/

section CochainMap

variable {H} {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)]
  [∀ i, CompleteSpace (W' i)] {H' : HilbertComplex 𝕜 c W'} {T : ∀ j, W' j →ₗ[𝕜] W j}

/-- **Cochain maps preserve cycles**: linear maps `T` with `T D(d') ⊆ D(d)` and `d T = T d'` map
`𝔷ⁱ(H')` into `𝔷ⁱ(H)`. -/
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

/-- **Cochain maps preserve boundaries**: linear maps `T` with `T D(d') ⊆ D(d)` and `d T = T d'`
map `𝔅ⁱ(H')` into `𝔅ⁱ(H)`. -/
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

/-- **Finite-dimensional cohomology passes to a finite sum of retracts**: if linear maps
`P a : W'ⁱ → Wⁱ` and `R a : Wⁱ → W'ⁱ` (`a` in a finite type) with `Σ_a R a ∘ P a = 1` map the
cycles and boundaries of `H'` into those of `H` and the boundaries of `H` into those of `H'`
(e.g. restrictions of cochain maps, `apply_mem_cycles`, `apply_mem_boundaries`), then `Hⁱ(H')`
is finite-dimensional when `Hⁱ(H)` is: `[z] ↦ ([P a z])_a` is one-to-one. -/
theorem finiteDimensional_cohomology_of_sum_eq_id {α : Type*} [Fintype α] {i : ι}
    (P : α → W' i →ₗ[𝕜] W i) (R : α → W i →ₗ[𝕜] W' i)
    (hPz : ∀ a, ∀ x ∈ H'.cycles i, P a x ∈ H.cycles i)
    (hPb : ∀ a, ∀ x ∈ H'.boundaries i, P a x ∈ H.boundaries i)
    (hRb : ∀ a, ∀ x ∈ H.boundaries i, R a x ∈ H'.boundaries i)
    (hRP : ∀ x, ∑ a, R a (P a x) = x) [FiniteDimensional 𝕜 (H.cohomology i)] :
    FiniteDimensional 𝕜 (H'.cohomology i) := by
  let Φ : H'.cohomology i →ₗ[𝕜] α → H.cohomology i := LinearMap.pi fun a =>
    Submodule.mapQ _ _ ((P a).restrict (hPz a)) fun x hx => hPb a _ hx
  refine Module.Finite.of_injective Φ (injective_iff_map_eq_zero _ |>.2 fun q hq => ?_)
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hz : ∀ a, P a z ∈ H.boundaries i := fun a => by
    have : (Submodule.Quotient.mk ((P a).restrict (hPz a) z) : H.cohomology i) = 0 :=
      congrFun hq a
    rwa [Submodule.Quotient.mk_eq_zero] at this
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, ← hRP z]
  exact Submodule.sum_mem _ fun a _ => hRb a _ (hz a)

end CochainMap

end Feec.HilbertComplex
