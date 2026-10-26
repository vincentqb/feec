module

public import Feec.FiniteElement.Assembly
public import Feec.Mesh.Freudenthal

/-!
# The Whitney complex on simplicial meshes

The Whitney forms `P₁⁻Λᵏ(T)` (`Feec.FiniteElement.whitneySpace`) with the face integrals
`ω ↦ ∫_g ω` as degrees of freedom form an element family `Feec.FiniteElement.whitneyElement n`
(`Feec.FiniteElement.LocalElement`). On any conforming simplicial mesh of an open `Ω ⊆ ℝⁿ` the
assembled global spaces are the **lowest-order Whitney complex**
`P₁⁻Λ⁰ → P₁⁻Λ¹ → ⋯ → P₁⁻Λⁿ` (in `ℝ³`: Lagrange `P₁`, Nédélec, Raviart–Thomas, piecewise constants),
a subcomplex of the `L²` de Rham complex `HΛ(Ω)` (`whitneySubcomplex`) whose `k`-th space has
dimension the number of `k`-faces of the mesh (`finrank_whitney_globalSpace`); with vanishing
boundary DOFs it is a subcomplex of `H̊Λ(Ω)` for strictly star-shaped (e.g. convex) `Ω`
(`whitneySubcomplexMin`), in particular for the Freudenthal meshes of a cube.

The key algebraic facts are that every Whitney form is a trimmed linear form
`x ↦ α + ι_x β` (`whitneySpace_le_p1MinusForms`), that affine pullbacks preserve these
(`affinePullback_mem_p1MinusForms`, from `B^* (ι_{B v} β) = ι_v (B^* β)`,
`Feec.ExteriorFibre.pullback_interior`), and
that on the reference simplex they are exactly the Whitney forms
(`p1MinusForms_le_whitneySpace_refVertex`). The tangential trace of a Whitney form on a facet is
therefore a Whitney form of the facet, determined by the DOFs of the faces of the facet
(`tangentialTraceEq_of_whitneyFaceDof_eq`).

## Main definitions

* `Feec.FiniteElement.p1MinusForms n k`: the trimmed linear `k`-forms `x ↦ α + ι_x β` on `ℝⁿ`.
* `Feec.FiniteElement.whitneyFaceDof g k`: the face integral over the face `g`, enumerated by
  `faceEnum g`.
* `Feec.FiniteElement.whitneyElement n`: the Whitney element family.
* `Feec.FiniteElement.whitneySubcomplex M hΩ`, `whitneySubcomplexMin M hΩ x₀ hstar`: the Whitney
  subcomplexes.

## Main results

* `whitneySpace_le_p1MinusForms`, `affinePullback_mem_p1MinusForms`,
  `p1MinusForms_le_whitneySpace_refVertex`: Whitney forms are trimmed linear forms, stable
  under affine pullback; `whitneySpace_eq_p1MinusForms`: **`P₁⁻Λᵏ(T)` is the space of trimmed
  linear forms** for every simplex (by a dimension count).
* `isUnisolvent_whitneyFaceDof`, `tangentialTraceEq_of_whitneyFaceDof_eq`,
  `whitneyFaceDof_congr`, `whitneyFaceDof_comp_extDerivC1_mem_span`: the axioms of an element
  family.
* `finrank_whitney_globalSpace`: **`dim = #{k-faces}`**.

The Whitney element is the trimmed element `P₁⁻Λ` of `Feec.FiniteElement.PolySeq.trimmed 1`, with
the same subcomplexes on every mesh (`whitneySubcomplex_eq_trimmed` in
`Feec.FiniteElement.PolyComplex`).

## References

* [H. Whitney, *Geometric Integration Theory*][Whitney1957], Ch. IV, §27
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3–5 (Whitney forms, `P₁⁻Λᵏ = P₀Λᵏ + κ H₀Λ^{k+1}`, the global spaces)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7

Bibliography: [references.bib](../../docs/references.bib)
-/

open MeasureTheory Set Finset

@[expose] public noncomputable section

namespace Feec.ExteriorFibre

variable {R : Type*} [CommRing R] {d : Type*} [LinearOrder d] {ι : Type*} [LinearOrder ι]

theorem whitneyFibre_add_coeff (c c' : ι → R) (θ : ι → d → R) (g : Finset ι) :
    whitneyFibre (c + c') θ g = whitneyFibre c θ g + whitneyFibre c' θ g := by
  simp only [whitneyFibre, Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]

end Feec.ExteriorFibre

namespace Feec.FiniteElement

open ExteriorFibre

variable {n m : ℕ}

/-! ### Trimmed linear forms `P₁⁻Λᵏ = P₀Λᵏ + κ H₀Λ^{k+1}` -/

/-- The **trimmed linear `k`-forms** `x ↦ α + ι_x β` on `ℝⁿ` (`α`, `β` constant of degrees `k`,
`k + 1`), as a space of form fields. -/
def p1MinusForms (n k : ℕ) : Submodule ℝ (FormField n) :=
  Submodule.span ℝ ({w | ∃ α, IsDeg k α ∧ w = fun _ => α} ∪
    {w | ∃ β, IsDeg (k + 1) β ∧ w = fun x => interior x β})

theorem const_mem_p1MinusForms {k : ℕ} {α : Finset (Fin n) → ℝ} (hα : IsDeg k α) :
    (fun _ => α) ∈ p1MinusForms n k :=
  Submodule.subset_span (Or.inl ⟨α, hα, rfl⟩)

theorem interior_mem_p1MinusForms {k : ℕ} {β : Finset (Fin n) → ℝ} (hβ : IsDeg (k + 1) β) :
    (fun x => interior x β) ∈ p1MinusForms n k :=
  Submodule.subset_span (Or.inr ⟨β, hβ, rfl⟩)

/-- Every Whitney form is a trimmed linear form:
`φ_f(x) = k! (W_f(λ(0)) + ι_x dλ_f^∧)`. -/
theorem whitneyForm_mem_p1MinusForms (p : Fin (n + 1) → Fin n → ℝ) {k : ℕ} (f : Faces n k) :
    whitneyForm p f.1 ∈ p1MinusForms n k := by
  have hc : ∀ x, baryCoord p x = baryCoord p 0 + fun i => ∑ l, baryGrad p i l * x l := by
    intro x
    funext i
    have := baryCoord_sub p x 0 i
    simp only [Pi.zero_apply, sub_zero] at this
    rw [Pi.add_apply, ← this]
    ring
  have hw : whitneyForm p f.1 = ((#f.1 - 1).factorial : ℝ) •
      ((fun _ => whitneyFibre (baryCoord p 0) (baryGrad p) f.1) +
        fun x => interior x (wedgeProd (baryGrad p) f.1)) := by
    funext x
    rw [whitneyForm, hc x, whitneyFibre_add_coeff, ← interior_wedgeProd]
    rfl
  rw [hw]
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ (const_mem_p1MinusForms ?_)
    (interior_mem_p1MinusForms ?_))
  · exact isDeg_whitneyFibre _ _ f.2
  · have := isDeg_wedgeProd (baryGrad p) f.1
    rwa [f.2] at this

theorem whitneySpace_le_p1MinusForms (p : Fin (n + 1) → Fin n → ℝ) (k : ℕ) :
    whitneySpace p k ≤ p1MinusForms n k :=
  Submodule.span_le.2 (Set.range_subset_iff.2 fun f => whitneyForm_mem_p1MinusForms p f)

/-- On the reference simplex the trimmed linear forms are the Whitney forms. -/
theorem p1MinusForms_le_whitneySpace_refVertex (k : ℕ) :
    p1MinusForms n k ≤ whitneySpace (refVertex n) k := by
  refine Submodule.span_le.2 ?_
  rintro w (⟨α, hα, rfl⟩ | ⟨β, hβ, rfl⟩)
  · exact const_mem_whitneySpace hα
  · exact interior_mem_whitneySpace hβ

/-- **Affine pullbacks preserve trimmed linear forms**. -/
theorem affinePullback_mem_p1MinusForms (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) {k : ℕ}
    {w : FormField n} (hw : w ∈ p1MinusForms n k) :
    affinePullback B b w ∈ p1MinusForms m k := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    rcases hw with ⟨α, hα, rfl⟩ | ⟨β, hβ, rfl⟩
    · exact const_mem_p1MinusForms (hα.pullback B)
    · have e : affinePullback B b (fun x => interior x β) =
          (fun y => interior y (pullback B β)) + fun _ => pullback B (interior b β) := by
        funext y
        rw [affinePullback_apply]
        have ha : affine B b y = (fun i => ∑ l, B i l * y l) + b := by
          funext i; rw [affine_apply]; rfl
        rw [ha, interior_add_left, pullback_add, pullback_interior]
        rfl
      rw [e]
      exact Submodule.add_mem _ (interior_mem_p1MinusForms (hβ.pullback B))
        (const_mem_p1MinusForms ((hβ.interior b).pullback B))
  | zero =>
    have : affinePullback B b (0 : FormField n) = 0 := by
      funext y; simp [affinePullback_apply]
    rw [this]; exact Submodule.zero_mem _
  | add w w' _ _ hw hw' =>
    rw [affinePullback_add]; exact Submodule.add_mem _ hw hw'
  | smul c w _ hw =>
    rw [affinePullback_smul]; exact Submodule.smul_mem _ _ hw

/-- **`P₁⁻Λᵏ(T)` is the space of trimmed linear forms** for every `n`-simplex `T` (dimension
count: `P₁⁻Λᵏ(T) ⊆ P₁⁻Λᵏ ⊆ P₁⁻Λᵏ(T̂)`, and both ends have dimension `(n+1 choose k+1)`). [AFW2006], §3–4 -/
theorem whitneySpace_eq_p1MinusForms (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    whitneySpace T.points k = p1MinusForms n k := by
  have href : IsUnit (edgeMatrix (refVertex n)).det := by
    rw [edgeMatrix_refVertex, Matrix.det_one]; exact isUnit_one
  have hle := p1MinusForms_le_whitneySpace_refVertex (n := n) k
  have : FiniteDimensional ℝ (p1MinusForms n k) := Submodule.finiteDimensional_of_le hle
  refine Submodule.eq_of_le_of_finrank_le (whitneySpace_le_p1MinusForms _ k) ?_
  rw [finrank_whitneySpace_simplex]
  exact (Submodule.finrank_mono hle).trans (finrank_whitneySpace href k).le

end Feec.FiniteElement

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh

variable {n : ℕ}

/-! ### Face integrals with the fixed enumerations -/

/-- Two injective enumerations of the same face give the same integral up to a sign. -/
theorem exists_sign_simplexIntegral_eq {k : ℕ} {q q' : Fin (k + 1) → Fin n → ℝ}
    (hq : Function.Injective q) (hq' : Function.Injective q') (h : Set.range q = Set.range q') :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ w, simplexIntegral q w = ε * simplexIntegral q' w := by
  obtain ⟨π, rfl⟩ := exists_perm_comp_eq hq hq' h
  exact ⟨_, intCast_units_eq_one_or _, fun w => simplexIntegral_comp_perm q' π w⟩

/-- The face integral `w ↦ ∫_g w` over the face `g` enumerated by `faceEnum g`. -/
def whitneyFaceDof (g : Finset (Fin n → ℝ)) (k : ℕ) : contForms n →ₗ[ℝ] ℝ where
  toFun w := simplexIntegral (faceEnum g (k + 1)) w
  map_add' w w' := simplexIntegral_add (Continuous.continuousOn (mem_contForms.1 w.2))
    (Continuous.continuousOn (mem_contForms.1 w'.2))
  map_smul' c w := by
    simp only [RingHom.id_apply, smul_eq_mul, Submodule.coe_smul]
    exact simplexIntegral_smul _ c _

theorem whitneyFaceDof_apply (g : Finset (Fin n → ℝ)) (k : ℕ) (w : contForms n) :
    whitneyFaceDof g k w = simplexIntegral (faceEnum g (k + 1)) w := rfl

/-- The DOF index of the face `g` in degree `k`: one DOF if `g` is a `k`-face. -/
abbrev WhitneyDofIdx (g : Finset (Fin n → ℝ)) (k : ℕ) := {_u : Unit // g.card = k + 1}

theorem card_whitneyDofIdx (g : Finset (Fin n → ℝ)) (k : ℕ) :
    Fintype.card (WhitneyDofIdx g k) = if g.card = k + 1 then 1 else 0 := by
  split_ifs with h
  · exact Fintype.card_eq_one_iff.2 ⟨⟨(), h⟩, fun x => Subtype.ext rfl⟩
  · exact Fintype.card_eq_zero_iff.2 ⟨fun x => h x.2⟩

theorem card_sigma_whitneyDofIdx (s : Finset (Fin n → ℝ)) (k : ℕ) :
    Fintype.card (Σ g : s.powerset, WhitneyDofIdx (g : Finset (Fin n → ℝ)) k) =
      s.card.choose (k + 1) := by
  classical
  rw [Fintype.card_sigma]
  simp only [card_whitneyDofIdx]
  rw [Finset.sum_coe_sort s.powerset (fun g => if g.card = k + 1 then 1 else 0), Finset.sum_boole,
    ← Finset.powersetCard_eq_filter, Finset.card_powersetCard]
  simp

/-- The face integrals over the faces of `T` (with the fixed enumerations) are unisolvent on
`P₁⁻Λᵏ(T)`. -/
theorem isUnisolvent_whitneyFaceDof (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    IsUnisolvent fun p : Σ g : (vertexSet T).powerset, WhitneyDofIdx (g : Finset (Fin n → ℝ)) k =>
      whitneyFaceDof (p.1 : Finset (Fin n → ℝ)) k ∘ₗ
        Submodule.inclusion (whitneySpace_le_contForms T.points k) := by
  classical
  rw [isUnisolvent_iff_forall_eq_zero _ (by
    rw [finrank_whitneySpace_simplex, card_sigma_whitneyDofIdx, card_vertexSet])]
  intro w hw
  refine (isUnisolvent_whitneyDof_simplex T k).ext fun f => ?_
  rw [map_zero]
  set g := f.1.image T.points
  have hgT : g ⊆ vertexSet T := fun x hx => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact points_mem_vertexSet T i
  have hinj : Function.Injective (faceVertices T.points f.1 f.2) :=
    T.independent.injective.comp (f.1.orderEmbOfFin f.2).injective
  have hcard : g.card = k + 1 := by
    rw [Finset.card_image_of_injective _ T.independent.injective, f.2]
  have hrange : Set.range (faceVertices T.points f.1 f.2) = Set.range (faceEnum g (k + 1)) := by
    rw [range_faceEnum hcard, faceVertices, Set.range_comp, Finset.range_orderEmbOfFin,
      Finset.coe_image]
  obtain ⟨ε, -, hε⟩ := exists_sign_simplexIntegral_eq hinj (injective_faceEnum hcard) hrange
  have h0 := hw ⟨⟨g, Finset.mem_powerset.2 hgT⟩, ⟨(), hcard⟩⟩
  change simplexIntegral (faceVertices T.points f.1 f.2) (w : FormField n) = 0
  rw [hε]
  change ε * whitneyFaceDof g k ⟨w, whitneySpace_le_contForms T.points k w.2⟩ = 0
  rw [show whitneyFaceDof g k ⟨w, whitneySpace_le_contForms T.points k w.2⟩ = 0 from h0, mul_zero]

end Feec.FiniteElement

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh

variable {n : ℕ}

/-! ### Traces of Whitney forms on facets -/

/-- Points of the convex hull of a vertex family are values of its parametrization. -/
theorem exists_simplexMap_eq_of_mem_convexHull {k : ℕ} (q : Fin (k + 1) → Fin n → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ convexHull ℝ (Set.range q)) :
    ∃ y ∈ refSimplex k, simplexMap q y = x := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, w, hw0, hw1, rfl⟩ := hx
  set w' : Fin (k + 1) → ℝ := fun i => if i ∈ s then w i else 0
  have hw'0 : ∀ i, 0 ≤ w' i := fun i => by simp only [w']; split_ifs with h <;> simp [hw0, h]
  have hw'1 : ∑ i, w' i = 1 := by
    rw [← hw1, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ s)]
    simp only [w']
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun i => i ∉ s) fun i hi => by
      simp [(Finset.mem_filter.1 hi).2], add_zero]
    rw [Finset.sum_filter, ← Finset.sum_subset (Finset.subset_univ s) fun i _ hi => by simp [hi]]
    exact Finset.sum_congr rfl fun i hi => by simp [hi]
  have hb : refBary (fun l : Fin k => w' l.succ) = w' := by
    funext i
    refine Fin.cases ?_ (fun l => rfl) i
    rw [refBary_zero]
    rw [Fin.sum_univ_succ] at hw'1
    linarith
  refine ⟨fun l => w' l.succ, fun i => by rw [hb]; exact hw'0 i, ?_⟩
  rw [simplexMap_eq_sum, hb, Finset.affineCombination_eq_linear_combination _ _ _ hw1]
  rw [← Finset.sum_subset (Finset.subset_univ s) fun i _ hi => by simp [w', hi]]
  exact Finset.sum_congr rfl fun i hi => by simp [w', hi]

/-- Tangential traces through a parametrization of the facet: if the pullbacks along the edge
matrix `B_q` agree, the tangential traces agree. -/
theorem tangentialTraceEq_of_pullback_eq {m : ℕ} {F : Finset (Fin (m + 1) → ℝ)} {k : ℕ}
    (q : Fin (m + 1) → Fin (m + 1) → ℝ) (hq : Set.range q = F) {α β : Finset (Fin (m + 1)) → ℝ}
    (h : pullback (simplexMatrix q) α = pullback (simplexMatrix q) β) :
    TangentialTraceEq F k α β := by
  intro V hV
  have hV' : ∀ l, ∃ c : Fin m → ℝ, ∀ i, V i l = ∑ j, simplexMatrix q i j * c j := by
    intro l
    have h1 := hV l
    rw [← hq, vectorSpan_range_eq_span_range_vsub_right ℝ q 0,
      Submodule.mem_span_range_iff_exists_fun] at h1
    obtain ⟨c, hc⟩ := h1
    refine ⟨fun j => c j.succ, fun i => ?_⟩
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, vsub_eq_sub, Pi.sub_apply, smul_eq_mul,
      Fin.sum_univ_succ, sub_self, mul_zero, zero_add] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by simp [simplexMatrix, mul_comm]
  choose C hC using hV'
  have hVC : V = fun i l => ∑ j, simplexMatrix q i j * C l j := by
    funext i l; exact hC l i
  rw [hVC, ← pullback_pullback (simplexMatrix q) (fun j l => C l j), h, pullback_pullback]

/-- **Trace determination for Whitney forms**: on a common facet `F` of `T` and `T'`, Whitney
forms with the same integrals over the faces of `F` have the same tangential trace on `F`. -/
theorem tangentialTraceEq_of_whitneyFaceDof_eq {k : ℕ} {T T' : Affine.Simplex ℝ (Fin n → ℝ) n}
    {F : Finset (Fin n → ℝ)} (hT : F ⊆ vertexSet T) (hT' : F ⊆ vertexSet T') (hc : F.card = n)
    {w η : FormField n} (hw : w ∈ whitneySpace T.points k) (hη : η ∈ whitneySpace T'.points k)
    (hdof : ∀ g ⊆ F, ∀ _i : WhitneyDofIdx g k,
      whitneyFaceDof g k ⟨w, whitneySpace_le_contForms T.points k hw⟩ =
        whitneyFaceDof g k ⟨η, whitneySpace_le_contForms T'.points k hη⟩) :
    ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)), TangentialTraceEq F k (w x) (η x) := by
  rcases n with _ | m
  · intro x hx
    have : F = ∅ := Finset.card_eq_zero.1 hc
    simp [this] at hx
  set q := faceEnum F (m + 1)
  have hq : Set.range q = F := range_faceEnum hc
  have hqi : Function.Injective q := injective_faceEnum hc
  set B := simplexMatrix q
  have hwc : ContDiff ℝ 1 w := whitneySpace_le_c1Forms T.points k hw
  have hηc : ContDiff ℝ 1 η := whitneySpace_le_c1Forms T'.points k hη
  have hw' := affinePullback_mem_p1MinusForms B (q 0) (whitneySpace_le_p1MinusForms _ k hw)
  have hη' := affinePullback_mem_p1MinusForms B (q 0) (whitneySpace_le_p1MinusForms _ k hη)
  have hδ : affinePullback B (q 0) w - affinePullback B (q 0) η ∈ whitneySpace (refVertex m) k :=
    p1MinusForms_le_whitneySpace_refVertex k (Submodule.sub_mem _ hw' hη')
  have href : IsUnit (edgeMatrix (refVertex m)).det := by
    rw [edgeMatrix_refVertex, Matrix.det_one]; exact isUnit_one
  have heq : affinePullback B (q 0) w = affinePullback B (q 0) η := by
    have h0 : (⟨_, hδ⟩ : whitneySpace (refVertex m) k) = 0 :=
      (isUnisolvent_whitneyDof href k).ext fun r => by
        rw [map_zero]
        change simplexIntegral (faceVertices (refVertex m) r.1 r.2)
          (affinePullback B (q 0) w - affinePullback B (q 0) η) = 0
        rw [simplexIntegral_sub ((contDiff_affinePullback B (q 0) hwc).continuous.continuousOn)
          ((contDiff_affinePullback B (q 0) hηc).continuous.continuousOn), sub_eq_zero,
          ← simplexIntegral_comp_affine, ← simplexIntegral_comp_affine]
        have hface : (fun i => affine B (q 0) (faceVertices (refVertex m) r.1 r.2 i)) =
            q ∘ r.1.orderEmbOfFin r.2 := by
          funext i
          exact simplexMap_refVertex q _
        rw [hface]
        set g := r.1.image q
        have hcard : g.card = k + 1 := by rw [Finset.card_image_of_injective _ hqi, r.2]
        have hgF : g ⊆ F := fun x hx => by
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
          rw [← Finset.mem_coe, ← hq]; exact ⟨i, rfl⟩
        have hrange : Set.range (q ∘ r.1.orderEmbOfFin r.2) = Set.range (faceEnum g (k + 1)) := by
          rw [range_faceEnum hcard, Set.range_comp, Finset.range_orderEmbOfFin, Finset.coe_image]
        obtain ⟨ε, -, hε⟩ := exists_sign_simplexIntegral_eq
          (hqi.comp (r.1.orderEmbOfFin r.2).injective) (injective_faceEnum hcard) hrange
        rw [hε, hε]
        congr 1
        exact hdof g hgF ⟨(), hcard⟩
    exact sub_eq_zero.1 (congrArg Subtype.val h0)
  intro x hx
  rw [← hq] at hx
  obtain ⟨y, -, rfl⟩ := exists_simplexMap_eq_of_mem_convexHull q hx
  refine tangentialTraceEq_of_pullback_eq q hq ?_
  have := congrFun heq y
  simpa [affinePullback_apply, simplexMap] using this

end Feec.FiniteElement

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh

variable {n : ℕ}

/-- The face integral over `g` only sees the tangential trace on `g`. -/
theorem whitneyFaceDof_congr {g : Finset (Fin n → ℝ)} {k : ℕ} (i : WhitneyDofIdx g k)
    {w η : contForms n}
    (h : ∀ x ∈ convexHull ℝ (g : Set (Fin n → ℝ)),
      TangentialTraceEq g k ((w : FormField n) x) ((η : FormField n) x)) :
    whitneyFaceDof g k w = whitneyFaceDof g k η := by
  set q := faceEnum g (k + 1)
  have hq : Set.range q = g := range_faceEnum i.2
  have hqg : ∀ j, q j ∈ g := fun j => by rw [← Finset.mem_coe, ← hq]; exact ⟨j, rfl⟩
  rw [whitneyFaceDof_apply, whitneyFaceDof_apply, simplexIntegral, simplexIntegral]
  refine setIntegral_congr_fun (measurableSet_refSimplex k) fun y hy => ?_
  simp only [affinePullback_apply]
  refine h _ ?_ _ fun l => ?_
  · rw [← hq]; exact simplexMap_mem_convexHull q hy
  · have : (fun j => simplexMatrix q j l) = q l.succ -ᵥ q 0 := by
      funext j; simp [simplexMatrix]
    rw [this]
    exact vsub_mem_vectorSpan ℝ (Finset.mem_coe.2 (hqg _)) (Finset.mem_coe.2 (hqg 0))

/-- **Stokes compatibility of the face integrals**: `∫_g dw = Σᵢ ± ∫_{g ∖ gᵢ} w`. -/
theorem whitneyFaceDof_comp_extDerivC1_mem_span (g : Finset (Fin n → ℝ)) (k : ℕ) (i : WhitneyDofIdx g (k + 1)) :
    whitneyFaceDof g (k + 1) ∘ₗ extDerivC1 ∈
      Submodule.span ℝ (Set.range fun p : Σ g' : g.powerset,
        WhitneyDofIdx (g' : Finset (Fin n → ℝ)) k =>
          whitneyFaceDof (p.1 : Finset (Fin n → ℝ)) k ∘ₗ
            Submodule.inclusion c1Forms_le_contForms) := by
  classical
  set q := faceEnum g (k + 2)
  have hq : Set.range q = g := range_faceEnum i.2
  have hqi : Function.Injective q := injective_faceEnum i.2
  -- the faces `gⱼ = q(univ ∖ j)`
  set gj : Fin (k + 2) → Finset (Fin n → ℝ) := fun j => Finset.univ.image (q ∘ j.succAbove)
  have hgj : ∀ j, (gj j).card = k + 1 := fun j => by
    rw [Finset.card_image_of_injective _ (hqi.comp Fin.succAbove_right_injective),
      Finset.card_univ, Fintype.card_fin]
  have hgjg : ∀ j, gj j ⊆ g := fun j x hx => by
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hx
    rw [← Finset.mem_coe, ← hq]; exact ⟨_, rfl⟩
  have hsign : ∀ j, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ w, simplexIntegral (q ∘ j.succAbove) w =
      ε * simplexIntegral (faceEnum (gj j) (k + 1)) w := fun j =>
    exists_sign_simplexIntegral_eq (hqi.comp Fin.succAbove_right_injective)
      (injective_faceEnum (hgj j)) (by
        rw [range_faceEnum (hgj j), Finset.coe_image, Finset.coe_univ, Set.image_univ])
  choose ε _ hε using hsign
  have heq : whitneyFaceDof g (k + 1) ∘ₗ extDerivC1 = ∑ j : Fin (k + 2),
      ((-1 : ℝ) ^ (j : ℕ) * ε j) • (whitneyFaceDof (gj j) k ∘ₗ
        Submodule.inclusion c1Forms_le_contForms) := by
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
    change simplexIntegral q (extDeriv (w : FormField n)) = _
    rw [simplexIntegral_extDeriv q isOpen_univ (Set.subset_univ _)
      (ContDiff.contDiffOn (mem_c1Forms.1 w.2))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hε j, whitneyFaceDof_apply]
    ring_nf
    rfl
  rw [heq]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨⟨⟨gj j, Finset.mem_powerset.2 (hgjg j)⟩, ⟨(), hgj j⟩⟩, rfl⟩

/-- **The Whitney element family** `P₁⁻Λᵏ(T)` with the face integrals as DOFs. -/
def whitneyElement (n : ℕ) : LocalElement n where
  space T k := whitneySpace T.points k
  contDiff_of_mem h := whitneySpace_le_c1Forms _ _ h
  isDeg_of_mem h x := isDeg_of_mem_whitneySpace h x
  extDeriv_mem h := extDeriv_mem_whitneySpace h
  finiteDimensional _ _ := inferInstance
  DofIdx := WhitneyDofIdx
  dofIdxFintype _ _ := inferInstance
  dof g k _ := whitneyFaceDof g k
  unisolvent T k := isUnisolvent_whitneyFaceDof T k
  trace := fun hT hT' hc hw hη h => tangentialTraceEq_of_whitneyFaceDof_eq hT hT' hc hw hη h
  dof_congr := whitneyFaceDof_congr
  dof_extDeriv := fun g k i => whitneyFaceDof_comp_extDerivC1_mem_span g k i

end Feec.FiniteElement

namespace Feec.FiniteElement

open Feec.Domain Feec.Mesh

variable {n : ℕ}

/-! ### The global Whitney spaces and the Whitney complex -/

theorem coe_filter_meshFaces (M : SimplicialMesh n) (k : ℕ) :
    (((LocalElement.meshFaces M).filter fun g => g.card = k + 1 : Finset _) :
      Set (Finset (Fin n → ℝ))) = M.faces k := by
  ext g
  simp only [Finset.coe_filter, LocalElement.mem_meshFaces, Set.mem_ofPred_eq, SimplicialMesh.faces]
  tauto

theorem card_globalDofIdx_whitneyElement (M : SimplicialMesh n) (k : ℕ) :
    Fintype.card ((whitneyElement n).GlobalDofIdx M k) = (M.faces k).ncard := by
  classical
  rw [← coe_filter_meshFaces, Set.ncard_coe_finset, Fintype.card_sigma]
  change ∑ g : LocalElement.meshFaces M,
    Fintype.card (WhitneyDofIdx (g : Finset (Fin n → ℝ)) k) = _
  simp only [card_whitneyDofIdx]
  rw [Finset.sum_coe_sort (LocalElement.meshFaces M) (fun g => if g.card = k + 1 then 1 else 0),
    Finset.sum_boole]
  simp

/-- **`dim Λ_hᵏ(M) = #{k-faces of M}`** for the Whitney complex. -/
theorem finrank_whitney_globalSpace (M : SimplicialMesh n) (k : ℕ) :
    Module.finrank ℝ ((whitneyElement n).globalSpace M k) = (M.faces k).ncard := by
  rw [LocalElement.finrank_globalSpace, card_globalDofIdx_whitneyElement]

instance (k : ℕ) : IsEmpty (WhitneyDofIdx (∅ : Finset (Fin n → ℝ)) k) :=
  ⟨fun i => by have := i.2; simp at this⟩

/-- **The lowest-order Whitney complex** `P₁⁻Λ⁰(M) → P₁⁻Λ¹(M) → ⋯ → P₁⁻Λⁿ(M)` on a conforming mesh
of an open `Ω ⊆ ℝⁿ`, as a subcomplex of the maximal `L²` de Rham complex `HΛ(Ω)` (in `ℝ³`:
Lagrange `P₁`, Nédélec edge elements, Raviart–Thomas face elements, piecewise constants). -/
def whitneySubcomplex [NeZero n] (M : SimplicialMesh n) (hΩ : IsOpen M.domain) :
    ((deRham ℝ n).maximalComplex hΩ).Subcomplex :=
  (whitneyElement n).subcomplex M hΩ

instance [NeZero n] (M : SimplicialMesh n) (hΩ : IsOpen M.domain) (k : ℤ) :
    FiniteDimensional ℝ ((whitneySubcomplex M hΩ).V k) :=
  inferInstanceAs (FiniteDimensional ℝ ((whitneyElement n).V M k))

/-- **The Whitney complex with vanishing boundary DOFs** as a subcomplex of the minimal `L²` de
Rham complex `H̊Λ(Ω)`, for `Ω` strictly star-shaped with respect to `x₀`. -/
def whitneySubcomplexMin [NeZero n] (M : SimplicialMesh n) (hΩ : IsOpen M.domain)
    (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain) :
    ((deRham ℝ n).minimalComplex hΩ).Subcomplex :=
  (whitneyElement n).subcomplexMin M hΩ x₀ hstar

instance [NeZero n] (M : SimplicialMesh n) (hΩ : IsOpen M.domain) (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain)
    (k : ℤ) : FiniteDimensional ℝ ((whitneySubcomplexMin M hΩ x₀ hstar).V k) :=
  inferInstanceAs (FiniteDimensional ℝ ((whitneyElement n).V₀ M k))

/-- A convex open set is strictly star-shaped with respect to each of its points. -/
theorem add_smul_sub_mem_of_convex {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) {x₀ : Fin n → ℝ}
    (hx₀ : x₀ ∈ Ω) : ∀ x ∈ closure Ω, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ Ω := by
  intro x hx t ht0 ht1
  have h := hconv.combo_interior_closure_mem_interior (hΩ.interior_eq.symm ▸ hx₀) hx
    (a := 1 - t) (b := t) (by linarith) ht0 (by ring)
  rw [hΩ.interior_eq] at h
  convert h using 1
  rw [smul_sub, sub_smul, one_smul]; abel

/-! ### Freudenthal meshes of cubes -/

theorem isOpen_freudenthalMesh_domain (b : Fin n → ℝ) (s : ℝ) (hs : 0 < s) (N : ℕ) [NeZero N] :
    IsOpen (freudenthalMesh b s hs N).domain := by
  rw [freudenthalMesh_domain]
  exact isOpen_set_pi Set.finite_univ fun i _ => isOpen_Ioo

theorem convex_freudenthalMesh_domain (b : Fin n → ℝ) (s : ℝ) (hs : 0 < s) (N : ℕ) [NeZero N] :
    Convex ℝ (freudenthalMesh b s hs N).domain := by
  rw [freudenthalMesh_domain]
  exact convex_pi fun i _ => convex_Ioo _ _

theorem center_mem_freudenthalMesh_domain (b : Fin n → ℝ) (s : ℝ) (hs : 0 < s) (N : ℕ)
    [NeZero N] : b + (s / 2) • (fun _ => (1 : ℝ)) ∈ (freudenthalMesh b s hs N).domain := by
  rw [freudenthalMesh_domain]
  intro i _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, Set.mem_Ioo]
  constructor <;> linarith

end Feec.FiniteElement
