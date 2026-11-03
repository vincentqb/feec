module

public import Feec.FiniteElement.WhitneyComplex
public import Feec.FiniteElement.LocalDof
public import Feec.FiniteElement.PolyKind

/-!
# The global element families `P_rΛᵏ` and `P_r⁻Λᵏ` of any order

An **admissible sequence** (`Feec.FiniteElement.PolySeq`) chooses in every form degree `k` a
family `P_{r_k}Λᵏ` or `P_{r_k}⁻Λᵏ` (`r_k ≥ 1`), consecutive degrees related by the transitions
`Xᵏ → P_{r_k}⁻Λᵏ⁺¹` or `Xᵏ → P_{r_k-1}Λᵏ⁺¹` of [AFW2006], §5 and [AFW2010], §5.2
(`PolyKind.Transition`). Each admissible sequence is an element family
`Feec.FiniteElement.polyElement n S : LocalElement n`, so that `Feec.FiniteElement.Assembly`
provides the global spaces, their dimensions, the subcomplexes of `HΛ(Ω)` and `H̊Λ(Ω)`, and the
global canonical interpolant commuting with `d`.

**Degrees of freedom depending only on the face.** For a face (vertex set) `g` of `m + 1`
points, `lexEnum g m` lists the points of `g` in increasing lexicographic order (`toLex`), and
the degrees of freedom are the moments `ℓ_{g,i}(ω) = ∫_{T̂_m} F_q^* ω ∧ ηᵢ` along the
parametrization `F_q` of `q = lexEnum g m`, with `ηᵢ` a fixed basis of the test space
`P⁻_{r+k-m}Λ^{m-k}` (for `P_rΛᵏ`) or `P_{r+k-m-1}Λ^{m-k}` (for `P_r⁻Λᵏ`)
(`testSpace`, `testSpaceMinus` of `Feec.FiniteElement.LocalDof`), applied to the degree-`k` part of
`ω` (`degField`). They vanish for `#g < k + 1` (`PolySeq.isEmpty_dofIdx_of_card_lt`).

**Reduction to the local theory.** The lexicographic enumeration `p'` of the vertices of an
`n`-simplex `T` is an affinely independent enumeration of `T` (`isUnit_det_edgeMatrix_lexEnum`)
whose faces `p' ∘ e` (`e` increasing) are exactly the enumerations `lexEnum` of their vertex sets
(`lexEnum_image_comp`). Hence on `T` the degrees of freedom are those of
`Feec.FiniteElement.localDof p'` (resp. `localDofMinus p'`), with the same test bases, and
unisolvence and trace determination follow from `isUnisolvent_localDof`
(`eq_zero_of_faceMoment_eq_zero_simplex`) and `faceTrace_eq_of_localDof_eq`; the local spaces
are the same for all simplices by affine invariance (`localPolySpace_eq`).

## Main definitions

* `PolyKind.space`, `PolyKind.test`: the form fields over `ℝ` of the families
  `Feec.FiniteElement.PolyKind` (defined in `Feec.FiniteElement.PolyKind`), the evaluations of the polynomial
  forms `PolyKind.form ℝ`, `PolyKind.testForm ℝ` (`PolyKind.space_eq_map_form`,
  `PolyKind.test_eq_map_testForm`).
* `Feec.FiniteElement.lexEnum g m`: the points of `g` in lexicographic order.
* `Feec.FiniteElement.vertexMoment q η ω = ∫_{T̂_m} F_q^* ω ∧ η`, `degField k ω`, `degMoment`.
* `Feec.FiniteElement.PolySeq`: admissible sequences; `PolySeq.DofIdx`, `PolySeq.dof`.
* `Feec.FiniteElement.polyElement n S`: the element family.

## Main results

* `PolyKind.extDeriv_mem_space`: `d` maps the source space into the target space of an
  admissible transition;
* `PolyKind.test_of_transition`: **for each of the four transitions**, the traces on the facets
  and the exterior derivative of a target test form are source test forms;
* `vertexMoment_extDeriv`: Stokes' formula for moments along any vertex family;
* `PolySeq.isUnisolvent_dof`, `PolySeq.tangentialTraceEq_of_dof_eq`, `PolySeq.dof_congr`,
  `PolySeq.dof_comp_extDerivC1_mem_span`: the axioms of an element family;
* `PolyKind.finrank_space_eq_sum`: `dim = Σ_m C(n+1, m+1) dim(test forms on m-faces)`, the
  count `PolyKind.finrank_form_eq_sum` over `ℝ`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3–5 (the spaces, degrees of freedom, admissible sequences, assembly)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.2 (degrees of freedom, the complexes `P_r⁻Λ`, `P_rΛ` and their mixtures)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7

Bibliography: [references.bib](../../docs/references.bib)
-/

open MeasureTheory Set Finset

@[expose] public noncomputable section

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh

variable {n : ℕ}

/-! ### The form fields of the two polynomial families -/

namespace PolyKind

/-- The space of polynomial `k`-form fields of degree `r` of the family: `P_rΛᵏ(ℝⁿ)` or
`P_r⁻Λᵏ(ℝⁿ)`. -/
def space (n : ℕ) : PolyKind → ℕ → ℕ → Submodule ℝ (FormField n)
  | full, r, k => polySpace n r k
  | trimmed, r, k => polyMinusSpace n r k

/-- The test forms of the degrees of freedom of the family on `m`-faces: `P⁻_{r+k-m}Λ^{m-k}` for
`P_rΛᵏ` and `P_{r+k-m-1}Λ^{m-k}` for `P_r⁻Λᵏ` (`testSpace`, `testSpaceMinus`). -/
def test : PolyKind → ℕ → ℕ → (m : ℕ) → Submodule ℝ (FormField m)
  | full, r, k, m => testSpace r k m
  | trimmed, r, k, m => testSpaceMinus r k m

@[simp] theorem space_full (r k : ℕ) : full.space n r k = polySpace n r k := rfl
@[simp] theorem space_trimmed (r k : ℕ) : trimmed.space n r k = polyMinusSpace n r k := rfl
@[simp] theorem test_full (r k m : ℕ) : full.test r k m = testSpace r k m := rfl
@[simp] theorem test_trimmed (r k m : ℕ) : trimmed.test r k m = testSpaceMinus r k m := rfl

instance (κ : PolyKind) (r k : ℕ) : FiniteDimensional ℝ (κ.space n r k) := by
  cases κ
  · exact inferInstanceAs (FiniteDimensional ℝ (polySpace n r k))
  · exact inferInstanceAs (FiniteDimensional ℝ (polyMinusSpace n r k))

instance (κ : PolyKind) (r k m : ℕ) : FiniteDimensional ℝ (κ.test r k m) := by
  cases κ
  · exact inferInstanceAs (FiniteDimensional ℝ (testSpace r k m))
  · exact inferInstanceAs (FiniteDimensional ℝ (testSpaceMinus r k m))

theorem contDiff_of_mem_space {κ : PolyKind} {r k : ℕ} {ω : FormField n}
    (h : ω ∈ κ.space n r k) : ContDiff ℝ ⊤ ω := by
  cases κ
  · exact polySpace_le_c1 h
  · exact contDiff_of_mem_polyMinusSpace h

theorem isDeg_of_mem_space {κ : PolyKind} {r k : ℕ} {ω : FormField n}
    (h : ω ∈ κ.space n r k) (x : Fin n → ℝ) : IsDeg k (ω x) := by
  cases κ
  · exact (polySpace_le_c1DegForms r k h).2 x
  · exact (polyMinusSpace_le_c1DegForms r k h).2 x

theorem contDiff_of_mem_test {κ : PolyKind} {r k m : ℕ} {η : FormField m}
    (h : η ∈ κ.test r k m) : ContDiff ℝ ⊤ η := by
  cases κ
  · exact contDiff_of_mem_testSpace h
  · exact contDiff_of_mem_testSpaceMinus h

theorem space_eq_bot_of_lt {κ : PolyKind} {r k : ℕ} (h : n < k) : κ.space n r k = ⊥ := by
  cases κ
  · exact polySpace_eq_bot_of_lt h
  · exact polyMinusSpace_eq_bot_of_lt h

theorem test_eq_bot {κ : PolyKind} {r k m : ℕ} (h : ¬(k ≤ m ∧ m < r + k)) : κ.test r k m = ⊥ := by
  cases κ
  · exact testSpace_eq_bot h
  · exact testSpaceMinus_eq_bot h

/-- The form fields are the evaluations of the polynomial forms over `ℝ`. -/
theorem space_eq_map_form (κ : PolyKind) (r k : ℕ) :
    κ.space n r k = (κ.form ℝ r k).map (evalForm n) := by
  cases κ <;> rfl

theorem test_eq_map_testForm (κ : PolyKind) (r k m : ℕ) :
    κ.test r k m = (κ.testForm ℝ r k m).map (evalForm m) := by
  by_cases h : k ≤ m ∧ m < r + k
  · cases κ
    · rw [test_full, testSpace_eq h, testForm_full h]; rfl
    · rw [test_trimmed, testSpaceMinus_eq h, testForm_trimmed h]; rfl
  · rw [κ.testForm_eq_bot h, Submodule.map_bot]
    exact test_eq_bot h

/-- The form fields have the dimension of the polynomial forms (`evalForm` is injective). -/
theorem finrank_map_evalForm (W : Submodule ℝ (Koszul.PolyForm ℝ (Fin n))) :
    Module.finrank ℝ (W.map (evalForm n)) = Module.finrank ℝ W :=
  Koszul.finrank_map_of_injOn _ _ fun _ _ hx => evalForm_injective (by rw [hx, map_zero])

theorem finrank_space_eq_finrank_form (κ : PolyKind) (r k : ℕ) :
    Module.finrank ℝ (κ.space n r k) = Module.finrank ℝ (κ.form ℝ (n := n) r k) := by
  rw [κ.space_eq_map_form, finrank_map_evalForm]

theorem finrank_test (κ : PolyKind) {r : ℕ} (hr : 1 ≤ r) (k m : ℕ) :
    Module.finrank ℝ (κ.test r k m) = κ.testDim r k m := by
  rw [κ.test_eq_map_testForm, finrank_map_evalForm, κ.finrank_testForm hr]

/-- `dim P_rΛᵏ(ℝⁿ)` (resp. `P_r⁻Λᵏ`) is the number of degrees of freedom:
`Σ_{m ≤ n} C(n+1, m+1) dim(test forms on m-faces)` ([AFW2006], Thms 4.9, 4.13; over every field
of characteristic `0`, `PolyKind.finrank_form_eq_sum`). -/
theorem finrank_space_eq_sum (κ : PolyKind) {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    Module.finrank ℝ (κ.space n r k) =
      ∑ m ∈ range (n + 1), (n + 1).choose (m + 1) * Module.finrank ℝ (κ.test r k m) := by
  simp only [κ.finrank_space_eq_finrank_form, κ.finrank_form_eq_sum hr, κ.finrank_testForm hr,
    κ.finrank_test hr]

/-- **Vanishing moments force `ω = 0`** on `P_rΛᵏ(T)` (resp. `P_r⁻Λᵏ(T)`)
(`eq_zero_of_faceMoment_eq_zero_simplex`, `eq_zero_of_faceMoment_eq_zero_minus_simplex`). -/
theorem eq_zero_of_faceMoment {p : Fin (n + 1) → Fin n → ℝ} (κ : PolyKind)
    (hp : IsUnit (edgeMatrix p).det) {r : ℕ} (hr : 1 ≤ r) {k : ℕ} {ω : FormField n}
    (hω : ω ∈ κ.space n r k)
    (hdof : ∀ (m : ℕ) (e : Fin (m + 1) ↪o Fin (n + 1)), ∀ η ∈ κ.test r k m,
      faceMoment p e η ω = 0) : ω = 0 := by
  cases κ
  · exact eq_zero_of_faceMoment_eq_zero_simplex hp hr k hω hdof
  · exact eq_zero_of_faceMoment_eq_zero_minus_simplex hp hr k hω hdof

/-- **Trace determination** (`faceTrace_eq_of_localDof_eq`, `faceTrace_eq_of_localDofMinus_eq`):
the moments on a face `f` of `p` and on its subfaces determine the trace on `f`. -/
theorem faceTrace_eq {p : Fin (n + 1) → Fin n → ℝ} (κ : PolyKind)
    (hp : IsUnit (edgeMatrix p).det) {r : ℕ} (hr : 1 ≤ r) {k : ℕ} (f : Face n)
    {ω ω' : FormField n} (hω : ω ∈ κ.space n r k) (hω' : ω' ∈ κ.space n r k)
    (h : ∀ g : Face n, g.2.1 ⊆ f.2.1 → ∀ η ∈ κ.test r k g.dim,
      faceMoment p g.emb η ω = faceMoment p g.emb η ω') :
    faceTrace p f.emb ω = faceTrace p f.emb ω' := by
  cases κ
  · exact faceTrace_eq_of_localDof_eq hp hr f (ω := ⟨ω, (localPolySpace_eq hp r k).symm ▸ hω⟩)
      (ω' := ⟨ω', (localPolySpace_eq hp r k).symm ▸ hω'⟩)
      fun g hg i => h g hg _ (testBasis r k g.dim i).2
  · exact faceTrace_eq_of_localDofMinus_eq hp hr f
      (ω := ⟨ω, (localPolyMinusSpace_eq hp r k).symm ▸ hω⟩)
      (ω' := ⟨ω', (localPolyMinusSpace_eq hp r k).symm ▸ hω'⟩)
      fun g hg i => h g hg _ (testBasisMinus r k g.dim i).2

/-! ### Admissible transitions -/

/-- **`d` maps the source space into the target space** along an admissible transition:
`d P_rΛᵏ ⊆ P_{r-1}Λᵏ⁺¹ ⊆ P_r⁻Λᵏ⁺¹` and `d P_r⁻Λᵏ ⊆ P_{r-1}Λᵏ⁺¹ ⊆ P_r⁻Λᵏ⁺¹` (`r ≥ 1`). -/
theorem extDeriv_mem_space (κ : PolyKind) {r : ℕ} (hr : 1 ≤ r) {κ' : PolyKind} {r' : ℕ}
    (ht : Transition r κ' r') {k : ℕ} {ω : FormField n} (hω : ω ∈ κ.space n r k) :
    extDeriv ω ∈ κ'.space n r' (k + 1) := by
  have hfull : extDeriv ω ∈ polySpace n (r - 1) (k + 1) := by
    cases κ
    · exact extDeriv_mem_polySpace hω
    · exact extDeriv_mem_polySpace (polyMinusSpace_le_polySpace hr hω)
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact polySpace_le_polyMinusSpace r' (k + 1) hfull
  · simpa using hfull

/-- **Test forms along an admissible transition**: if `η` is a test form of the target family in
degree `k + 1` on an `(M+1)`-face, its traces on the facets and `dη` are test forms of the source
family in degree `k` (this is what makes the moments of `dω` combinations of the moments of `ω`,
by Stokes' theorem). -/
theorem test_of_transition (κ : PolyKind) {r : ℕ} {κ' : PolyKind} {r' : ℕ}
    (ht : Transition r κ' r') {k M : ℕ} {η : FormField (M + 1)}
    (hη : η ∈ κ'.test r' (k + 1) (M + 1)) :
    (∀ i : Fin (M + 2), faceTrace (refVertex (M + 1)) i.succAbove η ∈ κ.test r k M) ∧
      extDeriv η ∈ κ.test r k (M + 1) := by
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases κ
    · -- `P_rΛᵏ → P_r⁻Λᵏ⁺¹`
      change η ∈ testSpaceMinus r' (k + 1) (M + 1) at hη
      by_cases hc : k + 1 ≤ M + 1 ∧ M + 1 < r' + (k + 1)
      · rw [testSpaceMinus_eq hc] at hη
        refine ⟨fun i => ?_, ?_⟩
        · change _ ∈ testSpace r' k M
          rw [testSpace_eq (by omega)]
          have := affinePullback_mem_polySpace (simplexMatrix (refVertex (M + 1) ∘ i.succAbove))
            (refVertex (M + 1) (i.succAbove 0)) hη
          have h2 := polySpace_le_polyMinusSpace (n := M) (r' + k - M) (M - k)
          rw [show r' + k - M - 1 = r' + (k + 1) - (M + 1) - 1 by omega,
            show M - k = M + 1 - (k + 1) by omega] at h2
          rw [show M - k = M + 1 - (k + 1) by omega]
          exact h2 this
        · change _ ∈ testSpace r' k (M + 1)
          by_cases hc' : M + 1 < r' + k
          · rw [testSpace_eq (by omega)]
            have := extDeriv_mem_polySpace hη
            have h2 := polySpace_le_polyMinusSpace (n := M + 1) (r' + k - (M + 1)) (M + 1 - k)
            rw [show r' + k - (M + 1) - 1 = r' + (k + 1) - (M + 1) - 1 - 1 by omega,
              show M + 1 - k = M + 1 - (k + 1) + 1 by omega] at h2
            rw [show M + 1 - k = M + 1 - (k + 1) + 1 by omega]
            exact h2 this
          · obtain ⟨H, hH, rfl⟩ := hη
            rw [show r' + (k + 1) - (M + 1) - 1 = 0 by omega] at hH
            rw [extDeriv_evalForm, extDeriv_eq_zero_of_mem_polyForm_zero hH, map_zero]
            exact Submodule.zero_mem _
      · rw [testSpaceMinus_eq_bot hc, Submodule.mem_bot] at hη
        subst hη
        exact ⟨fun i => by rw [map_zero]; exact Submodule.zero_mem _,
          by rw [extDeriv_zero_field]; exact Submodule.zero_mem _⟩
    · -- `P_r⁻Λᵏ → P_r⁻Λᵏ⁺¹`
      exact ⟨fun i => faceTrace_mem_testSpaceMinus hη i, extDeriv_mem_testSpaceMinus hη⟩
  · cases κ
    · -- `P_{r+1}Λᵏ → P_rΛᵏ⁺¹`
      exact ⟨fun i => faceTrace_mem_testSpace hη i, extDeriv_mem_testSpace hη⟩
    · -- `P_{r+1}⁻Λᵏ → P_rΛᵏ⁺¹`
      change η ∈ testSpace r' (k + 1) (M + 1) at hη
      by_cases hc : k + 1 ≤ M + 1 ∧ M + 1 < r' + (k + 1)
      · rw [testSpace_eq hc] at hη
        have hs : 1 ≤ r' + (k + 1) - (M + 1) := by omega
        have hη' := polyMinusSpace_le_polySpace hs hη
        refine ⟨fun i => ?_, ?_⟩
        · change _ ∈ testSpaceMinus (r' + 1) k M
          rw [testSpaceMinus_eq (by omega)]
          have := affinePullback_mem_polySpace (simplexMatrix (refVertex (M + 1) ∘ i.succAbove))
            (refVertex (M + 1) (i.succAbove 0)) hη'
          rwa [show r' + 1 + k - M - 1 = r' + (k + 1) - (M + 1) by omega,
            show M - k = M + 1 - (k + 1) by omega]
        · change _ ∈ testSpaceMinus (r' + 1) k (M + 1)
          rw [testSpaceMinus_eq (by omega)]
          have := extDeriv_mem_polySpace hη'
          rwa [show r' + 1 + k - (M + 1) - 1 = r' + (k + 1) - (M + 1) - 1 by omega,
            show M + 1 - k = M + 1 - (k + 1) + 1 by omega]
      · rw [testSpace_eq_bot hc, Submodule.mem_bot] at hη
        subst hη
        exact ⟨fun i => by rw [map_zero]; exact Submodule.zero_mem _,
          by rw [extDeriv_zero_field]; exact Submodule.zero_mem _⟩

end PolyKind

/-! ### Lexicographically sorted vertex sets -/

/-- The points of `g` in increasing lexicographic order (`toLex`), as a family
`Fin (m + 1) → ℝⁿ` when `#g = m + 1` (and `0` otherwise). This enumeration depends only on the
set `g`, and the enumeration of a subset is the restriction (`lexEnum_eq`). -/
def lexEnum (g : Finset (Fin n → ℝ)) (m : ℕ) : Fin (m + 1) → Fin n → ℝ :=
  if h : #g = m + 1 then fun i =>
    ofLex ((g.map toLex.toEmbedding).orderEmbOfFin (by rw [card_map, h]) i)
  else 0

theorem lexEnum_of_card {g : Finset (Fin n → ℝ)} {m : ℕ} (h : #g = m + 1) (i : Fin (m + 1)) :
    lexEnum g m i = ofLex ((g.map toLex.toEmbedding).orderEmbOfFin (by rw [card_map, h]) i) := by
  simp only [lexEnum, h, ↓reduceDIte]

theorem lexEnum_mem {g : Finset (Fin n → ℝ)} {m : ℕ} (h : #g = m + 1) (i : Fin (m + 1)) :
    lexEnum g m i ∈ g := by
  rw [lexEnum_of_card h]
  obtain ⟨x, hx, hx'⟩ := mem_map.1 (orderEmbOfFin_mem (g.map toLex.toEmbedding)
    (by rw [card_map, h]) i)
  rw [← hx']
  exact hx

theorem strictMono_lexEnum {g : Finset (Fin n → ℝ)} {m : ℕ} (h : #g = m + 1) :
    StrictMono fun i => toLex (lexEnum g m i) := by
  intro i j hij
  simp only [lexEnum_of_card h, toLex_ofLex]
  exact ((g.map toLex.toEmbedding).orderEmbOfFin _).strictMono hij

theorem lexEnum_injective {g : Finset (Fin n → ℝ)} {m : ℕ} (h : #g = m + 1) :
    Function.Injective (lexEnum g m) := fun _ _ hij =>
  (strictMono_lexEnum h).injective (congrArg toLex hij)

/-- **Uniqueness of the sorted enumeration**: a lexicographically increasing enumeration of `g`
is `lexEnum g m`. -/
theorem lexEnum_eq {g : Finset (Fin n → ℝ)} {m : ℕ} (h : #g = m + 1)
    {q : Fin (m + 1) → Fin n → ℝ} (hq : ∀ i, q i ∈ g) (hmono : StrictMono fun i => toLex (q i)) :
    lexEnum g m = q := by
  funext i
  rw [lexEnum_of_card h]
  have := orderEmbOfFin_unique (s := g.map toLex.toEmbedding) (by rw [card_map, h])
    (f := fun i => toLex (q i)) (fun x => mem_map_of_mem _ (hq x)) hmono
  rw [← this]
  rfl

theorem image_lexEnum {g : Finset (Fin n → ℝ)} {m : ℕ} (h : #g = m + 1) :
    Finset.univ.image (lexEnum g m) = g := by
  refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
  · obtain ⟨i, -, rfl⟩ := mem_image.1 hx
    exact lexEnum_mem h i
  · rw [Finset.card_image_of_injective _ (lexEnum_injective h), card_univ, Fintype.card_fin, h]

theorem range_lexEnum {g : Finset (Fin n → ℝ)} {m : ℕ} (h : #g = m + 1) :
    Set.range (lexEnum g m) = g := by
  conv_rhs => rw [← image_lexEnum h]
  rw [coe_image, coe_univ, Set.image_univ]

/-- A subfamily of a sorted family is the sorted enumeration of its range. -/
theorem lexEnum_image_comp {N m : ℕ} {p : Fin (N + 1) → Fin n → ℝ}
    (hp : StrictMono fun i => toLex (p i)) {e : Fin (m + 1) → Fin (N + 1)} (he : StrictMono e) :
    #(Finset.univ.image (p ∘ e)) = m + 1 ∧ lexEnum (Finset.univ.image (p ∘ e)) m = p ∘ e := by
  have hc : #(Finset.univ.image (p ∘ e)) = m + 1 := by
    rw [Finset.card_image_of_injective _ ((hp.injective.of_comp).comp he.injective), card_univ,
      Fintype.card_fin]
  exact ⟨hc, lexEnum_eq hc (fun i => mem_image_of_mem _ (mem_univ i)) (hp.comp he)⟩

/-- A subset of the range of a sorted family is enumerated by a subfamily. -/
theorem exists_orderEmb_comp_eq_lexEnum {N m : ℕ} {p : Fin (N + 1) → Fin n → ℝ}
    (hp : StrictMono fun i => toLex (p i)) {g : Finset (Fin n → ℝ)} (hg : #g = m + 1)
    (hgp : ∀ x ∈ g, ∃ i, p i = x) : ∃ e : Fin (m + 1) ↪o Fin (N + 1), p ∘ e = lexEnum g m := by
  choose f hf using fun i => hgp _ (lexEnum_mem hg i)
  have hmono : StrictMono f := fun i j hij => by
    have := strictMono_lexEnum hg hij
    simp only [← hf] at this
    exact hp.lt_iff_lt.1 this
  exact ⟨OrderEmbedding.ofStrictMono f hmono, funext fun i => hf i⟩

/-- The vertices of an `n`-simplex in lexicographic order are an affinely independent
enumeration: their edge matrix is invertible. -/
theorem isUnit_det_edgeMatrix_lexEnum (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    IsUnit (edgeMatrix (lexEnum (vertexSet T) n)).det := by
  have hc := card_vertexSet T
  have hr : Set.range (lexEnum (vertexSet T) n) = Set.range T.points := by
    rw [range_lexEnum hc, coe_vertexSet]
  obtain ⟨π, hπ⟩ := exists_perm_comp_eq (lexEnum_injective hc) T.independent.injective hr
  rw [hπ, det_edgeMatrix_comp_perm]
  refine IsUnit.mul ?_ (isUnit_det_edgeMatrix T)
  rcases intCast_units_eq_one_or (Equiv.Perm.sign π) with h | h <;> rw [h] <;> simp

theorem exists_lexEnum_eq_of_mem_vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    {x : Fin n → ℝ} (hx : x ∈ vertexSet T) : ∃ i, lexEnum (vertexSet T) n i = x := by
  rw [← image_lexEnum (card_vertexSet T)] at hx
  obtain ⟨i, -, hi⟩ := mem_image.1 hx
  exact ⟨i, hi⟩

/-! ### Moments along vertex families -/

/-- The moment `∫_{T̂_m} F_q^* ω ∧ η` along the parametrization `F_q` of the ordered (possibly
degenerate) simplex `q`; for `q = p ∘ e` it is `faceMoment p e η ω`. -/
def vertexMoment {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ) (η : FormField m) (ω : FormField n) :
    ℝ :=
  simplexIntegral (refVertex m) (wedgeField (affinePullback (simplexMatrix q) (q 0) ω) η)

theorem faceMoment_eq_vertexMoment (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) (η : FormField m) (ω : FormField n) :
    faceMoment p e η ω = vertexMoment (p ∘ e) η ω := rfl

theorem vertexMoment_eq_integral {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ) (η : FormField m)
    (ω : FormField n) : vertexMoment q η ω =
      ∫ x in refSimplex m, wedgeField (affinePullback (simplexMatrix q) (q 0) ω) η x univ :=
  simplexIntegral_refVertex _

theorem vertexMoment_add_left {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ) {η : FormField m}
    (hη : Continuous η) {ω ω' : FormField n} (hω : Continuous ω) (hω' : Continuous ω') :
    vertexMoment q η (ω + ω') = vertexMoment q η ω + vertexMoment q η ω' := by
  simp only [vertexMoment_eq_integral]
  rw [← integral_add (integrableOn_wedgeField (continuous_affinePullback _ _ hω) hη)
    (integrableOn_wedgeField (continuous_affinePullback _ _ hω') hη)]
  congr 1
  funext x
  simp [wedgeField, wedgeForm_add_left, affinePullback_add]

theorem vertexMoment_smul_left {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ) (η : FormField m) (c : ℝ)
    (ω : FormField n) : vertexMoment q η (c • ω) = c • vertexMoment q η ω := by
  simp only [vertexMoment_eq_integral, smul_eq_mul, ← integral_const_mul]
  congr 1
  funext x
  simp [wedgeField, wedgeForm_smul_left, affinePullback_smul]

theorem vertexMoment_add_right {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ) {η η' : FormField m}
    (hη : Continuous η) (hη' : Continuous η') {ω : FormField n} (hω : Continuous ω) :
    vertexMoment q (η + η') ω = vertexMoment q η ω + vertexMoment q η' ω := by
  simp only [vertexMoment_eq_integral]
  rw [← integral_add (integrableOn_wedgeField (continuous_affinePullback _ _ hω) hη)
    (integrableOn_wedgeField (continuous_affinePullback _ _ hω) hη')]
  congr 1
  funext x
  simp [wedgeField, wedgeForm_add_right]

theorem vertexMoment_smul_right {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ) (η : FormField m) (c : ℝ)
    (ω : FormField n) : vertexMoment q (c • η) ω = c • vertexMoment q η ω := by
  simp only [vertexMoment_eq_integral, smul_eq_mul, ← integral_const_mul]
  congr 1
  funext x
  simp [wedgeField, wedgeForm_smul_right]

theorem vertexMoment_sum_smul_right {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ) {ι : Type*}
    (u : Finset ι) (c : ι → ℝ) {η : ι → FormField m} (hη : ∀ i, Continuous (η i))
    {ω : FormField n} (hω : Continuous ω) :
    vertexMoment q (∑ i ∈ u, c i • η i) ω = ∑ i ∈ u, c i * vertexMoment q (η i) ω := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    simp [vertexMoment_eq_integral, wedgeField]
  | insert a u ha ih =>
    have hs : Continuous (∑ i ∈ u, c i • η i) := by
      rw [Finset.sum_fn]; exact continuous_finsetSum _ fun i _ => (hη i).const_smul (c i)
    rw [sum_insert ha, sum_insert ha, vertexMoment_add_right q ((hη a).const_smul (c a)) hs hω,
      vertexMoment_smul_right, ih, smul_eq_mul]

/-- **Traces compose** along vertex families: the trace on a face `e'` of the reference simplex of
`F_q^* ω` is the trace along `q ∘ e'`. -/
theorem faceTrace_affinePullback_simplexMatrix {m m' : ℕ} (q : Fin (m + 1) → Fin n → ℝ)
    (e' : Fin (m' + 1) → Fin (m + 1)) (ω : FormField n) :
    faceTrace (refVertex m) e' (affinePullback (simplexMatrix q) (q 0) ω) =
      affinePullback (simplexMatrix (q ∘ e')) (q (e' 0)) ω := by
  have hq : (q ∘ e') = fun i => affine (simplexMatrix q) (q 0) ((refVertex m ∘ e') i) := by
    funext i
    exact (simplexMap_refVertex q (e' i)).symm
  rw [faceTrace_apply, affinePullback_affinePullback]
  congr 1
  · rw [hq, simplexMatrix_comp_affine]
  · exact simplexMap_refVertex q (e' 0)

/-- **Stokes' formula for moments along a vertex family**: for a `C¹` `k`-form `ω`, an ordered
`(M+1)`-simplex `q` and a smooth test form `η` on `T̂_{M+1}`,
`∫ F_q^* dω ∧ η = Σᵢ (-1)ⁱ ∫ F_{q ∘ δᵢ}^* ω ∧ δᵢ^* η - (-1)^k ∫ F_q^* ω ∧ dη`
(the version of `faceMoment_extDeriv` for faces that are not faces of a given `n`-simplex). -/
theorem vertexMoment_extDeriv {M k : ℕ} (q : Fin (M + 2) → Fin n → ℝ) {η : FormField (M + 1)}
    (hη : ContDiff ℝ ⊤ η) {ω : FormField n} (hω : ContDiff ℝ 1 ω) (hk : ∀ y, IsDeg k (ω y)) :
    vertexMoment q η (extDeriv ω) =
      ∑ i : Fin (M + 2), (-1) ^ (i : ℕ) * vertexMoment (q ∘ i.succAbove)
        (faceTrace (refVertex (M + 1)) i.succAbove η) ω -
      (-1) ^ k * vertexMoment q (extDeriv η) ω := by
  set ψ := wedgeField (affinePullback (simplexMatrix q) (q 0) ω) η
  have hψ : ContDiff ℝ 1 ψ :=
    contDiff_wedgeField (contDiff_affinePullback _ _ hω) (hη.of_le le_top)
  have hS := setIntegral_refSimplex_extDeriv (m := M) (η := ψ) isOpen_univ (Set.subset_univ _)
    hψ.contDiffOn
  have hface : ∀ i : Fin (M + 2), simplexIntegral (refVertex (M + 1) ∘ i.succAbove) ψ =
      vertexMoment (q ∘ i.succAbove) (faceTrace (refVertex (M + 1)) i.succAbove η) ω := by
    intro i
    have : simplexIntegral (refVertex (M + 1) ∘ i.succAbove) ψ =
        simplexIntegral (refVertex M) (faceTrace (refVertex (M + 1)) i.succAbove ψ) := by
      rw [simplexIntegral_refVertex]; rfl
    rw [this, faceTrace_wedgeField, faceTrace_affinePullback_simplexMatrix]
    rfl
  simp only [hface] at hS
  have hd : extDeriv (affinePullback (simplexMatrix q) (q 0) ω) =
      affinePullback (simplexMatrix q) (q 0) (extDeriv ω) :=
    funext fun y => extDeriv_affinePullback_apply _ _ ((hω.differentiable one_ne_zero) _)
  have hdiff : ∀ x, extDeriv ψ x univ =
      wedgeField (affinePullback (simplexMatrix q) (q 0) (extDeriv ω)) η x univ +
      (-1) ^ k * wedgeField (affinePullback (simplexMatrix q) (q 0) ω) (extDeriv η) x univ := by
    intro x
    rw [extDeriv_wedgeField_apply (IsDeg.affinePullback hk _ _)
      ((contDiff_affinePullback _ _ hω).differentiable one_ne_zero x)
      ((hη.of_le le_top : ContDiff ℝ 1 η).differentiable one_ne_zero x), hd]
    rfl
  simp only [hdiff] at hS
  have hc1 : Continuous (affinePullback (simplexMatrix q) (q 0) (extDeriv ω)) :=
    continuous_affinePullback _ _ (continuous_extDeriv hω)
  have hc2 : Continuous (extDeriv η) := continuous_extDeriv (hη.of_le le_top)
  rw [integral_add (integrableOn_wedgeField hc1 hη.continuous)
    ((integrableOn_wedgeField (continuous_affinePullback _ _ hω.continuous) hc2).const_mul _),
    integral_const_mul] at hS
  rw [vertexMoment_eq_integral, vertexMoment_eq_integral q (extDeriv η)]
  linarith

/-! ### The degree-`k` part of a form field -/

/-- The degree-`k` part `Σ_{#s = k} ω_s dx_s` of a form field. -/
def degField (k : ℕ) (ω : FormField n) : FormField n := fun x s => if #s = k then ω x s else 0

theorem isDeg_degField (k : ℕ) (ω : FormField n) (x : Fin n → ℝ) : IsDeg k (degField k ω x) :=
  fun s hs => by simp [degField, hs]

theorem degField_eq_self {k : ℕ} {ω : FormField n} (h : ∀ x, IsDeg k (ω x)) :
    degField k ω = ω := by
  funext x s
  by_cases hs : #s = k
  · simp [degField, hs]
  · simp [degField, hs, h x s hs]

theorem degField_add (k : ℕ) (ω ω' : FormField n) :
    degField k (ω + ω') = degField k ω + degField k ω' := by
  funext x s; by_cases hs : #s = k <;> simp [degField, hs]

theorem degField_smul (k : ℕ) (c : ℝ) (ω : FormField n) :
    degField k (c • ω) = c • degField k ω := by
  funext x s; by_cases hs : #s = k <;> simp [degField, hs]

theorem degField_zero (k : ℕ) : degField k (0 : FormField n) = 0 := by
  funext x s; simp [degField]

theorem continuous_degField (k : ℕ) {ω : FormField n} (h : Continuous ω) :
    Continuous (degField k ω) := by
  refine continuous_pi fun s => ?_
  by_cases hs : #s = k
  · simp only [degField, hs, ↓reduceIte]; exact (continuous_apply s).comp h
  · simp only [degField, hs, ↓reduceIte]; exact continuous_const

theorem contDiff_degField (k : ℕ) {r : WithTop ℕ∞} {ω : FormField n} (h : ContDiff ℝ r ω) :
    ContDiff ℝ r (degField k ω) := by
  refine contDiff_pi.2 fun s => ?_
  by_cases hs : #s = k
  · simp only [degField, hs, ↓reduceIte]; exact contDiff_pi.1 h s
  · simp only [degField, hs, ↓reduceIte]; exact contDiff_const

/-- `d` maps the degree-`k` part to the degree-`(k+1)` part: `d (ω_k) = (dω)_{k+1}`. -/
theorem extDeriv_degField (k : ℕ) (ω : FormField n) :
    extDeriv (degField k ω) = degField (k + 1) (extDeriv ω) := by
  funext x s
  by_cases hs : #s = k + 1
  · simp only [degField, hs, ↓reduceIte, extDeriv_apply]
    refine sum_congr rfl fun j hj => ?_
    have : #(s.erase j) = k := by rw [card_erase_of_mem hj]; omega
    simp only [this, ↓reduceIte]
  · rw [show degField (k + 1) (extDeriv ω) x s = 0 by simp [degField, hs]]
    exact IsDeg.extDeriv (isDeg_degField k ω) x s hs

/-- The pullback by `k` vectors only sees the degree-`k` part. -/
theorem pullback_degField_univ {k : ℕ} (V : Fin n → Fin k → ℝ) (ω : FormField n)
    (x : Fin n → ℝ) : pullback V (degField k ω x) univ = pullback V (ω x) univ := by
  rw [pullback_apply, pullback_apply]
  refine sum_congr rfl fun s _ => ?_
  by_cases hs : #s = k
  · simp [degField, hs]
  · rw [isDeg_wedgeProd V s univ (by rw [card_univ, Fintype.card_fin]; exact Ne.symm hs),
      mul_zero, mul_zero]

theorem TangentialTraceEq.degField {g : Finset (Fin n → ℝ)} {k : ℕ} {ω ω' : FormField n}
    {x : Fin n → ℝ} (h : TangentialTraceEq g k (ω x) (ω' x)) :
    TangentialTraceEq g k (degField k ω x) (degField k ω' x) := fun V hV => by
  rw [pullback_degField_univ, pullback_degField_univ]; exact h V hV

/-- **Tangential traces through a vertex family**: forms of degree `k` with the same tangential
trace on `g` have the same pullback along the edge matrix of any enumeration of points of `g`. -/
theorem pullback_simplexMatrix_eq_of_tangentialTraceEq {m k : ℕ} {g : Finset (Fin n → ℝ)}
    (q : Fin (m + 1) → Fin n → ℝ) (hq : ∀ l, q l ∈ g) {α β : Finset (Fin n) → ℝ}
    (hα : IsDeg k α) (hβ : IsDeg k β) (h : TangentialTraceEq g k α β) :
    pullback (simplexMatrix q) α = pullback (simplexMatrix q) β := by
  funext t
  by_cases ht : #t = k
  · set e := t.orderEmbOfFin ht
    set incl : Fin m → Fin k → ℝ := fun l a => if l = e a then 1 else 0
    have key : ∀ γ : Finset (Fin n) → ℝ, pullback (simplexMatrix q) γ t =
        pullback (fun i a => ∑ l, simplexMatrix q i l * incl l a) γ univ := by
      intro γ
      have h1 : pullback incl (pullback (simplexMatrix q) γ) =
          ExteriorFibre.restrict e (pullback (simplexMatrix q) γ) :=
        pullback_eq_restrict e (fun l a => ⟨fun hl => by simp [incl, hl],
          fun hl => by simp only [incl]; exact ite_eq_right_iff.2 fun h' => absurd h' hl⟩) _
      have h2 := congrFun h1 univ
      rw [ExteriorFibre.restrict, map_orderEmbOfFin_univ, pullback_pullback] at h2
      exact h2.symm
    rw [key, key]
    refine h _ fun a => ?_
    have : (fun i => ∑ l, simplexMatrix q i l * incl l a) = q (e a).succ -ᵥ q 0 := by
      funext i
      simp only [incl, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, simplexMatrix, vsub_eq_sub, Pi.sub_apply]
    rw [this]
    exact vsub_mem_vectorSpan ℝ (Finset.mem_coe.2 (hq _)) (Finset.mem_coe.2 (hq 0))
  · rw [(hα.pullback _) t ht, (hβ.pullback _) t ht]

/-- The moment of the degree-`k` part, `ω ↦ ∫_{T̂_m} F_q^* ω_k ∧ η`, as a linear functional on
continuous forms. -/
def degMoment (k : ℕ) {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ) (η : FormField m)
    (hη : Continuous η) : contForms n →ₗ[ℝ] ℝ where
  toFun ω := vertexMoment q η (degField k ω)
  map_add' ω ω' := by
    rw [Submodule.coe_add, degField_add]
    exact vertexMoment_add_left q hη (continuous_degField k ω.2) (continuous_degField k ω'.2)
  map_smul' c ω := by
    rw [Submodule.coe_smul, degField_smul]
    exact vertexMoment_smul_left q η c _

theorem degMoment_apply (k : ℕ) {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ) (η : FormField m)
    (hη : Continuous η) (ω : contForms n) :
    degMoment k q η hη ω = vertexMoment q η (degField k ω) := rfl

/-! ### Admissible sequences and their degrees of freedom -/

/-- **An admissible sequence** of polynomial families ([AFW2006], §5; [AFW2010], §5.2): in every
form degree `k` a family `P_{r_k}Λᵏ` or `P_{r_k}⁻Λᵏ` with `r_k ≥ 1`, consecutive degrees being
related by an admissible transition `Xᵏ → P_{r_k}⁻Λᵏ⁺¹` or `Xᵏ → P_{r_k-1}Λᵏ⁺¹`. (The degrees
`k > n` carry the zero space.) `P_0Λⁿ`, the piecewise constants, is represented by the equal
space `P_1⁻Λⁿ` (`polyMinusSpace_top`). -/
@[ext] structure PolySeq where
  /-- the family in degree `k` -/
  kind : ℕ → PolyKind
  /-- the polynomial degree `r_k` in degree `k` -/
  deg : ℕ → ℕ
  one_le_deg : ∀ k, 1 ≤ deg k
  transition : ∀ k, PolyKind.Transition (deg k) (kind (k + 1)) (deg (k + 1))

namespace PolySeq

variable (S : PolySeq)

/-- The space `P_{r_k}Λᵏ(ℝⁿ)` or `P_{r_k}⁻Λᵏ(ℝⁿ)` of the sequence in degree `k`. -/
abbrev space (n k : ℕ) : Submodule ℝ (FormField n) := (S.kind k).space n (S.deg k) k

/-- The test forms of the degree-`k` degrees of freedom on `m`-faces. -/
abbrev test (k m : ℕ) : Submodule ℝ (FormField m) := (S.kind k).test (S.deg k) k m

/-- The fixed basis of the test forms on `m`-faces (on the reference `m`-simplex). -/
def testBasis (k m : ℕ) : Module.Basis (Fin (Module.finrank ℝ (S.test k m))) ℝ (S.test k m) :=
  Module.finBasis ℝ _

theorem continuous_testBasis (k m : ℕ) (i : Fin (Module.finrank ℝ (S.test k m))) :
    Continuous (S.testBasis k m i : FormField m) :=
  (PolyKind.contDiff_of_mem_test (S.testBasis k m i).2).continuous

/-- The degrees of freedom of degree `k` attached to the face (vertex set) `g`: a basis of the
test forms on `(#g - 1)`-faces, none for `g = ∅`. -/
abbrev DofIdx (g : Finset (Fin n → ℝ)) (k : ℕ) : Type :=
  {_i : Fin (Module.finrank ℝ (S.test k (#g - 1))) // g.Nonempty}

theorem card_dofIdx (g : Finset (Fin n → ℝ)) (k : ℕ) :
    Fintype.card (S.DofIdx g k) =
      if g.Nonempty then Module.finrank ℝ (S.test k (#g - 1)) else 0 := by
  split_ifs with h
  · rw [Fintype.card_subtype]; simp [h]
  · exact Fintype.card_eq_zero_iff.2 ⟨fun x => h x.2⟩

instance (k : ℕ) : IsEmpty (S.DofIdx (∅ : Finset (Fin n → ℝ)) k) :=
  ⟨fun i => Finset.not_nonempty_empty i.2⟩

/-- There are no degrees of freedom of degree `k` on faces with fewer than `k + 1` vertices. -/
theorem isEmpty_dofIdx_of_card_lt {g : Finset (Fin n → ℝ)} {k : ℕ} (h : #g < k + 1) :
    IsEmpty (S.DofIdx g k) := by
  refine ⟨fun i => ?_⟩
  have h1 := card_pos.2 i.2
  have h0 : Module.finrank ℝ (S.test k (#g - 1)) = 0 := by
    have hb : S.test k (#g - 1) = ⊥ := PolyKind.test_eq_bot (by omega)
    rw [hb, finrank_bot]
  have := i.1.isLt
  omega

/-- **The degrees of freedom** of the face `g`: with `q = lexEnum g (#g - 1)` the vertices of `g`
in lexicographic order and `ηᵢ` the basis of the test forms,
`ℓ_{g,i}(ω) = ∫_{T̂_m} F_q^* ω ∧ ηᵢ` ([AFW2006], §4.5–4.6, §5.1), applied to the degree-`k`
part of `ω`. They depend only on the vertex set `g`. -/
def dof (g : Finset (Fin n → ℝ)) (k : ℕ) (i : S.DofIdx g k) : contForms n →ₗ[ℝ] ℝ :=
  degMoment k (lexEnum g (#g - 1)) (S.testBasis k (#g - 1) i.1 : FormField (#g - 1))
    (S.continuous_testBasis k _ i.1)

theorem dof_apply (g : Finset (Fin n → ℝ)) (k : ℕ) (i : S.DofIdx g k) (ω : contForms n) :
    S.dof g k i ω = vertexMoment (lexEnum g (#g - 1))
      (S.testBasis k (#g - 1) i.1 : FormField (#g - 1)) (degField k ω) := rfl

/-- **Moments against test forms are combinations of the degrees of freedom**: for `#g = m + 1`
and a test form `η` on `m`-faces, `ω ↦ ∫ F_q^* ω_k ∧ η` is a combination of the `ℓ_{g,i}`. -/
theorem exists_degMoment_eq_sum {g : Finset (Fin n → ℝ)} {m : ℕ} (hg : #g = m + 1) {k : ℕ}
    {η : FormField m} (hη : η ∈ S.test k m) :
    ∃ c : S.DofIdx g k → ℝ, degMoment k (lexEnum g m) η
      (PolyKind.contDiff_of_mem_test hη).continuous = ∑ i, c i • S.dof g k i := by
  obtain rfl : m = #g - 1 := by omega
  have hne : g.Nonempty := card_pos.1 (by omega)
  set b := S.testBasis k (#g - 1)
  refine ⟨fun i => b.repr ⟨η, hη⟩ i.1, LinearMap.ext fun ω => ?_⟩
  rw [degMoment_apply, LinearMap.sum_apply]
  conv_lhs => rw [eq_sum_repr_basis b hη]
  rw [vertexMoment_sum_smul_right _ _ _ (fun l => S.continuous_testBasis k _ l)
    (continuous_degField k ω.2)]
  refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun _ => hne).symm _ _ fun l => ?_
  rw [LinearMap.smul_apply, smul_eq_mul, dof_apply]
  rfl

theorem degMoment_comp_mem_span {g : Finset (Fin n → ℝ)} {m : ℕ} (hg : #g = m + 1) {k : ℕ}
    {η : FormField m} (hη : η ∈ S.test k m) {X : Type*} [AddCommGroup X] [Module ℝ X]
    (φ : X →ₗ[ℝ] contForms n) :
    degMoment k (lexEnum g m) η (PolyKind.contDiff_of_mem_test hη).continuous ∘ₗ φ ∈
      Submodule.span ℝ (Set.range fun i : S.DofIdx g k => S.dof g k i ∘ₗ φ) := by
  obtain ⟨c, hc⟩ := S.exists_degMoment_eq_sum hg hη
  have : (∑ i, c i • S.dof g k i) ∘ₗ φ = ∑ i, c i • (S.dof g k i ∘ₗ φ) := by
    ext x; simp
  rw [hc, this]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **The degrees of freedom of `g` determine the moments** against all test forms. -/
theorem degMoment_eq_of_dof_eq {g : Finset (Fin n → ℝ)} {m : ℕ} (hg : #g = m + 1) {k : ℕ}
    {ω ω' : contForms n} (h : ∀ i, S.dof g k i ω = S.dof g k i ω') {η : FormField m}
    (hη : η ∈ S.test k m) :
    vertexMoment (lexEnum g m) η (degField k ω) = vertexMoment (lexEnum g m) η (degField k ω') := by
  obtain ⟨c, hc⟩ := S.exists_degMoment_eq_sum hg hη
  have := congrArg (fun L : contForms n →ₗ[ℝ] ℝ => L ω - L ω') hc
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, h, sub_self] at this
  rw [← sub_eq_zero]
  exact this

theorem space_le_contForms (n k : ℕ) : S.space n k ≤ contForms n := fun _ h =>
  (PolyKind.contDiff_of_mem_space h).continuous

theorem card_sigma_dofIdx (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    Fintype.card (Σ g : (vertexSet T).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k) =
      Module.finrank ℝ (S.space n k) := by
  classical
  rw [Fintype.card_sigma, PolyKind.finrank_space_eq_sum _ (S.one_le_deg k)]
  simp only [card_dofIdx]
  rw [Finset.sum_coe_sort (vertexSet T).powerset (fun g =>
    if g.Nonempty then Module.finrank ℝ (S.test k (#g - 1)) else 0)]
  have h1 : ∀ g ∈ (vertexSet T).powerset, (if g.Nonempty then
      Module.finrank ℝ (S.test k (#g - 1)) else 0) =
      (fun j => if 0 < j then Module.finrank ℝ (S.test k (j - 1)) else 0) #g := fun g _ => by
    simp only [card_pos]
  rw [sum_congr rfl h1, sum_powerset_apply_card
    (fun j => if 0 < j then Module.finrank ℝ (S.test k (j - 1)) else 0), card_vertexSet,
    sum_range_succ']
  simp only [smul_eq_mul, Nat.succ_pos, ↓reduceIte, lt_irrefl, mul_zero, add_zero]
  exact sum_congr rfl fun x _ => rfl

/-- **Unisolvence** of the degrees of freedom of the faces of `T` on `P_{r_k}Λᵏ` (resp.
`P_{r_k}⁻Λᵏ`). The lexicographic enumeration of the vertices of `T` is an enumeration `p'` of
`T` whose faces are enumerated by `lexEnum`, so these are the degrees of freedom of
`isUnisolvent_localDof` (resp. `isUnisolvent_localDofMinus`) on `p'`, for the same test bases. -/
theorem isUnisolvent_dof (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    IsUnisolvent fun p : Σ g : (vertexSet T).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k =>
      S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ∘ₗ Submodule.inclusion (S.space_le_contForms n k) := by
  classical
  rw [isUnisolvent_iff_forall_eq_zero _ (S.card_sigma_dofIdx T k).symm]
  intro ω hω
  set p' := lexEnum (vertexSet T) n
  have hp' := isUnit_det_edgeMatrix_lexEnum T
  have hmono := strictMono_lexEnum (card_vertexSet T)
  refine Subtype.ext (PolyKind.eq_zero_of_faceMoment (S.kind k) hp' (S.one_le_deg k) ω.2
    fun m e η hη => ?_)
  obtain ⟨hcard, hq⟩ := lexEnum_image_comp hmono e.strictMono
  set g := Finset.univ.image (p' ∘ e)
  have hgT : g ⊆ vertexSet T := fun x hx => by
    obtain ⟨i, -, rfl⟩ := mem_image.1 hx
    rw [← image_lexEnum (card_vertexSet T)]
    exact mem_image_of_mem _ (mem_univ _)
  have h := S.degMoment_eq_of_dof_eq hcard (ω := ⟨ω, S.space_le_contForms n k ω.2⟩) (ω' := 0)
    (fun i => by rw [map_zero]; exact hω ⟨⟨g, mem_powerset.2 hgT⟩, i⟩) hη
  rw [hq, Submodule.coe_zero, degField_zero, degField_eq_self (PolyKind.isDeg_of_mem_space ω.2)]
    at h
  rw [faceMoment_eq_vertexMoment]
  refine h.trans ?_
  simpa using vertexMoment_smul_left (p' ∘ ⇑e) η 0 0

/-- **Trace determination**: on a facet `F` of `T`, two forms of the local space with the same
degrees of freedom on the faces of `F` have the same tangential trace on `F`. -/
theorem tangentialTraceEq_of_dof_eq {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    {F : Finset (Fin n → ℝ)} {k : ℕ} (hT : F ⊆ vertexSet T) (hc : #F = n) {w η : FormField n}
    (hw : w ∈ S.space n k) (hη : η ∈ S.space n k)
    (hdof : ∀ g ⊆ F, ∀ i : S.DofIdx g k, S.dof g k i ⟨w, S.space_le_contForms n k hw⟩ =
      S.dof g k i ⟨η, S.space_le_contForms n k hη⟩) :
    ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)), TangentialTraceEq F k (w x) (η x) := by
  rcases n with _ | m
  · intro x hx
    have : F = ∅ := Finset.card_eq_zero.1 hc
    simp [this] at hx
  set p' := lexEnum (vertexSet T) (m + 1)
  have hp' := isUnit_det_edgeMatrix_lexEnum T
  have hmono := strictMono_lexEnum (card_vertexSet T)
  obtain ⟨eF, heF⟩ := exists_orderEmb_comp_eq_lexEnum hmono hc fun x hx =>
    exists_lexEnum_eq_of_mem_vertexSet T (hT hx)
  set q := lexEnum F m
  have hq : Set.range q = F := range_lexEnum hc
  have htr := PolyKind.faceTrace_eq (S.kind k) hp' (S.one_le_deg k) (Face.ofEmb eF) hw hη
    fun g hg ζ hζ => by
      obtain ⟨hcard, hG⟩ := lexEnum_image_comp hmono g.emb.strictMono
      have hGF : Finset.univ.image (p' ∘ g.emb) ⊆ F := fun x hx => by
        obtain ⟨j, -, rfl⟩ := mem_image.1 hx
        have hj := hg (orderEmbOfFin_mem g.2.1 g.2.2 j)
        obtain ⟨a, -, ha⟩ := mem_map.1 hj
        change p' (g.2.1.orderEmbOfFin g.2.2 j) ∈ F
        rw [← ha]
        change (p' ∘ eF) a ∈ F
        rw [heF]
        exact lexEnum_mem hc a
      have h := S.degMoment_eq_of_dof_eq hcard (fun i => hdof _ hGF i) hζ
      rw [hG, degField_eq_self (PolyKind.isDeg_of_mem_space hw),
        degField_eq_self (PolyKind.isDeg_of_mem_space hη)] at h
      exact h
  rw [Face.emb_ofEmb, faceTrace_apply, faceTrace_apply] at htr
  rw [heF, show lexEnum (vertexSet T) (m + 1) (eF 0) = q 0 from congrFun heF 0] at htr
  intro x hx
  rw [← hq] at hx
  obtain ⟨y, -, rfl⟩ := exists_simplexMap_eq_of_mem_convexHull q hx
  refine tangentialTraceEq_of_pullback_eq q hq ?_
  have := congrFun htr y
  simpa [affinePullback_apply, simplexMap] using this

/-- **The degrees of freedom of `g` only see the tangential traces on `g`.** -/
theorem dof_congr {g : Finset (Fin n → ℝ)} {k : ℕ} (i : S.DofIdx g k) {w η : contForms n}
    (h : ∀ x ∈ convexHull ℝ (g : Set (Fin n → ℝ)),
      TangentialTraceEq g k ((w : FormField n) x) ((η : FormField n) x)) :
    S.dof g k i w = S.dof g k i η := by
  have hg : #g = #g - 1 + 1 := by have := card_pos.2 i.2; omega
  set q := lexEnum g (#g - 1)
  have hqg : ∀ l, q l ∈ g := lexEnum_mem hg
  rw [dof_apply, dof_apply, vertexMoment_eq_integral, vertexMoment_eq_integral]
  refine setIntegral_congr_fun (measurableSet_refSimplex _) fun y hy => ?_
  have hx : affine (simplexMatrix q) (q 0) y ∈ convexHull ℝ (g : Set (Fin n → ℝ)) := by
    rw [← range_lexEnum hg]
    exact simplexMap_mem_convexHull q hy
  simp only [wedgeField, affinePullback_apply]
  rw [pullback_simplexMatrix_eq_of_tangentialTraceEq q hqg (isDeg_degField k _ _)
    (isDeg_degField k _ _) (TangentialTraceEq.degField (h _ hx))]

/-- Stokes compatibility for one test form: `ω ↦ ∫ F_q^* (dω)_{k+1} ∧ η`, for a test form `η` of
degree `k + 1`, is a combination of the degree-`k` degrees of freedom of the faces of `g`. -/
theorem degMoment_comp_extDerivC1_mem_span {g : Finset (Fin n → ℝ)} {m k : ℕ}
    (hg : #g = m + 1) {η : FormField m} (hη : η ∈ S.test (k + 1) m) :
    degMoment (k + 1) (lexEnum g m) η (PolyKind.contDiff_of_mem_test hη).continuous ∘ₗ
        extDerivC1 ∈
      Submodule.span ℝ (Set.range fun p : Σ g' : g.powerset,
        S.DofIdx (g' : Finset (Fin n → ℝ)) k =>
          S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ∘ₗ Submodule.inclusion c1Forms_le_contForms) := by
  have hsub : ∀ g' ⊆ g, Submodule.span ℝ (Set.range fun i : S.DofIdx g' k =>
      S.dof g' k i ∘ₗ Submodule.inclusion c1Forms_le_contForms) ≤
      Submodule.span ℝ (Set.range fun p : Σ g' : g.powerset,
        S.DofIdx (g' : Finset (Fin n → ℝ)) k =>
          S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ∘ₗ Submodule.inclusion c1Forms_le_contForms) :=
    fun g' hg' => Submodule.span_mono (by
      rintro _ ⟨i, rfl⟩
      exact ⟨⟨⟨g', mem_powerset.2 hg'⟩, i⟩, rfl⟩)
  cases m with
  | zero =>
    have h0 : η = 0 := by
      have : S.test (k + 1) 0 = ⊥ := PolyKind.test_eq_bot (by omega)
      rw [this, Submodule.mem_bot] at hη; exact hη
    subst h0
    have : degMoment (k + 1) (lexEnum g 0) (0 : FormField 0)
        (PolyKind.contDiff_of_mem_test hη).continuous = 0 := LinearMap.ext fun ω => by
      rw [degMoment_apply, LinearMap.zero_apply, vertexMoment_eq_integral]
      simp [wedgeField]
    rw [this, LinearMap.zero_comp]
    exact Submodule.zero_mem _
  | succ M =>
    set q := lexEnum g (M + 1)
    have hqm := strictMono_lexEnum hg
    obtain ⟨htr, hd⟩ := PolyKind.test_of_transition (S.kind k) (S.transition k) hη
    have heq : degMoment (k + 1) q η (PolyKind.contDiff_of_mem_test hη).continuous ∘ₗ
        extDerivC1 = ∑ i : Fin (M + 2), ((-1 : ℝ) ^ (i : ℕ)) •
          (degMoment k (q ∘ i.succAbove) _ (PolyKind.contDiff_of_mem_test (htr i)).continuous ∘ₗ
            Submodule.inclusion c1Forms_le_contForms) -
        ((-1 : ℝ) ^ k) • (degMoment k q _ (PolyKind.contDiff_of_mem_test hd).continuous ∘ₗ
            Submodule.inclusion c1Forms_le_contForms) := by
      refine LinearMap.ext fun ω => ?_
      rw [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply]
      simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, degMoment_apply]
      change vertexMoment q η (degField (k + 1) (extDeriv (ω : FormField n))) = _
      rw [← extDeriv_degField]
      exact vertexMoment_extDeriv q (PolyKind.contDiff_of_mem_test hη)
        (contDiff_degField k (mem_c1Forms.1 ω.2)) (isDeg_degField k _)
    rw [heq]
    refine Submodule.sub_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ (hsub g subset_rfl (S.degMoment_comp_mem_span hg hd _)))
    obtain ⟨hcard, hG⟩ := lexEnum_image_comp hqm (Fin.strictMono_succAbove i)
    have hGg : Finset.univ.image (q ∘ i.succAbove) ⊆ g := fun x hx => by
      obtain ⟨j, -, rfl⟩ := mem_image.1 hx
      exact lexEnum_mem hg _
    have := S.degMoment_comp_mem_span hcard (htr i) (Submodule.inclusion c1Forms_le_contForms)
    rw [hG] at this
    exact hsub _ hGg this

/-- **Stokes compatibility of the degrees of freedom**: `ℓ_{g,i} ∘ d` is a combination of the
degrees of freedom of the faces of `g` (Stokes' theorem on `g`, `vertexMoment_extDeriv`, and
`PolyKind.test_of_transition`). -/
theorem dof_comp_extDerivC1_mem_span (g : Finset (Fin n → ℝ)) (k : ℕ)
    (i : S.DofIdx g (k + 1)) :
    S.dof g (k + 1) i ∘ₗ extDerivC1 ∈
      Submodule.span ℝ (Set.range fun p : Σ g' : g.powerset,
        S.DofIdx (g' : Finset (Fin n → ℝ)) k =>
          S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ∘ₗ Submodule.inclusion c1Forms_le_contForms) := by
  have hg : #g = #g - 1 + 1 := by have := card_pos.2 i.2; omega
  exact S.degMoment_comp_extDerivC1_mem_span hg (S.testBasis (k + 1) (#g - 1) i.1).2

end PolySeq

/-- **The element family of an admissible sequence** `S`: on every `n`-simplex the spaces
`P_{r_k}Λᵏ` or `P_{r_k}⁻Λᵏ` (the same polynomial spaces for every simplex, by affine
invariance), with the moment degrees of freedom `PolySeq.dof` attached to the faces. -/
def polyElement (n : ℕ) (S : PolySeq) : LocalElement n where
  space _ k := S.space n k
  contDiff_of_mem h := (PolyKind.contDiff_of_mem_space h).of_le le_top
  isDeg_of_mem h x := PolyKind.isDeg_of_mem_space h x
  extDeriv_mem {_ k _} h := PolyKind.extDeriv_mem_space _ (S.one_le_deg k) (S.transition k) h
  finiteDimensional _ _ := inferInstance
  DofIdx := S.DofIdx
  dofIdxFintype _ _ := inferInstance
  dof := S.dof
  unisolvent T k := S.isUnisolvent_dof T k
  trace := fun hT _ hc hw hη h => S.tangentialTraceEq_of_dof_eq hT hc hw hη h
  dof_congr := S.dof_congr
  dof_extDeriv := S.dof_comp_extDerivC1_mem_span

/-! ### Naturality of the higher-order families under affine maps -/

theorem PolySeq.affinePullback_mem_space (S : PolySeq) {m n' : ℕ} (B : Fin n' → Fin m → ℝ)
    (b' : Fin n' → ℝ) (k : ℕ) {w : FormField n'} (hw : w ∈ S.space n' k) :
    affinePullback B b' w ∈ S.space m k := by
  change _ ∈ (S.kind k).space m (S.deg k) k
  change w ∈ (S.kind k).space n' (S.deg k) k at hw
  generalize S.kind k = κ at hw ⊢
  cases κ
  · exact affinePullback_mem_polySpace B b' hw
  · exact affinePullback_mem_polyMinusSpace B b' hw

theorem PolySeq.affinePullback_mem_test (S : PolySeq) {m : ℕ} (B : Fin m → Fin m → ℝ)
    (b' : Fin m → ℝ) (k : ℕ) {η : FormField m} (hη : η ∈ S.test k m) :
    affinePullback B b' η ∈ S.test k m := by
  change _ ∈ (S.kind k).test (S.deg k) k m
  change η ∈ (S.kind k).test (S.deg k) k m at hη
  by_cases hc : k ≤ m ∧ m < S.deg k + k
  · generalize S.kind k = κ at hη ⊢
    cases κ
    · change η ∈ testSpace _ k m at hη
      change _ ∈ testSpace _ k m
      rw [testSpace_eq hc] at hη ⊢
      exact affinePullback_mem_polyMinusSpace B b' hη
    · change η ∈ testSpaceMinus _ k m at hη
      change _ ∈ testSpaceMinus _ k m
      rw [testSpaceMinus_eq hc] at hη ⊢
      exact affinePullback_mem_polySpace B b' hη
  · rw [PolyKind.test_eq_bot hc, Submodule.mem_bot] at hη ⊢
    subst hη
    funext x s
    simp [affinePullback_apply, pullback_apply]

/-- `degField` commutes with the pullback (the pullback preserves degrees). -/
theorem degField_affinePullback {m n' : ℕ} (k : ℕ) (B : Fin n' → Fin m → ℝ) (b' : Fin n' → ℝ)
    (w : FormField n') :
    degField k (affinePullback B b' w) = affinePullback B b' (degField k w) := by
  funext x s
  simp only [degField, affinePullback_apply, pullback_apply]
  by_cases hs : #s = k
  · simp only [hs, ite_true]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : #t = k
    · simp only [ht, ite_true]
    · simp only [ht, ite_false, isDeg_wedgeProd B t s (by rw [hs]; exact Ne.symm ht), mul_zero]
  · simp only [hs, ite_false]
    refine (Finset.sum_eq_zero fun t _ => ?_).symm
    by_cases ht : #t = k
    · rw [isDeg_wedgeProd B t s (by rw [ht]; exact hs), mul_zero]
    · simp only [ht, ite_false, zero_mul]

/-- **Moments along an affine image**: `∫_{T̂} F_q^* (G^* ω) ∧ η = ∫_{T̂} F_{G ∘ q}^* ω ∧ η`. -/
theorem vertexMoment_affinePullback {m n' : ℕ} (q : Fin (m + 1) → Fin n → ℝ) (η : FormField m)
    (B : Fin n' → Fin n → ℝ) (b' : Fin n' → ℝ) (w : FormField n') :
    vertexMoment q η (affinePullback B b' w) = vertexMoment (fun i => affine B b' (q i)) η w := by
  simp only [vertexMoment, affinePullback_affinePullback, simplexMatrix_comp_affine]

/-- `wedgeField` commutes with the pullback. -/
theorem affinePullback_wedgeField {m : ℕ} (B : Fin m → Fin m → ℝ) (b' : Fin m → ℝ)
    (α β : FormField m) :
    affinePullback B b' (wedgeField α β) =
      wedgeField (affinePullback B b' α) (affinePullback B b' β) := by
  funext x
  simp only [affinePullback_apply, wedgeField, pullback_wedgeForm]

/-- `(A_π)^* (A_{π⁻¹})^* η = η`. -/
theorem affinePullback_permMap_inv {m : ℕ} (π : Equiv.Perm (Fin (m + 1))) (η : FormField m) :
    affinePullback (simplexMatrix (refVertex m ∘ π)) (refVertex m (π 0))
      (affinePullback (simplexMatrix (refVertex m ∘ ⇑(π⁻¹))) (refVertex m (π⁻¹ 0)) η) = η := by
  rw [affinePullback_affinePullback, ← simplexMatrix_perm_mul π⁻¹ π]
  have h0 : affine (simplexMatrix (refVertex m ∘ ⇑(π⁻¹))) (refVertex m (π⁻¹ 0))
      (refVertex m (π 0)) = refVertex m 0 := by
    have := simplexMap_refVertex (refVertex m ∘ ⇑(π⁻¹)) (π 0)
    simpa [simplexMap] using this
  rw [h0, inv_mul_cancel, show refVertex m ∘ (1 : Equiv.Perm (Fin (m + 1))) = refVertex m from rfl,
    simplexMatrix_refVertex, refVertex_zero]
  exact affinePullback_id η

/-- **Moments under a reparametrization of the face**: permuting the vertices by `π` multiplies
the moment by `sign π` and transforms the test form by `A_{π⁻¹}`. -/
theorem vertexMoment_comp_perm {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) (η : FormField m) (w : FormField n) :
    vertexMoment (q ∘ π) η w = ((Equiv.Perm.sign π : ℤ) : ℝ) *
      vertexMoment q (affinePullback (simplexMatrix (refVertex m ∘ ⇑(π⁻¹))) (refVertex m (π⁻¹ 0))
        η) w := by
  set P := simplexMatrix (refVertex m ∘ π)
  set p0 := refVertex m (π 0)
  set η' := affinePullback (simplexMatrix (refVertex m ∘ ⇑(π⁻¹)))
    (refVertex m (π⁻¹ 0)) η
  have hq : q ∘ π = fun i => affine (simplexMatrix q) (q 0) ((refVertex m ∘ π) i) := by
    funext i; exact (simplexMap_refVertex q (π i)).symm
  have hF : affinePullback (simplexMatrix (q ∘ π)) ((q ∘ π) 0) w =
      affinePullback P p0 (affinePullback (simplexMatrix q) (q 0) w) := by
    rw [affinePullback_affinePullback, hq, simplexMatrix_comp_affine]
    rfl
  have hη : η = affinePullback P p0 η' := (affinePullback_permMap_inv π η).symm
  have hp : (fun i => affine P p0 (refVertex m i)) = refVertex m ∘ π := by
    funext i; exact simplexMap_refVertex (refVertex m ∘ π) i
  simp only [vertexMoment]
  rw [hF]
  conv_lhs => rw [hη]
  rw [← affinePullback_wedgeField, ← simplexIntegral_comp_affine, hp, simplexIntegral_comp_perm]

end Feec.FiniteElement
