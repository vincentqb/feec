module

public import Feec.FiniteElement.AffineInvariantForm
public import Feec.FiniteElement.PolyElement

/-!
# Higher-order finite element complexes on meshes

For an admissible sequence `S` (`Feec.FiniteElement.PolySeq`) the element family
`Feec.FiniteElement.polyElement n S` gives, on every conforming simplicial mesh `M` of an open
`Ω ⊆ ℝⁿ`, the global spaces of piecewise `P_{r_k}Λᵏ` / `P_{r_k}⁻Λᵏ` forms with continuous
tangential traces, a subcomplex of `HΛ(Ω)` and, with vanishing boundary degrees of freedom, of
`H̊Λ(Ω)` for strictly star-shaped `Ω`; this file names the classical sequences, computes the
dimensions, and specializes to the Freudenthal meshes of cubes.

* **The periodic table** ([ArnoldLogg2014]): `PolySeq.ofKinds n κ s` is the admissible sequence
  with the kinds `κ k` in the degrees `k < n` ending in `P_sΛⁿ` (`PolySeq.ofKinds_space_top`,
  from `P_{s+1}⁻Λⁿ = P_sΛⁿ`, `polyMinusSpace_top`): every choice of kinds gives an admissible
  sequence. That every admissible sequence ending in `P_sΛⁿ` has, up to its spaces, this form is
  not formalized; as `P_r⁻Λ⁰ = P_rΛ⁰` (`polyMinusSpace_zero`) only `κ 1, …, κ (n-1)` matter:
  `2ⁿ⁻¹` sequences for each `s` (this count is not formalized either). Named corners:
  `PolySeq.trimmed r` (`P_r⁻Λ⁰ → ⋯ → P_r⁻Λⁿ`: Lagrange, Nédélec first kind [Nedelec1980],
  Raviart–Thomas–Nédélec [RaviartThomas1977], discontinuous `P_{r-1}`;
  `PolySeq.trimmed_eq_ofKinds`),
  `PolySeq.full n r` (`P_rΛ⁰ → P_{r-1}Λ¹ → ⋯ → P_{r-n}Λⁿ`, `n ≤ r`: Lagrange, Nédélec second kind
  [Nedelec1986], Brezzi–Douglas–Marini [BrezziDouglasMarini1985], discontinuous `P_{r-n}`;
  `PolySeq.full_space`), and the two rows of Tables 5.1 and 6.1 of [QuennevilleBelair2015]
  (§5.3, §6.3): `PolySeq.lowestOrder` (`P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ² → P₁⁻Λ³`) and `PolySeq.lagrangeP2`
  (`P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³`) (`PolySeq.lowestOrder_eq_ofKinds`,
  `PolySeq.lagrangeP2_eq_ofKinds`).
* **The classical elements in closed form**: in `ℝ³`, `dim P_rΛ⁰ = dim P_rΛ³ = (r+1)(r+2)(r+3)/6`
  (Lagrange, discontinuous `P_r`), `dim P_r⁻Λ¹ = r(r+2)(r+3)/2` (Nédélec first kind),
  `dim P_rΛ¹ = dim P_rΛ² = (r+1)(r+2)(r+3)/2` (Nédélec second kind, Brezzi–Douglas–Marini),
  `dim P_r⁻Λ² = r(r+1)(r+3)/2` (Raviart–Thomas–Nédélec): `finrank_polySpace_three_zero`, …,
  `finrank_polyMinusSpace_three_two`; in `ℝ²`, `dim P_r⁻Λ¹ = r(r+2)` (Raviart–Thomas),
  `dim P_rΛ¹ = (r+1)(r+2)` (Brezzi–Douglas–Marini): `finrank_polySpace_two_zero`, …,
  `finrank_polyMinusSpace_two_one`.
* **The Whitney complex is `P₁⁻Λ`**: the Whitney element and the element of `PolySeq.trimmed 1`
  are equivalent (`whitneyElement_equivalent_trimmed`: the same local spaces,
  `polyMinusSpace_one_eq_p1MinusForms`, and on every face the moment degrees of freedom are
  nonzero multiples of the face integrals, `PolySeq.trimmed_one_dof_eq`), so they assemble the
  same subcomplexes on every mesh (`whitneySubcomplex_eq_trimmed`,
  `whitneySubcomplexMin_eq_trimmed`, by `LocalElement.Equivalent.subcomplex_eq`).
* Dimensions: `PolySeq.finrank_globalSpace`: `Σ_m #{m-faces} · dim(test forms on m-faces)`;
  `PolySeq.finrank_globalSpace₀`, `PolySeq.finrank_V₀`: the same with the faces not contained in
  a boundary facet.
* Subcomplexes: `PolySeq.subcomplex`, `PolySeq.subcomplexMin`, and on the level-`N` Freudenthal
  mesh of a cube `PolySeq.freudenthalSubcomplexMin`.
* **Nonzero interior spaces**: a face of `M` whose convex hull meets `Ω` is not contained in a
  boundary facet (`LocalElement.not_isBoundaryDof_of_mem_convexHull`), and on the Freudenthal
  meshes the faces of `b + (s/N) K_id` containing the diagonal from `b` to `b + (s/N)(1, …, 1)`
  are such faces (`exists_meshFace_freudenthalMesh`). Hence `V̊ₕᵏ ≠ 0` for `1 ≤ k ≤ n` for every
  admissible sequence (`PolySeq.finrank_V₀_freudenthalMesh_pos_of_one_le`) and for the Whitney
  forms (`finrank_whitney_V₀_freudenthalMesh_pos`), and for `k = 0` when `r₀ ≥ 2`
  (`PolySeq.finrank_V₀_freudenthalMesh_pos_zero`), on every level `N ≥ 1`. In particular the
  interior spaces of the second row of Tables 5.1/6.1 on the level-`(N+1)` Freudenthal mesh of
  `(0, ½)³` are nonzero in every degree (`PolySeq.lagrangeP2_V₀_ne_bot`). For `k = 0` and
  `r₀ = 1` an interior vertex is needed: on every level `N ≥ 2` the lattice point
  `b + (s/N)(1, …, 1)` is one (`exists_vertex_freudenthalMesh`), so `V̊ₕᵏ ≠ 0` in every degree
  for every admissible sequence (`PolySeq.finrank_V₀_freudenthalMesh_pos_of_two_le`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3 (the spaces `P_rΛᵏ`, `P_r⁻Λᵏ` and their dimensions), §4 (degrees of freedom, Thms 4.9,
  4.13), §5 (assembly, dimension counts)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.2
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3, Table 5.1; §6.3, Table 6.1
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [H. Whitney, *Geometric Integration Theory*][Whitney1957], Ch. IV, §27 (Whitney forms)
* [D. N. Arnold, A. Logg, *Periodic table of the finite elements*][ArnoldLogg2014]
* [J.-C. Nédélec, *Mixed finite elements in ℝ³*][Nedelec1980] (`P_r⁻Λ¹`, `P_r⁻Λ²` in `ℝ³`)
* [J.-C. Nédélec, *A new family of mixed finite elements in ℝ³*][Nedelec1986] (`P_rΛ¹`, `P_rΛ²`
  in `ℝ³`)
* [P.-A. Raviart, J.-M. Thomas, *A mixed finite element method for 2-nd order elliptic problems*][RaviartThomas1977]
  (`P_r⁻Λ¹` in `ℝ²`)
* [F. Brezzi, J. Douglas, Jr., L. D. Marini, *Two families of mixed finite elements for second order elliptic problems*][BrezziDouglasMarini1985]
  (`P_rΛ¹` in `ℝ²`)

Bibliography: [references.bib](../../docs/references.bib)
-/

open MeasureTheory Set Finset

@[expose] public noncomputable section

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh Feec.Domain

variable {n : ℕ}

/-! ### The admissible sequences of the periodic table -/

namespace PolySeq

/-- **The admissible sequence of kinds `κ` ending in `P_sΛⁿ`** ([AFW2006], §5; [AFW2010], §5.2;
[ArnoldLogg2014]): in each degree `k < n` the family `κ k` of degree
`r_k = s + 1 + #{j | k < j < n, κ j = full}`, and in the top degree `P_{s+1}⁻Λⁿ = P_sΛⁿ`
(`ofKinds_space_top`). Read from the top down, a full space `P_{r_j}Λʲ` raises the degree of the
space below it by one and a trimmed space `P_{r_j}⁻Λʲ` keeps it, which is the admissibility
condition `PolyKind.Transition`. As `P_r⁻Λ⁰ = P_rΛ⁰` (`polyMinusSpace_zero`), `κ 0` does not
change the spaces: the `2ⁿ⁻¹` choices of `κ 1, …, κ (n-1)` give the admissible sequences ending
in `P_sΛⁿ`. -/
def ofKinds (n : ℕ) (κ : ℕ → PolyKind) (s : ℕ) : PolySeq where
  kind k := if k < n then κ k else .trimmed
  deg k := s + 1 + #{j ∈ Finset.Ioo k n | κ j = .full}
  one_le_deg _ := by omega
  transition k := by
    by_cases hk : k + 1 < n
    · have hI : Finset.Ioo k n = insert (k + 1) (Finset.Ioo (k + 1) n) := by
        ext j; simp only [Finset.mem_Ioo, Finset.mem_insert]; omega
      rw [hI, Finset.filter_insert]
      cases h : κ (k + 1)
      · refine Or.inr ⟨by simp [hk], ?_⟩
        simp only [↓reduceIte]
        rw [Finset.card_insert_of_notMem (by simp)]
        omega
      · exact Or.inl ⟨by simp [hk], by simp⟩
    · have h0 : ∀ i, k ≤ i → Finset.Ioo i n = ∅ := fun i hi => by
        ext j; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega
      rw [h0 k le_rfl, h0 (k + 1) (by omega)]
      exact Or.inl ⟨by simp [hk], rfl⟩

variable {κ : ℕ → PolyKind} {s : ℕ}

theorem ofKinds_kind_of_lt {k : ℕ} (hk : k < n) : (ofKinds n κ s).kind k = κ k := by
  simp [ofKinds, hk]

theorem ofKinds_deg (k : ℕ) :
    (ofKinds n κ s).deg k = s + 1 + #{j ∈ Finset.Ioo k n | κ j = .full} := rfl

/-- **The admissible sequence `ofKinds n κ s` ends in `P_sΛⁿ`** (as `P_{s+1}⁻Λⁿ`,
`polyMinusSpace_top`). [ArnoldLogg2014] -/
theorem ofKinds_space_top : (ofKinds n κ s).space n n = polySpace n s n := by
  change (if n < n then κ n else .trimmed).space n (s + 1 + #{j ∈ Finset.Ioo n n | κ j = .full})
    n = _
  simp only [lt_irrefl, ↓reduceIte, Finset.Ioo_self, Finset.filter_empty, Finset.card_empty,
    add_zero, PolyKind.space_trimmed]
  rw [polyMinusSpace_top (by omega), Nat.add_sub_cancel]

/-- The trimmed sequence `P_r⁻Λ⁰ → P_r⁻Λ¹ → ⋯ → P_r⁻Λⁿ` (`r ≥ 1`): in `ℝ³` Lagrange `P_r`, the
Nédélec edge elements of the first kind ([Nedelec1980]), the Raviart–Thomas–Nédélec face elements
([RaviartThomas1977], [Nedelec1980]) and discontinuous `P_{r-1}`; for `r = 1` the Whitney forms
(`whitneyElement_equivalent_trimmed`). -/
def trimmed (r : ℕ) (hr : 1 ≤ r) : PolySeq where
  kind _ := .trimmed
  deg _ := r
  one_le_deg _ := hr
  transition _ := Or.inl ⟨rfl, rfl⟩

/-- The trimmed sequence is the admissible sequence of trimmed kinds ending in `P_{r-1}Λⁿ`. -/
theorem trimmed_eq_ofKinds {r : ℕ} (hr : 1 ≤ r) :
    trimmed r hr = ofKinds n (fun _ => .trimmed) (r - 1) := by
  ext k
  · simp only [trimmed, ofKinds, ite_self]
  · simp only [trimmed, ofKinds, reduceCtorEq, Finset.filter_false, Finset.card_empty, add_zero]
    omega

/-- **The full sequence** `P_rΛ⁰ → P_{r-1}Λ¹ → ⋯ → P_{r-n}Λⁿ` on `ℝⁿ` (`n ≤ r`), the admissible
sequence of full kinds ending in `P_{r-n}Λⁿ` (`full_space`): in `ℝ³` Lagrange `P_r`, the Nédélec
edge elements of the second kind `P_{r-1}Λ¹` ([Nedelec1986]), the Brezzi–Douglas–Marini face
elements `P_{r-2}Λ²` ([BrezziDouglasMarini1985], [Nedelec1986]) and discontinuous `P_{r-3}`. -/
def full (n r : ℕ) (_hr : n ≤ r) : PolySeq := ofKinds n (fun _ => .full) (r - n)

theorem full_kind {r : ℕ} (hr : n ≤ r) {k : ℕ} (hk : k < n) : (full n r hr).kind k = .full :=
  ofKinds_kind_of_lt hk

theorem full_deg {r : ℕ} (hr : n ≤ r) {k : ℕ} (hk : k < n) : (full n r hr).deg k = r - k := by
  rw [full, ofKinds_deg, Finset.filter_true_of_mem fun _ _ => rfl, Nat.card_Ioo]
  omega

/-- **The spaces of the full sequence**: `P_{r-k}Λᵏ` in every degree `k ≤ n`. [AFW2006], §3;
[ArnoldLogg2014] -/
theorem full_space {r : ℕ} (hr : n ≤ r) {k : ℕ} (hk : k ≤ n) :
    (full n r hr).space n k = polySpace n (r - k) k := by
  rcases hk.lt_or_eq with hk | rfl
  · change ((full n r hr).kind k).space n ((full n r hr).deg k) k = _
    rw [full_kind hr hk, full_deg hr hk, PolyKind.space_full]
  · rw [full, ofKinds_space_top]

/-- **The first row of Tables 5.1 and 6.1** of [QuennevilleBelair2015] (§5.3, §6.3), in `ℝ³`:
`P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ² → P₁⁻Λ³`, i.e. Lagrange `P₁`, the lowest-order Nédélec `H(curl)`
elements of the first kind, the lowest-order Raviart–Thomas elements, and piecewise
constants (the Whitney forms, with moment degrees of freedom). -/
def lowestOrder : PolySeq where
  kind k := if k = 0 then .full else .trimmed
  deg _ := 1
  one_le_deg _ := le_rfl
  transition _ := Or.inl ⟨by simp, rfl⟩

/-- **The second row of Tables 5.1 and 6.1** of [QuennevilleBelair2015] (§5.3, §6.3), in `ℝ³`:
`P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` (with `P₀Λ³ = P₁⁻Λ³`), i.e. Lagrange `P₂`, the second-lowest-order
Nédélec `H(curl)` elements of the first kind, the lowest-order Brezzi–Douglas–Marini elements
`BDM₁`, and piecewise constants. -/
def lagrangeP2 : PolySeq where
  kind k := if k = 0 ∨ k = 2 then .full else .trimmed
  deg k := if k ≤ 1 then 2 else 1
  one_le_deg k := by split_ifs <;> omega
  transition k := by
    rcases k with _ | _ | _ | k
    · exact Or.inl ⟨by simp, rfl⟩
    · exact Or.inr ⟨by simp, rfl⟩
    · exact Or.inl ⟨by simp, rfl⟩
    · exact Or.inl ⟨by simp, by simp⟩

@[simp] theorem lagrangeP2_kind_zero : lagrangeP2.kind 0 = .full := rfl
@[simp] theorem lagrangeP2_kind_one : lagrangeP2.kind 1 = .trimmed := rfl
@[simp] theorem lagrangeP2_kind_two : lagrangeP2.kind 2 = .full := rfl
@[simp] theorem lagrangeP2_kind_three : lagrangeP2.kind 3 = .trimmed := rfl
@[simp] theorem lagrangeP2_deg_zero : lagrangeP2.deg 0 = 2 := rfl
@[simp] theorem lagrangeP2_deg_one : lagrangeP2.deg 1 = 2 := rfl
@[simp] theorem lagrangeP2_deg_two : lagrangeP2.deg 2 = 1 := rfl
@[simp] theorem lagrangeP2_deg_three : lagrangeP2.deg 3 = 1 := rfl

/-- The first row of Tables 5.1/6.1 is the admissible sequence of the trimmed kinds above degree
`0` ending in `P_0Λⁿ`, on every `ℝⁿ`, `n ≥ 1`. -/
theorem lowestOrder_eq_ofKinds (hn : 1 ≤ n) :
    lowestOrder = ofKinds n (fun k => if k = 0 then .full else .trimmed) 0 := by
  ext k
  · simp only [lowestOrder, ofKinds]
    split_ifs <;> first | rfl | omega
  · simp only [lowestOrder, ofKinds, zero_add, left_eq_add, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff, Finset.mem_Ioo]
    intro j hj
    simp [show j ≠ 0 by omega]

/-- The second row of Tables 5.1/6.1 is the admissible sequence of kinds `(full, trimmed, full)`
ending in `P_0Λ³`. -/
theorem lagrangeP2_eq_ofKinds :
    lagrangeP2 = ofKinds 3 (fun k => if k = 0 ∨ k = 2 then .full else .trimmed) 0 := by
  ext k
  · rcases k with _ | _ | _ | k
    · rfl
    · rfl
    · rfl
    · simp [lagrangeP2, ofKinds]
  · rcases k with _ | _ | _ | k
    · decide
    · decide
    · decide
    · simp only [lagrangeP2, ofKinds, Finset.Ioo_eq_empty (show ¬(k + 3 < 3) by omega),
        Finset.filter_empty, Finset.card_empty]
      simp

end PolySeq

/-! ### The shape spaces among the affinely invariant spaces -/

namespace PolyKind

/-- The polynomial forms of the family, `P_rΛᵏ` or `P_r⁻Λᵏ`, in `Koszul.PolyForm`. -/
def form : PolyKind → ℕ → ℕ → Submodule ℝ (Koszul.PolyForm ℝ (Fin n))
  | full, r, k => Koszul.polyForm ℝ (Fin n) r k
  | trimmed, r, k => Koszul.polyFormMinus ℝ (Fin n) r k

theorem space_eq_map_form (κ : PolyKind) (r k : ℕ) :
    κ.space n r k = (κ.form r k).map (evalForm n) := by
  cases κ <;> rfl

/-- The degree `r'` of the `d`-part `dP_{r'+1}Λ^{k-1}` of the family: `r` for `P_rΛᵏ`, `r - 1`
for `P_r⁻Λᵏ`. -/
def dDeg : PolyKind → ℕ → ℕ
  | full, r => r
  | trimmed, r => r - 1

/-- **The shape spaces of the periodic table are spaces `X(r', r - 1, k, n)` of [AFW2006],
Theorem 3.5** (`1 ≤ r`, `1 ≤ k`): `P_rΛᵏ = dP_{r+1}Λ^{k-1} + κP_{r-1}Λ^{k+1}` and
`P_r⁻Λᵏ = dP_rΛ^{k-1} + κP_{r-1}Λ^{k+1}`. -/
theorem form_eq_sup (κ : PolyKind) {r k : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) :
    κ.form (n := n) r k =
      (Koszul.polyForm ℝ (Fin n) (κ.dDeg r + 1) (k - 1)).map (Koszul.extDerivₗ ℝ (Fin n)) ⊔
        (Koszul.polyForm ℝ (Fin n) (r - 1) (k + 1)).map (Koszul.koszulₗ ℝ (Fin n)) := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  cases κ
  · exact (sup_eq_polyForm hk).symm
  · exact (sup_eq_polyFormMinus hk).symm

theorem le_dDeg (κ : PolyKind) (r : ℕ) : r - 1 ≤ κ.dDeg r := by
  cases κ <;> simp [dDeg]

/-- **The shape spaces of the periodic table are affinely invariant** ([AFW2006], Theorem 3.5). -/
theorem isAffineInvariant_form (κ : PolyKind) {r k : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) :
    IsAffineInvariant (κ.form (n := n) r k) := by
  rw [κ.form_eq_sup hr hk]
  exact isAffineInvariant_sup hk (κ.le_dDeg r)

end PolyKind

namespace PolySeq

/-- **The shape spaces of an admissible sequence are affinely invariant** ([AFW2006],
Theorem 3.5) in every degree `k ≥ 1`: the spaces `P_rΛᵏ = X(r, r - 1)` and `P_r⁻Λᵏ = X(r - 1, r - 1)`
(`PolyKind.form_eq_sup`), the first two of the three kinds of affinely invariant spaces of
polynomial `k`-forms, which are all of them for `0 < k < n` ([AFW2006], Theorem 3.6,
`IsAffineInvariant.eq_sup`). -/
theorem isAffineInvariant_form (S : PolySeq) {k : ℕ} (hk : 1 ≤ k) :
    IsAffineInvariant ((S.kind k).form (n := n) (S.deg k) k) :=
  (S.kind k).isAffineInvariant_form (S.one_le_deg k) hk

end PolySeq

/-! ### The classical elements in `ℝ³` and `ℝ²`

The local spaces of the periodic table ([ArnoldLogg2014]; [AFW2006], §3; [AFW2010], §5.1),
specializing `finrank_polySpace`, `finrank_polyMinusSpace`. -/

private theorem two_mul_choose_two (m : ℕ) : 2 * (m + 2).choose 2 = (m + 2) * (m + 1) := by
  have := Nat.add_one_mul_choose_eq (m + 1) 1
  simp only [Nat.choose_one_right] at this
  linarith

private theorem six_mul_choose_three (m : ℕ) :
    6 * (m + 3).choose 3 = (m + 3) * (m + 2) * (m + 1) := by
  have h := Nat.add_one_mul_choose_eq (m + 2) 2
  have h2 := two_mul_choose_two m
  nlinarith

/-- **Lagrange `P_r` on tetrahedra**: `dim P_rΛ⁰(ℝ³) = (r+1)(r+2)(r+3)/6`. [AFW2006], §3 -/
theorem finrank_polySpace_three_zero (r : ℕ) :
    6 * Module.finrank ℝ (polySpace 3 r 0) = (r + 1) * (r + 2) * (r + 3) := by
  rw [finrank_polySpace, add_zero, Nat.choose_zero_right, mul_one,
    Nat.choose_symm_of_eq_add (show r + 3 = r + 3 by rfl), six_mul_choose_three]
  ring

/-- **Nédélec edge elements of the second kind** ([Nedelec1986]):
`dim P_rΛ¹(ℝ³) = (r+1)(r+2)(r+3)/2`. -/
theorem finrank_polySpace_three_one (r : ℕ) :
    2 * Module.finrank ℝ (polySpace 3 r 1) = (r + 1) * (r + 2) * (r + 3) := by
  rw [finrank_polySpace, Nat.choose_one_right,
    Nat.choose_symm_of_eq_add (show r + 3 = r + 1 + 2 by omega), ← mul_assoc,
    show r + 1 + 2 = r + 1 + 2 from rfl, two_mul_choose_two (r + 1)]
  ring

/-- **Brezzi–Douglas–Marini face elements** ([BrezziDouglasMarini1985], [Nedelec1986]):
`dim P_rΛ²(ℝ³) = (r+1)(r+2)(r+3)/2`. -/
theorem finrank_polySpace_three_two (r : ℕ) :
    2 * Module.finrank ℝ (polySpace 3 r 2) = (r + 1) * (r + 2) * (r + 3) := by
  rw [finrank_polySpace, Nat.choose_symm_of_eq_add (show r + 3 = r + 2 + 1 by omega),
    Nat.choose_one_right, mul_left_comm, two_mul_choose_two r]
  ring

/-- **Discontinuous `P_r` on tetrahedra**: `dim P_rΛ³(ℝ³) = (r+1)(r+2)(r+3)/6`. [AFW2006], §3 -/
theorem finrank_polySpace_three_three (r : ℕ) :
    6 * Module.finrank ℝ (polySpace 3 r 3) = (r + 1) * (r + 2) * (r + 3) := by
  rw [finrank_polySpace, Nat.choose_self, one_mul, six_mul_choose_three]
  ring

/-- **Nédélec edge elements of the first kind** ([Nedelec1980]):
`dim P_r⁻Λ¹(ℝ³) = r(r+2)(r+3)/2`. -/
theorem finrank_polyMinusSpace_three_one {r : ℕ} (hr : 1 ≤ r) :
    2 * Module.finrank ℝ (polyMinusSpace 3 r 1) = r * (r + 2) * (r + 3) := by
  rw [finrank_polyMinusSpace 3 hr, Nat.add_sub_cancel, Nat.choose_one_right,
    Nat.choose_symm_of_eq_add (show r + 3 = r + 1 + 2 by omega), ← mul_assoc,
    two_mul_choose_two (r + 1)]
  ring

/-- **Raviart–Thomas–Nédélec face elements** ([RaviartThomas1977], [Nedelec1980]):
`dim P_r⁻Λ²(ℝ³) = r(r+1)(r+3)/2`. -/
theorem finrank_polyMinusSpace_three_two {r : ℕ} (hr : 1 ≤ r) :
    2 * Module.finrank ℝ (polyMinusSpace 3 r 2) = r * (r + 1) * (r + 3) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
  rw [finrank_polyMinusSpace 3 hr, Nat.choose_symm_of_eq_add (show t + 1 + 3 = t + 1 + 2 + 1 by
    omega), Nat.choose_one_right, show t + 1 + 2 - 1 = t + 2 by omega, mul_left_comm,
    two_mul_choose_two t]
  ring

/-- **Lagrange `P_r` on triangles**: `dim P_rΛ⁰(ℝ²) = (r+1)(r+2)/2`. [AFW2006], §3 -/
theorem finrank_polySpace_two_zero (r : ℕ) :
    2 * Module.finrank ℝ (polySpace 2 r 0) = (r + 1) * (r + 2) := by
  rw [finrank_polySpace, add_zero, Nat.choose_zero_right, mul_one,
    Nat.choose_symm_of_eq_add (show r + 2 = r + 2 by rfl), two_mul_choose_two]
  ring

/-- **Brezzi–Douglas–Marini elements on triangles** ([BrezziDouglasMarini1985]):
`dim P_rΛ¹(ℝ²) = (r+1)(r+2)`. -/
theorem finrank_polySpace_two_one (r : ℕ) :
    Module.finrank ℝ (polySpace 2 r 1) = (r + 1) * (r + 2) := by
  rw [finrank_polySpace, Nat.choose_symm_of_eq_add (show r + 2 = r + 1 + 1 by omega),
    Nat.choose_one_right, Nat.choose_one_right]
  ring

/-- **Discontinuous `P_r` on triangles**: `dim P_rΛ²(ℝ²) = (r+1)(r+2)/2`. [AFW2006], §3 -/
theorem finrank_polySpace_two_two (r : ℕ) :
    2 * Module.finrank ℝ (polySpace 2 r 2) = (r + 1) * (r + 2) := by
  rw [finrank_polySpace, Nat.choose_self, one_mul, two_mul_choose_two]
  ring

/-- **Raviart–Thomas elements on triangles** ([RaviartThomas1977]; the rotated Nédélec edge
elements of the first kind): `dim P_r⁻Λ¹(ℝ²) = r(r+2)`. -/
theorem finrank_polyMinusSpace_two_one {r : ℕ} (hr : 1 ≤ r) :
    Module.finrank ℝ (polyMinusSpace 2 r 1) = r * (r + 2) := by
  rw [finrank_polyMinusSpace 2 hr, Nat.add_sub_cancel, Nat.choose_one_right,
    Nat.choose_symm_of_eq_add (show r + 2 = r + 1 + 1 by omega), Nat.choose_one_right]
  ring

namespace PolySeq

/-! ### The Whitney forms are the trimmed sequence of degree one -/

/-- **`P₁⁻Λᵏ(ℝⁿ)` is the space of trimmed linear forms** `x ↦ α + ι_x β` ([AFW2006], §3.3). -/
theorem _root_.Feec.FiniteElement.polyMinusSpace_one_eq_p1MinusForms (k : ℕ) :
    polyMinusSpace n 1 k = p1MinusForms n k := by
  rw [polyMinusSpace, ← whitneySpace_refVertex_eq_map_polyFormMinus]
  exact le_antisymm (whitneySpace_le_p1MinusForms _ k) (p1MinusForms_le_whitneySpace_refVertex k)

/-- A test form of `P₁⁻Λᵏ` on a `k`-face is constant, of degree `0`. -/
theorem _root_.Feec.FiniteElement.eq_single_of_mem_testSpaceMinus_one {k : ℕ} {η : FormField k}
    (hη : η ∈ testSpaceMinus 1 k k) : η = fun _ => Pi.single ∅ (η 0 ∅) := by
  rw [testSpaceMinus_eq ⟨le_rfl, by omega⟩, show 1 + k - k - 1 = 0 by omega, Nat.sub_self] at hη
  obtain ⟨Ω, ⟨hdeg, htot⟩, rfl⟩ := hη
  funext x s
  by_cases hs : s = ∅
  · subst hs
    rw [Pi.single_eq_same, evalForm_apply, evalForm_apply,
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 (htot ∅))]
    simp
  · rw [Pi.single_eq_of_ne hs, evalForm_apply, hdeg s (by simpa using hs), map_zero]

/-- **Moments against a constant test form are multiples of the face integral**: for the test
forms of `P₁⁻Λᵏ` on a `k`-face, `∫_{T̂_k} F_q^* ω_k ∧ η = η₀ ∫_q ω`. -/
theorem _root_.Feec.FiniteElement.degMoment_eq_mul_simplexIntegral {k : ℕ}
    (q : Fin (k + 1) → Fin n → ℝ) {η : FormField k} (hη : η ∈ testSpaceMinus 1 k k)
    (hc : Continuous η) (ω : contForms n) :
    degMoment k q η hc ω = η 0 ∅ * simplexIntegral q ω := by
  have hw : ∀ α : Finset (Fin k) → ℝ, wedgeForm α (Pi.single ∅ (η 0 ∅)) = η 0 ∅ • α := fun α => by
    rw [show (Pi.single ∅ (η 0 ∅) : Finset (Fin k) → ℝ) = η 0 ∅ • Pi.single ∅ 1 by
      rw [← Pi.single_smul, smul_eq_mul, mul_one], wedgeForm_smul_right, wedgeForm_one_right]
  rw [degMoment_apply, vertexMoment_eq_integral, simplexIntegral, ← integral_const_mul]
  congr 1
  funext x
  rw [eq_single_of_mem_testSpaceMinus_one hη]
  simp only [wedgeField, hw, Pi.smul_apply, smul_eq_mul, affinePullback_apply,
    pullback_degField_univ, Pi.single_eq_same]

/-- The degrees of freedom of `P₁⁻Λᵏ` live on the `k`-faces. -/
theorem card_eq_of_trimmed_one_dofIdx {g : Finset (Fin n → ℝ)} {k : ℕ}
    (i : (trimmed 1 le_rfl).DofIdx g k) : #g = k + 1 := by
  have h1 := card_pos.2 i.2
  by_contra h
  have h0 : Module.finrank ℝ ((trimmed 1 le_rfl).test k (#g - 1)) = 0 := by
    change Module.finrank ℝ (testSpaceMinus 1 k (#g - 1)) = 0
    rw [testSpaceMinus_eq_bot (show ¬(k ≤ #g - 1 ∧ #g - 1 < 1 + k) by omega), finrank_bot]
  have := i.1.isLt
  omega

theorem degMoment_eq_smul_whitneyFaceDof {g : Finset (Fin n → ℝ)} {k m : ℕ} (hm : m = k)
    (hg : #g = k + 1) {η : FormField m} (hη : η ∈ testSpaceMinus 1 k m) (hη0 : η ≠ 0)
    (hc : Continuous η) :
    ∃ c : ℝ, c ≠ 0 ∧ degMoment k (lexEnum g m) η hc = c • whitneyFaceDof g k := by
  subst hm
  have hc0 : η 0 ∅ ≠ 0 := fun h => hη0 (by
    rw [eq_single_of_mem_testSpaceMinus_one hη, h]; funext x s; simp)
  obtain ⟨ε, hε, hεeq⟩ := exists_sign_simplexIntegral_eq (lexEnum_injective hg)
    (injective_faceEnum hg) (by rw [range_lexEnum hg, range_faceEnum hg])
  refine ⟨η 0 ∅ * ε, mul_ne_zero hc0 (by rcases hε with rfl | rfl <;> norm_num),
    LinearMap.ext fun ω => ?_⟩
  rw [degMoment_eq_mul_simplexIntegral _ hη, LinearMap.smul_apply, whitneyFaceDof_apply, hεeq,
    smul_eq_mul, mul_assoc]

/-- **The degrees of freedom of `P₁⁻Λᵏ` are the face integrals**, up to nonzero factors.
[AFW2006], §4 -/
theorem trimmed_one_dof_eq {g : Finset (Fin n → ℝ)} {k : ℕ}
    (i : (trimmed 1 le_rfl).DofIdx g k) :
    ∃ c : ℝ, c ≠ 0 ∧ (trimmed 1 le_rfl).dof g k i = c • whitneyFaceDof g k := by
  have hg := card_eq_of_trimmed_one_dofIdx i
  exact degMoment_eq_smul_whitneyFaceDof (by omega) hg ((trimmed 1 le_rfl).testBasis k _ i.1).2
    (fun h => ((trimmed 1 le_rfl).testBasis k _).ne_zero i.1 (Subtype.ext h)) _

end PolySeq

/-- **The Whitney element is the trimmed element `P₁⁻Λ` of degree one**: the same local spaces
(`whitneySpace_eq_p1MinusForms`, `polyMinusSpace_one_eq_p1MinusForms`) and, on every face, the
face integral and the moment degrees of freedom are nonzero multiples of each other.
[Whitney1957], Ch. IV, §27; [AFW2006], §3–4 -/
theorem whitneyElement_equivalent_trimmed :
    (whitneyElement n).Equivalent (polyElement n (PolySeq.trimmed 1 le_rfl)) where
  space_eq T k :=
    (whitneySpace_eq_p1MinusForms T k).trans (polyMinusSpace_one_eq_p1MinusForms k).symm
  span_dof_eq g k := by
    by_cases hg : #g = k + 1
    · have : Nonempty ((whitneyElement n).DofIdx g k) := ⟨⟨(), hg⟩⟩
      have hW : Set.range ((whitneyElement n).dof g k) = {whitneyFaceDof g k} := Set.range_const
      have hpos : 0 < Module.finrank ℝ ((PolySeq.trimmed 1 le_rfl).test k (#g - 1)) := by
        change 0 < Module.finrank ℝ (testSpaceMinus 1 k (#g - 1))
        rw [finrank_testSpaceMinus le_rfl]
        simp only [show k ≤ #g - 1 ∧ #g - 1 < 1 + k by omega, and_self, ↓reduceIte,
          show #g - 1 - k = 0 by omega]
        simp
      set i₀ : (PolySeq.trimmed 1 le_rfl).DofIdx g k := ⟨⟨0, hpos⟩, card_pos.1 (by omega)⟩
      obtain ⟨c, hc, h₀⟩ := PolySeq.trimmed_one_dof_eq i₀
      rw [hW]
      refine le_antisymm ?_ (Submodule.span_le.2 ?_)
      · rw [Submodule.span_singleton_le_iff_mem, show whitneyFaceDof g k =
          c⁻¹ • (PolySeq.trimmed 1 le_rfl).dof g k i₀ by rw [h₀, smul_smul, inv_mul_cancel₀ hc,
            one_smul]]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i₀, rfl⟩)
      · rintro _ ⟨i, rfl⟩
        obtain ⟨c, -, h⟩ := PolySeq.trimmed_one_dof_eq i
        change (PolySeq.trimmed 1 le_rfl).dof g k i ∈ _
        rw [h]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · have : IsEmpty ((whitneyElement n).DofIdx g k) := ⟨fun i => hg i.2⟩
      have : IsEmpty ((polyElement n (PolySeq.trimmed 1 le_rfl)).DofIdx g k) :=
        ⟨fun i => hg (PolySeq.card_eq_of_trimmed_one_dofIdx i)⟩
      rw [Set.range_eq_empty, Set.range_eq_empty]

namespace PolySeq

/-! ### Counting the degrees of freedom on a set of faces -/

variable (S : PolySeq)

/-- The degrees of freedom of a set `F` of faces (of at most `n + 1` vertices):
`Σ_{m ≤ n} #{m-faces in F} · dim(test forms on m-faces)`. -/
theorem card_sigma_dofIdx_eq_sum (F : Finset (Finset (Fin n → ℝ)))
    (hF : ∀ g ∈ F, #g ≤ n + 1) (k : ℕ) :
    Fintype.card (Σ g : F, S.DofIdx (g : Finset (Fin n → ℝ)) k) =
      ∑ m ∈ range (n + 1), #(F.filter fun g => #g = m + 1) *
        Module.finrank ℝ (S.test k m) := by
  classical
  rw [Fintype.card_sigma]
  simp only [card_dofIdx]
  rw [Finset.sum_coe_sort F (fun g => if g.Nonempty then
    Module.finrank ℝ (S.test k (#g - 1)) else 0), ← sum_filter]
  rw [← sum_fiberwise_of_maps_to (s := F.filter fun g => g.Nonempty) (t := range (n + 1))
    (g := fun g => #g - 1) (fun g hg => by
      have h1 := hF g (mem_filter.1 hg).1
      have h2 := card_pos.2 (mem_filter.1 hg).2
      simp only [Finset.mem_range]; omega)]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_congr rfl fun g hg => by rw [(mem_filter.1 hg).2], sum_const, smul_eq_mul,
    filter_filter]
  congr 2
  refine filter_congr fun g _ => ?_
  rw [← card_pos]
  omega

end PolySeq

/-! ### The global spaces on a mesh -/

theorem card_le_of_mem_meshFaces (M : SimplicialMesh n) {g : Finset (Fin n → ℝ)}
    (hg : g ∈ LocalElement.meshFaces M) : #g ≤ n + 1 := by
  obtain ⟨T, -, hgT⟩ := (LocalElement.mem_meshFaces M).1 hg
  exact (Finset.card_le_card hgT).trans (card_vertexSet T).le

namespace PolySeq

variable (S : PolySeq) (M : SimplicialMesh n)

theorem card_globalDofIdx (k : ℕ) :
    Fintype.card ((polyElement n S).GlobalDofIdx M k) =
      ∑ m ∈ range (n + 1), (M.faces m).ncard * Module.finrank ℝ (S.test k m) := by
  classical
  refine (S.card_sigma_dofIdx_eq_sum _ (fun g hg => card_le_of_mem_meshFaces M hg) k).trans ?_
  refine sum_congr rfl fun m _ => ?_
  rw [← coe_filter_meshFaces M m, Set.ncard_coe_finset]

/-- **`dim Λ_hᵏ(M) = Σ_{m ≤ n} #{m-faces of M} · dim(test forms on m-faces)`** for the
global `P_{r_k}Λᵏ` (resp. `P_{r_k}⁻Λᵏ`) space ([AFW2006], Thms 4.9, 4.13 and §5.1). -/
theorem finrank_globalSpace (k : ℕ) :
    Module.finrank ℝ ((polyElement n S).globalSpace M k) =
      ∑ m ∈ range (n + 1), (M.faces m).ncard * Module.finrank ℝ (S.test k m) := by
  rw [LocalElement.finrank_globalSpace, card_globalDofIdx]

/-- The faces of `M` not contained in a boundary facet. -/
def interiorFaces (M : SimplicialMesh n) : Finset (Finset (Fin n → ℝ)) := by
  classical
  exact (LocalElement.meshFaces M).filter fun g => ¬ ∃ F, M.IsBoundaryFacet F ∧ g ⊆ F

theorem mem_interiorFaces {g : Finset (Fin n → ℝ)} :
    g ∈ interiorFaces M ↔
      g ∈ LocalElement.meshFaces M ∧ ¬ ∃ F, M.IsBoundaryFacet F ∧ g ⊆ F := by
  classical
  unfold interiorFaces; exact mem_filter

theorem card_interiorDofIdx (k : ℕ) :
    Fintype.card ((polyElement n S).InteriorDofIdx M k) =
      ∑ m ∈ range (n + 1), {g | g ∈ M.faces m ∧ ¬ ∃ F, M.IsBoundaryFacet F ∧ g ⊆ F}.ncard *
        Module.finrank ℝ (S.test k m) := by
  classical
  have e : (polyElement n S).InteriorDofIdx M k ≃
      Σ g : interiorFaces M, S.DofIdx (g : Finset (Fin n → ℝ)) k :=
    { toFun := fun p => ⟨⟨p.1.1.1, (mem_interiorFaces M).2 ⟨p.1.1.2, p.2⟩⟩, p.1.2⟩
      invFun := fun q => ⟨⟨⟨q.1.1, ((mem_interiorFaces M).1 q.1.2).1⟩, q.2⟩,
        ((mem_interiorFaces M).1 q.1.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, S.card_sigma_dofIdx_eq_sum _ (fun g hg => card_le_of_mem_meshFaces M
    ((mem_interiorFaces M).1 hg).1) k]
  refine sum_congr rfl fun m _ => ?_
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext g
  simp only [coe_filter, mem_interiorFaces, LocalElement.mem_meshFaces,
    SimplicialMesh.faces, Set.mem_ofPred_eq]
  tauto

/-- **`dim Λ̊_hᵏ(M) = Σ_{m ≤ n} #{m-faces not in a boundary facet} · dim(test forms)`** for the
global spaces with vanishing boundary degrees of freedom. -/
theorem finrank_globalSpace₀ (k : ℕ) :
    Module.finrank ℝ ((polyElement n S).globalSpace₀ M k) =
      ∑ m ∈ range (n + 1), {g | g ∈ M.faces m ∧ ¬ ∃ F, M.IsBoundaryFacet F ∧ g ⊆ F}.ncard *
        Module.finrank ℝ (S.test k m) := by
  rw [LocalElement.finrank_globalSpace₀, card_interiorDofIdx]

theorem finrank_V₀ (hΩ : IsOpen M.domain) (k : ℕ) :
    Module.finrank ℝ ((polyElement n S).V₀ M k) =
      ∑ m ∈ range (n + 1), {g | g ∈ M.faces m ∧ ¬ ∃ F, M.IsBoundaryFacet F ∧ g ⊆ F}.ncard *
        Module.finrank ℝ (S.test k m) := by
  rw [LocalElement.finrank_V₀ _ M hΩ, card_interiorDofIdx]

/-- `dim` of the test forms, in closed form ([AFW2006], Thms 4.9, 4.13). -/
theorem finrank_test (k m : ℕ) :
    Module.finrank ℝ (S.test k m) = (S.kind k).testDim (S.deg k) k m :=
  PolyKind.finrank_test _ (S.one_le_deg k) k m

/-- **The global space is the space of piecewise `P_{r_k}Λᵏ` (resp. `P_{r_k}⁻Λᵏ`) forms with
continuous tangential traces** (for meshes with facet-connected face stars; [AFW2006], §5.1,
[AFW2010], §5.2). -/
theorem mem_globalSpace_iff (hM : LocalElement.FacetConnected M) {k : ℕ}
    {u : (polyElement n S).Piecewise M k} :
    u ∈ (polyElement n S).globalSpace M k ↔ ∀ F ∈ M.facets, ∀ T T' : M.simplices,
      F ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) →
        F ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) →
          ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)),
            TangentialTraceEq F k ((u T : FormField n) x) ((u T' : FormField n) x) :=
  (polyElement n S).mem_globalSpace_iff M hM (inferInstanceAs (IsEmpty (S.DofIdx ∅ k)))

/-! ### The finite element subcomplexes -/

/-- **The finite element subcomplex** `Vₕ ⊆ HΛ(Ω)` of the admissible sequence `S` on a conforming
mesh of an open `Ω ⊆ ℝⁿ`. -/
def subcomplex [NeZero n] (hΩ : IsOpen M.domain) :
    ((deRham ℝ n).maximalComplex hΩ).Subcomplex :=
  (polyElement n S).subcomplex M hΩ

/-- **The finite element subcomplex with vanishing boundary degrees of freedom**
`V̊ₕ ⊆ H̊Λ(Ω)`, for `Ω` strictly star-shaped with respect to `x₀` (e.g. convex). -/
def subcomplexMin [NeZero n] (hΩ : IsOpen M.domain) (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain) :
    ((deRham ℝ n).minimalComplex hΩ).Subcomplex :=
  (polyElement n S).subcomplexMin M hΩ x₀ hstar

/-- **The finite element subcomplex with vanishing boundary degrees of freedom on the level-`N`
Freudenthal mesh of a cube**, a subcomplex of `H̊Λ` of the cube. -/
def freudenthalSubcomplexMin [NeZero n] (b : Fin n → ℝ) (s : ℝ) (hs : 0 < s) (N : ℕ)
    [NeZero N] :
    ((deRham ℝ n).minimalComplex (isOpen_freudenthalMesh_domain b s hs N)).Subcomplex :=
  S.subcomplexMin (freudenthalMesh b s hs N) (isOpen_freudenthalMesh_domain b s hs N) _
    (add_smul_sub_mem_of_convex (isOpen_freudenthalMesh_domain b s hs N)
      (convex_freudenthalMesh_domain b s hs N) (center_mem_freudenthalMesh_domain b s hs N))

end PolySeq

/-- **The Whitney complex is the trimmed complex of degree one**, `P₁⁻Λ⁰ → ⋯ → P₁⁻Λⁿ`, on every
conforming mesh: `whitneySubcomplex = (PolySeq.trimmed 1).subcomplex`. [AFW2006], §3–4 -/
theorem whitneySubcomplex_eq_trimmed [NeZero n] (M : SimplicialMesh n) (hΩ : IsOpen M.domain) :
    whitneySubcomplex M hΩ = (PolySeq.trimmed 1 le_rfl).subcomplex M hΩ :=
  whitneyElement_equivalent_trimmed.subcomplex_eq M hΩ

/-- **The Whitney complex with vanishing boundary degrees of freedom is the trimmed one of degree
one**, on every conforming mesh of a strictly star-shaped domain. -/
theorem whitneySubcomplexMin_eq_trimmed [NeZero n] (M : SimplicialMesh n) (hΩ : IsOpen M.domain)
    (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain) :
    whitneySubcomplexMin M hΩ x₀ hstar = (PolySeq.trimmed 1 le_rfl).subcomplexMin M hΩ x₀ hstar :=
  whitneyElement_equivalent_trimmed.subcomplexMin_eq M hΩ x₀ hstar

/-! ### Nonzero spaces with vanishing boundary degrees of freedom -/

namespace LocalElement

variable (E : LocalElement n) (M : SimplicialMesh n)

/-- A face whose convex hull meets the (open) domain carries **interior degrees of freedom**: it
is not contained in a boundary facet (boundary facets lie in `∂Ω`). -/
theorem not_isBoundaryDof_of_mem_convexHull (hΩ : IsOpen M.domain) {k : ℕ}
    (p : E.GlobalDofIdx M k) {x : Fin n → ℝ}
    (hx : x ∈ convexHull ℝ ((p.1 : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)))
    (hxΩ : x ∈ M.domain) : ¬ E.IsBoundaryDof M p := by
  rintro ⟨F, hF, hpF⟩
  have h := hF.2.2 (convexHull_mono (Finset.coe_subset.2 hpF) hx)
  exact h.2 (interior_mono subset_closure (hΩ.interior_eq.symm ▸ hxΩ))

/-- **`V̊ₕᵏ ≠ 0`** as soon as some face of `M` whose convex hull meets `Ω` carries a degree of
freedom of degree `k`. -/
theorem finrank_V₀_pos (hΩ : IsOpen M.domain) {k : ℕ} {g : Finset (Fin n → ℝ)}
    (hg : g ∈ meshFaces M) (i : E.DofIdx g k) {x : Fin n → ℝ}
    (hx : x ∈ convexHull ℝ (g : Set (Fin n → ℝ))) (hxΩ : x ∈ M.domain) :
    0 < Module.finrank ℝ (E.V₀ M k) := by
  rw [E.finrank_V₀ M hΩ k]
  exact Fintype.card_pos_iff.2
    ⟨⟨⟨⟨g, hg⟩, i⟩, E.not_isBoundaryDof_of_mem_convexHull M hΩ ⟨⟨g, hg⟩, i⟩ hx hxΩ⟩⟩

end LocalElement

/-- A `(d+1)`-subset of the vertices `{0, …, n}` containing `0` and `n`. -/
theorem exists_finset_zero_last_mem {d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n) :
    ∃ f : Finset (Fin (n + 1)), 0 ∈ f ∧ Fin.last n ∈ f ∧ #f = d + 1 := by
  classical
  have hne : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  set u := Finset.univ \ {0, Fin.last n}
  have hu : #u = n - 1 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, card_pair hne]
    omega
  obtain ⟨t, htu, htc⟩ := exists_subset_card_eq (show d - 1 ≤ #u by omega)
  have h0t : (0 : Fin (n + 1)) ∉ t := fun h => by
    have := htu h; simp [u] at this
  have hlt : Fin.last n ∉ t := fun h => by
    have := htu h; simp [u] at this
  refine ⟨insert 0 (insert (Fin.last n) t), mem_insert_self _ _,
    mem_insert_of_mem (mem_insert_self _ _), ?_⟩
  rw [card_insert_of_notMem (by simp [hne, h0t]), card_insert_of_notMem hlt, htc]
  omega

/-- **Faces of the Freudenthal mesh through the interior**: for `1 ≤ d ≤ n`, the level-`N`
Freudenthal mesh of the box `∏ (bᵢ, bᵢ + s)` has a `d`-face whose convex hull meets the open
box (a face of the simplex `b + (s/N) K_id` containing the diagonal from `b` to
`b + (s/N)(1, …, 1)`). -/
theorem exists_meshFace_freudenthalMesh {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s) {N : ℕ} [NeZero N]
    {d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n) :
    ∃ g ∈ LocalElement.meshFaces (freudenthalMesh b s hs N), #g = d + 1 ∧
      ∃ x ∈ convexHull ℝ (g : Set (Fin n → ℝ)), x ∈ (freudenthalMesh b s hs N).domain := by
  classical
  obtain ⟨f, hf0, hfl, hfc⟩ := exists_finset_zero_last_mem hd1 hdn
  set T₀ := mapEquiv (boxMap b (s / N) (freudenthalScale_ne_zero hs N))
    (freudenthalSimplex (finLattice (0 : Fin n → Fin N)) 1)
  have hT₀ : T₀ ∈ (freudenthalMesh b s hs N).simplices :=
    mem_freudenthalMesh_simplices.2 ⟨0, 1, rfl⟩
  have hpts : ∀ j, T₀.points j = b + (s / N) • kuhnVertex 1 j := fun j => by
    have : latticePoint (finLattice (0 : Fin n → Fin N)) = 0 := by
      funext i; simp [finLattice]
    simp [T₀, this]
  have hN : (1 : ℝ) ≤ N := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hh : 0 < s / N := div_pos hs (by linarith)
  have hhs : s / N ≤ s := div_le_self hs.le hN
  set g := f.image T₀.points
  refine ⟨g, (LocalElement.mem_meshFaces _).2 ⟨T₀, hT₀, fun x hx => ?_⟩, ?_, ?_⟩
  · obtain ⟨j, -, rfl⟩ := mem_image.1 hx
    exact points_mem_vertexSet T₀ j
  · rw [card_image_of_injective _ T₀.independent.injective, hfc]
  · refine ⟨(1 / 2 : ℝ) • T₀.points 0 + (1 / 2 : ℝ) • T₀.points (Fin.last n),
      convex_convexHull ℝ _ (subset_convexHull ℝ _ (mem_coe.2 (mem_image_of_mem _ hf0)))
        (subset_convexHull ℝ _ (mem_coe.2 (mem_image_of_mem _ hfl))) (by norm_num) (by norm_num)
        (by norm_num), ?_⟩
    rw [freudenthalMesh_domain]
    intro i _
    simp only [hpts, kuhnVertex_zero, kuhnVertex_last, smul_zero, add_zero, Pi.add_apply,
      Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, Set.mem_Ioo]
    constructor <;> nlinarith

namespace PolySeq

variable (S : PolySeq)

/-- **The interior spaces of every admissible sequence are nonzero** on every Freudenthal mesh of a
box, in degree `k` as soon as some `d`-face, `1 ≤ d ≤ n`, carries degrees of freedom of degree
`k`. -/
theorem finrank_V₀_freudenthalMesh_pos [NeZero n] {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s) {N : ℕ}
    [NeZero N] {k d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n)
    (hdim : 0 < Module.finrank ℝ (S.test k d)) :
    0 < Module.finrank ℝ ((polyElement n S).V₀ (freudenthalMesh b s hs N) k) := by
  obtain ⟨g, hg, hgc, x, hx, hxΩ⟩ := exists_meshFace_freudenthalMesh (b := b) hs (N := N) hd1 hdn
  have hgd : #g - 1 = d := by omega
  have hne : g.Nonempty := card_pos.1 (by omega)
  have hdim' : 0 < Module.finrank ℝ (S.test k (#g - 1)) := by rw [hgd]; exact hdim
  exact (polyElement n S).finrank_V₀_pos _ (isOpen_freudenthalMesh_domain b s hs N) hg
    (⟨⟨0, hdim'⟩, hne⟩ : S.DofIdx g k) hx hxΩ

theorem _root_.Feec.FiniteElement.PolyKind.testDim_self_pos (κ : PolyKind) {r : ℕ} (hr : 1 ≤ r)
    (k : ℕ) : 0 < κ.testDim r k k := by
  cases κ <;>
  · simp only [PolyKind.testDim, le_refl, true_and, show k < r + k by omega, ↓reduceIte,
      Nat.sub_self, Nat.choose_zero_right, mul_one]
    exact Nat.choose_pos (by omega)

/-- **`V̊ₕᵏ ≠ 0` for `1 ≤ k ≤ n`** on every Freudenthal mesh of a box, for every admissible
sequence (the `k`-faces through the interior carry degrees of freedom). -/
theorem finrank_V₀_freudenthalMesh_pos_of_one_le [NeZero n] {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s)
    {N : ℕ} [NeZero N] {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    0 < Module.finrank ℝ ((polyElement n S).V₀ (freudenthalMesh b s hs N) k) :=
  S.finrank_V₀_freudenthalMesh_pos hs hk1 hkn
    (by rw [finrank_test]; exact PolyKind.testDim_self_pos _ (S.one_le_deg k) k)

/-- **`V̊ₕ⁰ ≠ 0` for polynomial degree `r₀ ≥ 2`** on every Freudenthal mesh of a box (even the
coarsest one, without interior vertices: the edge through the interior carries a degree of
freedom). -/
theorem finrank_V₀_freudenthalMesh_pos_zero [NeZero n] {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s)
    {N : ℕ} [NeZero N] (h2 : 2 ≤ S.deg 0) :
    0 < Module.finrank ℝ ((polyElement n S).V₀ (freudenthalMesh b s hs N) 0) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  refine S.finrank_V₀_freudenthalMesh_pos hs le_rfl hn ?_
  rw [finrank_test]
  cases h : S.kind 0 <;>
  · simp only [PolyKind.testDim, zero_le, true_and, show 1 < S.deg 0 + 0 by omega, ↓reduceIte,
      Nat.sub_zero]
    refine Nat.mul_pos (Nat.choose_pos (by omega)) ?_
    rw [Nat.choose_one_right]
    omega

/-- **The interior spaces of the second row of Tables 5.1/6.1 are nonzero**: on the
level-`(N+1)` Freudenthal mesh of `(0, ½)³`, the spaces `P₂Λ⁰`, `P₂⁻Λ¹`, `P₁Λ²`, `P₀Λ³` with
vanishing boundary degrees of freedom are nonzero, for every `N`. (These are the boundary
conditions of Ch. 5, imposed in every degree; for the Ch. 6 pattern `V̊ₕ⁰, V̊ₕ¹, Vₕ²` see
`PolySeq.lagrangeP2_VPartial_bcFacets_ne_bot` in `Feec.FiniteElement.PolyElementMixed`.) -/
theorem lagrangeP2_V₀_ne_bot (N k : ℕ) (hk : k ≤ 3) :
    (polyElement 3 lagrangeP2).V₀ (freudenthalMesh 0 (1 / 2) (by norm_num) (N + 1)) k ≠ ⊥ := by
  intro h
  have hpos : 0 < Module.finrank ℝ
      ((polyElement 3 lagrangeP2).V₀ (freudenthalMesh 0 (1 / 2) (by norm_num) (N + 1)) k) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exact lagrangeP2.finrank_V₀_freudenthalMesh_pos_zero _ (by simp)
    · exact lagrangeP2.finrank_V₀_freudenthalMesh_pos_of_one_le _ hk1 hk
  rw [h, finrank_bot] at hpos
  exact lt_irrefl 0 hpos

end PolySeq

/-- **The interior Whitney spaces are nonzero in the degrees `1 ≤ k ≤ n`** on every Freudenthal
mesh of a box: the `k`-faces through the interior are not contained in boundary facets. (For
`k = 0`, `V̊ₕ⁰ ≠ 0` needs an interior vertex, i.e. level `N ≥ 2`.) -/
theorem finrank_whitney_V₀_freudenthalMesh_pos [NeZero n] {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s)
    {N : ℕ} [NeZero N] {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    0 < Module.finrank ℝ ((whitneyElement n).V₀ (freudenthalMesh b s hs N) k) := by
  obtain ⟨g, hg, hgc, x, hx, hxΩ⟩ := exists_meshFace_freudenthalMesh (b := b) hs (N := N) hk1 hkn
  exact (whitneyElement n).finrank_V₀_pos _ (isOpen_freudenthalMesh_domain b s hs N) hg
    (⟨(), hgc⟩ : WhitneyDofIdx g k) hx hxΩ

/-- **An interior vertex of the Freudenthal mesh**: for `N ≥ 2`, the lattice point
`b + (s/N)(1, …, 1)` (the first vertex of `b + (s/N)((1, …, 1) + K_id)`) is a vertex of the
level-`N` Freudenthal mesh of `∏ (bᵢ, bᵢ + s)` lying in the open box. -/
theorem exists_vertex_freudenthalMesh {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s) {N : ℕ} [NeZero N]
    (hN : 2 ≤ N) :
    ∃ g ∈ LocalElement.meshFaces (freudenthalMesh b s hs N), #g = 0 + 1 ∧
      ∃ x ∈ convexHull ℝ (g : Set (Fin n → ℝ)), x ∈ (freudenthalMesh b s hs N).domain := by
  classical
  set m : Fin n → Fin N := fun _ => ⟨1, by omega⟩
  set T₁ := mapEquiv (boxMap b (s / N) (freudenthalScale_ne_zero hs N))
    (freudenthalSimplex (finLattice m) 1)
  have hT₁ : T₁ ∈ (freudenthalMesh b s hs N).simplices :=
    mem_freudenthalMesh_simplices.2 ⟨m, 1, rfl⟩
  have hpt : T₁.points 0 = b + (s / N) • (1 : Fin n → ℝ) := by
    have : latticePoint (finLattice m) = 1 := by
      funext i; simp [finLattice, m]
    simp [T₁, this]
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hh : 0 < s / N := div_pos hs (by linarith)
  have hhs : s / N < s := div_lt_self hs (by linarith)
  refine ⟨{T₁.points 0}, (LocalElement.mem_meshFaces _).2 ⟨T₁, hT₁, fun x hx => ?_⟩,
    card_singleton _, T₁.points 0, subset_convexHull ℝ _ (by simp), ?_⟩
  · rw [mem_singleton.1 hx]
    exact points_mem_vertexSet T₁ 0
  · rw [freudenthalMesh_domain, hpt]
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, Set.mem_Ioo]
    constructor <;> linarith

namespace PolySeq

/-- **`V̊ₕ⁰ ≠ 0` on Freudenthal meshes of level `N ≥ 2`** for every admissible sequence (in
particular for `r₀ = 1`): the interior vertex carries a degree of freedom. -/
theorem finrank_V₀_freudenthalMesh_pos_zero_of_two_le (S : PolySeq) [NeZero n] {b : Fin n → ℝ}
    {s : ℝ} (hs : 0 < s) {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    0 < Module.finrank ℝ ((polyElement n S).V₀ (freudenthalMesh b s hs N) 0) := by
  obtain ⟨g, hg, hgc, x, hx, hxΩ⟩ := exists_vertex_freudenthalMesh (b := b) hs hN
  have hdim : 0 < Module.finrank ℝ (S.test 0 (#g - 1)) := by
    rw [hgc, finrank_test]; exact PolyKind.testDim_self_pos _ (S.one_le_deg 0) 0
  exact (polyElement n S).finrank_V₀_pos _ (isOpen_freudenthalMesh_domain b s hs N) hg
    (⟨⟨0, hdim⟩, card_pos.1 (by omega)⟩ : S.DofIdx g 0) hx hxΩ

/-- **`V̊ₕᵏ ≠ 0` in every degree `k ≤ n`** on the Freudenthal meshes of level `N ≥ 2`, for every
admissible sequence. -/
theorem finrank_V₀_freudenthalMesh_pos_of_two_le (S : PolySeq) [NeZero n] {b : Fin n → ℝ}
    {s : ℝ} (hs : 0 < s) {N : ℕ} [NeZero N] (hN : 2 ≤ N) {k : ℕ} (hkn : k ≤ n) :
    0 < Module.finrank ℝ ((polyElement n S).V₀ (freudenthalMesh b s hs N) k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact S.finrank_V₀_freudenthalMesh_pos_zero_of_two_le hs hN
  · exact S.finrank_V₀_freudenthalMesh_pos_of_one_le hs hk1 hkn

end PolySeq

end Feec.FiniteElement
