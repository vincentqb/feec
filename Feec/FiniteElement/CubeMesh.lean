module

public import Feec.FiniteElement.CubeDof

/-!
# `Q_r⁻Λᵏ` on uniform cubical meshes: global spaces, degrees of freedom, dimension

The global spaces `Q_b⁻Λᵏ(𝒯_h)` of tangentially continuous piecewise forms on uniform cubical
meshes form a complex and are assembled from global degrees of freedom
([ArnoldBoffiBonizzoni2015], §5; [ArnoldAwanou2014], §2; [AFW2006], §5).

## Main results

* `Cube.extDeriv_mem_cubeGlobalSpace`: `d Q_b⁻Λᵏ(𝒯_h) ⊆ Q_b⁻Λ^{k+1}(𝒯_h)`.
* `Cube.finrank_cubeGlobalSpace`: `dim Q_b⁻Λᵏ(𝒯_h) = Σ_{#s = k} Πⱼ (N_j b_j + 1 - [j ∈ s])` for
  `N, b ≥ 1`.
* `Cube.cubeGlobalInterp_extDeriv`: the global canonical interpolant commutes with `d`.

## References

* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015]
* [D. N. Arnold, G. Awanou, *Finite element differential forms on cubical meshes*][ArnoldAwanou2014]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.FiniteElement.Cube

open Koszul ExteriorFibre

/-! ### The one-dimensional numbering of the degrees of freedom -/

/-- The global degrees of freedom in one direction, on `N` cells of degree `b`. -/
def GlobalEdge (N b : ℕ) : Bool → Type
  | true => Fin N × Fin b
  | false => Fin (N + 1) ⊕ Fin N × Fin (b - 1)

instance instFintypeGlobalEdge (N b : ℕ) : ∀ e, Fintype (GlobalEdge N b e)
  | true => inferInstanceAs (Fintype (Fin N × Fin b))
  | false => inferInstanceAs (Fintype (Fin (N + 1) ⊕ Fin N × Fin (b - 1)))

theorem card_globalEdge (N : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    ∀ e, Fintype.card (GlobalEdge N b e) = N * b + 1 - if e then 1 else 0
  | true => by
    change Fintype.card (Fin N × Fin b) = _
    simp
  | false => by
    change Fintype.card (Fin (N + 1) ⊕ Fin N × Fin (b - 1)) = _
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Bool.false_eq_true,
      ↓reduceIte, tsub_zero, add_tsub_cancel_right]
    ring

/-- The global number of the local degree of freedom `a` of the cell `c`. -/
def toGlobalEdge {N b : ℕ} (c : Fin N) :
    ∀ (e : Bool) (a : ℕ), a + (if e then 1 else 0) ≤ b → GlobalEdge N b e
  | true, a, h => (c, ⟨a, by simp at h; omega⟩)
  | false, 0, _ => Sum.inl c.castSucc
  | false, 1, _ => Sum.inl c.succ
  | false, a + 2, h => Sum.inr (c, ⟨a, by simp at h; omega⟩)

/-- The canonical cell of a vertex `v` and its local index there. -/
def vertexCell {N : ℕ} (hN : 1 ≤ N) (v : Fin (N + 1)) : Fin N × ℕ :=
  if h : (v : ℕ) < N then (⟨v, h⟩, 0) else (⟨N - 1, by omega⟩, 1)

theorem vertexCell_snd_le {N : ℕ} (hN : 1 ≤ N) (v : Fin (N + 1)) : (vertexCell hN v).2 ≤ 1 := by
  unfold vertexCell; split_ifs <;> simp

/-- The canonical cell and local index of a global degree of freedom. -/
def ofGlobalEdge {N b : ℕ} (hN : 1 ≤ N) : ∀ e, GlobalEdge N b e → Fin N × ℕ
  | true, (c, a) => (c, a)
  | false, Sum.inl v => vertexCell hN v
  | false, Sum.inr (c, a) => (c, a + 2)

theorem ofGlobalEdge_le {N b : ℕ} (hN : 1 ≤ N) (hb : 1 ≤ b) :
    ∀ e (A : GlobalEdge N b e), (ofGlobalEdge hN e A).2 + (if e then 1 else 0) ≤ b
  | true, (c, a) => by simp [ofGlobalEdge]
  | false, Sum.inl v => by
    have := vertexCell_snd_le hN v
    simp only [ofGlobalEdge, Bool.false_eq_true, ↓reduceIte, add_zero]
    omega
  | false, Sum.inr (c, a) => by have := a.isLt; simp [ofGlobalEdge]; omega

theorem toGlobalEdge_ofGlobalEdge {N b : ℕ} (hN : 1 ≤ N) (hb : 1 ≤ b) :
    ∀ e (A : GlobalEdge N b e),
      toGlobalEdge (ofGlobalEdge hN e A).1 e (ofGlobalEdge hN e A).2 (ofGlobalEdge_le hN hb e A) = A
  | true, (c, a) => rfl
  | false, Sum.inl v => by
    change toGlobalEdge (vertexCell hN v).1 false (vertexCell hN v).2 _ = Sum.inl v
    generalize_proofs hp
    revert hp
    generalize hq : vertexCell hN v = q
    unfold vertexCell at hq
    split_ifs at hq with h <;> subst hq <;> intro hp
    · exact congrArg Sum.inl (Fin.ext rfl)
    · exact congrArg Sum.inl (Fin.ext (by simp; omega))
  | false, Sum.inr (c, a) => rfl

theorem toGlobalEdge_eq {N b : ℕ} {c c' : Fin N} {e : Bool} {a a' : ℕ}
    {h : a + (if e then 1 else 0) ≤ b} {h' : a' + (if e then 1 else 0) ≤ b}
    (heq : toGlobalEdge c e a h = toGlobalEdge c' e a' h') :
    (c = c' ∧ a = a') ∨ (e = false ∧ (c' : ℕ) = c + 1 ∧ a = 1 ∧ a' = 0) ∨
      (e = false ∧ (c : ℕ) = c' + 1 ∧ a = 0 ∧ a' = 1) := by
  cases e
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at h h'
    rcases a with _ | _ | a <;> rcases a' with _ | _ | a' <;> simp only [toGlobalEdge] at heq <;>
      first
      | exact absurd heq Sum.inl_ne_inr
      | exact absurd heq Sum.inr_ne_inl
      | (have h1 := congrArg Fin.val (Sum.inl.inj heq)
         simp only [Fin.val_castSucc, Fin.val_succ] at h1
         simp only [Fin.ext_iff, true_and, and_true]
         omega)
      | (obtain ⟨h1, h2⟩ := Prod.mk.inj (Sum.inr.inj heq)
         have h3 := congrArg Fin.val h2
         simp only [Fin.ext_iff, true_and] at h1 h3 ⊢
         omega)
  · obtain ⟨h1, h2⟩ := Prod.mk.inj heq
    exact Or.inl ⟨h1, congrArg Fin.val h2⟩

theorem toGlobalEdge_congr {N b : ℕ} {c c' : Fin N} {e : Bool} {a a' : ℕ}
    {h : a + (if e then 1 else 0) ≤ b} {h' : a' + (if e then 1 else 0) ≤ b} (hc : c = c')
    (ha : a = a') : toGlobalEdge c e a h = toGlobalEdge c' e a' h' := by
  subst hc ha; rfl

theorem toGlobalEdge_vertex {N b : ℕ} {c c' : Fin N} {e : Bool} {a a' : ℕ}
    {h : a + (if e then 1 else 0) ≤ b} {h' : a' + (if e then 1 else 0) ≤ b} (he : e = false)
    (hc : (c' : ℕ) = c + 1) (ha : a = 1) (ha' : a' = 0) :
    toGlobalEdge c e a h = toGlobalEdge c' e a' h' := by
  subst he ha ha'
  exact congrArg Sum.inl (Fin.ext (by simp [hc]))

/-! ### The mesh and the global spaces -/

variable {d : Type*} [LinearOrder d] [Fintype d] (N : d → ℕ)

/-- The cells `∏ⱼ [m_j, m_j + 1] / N_j` of the uniform cubical mesh of the unit cube. -/
abbrev CubeCell := ∀ j, Fin (N j)

/-- The closures of the cells `m`, `m'` meet: `|m_j - m'_j| ≤ 1` in every direction. -/
def CubeCell.Adj (m m' : CubeCell N) : Prop := ∀ j, (m j : ℕ) ≤ m' j + 1 ∧ (m' j : ℕ) ≤ m j + 1

/-- The common face of the cells `m`, `m'`, in the local coordinates of `m`. -/
def commonFace (m m' : CubeCell N) : d → Option ℝ := fun j =>
  if (m' j : ℕ) = m j + 1 then some 1 else if (m j : ℕ) = m' j + 1 then some 0 else none

omit [LinearOrder d] [Fintype d] in
variable {N} in
theorem commonFace_cases {m m' : CubeCell N} (hadj : CubeCell.Adj N m m') (j : d) :
    (commonFace N m m' j = some 1 ∧ commonFace N m' m j = some 0 ∧ (m' j : ℕ) = m j + 1) ∨
      (commonFace N m m' j = some 0 ∧ commonFace N m' m j = some 1 ∧ (m j : ℕ) = m' j + 1) ∨
      (commonFace N m m' j = none ∧ commonFace N m' m j = none ∧ m j = m' j) := by
  have := hadj j
  rcases lt_trichotomy (m j : ℕ) (m' j) with h | h | h
  · have c1 : (m' j : ℕ) = m j + 1 := by omega
    have c2 : ¬(m j : ℕ) = m' j + 1 := by omega
    exact Or.inl ⟨ite_eq_left c1, by rw [commonFace, ite_eq_right c2, ite_eq_left c1], c1⟩
  · have c1 : ¬(m' j : ℕ) = m j + 1 := by omega
    have c2 : ¬(m j : ℕ) = m' j + 1 := by omega
    exact Or.inr (Or.inr ⟨by rw [commonFace, ite_eq_right c1, ite_eq_right c2],
      by rw [commonFace, ite_eq_right c2, ite_eq_right c1], Fin.ext h⟩)
  · have c1 : ¬(m' j : ℕ) = m j + 1 := by omega
    have c2 : (m j : ℕ) = m' j + 1 := by omega
    exact Or.inr (Or.inl ⟨by rw [commonFace, ite_eq_right c1, ite_eq_left c2],
      ite_eq_left c2, c2⟩)

/-- The piecewise polynomial forms whose traces agree on the common faces of neighbouring cells. -/
def cubeCompatible : Submodule ℝ (CubeCell N → PolyForm ℝ d) where
  carrier := {ω | ∀ m m', CubeCell.Adj N m m' →
    cubeTrace (commonFace N m m') (ω m) = cubeTrace (commonFace N m' m) (ω m')}
  zero_mem' _ _ _ := by simp
  add_mem' hω hη m m' h := by simp only [Pi.add_apply, cubeTrace_add, hω m m' h, hη m m' h]
  smul_mem' c ω hω m m' h := by simp only [Pi.smul_apply, cubeTrace_smul, hω m m' h]

/-- The global space `Q_b⁻Λᵏ(𝒯_h)`: the tangentially continuous piecewise forms of `Q_b⁻Λᵏ`. -/
def cubeGlobalSpace (b : d → ℕ) (k : ℕ) : Submodule ℝ (CubeCell N → PolyForm ℝ d) :=
  cubeCompatible N ⊓ Submodule.pi Set.univ fun _ => cubeFormMinus ℝ b k

instance (b : d → ℕ) (k : ℕ) : FiniteDimensional ℝ (cubeGlobalSpace N b k) := by
  have : Submodule.pi Set.univ (fun _ : CubeCell N => cubeFormMinus ℝ b k) =
      LinearMap.range (LinearMap.pi fun m => (cubeFormMinus ℝ b k).subtype ∘ₗ LinearMap.proj m) :=
    Submodule.ext fun ω => ⟨fun h => ⟨fun m => ⟨ω m, h m (Set.mem_univ _)⟩, rfl⟩, by
      rintro ⟨u, rfl⟩ m _; exact (u m).2⟩
  exact Submodule.finiteDimensional_of_le (inf_le_right.trans this.le)

variable {N}

theorem mem_cubeGlobalSpace {b : d → ℕ} {k : ℕ} {ω : CubeCell N → PolyForm ℝ d} :
    ω ∈ cubeGlobalSpace N b k ↔ ω ∈ cubeCompatible N ∧ ∀ m, ω m ∈ cubeFormMinus ℝ b k := by
  simp [cubeGlobalSpace, Submodule.mem_pi]

theorem extDeriv_mem_cubeCompatible {ω : CubeCell N → PolyForm ℝ d}
    (hω : ω ∈ cubeCompatible N) : (fun m => extDeriv (ω m)) ∈ cubeCompatible N :=
  fun m m' h => by simp only [← extDeriv_cubeTrace, hω m m' h]

/-- `d Q_b⁻Λᵏ(𝒯_h) ⊆ Q_b⁻Λ^{k+1}(𝒯_h)`. -/
theorem extDeriv_mem_cubeGlobalSpace {b : d → ℕ} {k : ℕ} {ω : CubeCell N → PolyForm ℝ d}
    (hω : ω ∈ cubeGlobalSpace N b k) : (fun m => extDeriv (ω m)) ∈ cubeGlobalSpace N b (k + 1) :=
  mem_cubeGlobalSpace.2 ⟨extDeriv_mem_cubeCompatible (mem_cubeGlobalSpace.1 hω).1,
    fun m => extDeriv_mem_cubeFormMinus ((mem_cubeGlobalSpace.1 hω).2 m)⟩

/-! ### Moments on common faces -/

theorem momentDof_cubeTrace_of_le {f g : d → Option ℝ} {s : Finset d} {α : d →₀ ℕ}
    (h : ∀ j c, g j = some c → dofFace f s α j = some c) (ω : PolyForm ℝ d) :
    momentDof f s α (cubeTrace g ω) = momentDof f s α ω := by
  simp only [momentDof, cubeMoment, LinearMap.coe_mk, AddHom.coe_mk, cubeTrace_cubeTrace]
  congr 3
  funext j
  cases hg : g j with
  | none => rfl
  | some c => rw [h j c hg]; rfl

theorem momentDof_cubeTrace_congr {g : d → Option ℝ} {b : d → ℕ} {s : Finset d}
    {α α' : d →₀ ℕ} (hα : α ∈ cubeSupport b s) (hα' : α' ∈ cubeSupport b s)
    (heq : ∀ j, g j = none → α j = α' j) (hfix : ∀ j, g j ≠ none → j ∉ s ∧ α j ≤ 1 ∧ α' j ≤ 1)
    (ω : PolyForm ℝ d) :
    momentDof (fun _ => none) s α (cubeTrace g ω) =
      momentDof (fun _ => none) s α' (cubeTrace g ω) := by
  have hf : ∀ j, (fun _ : d => (none : Option ℝ)) j ≠ none → b j = 0 := fun _ h => absurd rfl h
  rw [momentDof_apply hf hα, momentDof_apply hf hα']
  have hfree : freeSet (dofFace (fun _ => none) s α) = freeSet (dofFace (fun _ => none) s α') := by
    ext j
    simp only [mem_freeSet, dofFace, Option.none_or]
    by_cases hg : g j = none
    · rw [heq j hg]
    · obtain ⟨hjs, h1, h2⟩ := hfix j hg
      simp [hjs, show ¬2 ≤ α j by omega, show ¬2 ≤ α' j by omega]
  rw [hfree]
  congr 1
  have key : tensorDof (fun _ => none) s α ∘ₗ faceSubst g =
      tensorDof (fun _ => none) s α' ∘ₗ faceSubst g :=
    (basisMonomials d ℝ).ext fun γ => by
      simp only [coe_basisMonomials, LinearMap.coe_comp, Function.comp_apply, faceSubst_monomial,
        one_mul, tensorDof_monomial]
      congr 1
      refine prod_congr rfl fun j _ => ?_
      by_cases hg : g j = none
      · rw [heq j hg]
      · obtain ⟨hjs, h1, h2⟩ := hfix j hg
        rw [show (γ.filter fun i => (g i).isNone) j = 0 by
          simp [Option.isNone_iff_eq_none, hg]]
        simp only [hjs, decide_false]
        interval_cases (α j) <;> interval_cases (α' j) <;> rfl
  simp only [cubeTrace]
  split_ifs
  · exact LinearMap.congr_fun key _
  · simp

/-- The lift to the cube of a local index on a face `g` of the cube. -/
def liftIdx (g : d → Option ℝ) (α : d →₀ ℕ) : d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => if g j = some 1 then 1 else α j

omit [Fintype d] in
theorem fixed_of_mem_cubeSupport {g : d → Option ℝ} {b : d → ℕ} {s : Finset d} {α : d →₀ ℕ}
    (hf : ∀ j, g j ≠ none → b j = 0) (hα : α ∈ cubeSupport b s) {j : d} (hj : g j ≠ none) :
    j ∉ s ∧ α j = 0 := by
  have := hα j
  rw [hf j hj] at this
  exact ⟨fun hjs => by simp [hjs] at this, by split_ifs at this <;> omega⟩

theorem dofFace_liftIdx {g : d → Option ℝ} {b : d → ℕ} {s : Finset d} {α : d →₀ ℕ}
    (hg : ∀ j c, g j = some c → c = 0 ∨ c = 1) (hf : ∀ j, g j ≠ none → b j = 0)
    (hα : α ∈ cubeSupport b s) : dofFace (fun _ => none) s (liftIdx g α) = dofFace g s α :=
  funext fun j => by
    cases hgj : g j with
    | none => simp [dofFace, liftIdx, hgj]
    | some c =>
      obtain ⟨hjs, h0⟩ := fixed_of_mem_cubeSupport hf hα (j := j) (by simp [hgj])
      rcases hg j c hgj with rfl | rfl <;> simp [dofFace, liftIdx, hgj, hjs, h0]

theorem momentDof_liftIdx {g : d → Option ℝ} {b : d → ℕ} {s : Finset d} {α : d →₀ ℕ}
    (hg : ∀ j c, g j = some c → c = 0 ∨ c = 1) (hf : ∀ j, g j ≠ none → b j = 0)
    (hα : α ∈ cubeSupport b s) :
    momentDof (fun _ => none) s (liftIdx g α) = momentDof g s α := by
  have htest : dofTest s (liftIdx g α) = dofTest s α := Finsupp.ext fun j => by
    cases hgj : g j with
    | none => simp [dofTest, liftIdx, hgj]
    | some c =>
      obtain ⟨hjs, h0⟩ := fixed_of_mem_cubeSupport hf hα (j := j) (by simp [hgj])
      simp only [dofTest, liftIdx, Finsupp.coe_equivFunOnFinite_symm, hjs, ↓reduceIte, hgj, h0]
      split_ifs <;> rfl
  simp only [momentDof, dofFace_liftIdx hg hf hα, htest]

theorem liftIdx_mem {g : d → Option ℝ} {b : d → ℕ} (hb : ∀ j, 1 ≤ b j) {s : Finset d}
    {α : d →₀ ℕ} (hα : α ∈ cubeSupport (faceDeg b g) s) : liftIdx g α ∈ cubeSupport b s := by
  intro j
  have := hα j
  simp only [liftIdx, Finsupp.coe_equivFunOnFinite_symm, faceDeg] at this ⊢
  by_cases hgj : (g j).isNone
  · simp only [hgj, ↓reduceIte] at this
    have : g j ≠ some 1 := by simp_all [Option.isNone_iff_eq_none]
    simpa [this] using ‹_ ≤ b j›
  · simp only [hgj, Bool.false_eq_true, ↓reduceIte] at this
    have hjs : j ∉ s := fun h => by simp [h] at this
    have := hb j
    split_ifs <;> simp <;> omega

/-! ### Global degrees of freedom -/

variable (N) in
/-- The global degrees of freedom of `Q_b⁻Λᵏ(𝒯_h)`. -/
abbrev CubeGlobalIdx (b : d → ℕ) (k : ℕ) :=
  Σ s : {s : Finset d // #s = k}, ∀ j, GlobalEdge (N j) (b j) (decide (j ∈ s.1))

/-- The global number of the local degree of freedom `i` of the cell `m`. -/
def toGlobal (m : CubeCell N) {b : d → ℕ} {k : ℕ} (i : CubeDofIdx b k) : CubeGlobalIdx N b k :=
  ⟨i.1, fun j => toGlobalEdge (m j) _ (i.2.1 j) (by simpa using i.2.2 j)⟩

variable {b : d → ℕ} {k : ℕ}

omit [Fintype d] in
theorem toGlobal_eq_iff {m m' : CubeCell N} {s : {s : Finset d // #s = k}}
    {α α' : cubeSupport b s.1} (h : toGlobal m ⟨s, α⟩ = toGlobal m' ⟨s, α'⟩) (j : d) :
    (m j = m' j ∧ α.1 j = α'.1 j) ∨ (j ∉ s.1 ∧ (m' j : ℕ) = m j + 1 ∧ α.1 j = 1 ∧ α'.1 j = 0) ∨
      (j ∉ s.1 ∧ (m j : ℕ) = m' j + 1 ∧ α.1 j = 0 ∧ α'.1 j = 1) := by
  have hj := congrFun (eq_of_heq (Sigma.mk.inj h).2) j
  rcases toGlobalEdge_eq hj with h1 | ⟨he, h2⟩ | ⟨he, h3⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨by simpa using he, h2⟩)
  · exact Or.inr (Or.inr ⟨by simpa using he, h3⟩)

theorem cubeDof_eq_of_toGlobal_eq {ω : CubeCell N → PolyForm ℝ d} (hω : ω ∈ cubeCompatible N)
    {m m' : CubeCell N} {i i' : CubeDofIdx b k} (h : toGlobal m i = toGlobal m' i') :
    cubeDof (fun _ => none) i (ω m) = cubeDof (fun _ => none) i' (ω m') := by
  obtain ⟨s, α⟩ := i
  obtain ⟨s', α'⟩ := i'
  obtain rfl : s = s' := Subtype.ext (congrArg (fun A => A.1.1) h)
  have tri := toGlobal_eq_iff h
  have hadj : CubeCell.Adj N m m' := fun j => by
    rcases tri j with ⟨h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩
    · rw [h1]; omega
    · omega
    · omega
  -- the moments live on the common face
  have hle : ∀ (m₁ m₂ : CubeCell N) (α₁ α₂ : cubeSupport b s.1),
      (∀ j, (m₁ j = m₂ j ∧ α₁.1 j = α₂.1 j) ∨
        (j ∉ s.1 ∧ (m₂ j : ℕ) = m₁ j + 1 ∧ α₁.1 j = 1 ∧ α₂.1 j = 0) ∨
        (j ∉ s.1 ∧ (m₁ j : ℕ) = m₂ j + 1 ∧ α₁.1 j = 0 ∧ α₂.1 j = 1)) →
      ∀ j c, commonFace N m₁ m₂ j = some c → dofFace (fun _ => none) s.1 α₁.1 j = some c := by
    intro m₁ m₂ α₁ α₂ t j c hc
    simp only [commonFace] at hc
    rcases t j with ⟨h1, -⟩ | ⟨hjs, h1, h2, -⟩ | ⟨hjs, h1, h2, -⟩
    · rw [h1] at hc; simp at hc
    · rw [ite_eq_left h1] at hc; cases hc; simp [dofFace, hjs, h2]
    · rw [ite_eq_right (by omega), ite_eq_left h1] at hc; cases hc; simp [dofFace, hjs, h2]
  have tri' : ∀ j, (m' j = m j ∧ α'.1 j = α.1 j) ∨
      (j ∉ s.1 ∧ (m j : ℕ) = m' j + 1 ∧ α'.1 j = 1 ∧ α.1 j = 0) ∨
      (j ∉ s.1 ∧ (m' j : ℕ) = m j + 1 ∧ α'.1 j = 0 ∧ α.1 j = 1) := fun j => by
    rcases tri j with ⟨h1, h2⟩ | h | h
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr (Or.inr ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩)
    · exact Or.inr (Or.inl ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩)
  simp only [cubeDof]
  rw [← momentDof_cubeTrace_of_le (hle m m' α α' tri) (ω m), hω m m' hadj,
    momentDof_cubeTrace_congr α.2 α'.2 (fun j hj => ?_) (fun j hj => ?_),
    momentDof_cubeTrace_of_le (hle m' m α' α tri') (ω m')]
  · rcases tri j with ⟨-, h2⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩
    · exact h2
    · rw [commonFace, ite_eq_right (by omega), ite_eq_left h1] at hj
      exact absurd hj (by simp)
    · rw [commonFace, ite_eq_left h1] at hj
      exact absurd hj (by simp)
  · rcases tri j with ⟨h1, -⟩ | ⟨hjs, -, h2, h3⟩ | ⟨hjs, -, h2, h3⟩
    · simp [commonFace, h1] at hj
    · exact ⟨hjs, by omega, by omega⟩
    · exact ⟨hjs, by omega, by omega⟩

variable (hN : ∀ j, 1 ≤ N j) (hb : ∀ j, 1 ≤ b j)

/-- The canonical cell of a global degree of freedom. -/
def globalCell (A : CubeGlobalIdx N b k) : CubeCell N := fun j => (ofGlobalEdge (hN j) _ (A.2 j)).1

/-- The local index of a global degree of freedom in its canonical cell. -/
def globalLocal (A : CubeGlobalIdx N b k) : CubeDofIdx b k :=
  ⟨A.1, ⟨Finsupp.equivFunOnFinite.symm fun j => (ofGlobalEdge (hN j) _ (A.2 j)).2,
    fun j => by simpa using ofGlobalEdge_le (hN j) (hb j) _ (A.2 j)⟩⟩

theorem toGlobal_globalLocal (A : CubeGlobalIdx N b k) :
    toGlobal (globalCell hN A) (globalLocal hN hb A) = A := by
  obtain ⟨s, A⟩ := A
  refine Sigma.ext rfl (heq_of_eq (funext fun j => ?_))
  exact toGlobalEdge_ofGlobalEdge (hN j) (hb j) _ (A j)

/-- The global degree of freedom `A`, read in its canonical cell. -/
def globalDof (A : CubeGlobalIdx N b k) : (CubeCell N → PolyForm ℝ d) →ₗ[ℝ] ℝ :=
  cubeDof (fun _ => none) (globalLocal hN hb A) ∘ₗ LinearMap.proj (globalCell hN A)

theorem globalDof_toGlobal {ω : CubeCell N → PolyForm ℝ d} (hω : ω ∈ cubeCompatible N)
    (m : CubeCell N) (i : CubeDofIdx b k) :
    globalDof hN hb (toGlobal m i) ω = cubeDof (fun _ => none) i (ω m) :=
  cubeDof_eq_of_toGlobal_eq hω (toGlobal_globalLocal hN hb _)

/-- The piecewise form with prescribed global degrees of freedom. -/
def ofGlobalDof (v : CubeGlobalIdx N b k → ℝ) : CubeCell N → PolyForm ℝ d := fun m =>
  ((isUnisolvent_cubeDof (isFaceDeg_none hb) k).equiv.symm fun i => v (toGlobal m i) :
    cubeFormMinus ℝ b k)

theorem cubeDof_ofGlobalDof (v : CubeGlobalIdx N b k → ℝ) (m : CubeCell N) (i : CubeDofIdx b k) :
    cubeDof (fun _ => none) i (ofGlobalDof hb v m) = v (toGlobal m i) :=
  (isUnisolvent_cubeDof (isFaceDeg_none hb) k).dof_equiv_symm _ i

theorem ofGlobalDof_add (v v' : CubeGlobalIdx N b k → ℝ) :
    ofGlobalDof hb (v + v') = ofGlobalDof hb v + ofGlobalDof hb v' := by
  funext m
  simp only [ofGlobalDof, Pi.add_apply]
  rw [show (fun i => v (toGlobal m i) + v' (toGlobal m i)) =
    (fun i => v (toGlobal m i)) + fun i => v' (toGlobal m i) from rfl, map_add]
  rfl

theorem ofGlobalDof_smul (c : ℝ) (v : CubeGlobalIdx N b k → ℝ) :
    ofGlobalDof hb (c • v) = c • ofGlobalDof hb v := by
  funext m
  simp only [ofGlobalDof, Pi.smul_apply]
  rw [show (fun i => c • v (toGlobal m i)) = c • fun i => v (toGlobal m i) from rfl, map_smul]
  rfl

omit [LinearOrder d] [Fintype d] in
theorem faceDeg_commonFace (b : d → ℕ) (m m' : CubeCell N) (hadj : CubeCell.Adj N m m') :
    faceDeg b (commonFace N m' m) = faceDeg b (commonFace N m m') := by
  funext j
  simp only [faceDeg]
  rcases commonFace_cases hadj j with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;> simp [h1, h2]

theorem ofGlobalDof_mem (v : CubeGlobalIdx N b k → ℝ) :
    ofGlobalDof hb v ∈ cubeGlobalSpace N b k := by
  refine mem_cubeGlobalSpace.2 ⟨fun m m' hadj => ?_, fun m => (Subtype.prop _)⟩
  set ω := ofGlobalDof hb v
  set g := commonFace N m m'
  set g' := commonFace N m' m
  have hQ : ∀ m, ω m ∈ cubeFormMinus ℝ b k := fun m => Subtype.prop _
  have h01 : ∀ (m₁ m₂ : CubeCell N) j c, commonFace N m₁ m₂ j = some c → c = 0 ∨ c = 1 :=
    fun m₁ m₂ j c h => by simp only [commonFace] at h; split_ifs at h <;> cases h <;> simp
  have hfz : ∀ (m₁ m₂ : CubeCell N) j, commonFace N m₁ m₂ j ≠ none →
      faceDeg b (commonFace N m₁ m₂) j = 0 := fun m₁ m₂ j h => by
    simp [faceDeg, Option.isNone_iff_eq_none, h]
  rw [← sub_eq_zero]
  refine eq_zero_of_cubeDof_eq_zero (isFaceDeg_faceDeg hb g) (Submodule.sub_mem _
    (cubeTrace_mem (hQ m) g) (faceDeg_commonFace b m m' hadj ▸ cubeTrace_mem (hQ m') g'))
    fun ⟨s, α, hα⟩ => ?_
  have hα' : α ∈ cubeSupport (faceDeg b g') s.1 := faceDeg_commonFace b m m' hadj ▸ hα
  have hnone : ∀ j, g' j = none ↔ g j = none := fun j => by
    rcases commonFace_cases hadj j with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;>
      simp [g, g', h1, h2]
  have hlift : ∀ (g₁ : d → Option ℝ) j, g₁ j = none → liftIdx g₁ α j = α j := fun g₁ j h => by
    simp [liftIdx, h]
  have hlift1 : ∀ (g₁ : d → Option ℝ) j, liftIdx g₁ α j ≤ 1 + α j := fun g₁ j => by
    simp only [liftIdx, Finsupp.coe_equivFunOnFinite_symm]; split_ifs <;> omega
  have hfix' : ∀ j, g' j ≠ none → j ∉ s.1 ∧ liftIdx g α j ≤ 1 ∧ liftIdx g' α j ≤ 1 :=
    fun j hj => by
      obtain ⟨hjs, h0⟩ := fixed_of_mem_cubeSupport (hfz m m') hα fun h => hj ((hnone j).2 h)
      exact ⟨hjs, by have := hlift1 g j; omega, by have := hlift1 g' j; omega⟩
  have hle' : ∀ j c, g' j = some c → dofFace (fun _ => none) s.1 (liftIdx g' α) j = some c :=
    fun j c hc => by
      simp only [g'] at hc
      rw [dofFace_liftIdx (h01 m' m) (hfz m' m) hα', dofFace, hc]
      rfl
  rw [map_sub, sub_eq_zero]
  simp only [cubeDof]
  -- the face moment is a cell moment of `m` and, through the trace, of `m'`
  rw [momentDof_cubeTrace, ← momentDof_liftIdx (h01 m m') (hfz m m') hα,
    momentDof_cubeTrace_congr (α' := liftIdx g' α) (liftIdx_mem hb hα) (liftIdx_mem hb hα')
      (fun j hj => by rw [hlift g j ((hnone j).1 hj), hlift g' j hj]) hfix',
    momentDof_cubeTrace_of_le hle']
  have e1 := cubeDof_ofGlobalDof hb v m ⟨s, ⟨liftIdx g α, liftIdx_mem hb hα⟩⟩
  have e2 := cubeDof_ofGlobalDof hb v m' ⟨s, ⟨liftIdx g' α, liftIdx_mem hb hα'⟩⟩
  simp only [cubeDof] at e1 e2
  rw [e1, e2]
  congr 1
  refine Sigma.ext rfl (heq_of_eq (funext fun j => ?_))
  rcases commonFace_cases hadj j with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · obtain ⟨hjs, h0⟩ := fixed_of_mem_cubeSupport (hfz m m') hα (j := j) (by simp [h1])
    exact toGlobalEdge_vertex (by simpa using hjs) h3 (by simp [liftIdx, g, h1])
      (by simp [liftIdx, g', h2, h0])
  · obtain ⟨hjs, h0⟩ := fixed_of_mem_cubeSupport (hfz m m') hα (j := j) (by simp [h1])
    exact (toGlobalEdge_vertex (by simpa using hjs) h3 (by simp [liftIdx, g', h2])
      (by simp [liftIdx, g, h1, h0])).symm
  · exact toGlobalEdge_congr h3 (by rw [hlift g j h1, hlift g' j h2])

/-- The global degrees of freedom as a linear isomorphism `Q_b⁻Λᵏ(𝒯_h) ≃ ℝ^{global DOFs}`. -/
def globalDofEquiv : cubeGlobalSpace N b k ≃ₗ[ℝ] (CubeGlobalIdx N b k → ℝ) where
  toFun ω A := globalDof hN hb A ω.1
  map_add' ω η := funext fun A => map_add _ _ _
  map_smul' c ω := funext fun A => map_smul _ _ _
  invFun v := ⟨ofGlobalDof hb v, ofGlobalDof_mem hb v⟩
  left_inv ω := by
    refine Subtype.ext (funext fun m => ?_)
    have hω := mem_cubeGlobalSpace.1 ω.2
    have := (isUnisolvent_cubeDof (isFaceDeg_none hb) k).ext
      (p := ⟨ofGlobalDof hb (fun A => globalDof hN hb A ω.1) m, Subtype.prop _⟩)
      (q := ⟨ω.1 m, hω.2 m⟩) fun i => by
        simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply]
        rw [cubeDof_ofGlobalDof, globalDof_toGlobal hN hb hω.1]
    exact congrArg Subtype.val this
  right_inv v := funext fun A => by
    simp only [globalDof, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
      Function.eval]
    rw [cubeDof_ofGlobalDof, toGlobal_globalLocal]

include hN hb in
/-- `dim Q_b⁻Λᵏ(𝒯_h) = Σ_{#s = k} Πⱼ (N_j b_j + 1 - [j ∈ s])` for `N, b ≥ 1`. -/
theorem finrank_cubeGlobalSpace :
    Module.finrank ℝ (cubeGlobalSpace N b k) =
      ∑ s ∈ powersetCard k univ, ∏ j, (N j * b j + 1 - if j ∈ s then 1 else 0) := by
  rw [(globalDofEquiv hN hb).finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_sigma]
  simp_rw [Fintype.card_pi, card_globalEdge _ (hb _), decide_eq_true_eq]
  exact (Finset.sum_subtype (powersetCard k univ) (p := fun s => #s = k)
    (fun s => by simp [mem_powersetCard])
    (fun s => ∏ j, (N j * b j + 1 - if j ∈ s then 1 else 0))).symm

theorem finrank_cubeGlobalSpace_const {M r : ℕ} (hM : 1 ≤ M) (hr : 1 ≤ r) :
    Module.finrank ℝ (cubeGlobalSpace (fun _ : d => M) (fun _ => r) k) =
      (Fintype.card d).choose k * ((M * r) ^ k * (M * r + 1) ^ (Fintype.card d - k)) := by
  rw [finrank_cubeGlobalSpace (fun _ => hM) (fun _ => hr), ← finrank_cubeFormMinus_const (K := ℝ),
    finrank_cubeFormMinus]

/-! ### The global canonical interpolant -/

/-- The global canonical interpolant `Π_h` onto `Q_b⁻Λᵏ(𝒯_h)`. -/
def cubeGlobalInterp : cubeCompatible N →ₗ[ℝ] cubeGlobalSpace N b k :=
  (globalDofEquiv hN hb).symm.toLinearMap ∘ₗ LinearMap.pi fun A => globalDof hN hb A ∘ₗ
    (cubeCompatible N).subtype

theorem cubeGlobalInterp_apply (ω : cubeCompatible N) (m : CubeCell N) :
    (cubeGlobalInterp (k := k) hN hb ω : CubeCell N → PolyForm ℝ d) m =
      cubeInterp (fun _ => none) b k (isFaceDeg_none hb) (ω.1 m) := by
  have := (isUnisolvent_cubeDof (isFaceDeg_none hb) k).ext
    (p := ⟨(cubeGlobalInterp (k := k) hN hb ω : CubeCell N → PolyForm ℝ d) m,
      (mem_cubeGlobalSpace.1 (cubeGlobalInterp (k := k) hN hb ω).2).2 m⟩)
    (q := cubeInterp (fun _ => none) b k (isFaceDeg_none hb) (ω.1 m)) fun i => by
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply]
      rw [cubeDof_cubeInterp]
      exact cubeDof_ofGlobalDof hb _ m i |>.trans (globalDof_toGlobal hN hb ω.2 m i)
  exact congrArg Subtype.val this

theorem cubeGlobalInterp_of_mem (ω : cubeCompatible N) (hω : ω.1 ∈ cubeGlobalSpace N b k) :
    (cubeGlobalInterp (k := k) hN hb ω : CubeCell N → PolyForm ℝ d) = ω.1 :=
  funext fun m => by
    rw [cubeGlobalInterp_apply, cubeInterp_of_mem _ ((mem_cubeGlobalSpace.1 hω).2 m)]

/-- The global interpolant commutes with `d`: `Π_h d = d Π_h` ([ArnoldBoffiBonizzoni2015], §5). -/
theorem cubeGlobalInterp_extDeriv (ω : cubeCompatible N) :
    (cubeGlobalInterp (k := k + 1) hN hb ⟨_, extDeriv_mem_cubeCompatible ω.2⟩ :
        CubeCell N → PolyForm ℝ d) =
      fun m => extDeriv ((cubeGlobalInterp (k := k) hN hb ω : CubeCell N → PolyForm ℝ d) m) :=
  funext fun m => by
    rw [cubeGlobalInterp_apply, cubeGlobalInterp_apply, cubeInterp_extDeriv]

end Feec.FiniteElement.Cube
