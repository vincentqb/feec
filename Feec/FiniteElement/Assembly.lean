module

public import Feec.FiniteElement.Conformity
public import Feec.FiniteElement.Dof
public import Feec.HilbertComplex.Approximation.Subcomplex

/-!
# Assembly of global finite element spaces on simplicial meshes

An abstract **element family** (`Feec.FiniteElement.LocalElement`) assigns to every `n`-simplex
`T` of `ℝⁿ` finite-dimensional spaces `P(T)ᵏ` of `C¹` real `k`-forms with `d P(T)ᵏ ⊆ P(T)ᵏ⁺¹`,
and to every face `g` (a vertex set) degrees of freedom `ℓ_{g,i}` on continuous forms, depending
only on `g`, such that

* the DOFs of the faces of `T` are unisolvent on `P(T)ᵏ`;
* **trace determination**: on a common facet `F` of `T` and `T'`, forms of `P(T)ᵏ` and `P(T')ᵏ`
  with the same DOFs on the faces of `F` have the same tangential trace on `F`;
* the DOFs of a face only see the tangential traces on the face (`dof_congr`);
* **Stokes compatibility**: `ℓ_{g,i} ∘ d` is a combination of the DOFs of the faces of `g`
  (for Whitney forms, Stokes' theorem).

On a conforming mesh `M` of an open `Ω`, the global space `Λ_hᵏ(M)` (`LocalElement.globalSpace`)
consists of the piecewise fields `u = (u_T)_T`, `u_T ∈ P(T)ᵏ`, whose DOFs agree on shared faces.
Then

* `Λ_hᵏ(M)` is finite-dimensional of dimension `Σ_g #DOF(g)` (`finrank_globalSpace`), the global
  DOFs being a linear isomorphism (`globalDofEquiv`); the gluing into `L²(Ω; Λᵏ)` is injective
  (`glue_injective`), so the glued spaces `Vₕᵏ` have the same dimension (`finrank_V`);
* `Λ_hᵏ(M) ⊆ {piecewise fields with continuous tangential traces}`
  (`tangentialTraceEq_of_mem_globalSpace`), with equality when the faces of `M` have facet-connected
  stars (`mem_globalSpace_iff`); the hypothesis is needed (two triangles sharing only a vertex);
* `d Λ_hᵏ ⊆ Λ_hᵏ⁺¹` (`extDeriv_mem_globalSpace`), so the glued `L²` spaces form a
  `Feec.HilbertComplex.Subcomplex` of the maximal de Rham complex `HΛ(Ω)`
  (`LocalElement.subcomplex`), and the global spaces with vanishing boundary DOFs form a subcomplex
  of the minimal complex `H̊Λ(Ω)` (`LocalElement.subcomplexMin`, `Ω` strictly star-shaped);
* the global canonical interpolant `Π_h` (`globalInterp`) commutes with `d` on `C¹` forms
  (`globalInterp_extDeriv`);
* the cases `k = 0` (continuity across facets, `tangentialTraceEq_zero_iff`) and `k = n` (no
  interface condition, `tangentialTraceEq_top`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §5 (assembly of `P_rΛᵏ` and `P_r⁻Λᵏ` from degrees of freedom, conformity, commuting
  projections)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7
-/

open scoped InnerProductSpace ContDiff
open MeasureTheory Set Finset

@[expose] public noncomputable section

namespace Feec.FiniteElement

open Feec.Domain Feec.Mesh ExteriorFibre

variable {n : ℕ}

/-- An abstract **element family** on the `n`-simplices of `ℝⁿ` (see the module docstring). -/
structure LocalElement (n : ℕ) where
  /-- the local spaces `P(T)ᵏ` -/
  space : Affine.Simplex ℝ (Fin n → ℝ) n → ℕ → Submodule ℝ (FormField n)
  contDiff_of_mem : ∀ {T k w}, w ∈ space T k → ContDiff ℝ 1 w
  isDeg_of_mem : ∀ {T k w}, w ∈ space T k → ∀ x, IsDeg k (w x)
  extDeriv_mem : ∀ {T k w}, w ∈ space T k → extDeriv w ∈ space T (k + 1)
  finiteDimensional : ∀ (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ), FiniteDimensional ℝ (space T k)
  /-- the DOFs of degree `k` attached to the face (vertex set) `g` -/
  DofIdx : Finset (Fin n → ℝ) → ℕ → Type
  dofIdxFintype : ∀ g k, Fintype (DofIdx g k)
  /-- the DOFs, on continuous forms; they depend only on the face `g` -/
  dof : ∀ g k, DofIdx g k → contForms n →ₗ[ℝ] ℝ
  /-- the DOFs of the faces of `T` are unisolvent on `P(T)ᵏ` -/
  unisolvent : ∀ (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ), IsUnisolvent fun p : Σ g : (vertexSet T).powerset,
      DofIdx (g : Finset (Fin n → ℝ)) k =>
    dof (p.1 : Finset (Fin n → ℝ)) k p.2 ∘ₗ
      Submodule.inclusion (show space T k ≤ contForms n from
        fun _ hw => (contDiff_of_mem hw).continuous)
  /-- **trace determination** on common facets -/
  trace : ∀ {T T' : Affine.Simplex ℝ (Fin n → ℝ) n} {F : Finset (Fin n → ℝ)} {k w η},
    F ⊆ vertexSet T → F ⊆ vertexSet T' → F.card = n → (hw : w ∈ space T k) →
      (hη : η ∈ space T' k) →
      (∀ g ⊆ F, ∀ i, dof g k i ⟨w, (contDiff_of_mem hw).continuous⟩ =
        dof g k i ⟨η, (contDiff_of_mem hη).continuous⟩) →
      ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)), TangentialTraceEq F k (w x) (η x)
  /-- the DOFs of a face `g` only see the tangential traces on `g` -/
  dof_congr : ∀ {g : Finset (Fin n → ℝ)} {k} (i : DofIdx g k) {w η : contForms n},
    (∀ x ∈ convexHull ℝ (g : Set (Fin n → ℝ)),
      TangentialTraceEq g k ((w : FormField n) x) ((η : FormField n) x)) →
      dof g k i w = dof g k i η
  /-- **Stokes compatibility**: `ℓ_{g,i} ∘ d` is a combination of the DOFs of the faces of `g` -/
  dof_extDeriv : ∀ (g : Finset (Fin n → ℝ)) (k : ℕ) (i : DofIdx g (k + 1)), dof g (k + 1) i ∘ₗ extDerivC1 ∈
    Submodule.span ℝ (Set.range fun p : Σ g' : g.powerset, DofIdx (g' : Finset (Fin n → ℝ)) k =>
      dof (p.1 : Finset (Fin n → ℝ)) k p.2 ∘ₗ Submodule.inclusion c1Forms_le_contForms)

/-! ### Linearity of piecewise `L²` fields -/

section PieceL2

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] (M : SimplicialMesh n)
  (S : Set (Fin n → ℝ))

omit [Fintype ι] in
theorem pieceL2_add {v w : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → 𝕜}
    (hv : ∀ T ∈ M.simplices, ∀ i, Continuous (v T i))
    (hw : ∀ T ∈ M.simplices, ∀ i, Continuous (w T i)) :
    pieceL2 M S (fun T i x => v T i x + w T i x) (fun T hT i => (hv T hT i).add (hw T hT i)) =
      pieceL2 M S v hv + pieceL2 M S w hw := by
  refine PiLp.ext fun i => Lp.ext ?_
  filter_upwards [coeFn_pieceL2 M S (fun T i x => v T i x + w T i x)
    (fun T hT i => (hv T hT i).add (hw T hT i)) i,
    Lp.coeFn_add (pieceL2 M S v hv i) (pieceL2 M S w hw i),
    coeFn_pieceL2 M S v hv i, coeFn_pieceL2 M S w hw i] with x h1 h2 h3 h4
  rw [PiLp.add_apply, h2, h1, Pi.add_apply, h3, h4]
  simp only [pieceFun, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hx : x ∈ interior T.closedInterior <;> simp [hx]

omit [Fintype ι] in
theorem pieceL2_smul (c : 𝕜) {v : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → 𝕜}
    (hv : ∀ T ∈ M.simplices, ∀ i, Continuous (v T i)) :
    pieceL2 M S (fun T i x => c * v T i x) (fun T hT i => continuous_const.mul (hv T hT i)) =
      c • pieceL2 M S v hv := by
  refine PiLp.ext fun i => Lp.ext ?_
  filter_upwards [coeFn_pieceL2 M S (fun T i x => c * v T i x)
    (fun T hT i => continuous_const.mul (hv T hT i)) i,
    Lp.coeFn_smul c (pieceL2 M S v hv i), coeFn_pieceL2 M S v hv i] with x h1 h2 h3
  rw [PiLp.smul_apply, h2, h1, Pi.smul_apply, h3, smul_eq_mul]
  simp only [pieceFun, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hx : x ∈ interior T.closedInterior <;> simp [hx]

end PieceL2

/-- Tangential traces on a facet determine those on its faces. -/
theorem TangentialTraceEq.mono {g F : Finset (Fin n → ℝ)} {k : ℕ} {α β : Finset (Fin n) → ℝ}
    (h : TangentialTraceEq F k α β) (hgF : g ⊆ F) : TangentialTraceEq g k α β :=
  fun V hV => h V fun l => vectorSpan_mono ℝ (Finset.coe_subset.2 hgF) (hV l)

namespace LocalElement

variable (E : LocalElement n)

attribute [instance] LocalElement.finiteDimensional LocalElement.dofIdxFintype

theorem le_contForms (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    E.space T k ≤ contForms n := fun _ hw => (E.contDiff_of_mem hw).continuous

theorem le_c1Forms (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    E.space T k ≤ c1Forms n := fun _ hw => E.contDiff_of_mem hw

/-- The local DOF of the face `g` on `P(T)ᵏ`. -/
def localDof (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) (g : Finset (Fin n → ℝ))
    (i : E.DofIdx g k) : E.space T k →ₗ[ℝ] ℝ :=
  E.dof g k i ∘ₗ Submodule.inclusion (E.le_contForms T k)

theorem localDof_apply (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) (g : Finset (Fin n → ℝ))
    (i : E.DofIdx g k) (u : E.space T k) :
    E.localDof T k g i u = E.dof g k i ⟨u, E.le_contForms T k u.2⟩ := rfl

/-- The local spaces are determined by the DOFs of the faces of `T`. -/
theorem localSpace_ext (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) {u v : E.space T k}
    (h : ∀ g ⊆ vertexSet T, ∀ i, E.localDof T k g i u = E.localDof T k g i v) : u = v :=
  (E.unisolvent T k).ext fun p => h p.1 (mem_powerset.1 p.1.2) p.2

/-! ### The global spaces -/

variable (M : SimplicialMesh n)

/-- The piecewise fields `(u_T)_{T ∈ M}`, `u_T ∈ P(T)ᵏ`. -/
abbrev Piecewise (k : ℕ) := ∀ T : M.simplices, E.space T k

/-- **The global finite element space** `Λ_hᵏ(M)`: piecewise fields whose DOFs agree on shared
faces. -/
def globalSpace (k : ℕ) : Submodule ℝ (E.Piecewise M k) where
  carrier := {u | ∀ T T' : M.simplices, ∀ g, g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) →
    g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) → ∀ i,
      E.localDof T k g i (u T) = E.localDof T' k g i (u T')}
  zero_mem' := fun T T' g _ _ i => by simp
  add_mem' := fun hu hv T T' g hg hg' i => by
    simp only [Pi.add_apply, map_add, hu T T' g hg hg' i, hv T T' g hg hg' i]
  smul_mem' := fun c u hu T T' g hg hg' i => by
    simp only [Pi.smul_apply, map_smul, hu T T' g hg hg' i]

theorem mem_globalSpace {k : ℕ} {u : E.Piecewise M k} :
    u ∈ E.globalSpace M k ↔ ∀ T T' : M.simplices, ∀ g,
      g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) →
        g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) → ∀ i,
          E.localDof T k g i (u T) = E.localDof T' k g i (u T') := Iff.rfl

instance (k : ℕ) : FiniteDimensional ℝ (E.globalSpace M k) := inferInstance

/-- The faces (vertex sets) of the mesh, as a `Finset`. -/
def meshFaces : Finset (Finset (Fin n → ℝ)) :=
  M.simplices.biUnion fun T => (vertexSet T).powerset

theorem mem_meshFaces {g : Finset (Fin n → ℝ)} :
    g ∈ meshFaces M ↔ ∃ T ∈ M.simplices, g ⊆ vertexSet T := by
  simp [meshFaces]

/-- A simplex of the mesh containing the face `g`. -/
def faceSimplex (g : meshFaces M) : M.simplices :=
  ⟨((mem_meshFaces M).1 g.2).choose, ((mem_meshFaces M).1 g.2).choose_spec.1⟩

theorem subset_faceSimplex (g : meshFaces M) :
    (g : Finset (Fin n → ℝ)) ⊆ vertexSet ((faceSimplex M g : M.simplices) :
      Affine.Simplex ℝ (Fin n → ℝ) n) :=
  ((mem_meshFaces M).1 g.2).choose_spec.2

/-- The global DOF index: the DOFs of all faces of the mesh. -/
abbrev GlobalDofIdx (k : ℕ) := Σ g : meshFaces M, E.DofIdx g k

/-- **The global DOFs** `Λ_hᵏ(M) → ℝ^{global DOFs}`. -/
def globalDof (k : ℕ) : E.globalSpace M k →ₗ[ℝ] (E.GlobalDofIdx M k → ℝ) where
  toFun u p := E.localDof (faceSimplex M p.1) k p.1 p.2 ((u : E.Piecewise M k) (faceSimplex M p.1))
  map_add' u v := funext fun p => by simp
  map_smul' c u := funext fun p => by simp

theorem globalDof_apply (k : ℕ) (u : E.globalSpace M k) (p : E.GlobalDofIdx M k)
    (T : M.simplices) (hT : (p.1 : Finset (Fin n → ℝ)) ⊆ vertexSet
      (T : Affine.Simplex ℝ (Fin n → ℝ) n)) :
    E.globalDof M k u p = E.localDof T k p.1 p.2 ((u : E.Piecewise M k) T) :=
  u.2 _ _ _ (subset_faceSimplex M p.1) hT p.2

/-- The piecewise field with prescribed global DOFs: on each `T`, the local field with the
DOFs of the faces of `T`. -/
def ofGlobalDof (k : ℕ) (c : E.GlobalDofIdx M k → ℝ) : E.Piecewise M k := fun T =>
  (E.unisolvent T k).equiv.symm fun p =>
    c ⟨⟨p.1, (mem_meshFaces M).2 ⟨T, T.2, mem_powerset.1 p.1.2⟩⟩, p.2⟩

theorem localDof_ofGlobalDof (k : ℕ) (c : E.GlobalDofIdx M k → ℝ) (T : M.simplices)
    (g : Finset (Fin n → ℝ)) (hg : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (i : E.DofIdx g k) :
    E.localDof T k g i (E.ofGlobalDof M k c T) =
      c ⟨⟨g, (mem_meshFaces M).2 ⟨T, T.2, hg⟩⟩, i⟩ :=
  (E.unisolvent T k).dof_equiv_symm _ ⟨⟨g, mem_powerset.2 hg⟩, i⟩

theorem ofGlobalDof_mem (k : ℕ) (c : E.GlobalDofIdx M k → ℝ) :
    E.ofGlobalDof M k c ∈ E.globalSpace M k := fun T T' g hg hg' i => by
  rw [localDof_ofGlobalDof _ _ _ _ _ _ hg, localDof_ofGlobalDof _ _ _ _ _ _ hg']

/-- **The global DOFs are a linear isomorphism** `Λ_hᵏ(M) ≃ ℝ^{global DOFs}`. -/
def globalDofEquiv (k : ℕ) : E.globalSpace M k ≃ₗ[ℝ] (E.GlobalDofIdx M k → ℝ) :=
  LinearEquiv.ofBijective (E.globalDof M k) ⟨fun u v huv => by
    refine Subtype.ext (funext fun T => E.localSpace_ext T k fun g hg i => ?_)
    have hu := E.globalDof_apply M k u ⟨⟨g, (mem_meshFaces M).2 ⟨T, T.2, hg⟩⟩, i⟩ T hg
    have hv := E.globalDof_apply M k v ⟨⟨g, (mem_meshFaces M).2 ⟨T, T.2, hg⟩⟩, i⟩ T hg
    rw [← hu, ← hv, huv], fun c => ⟨⟨_, E.ofGlobalDof_mem M k c⟩, funext fun p => by
      rw [E.globalDof_apply M k _ p (faceSimplex M p.1) (subset_faceSimplex M p.1)]
      exact localDof_ofGlobalDof _ _ _ _ _ _ (subset_faceSimplex M p.1) _⟩⟩

/-- **`dim Λ_hᵏ(M) = Σ_g #DOF(g)`**, the number of global DOFs. -/
theorem finrank_globalSpace (k : ℕ) :
    Module.finrank ℝ (E.globalSpace M k) = Fintype.card (E.GlobalDofIdx M k) := by
  rw [(E.globalDofEquiv M k).finrank_eq, Module.finrank_fintype_fun_eq_card]

/-! ### Traces of global fields -/

theorem dof_congr_of_mem_span {g : Finset (Fin n → ℝ)} {k : ℕ} {L : c1Forms n →ₗ[ℝ] ℝ}
    (hL : L ∈ Submodule.span ℝ (Set.range fun p : Σ g' : g.powerset,
      E.DofIdx (g' : Finset (Fin n → ℝ)) k =>
        E.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ∘ₗ Submodule.inclusion c1Forms_le_contForms))
    {a b : c1Forms n}
    (h : ∀ g' ⊆ g, ∀ i, E.dof g' k i (Submodule.inclusion c1Forms_le_contForms a) =
      E.dof g' k i (Submodule.inclusion c1Forms_le_contForms b)) : L a = L b := by
  induction hL using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact h _ (mem_powerset.1 p.1.2) p.2
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

/-- The exterior derivative `P(T)ᵏ → P(T)ᵏ⁺¹`. -/
def localD (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) : E.space T k →ₗ[ℝ] E.space T (k + 1) where
  toFun u := ⟨extDeriv u, E.extDeriv_mem u.2⟩
  map_add' u v := Subtype.ext (funext fun x => extDeriv_add_apply
    ((E.contDiff_of_mem u.2).differentiable one_ne_zero x)
    ((E.contDiff_of_mem v.2).differentiable one_ne_zero x))
  map_smul' c u := Subtype.ext (funext fun x => extDeriv_smul_const_apply c
    ((E.contDiff_of_mem u.2).differentiable one_ne_zero x))

@[simp] theorem coe_localD (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) (u : E.space T k) :
    (E.localD T k u : FormField n) = extDeriv u := rfl

theorem localDof_localD (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) (g : Finset (Fin n → ℝ))
    (i : E.DofIdx g (k + 1)) (u : E.space T k) :
    E.localDof T (k + 1) g i (E.localD T k u) =
      (E.dof g (k + 1) i ∘ₗ extDerivC1) ⟨u, E.le_c1Forms T k u.2⟩ := rfl

/-- **Global fields have continuous tangential traces**: on an interior facet `F` with
neighbours `T`, `T'`, the tangential traces of `u_T` and `u_T'` agree. -/
theorem tangentialTraceEq_of_mem_globalSpace {k : ℕ} {u : E.Piecewise M k}
    (hu : u ∈ E.globalSpace M k) {F : Finset (Fin n → ℝ)} (hF : F ∈ M.facets)
    (T T' : M.simplices) (hT : F ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (hT' : F ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n)) :
    ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)),
      TangentialTraceEq F k ((u T : FormField n) x) ((u T' : FormField n) x) :=
  E.trace hT hT' hF.1 (u T).2 (u T').2 fun g hg i =>
    hu T T' g (hg.trans hT) (hg.trans hT') i

/-- The stars of the faces of `M` are **facet-connected**: two `n`-simplices containing a face `g`
are joined by a chain of `n`-simplices containing `g`, consecutive ones sharing a facet that
contains `g`. (Fails for two triangles meeting only at a vertex.) -/
def FacetConnected : Prop :=
  ∀ g : Finset (Fin n → ℝ), ∀ T T' : M.simplices,
    g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) →
      g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) →
        Relation.ReflTransGen (fun T₁ T₂ : M.simplices => ∃ F ∈ M.facets, g ⊆ F ∧
          F ⊆ vertexSet (T₁ : Affine.Simplex ℝ (Fin n → ℝ) n) ∧
            F ⊆ vertexSet (T₂ : Affine.Simplex ℝ (Fin n → ℝ) n)) T T'

/-- **`Λ_hᵏ(M)` is the space of piecewise fields with continuous tangential traces** (for meshes
with facet-connected face stars): DOF agreement on shared faces is equivalent to the agreement
of the tangential traces on the facets. -/
theorem mem_globalSpace_iff (hM : FacetConnected M) {k : ℕ} {u : E.Piecewise M k} :
    u ∈ E.globalSpace M k ↔ ∀ F ∈ M.facets, ∀ T T' : M.simplices,
      F ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) →
        F ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) →
          ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)),
            TangentialTraceEq F k ((u T : FormField n) x) ((u T' : FormField n) x) := by
  refine ⟨fun hu F hF T T' hT hT' => E.tangentialTraceEq_of_mem_globalSpace M hu hF T T' hT hT',
    fun h T T' g hg hg' i => ?_⟩
  induction hM g T T' hg hg' with
  | refl => rfl
  | tail _ hstep ih =>
    obtain ⟨F, hF, hgF, h1, h2⟩ := hstep
    exact (ih (hgF.trans h1)).trans (E.dof_congr i fun x hx =>
      (h F hF _ _ h1 h2 x (convexHull_mono (Finset.coe_subset.2 hgF) hx)).mono hgF)

/-! ### `d Λ_hᵏ ⊆ Λ_hᵏ⁺¹` -/

/-- The elementwise exterior derivative of piecewise fields. -/
def dPiecewise (k : ℕ) : E.Piecewise M k →ₗ[ℝ] E.Piecewise M (k + 1) :=
  LinearMap.pi fun T => E.localD T k ∘ₗ LinearMap.proj T

@[simp] theorem dPiecewise_apply (k : ℕ) (u : E.Piecewise M k) (T : M.simplices) :
    E.dPiecewise M k u T = E.localD T k (u T) := rfl

/-- **`d Λ_hᵏ ⊆ Λ_hᵏ⁺¹`**: DOFs of `d u` on a face are combinations of DOFs of `u` on its
subfaces (`dof_extDeriv`). -/
theorem dPiecewise_mem_globalSpace {k : ℕ} {u : E.Piecewise M k} (hu : u ∈ E.globalSpace M k) :
    E.dPiecewise M k u ∈ E.globalSpace M (k + 1) := fun T T' g hg hg' i => by
  rw [dPiecewise_apply, dPiecewise_apply, localDof_localD, localDof_localD]
  exact E.dof_congr_of_mem_span (E.dof_extDeriv g k i) fun g' hg'g j =>
    hu T T' g' (hg'g.trans hg) (hg'g.trans hg') j

/-- The exterior derivative `Λ_hᵏ(M) → Λ_hᵏ⁺¹(M)`. -/
def dGlobal (k : ℕ) : E.globalSpace M k →ₗ[ℝ] E.globalSpace M (k + 1) :=
  (E.dPiecewise M k).restrict fun _ hu => E.dPiecewise_mem_globalSpace M hu

/-! ### Vanishing boundary DOFs -/

/-- The global space with **vanishing boundary DOFs** `Λ̊_hᵏ(M)`: the DOFs of the faces lying in
boundary facets vanish. -/
def globalSpace₀ (k : ℕ) : Submodule ℝ (E.Piecewise M k) :=
  E.globalSpace M k ⊓
    { carrier := {u | ∀ T : M.simplices, ∀ F, M.IsBoundaryFacet F →
        F ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) → ∀ g ⊆ F, ∀ i,
          E.localDof T k g i (u T) = 0}
      zero_mem' := fun T F _ _ g _ i => by simp
      add_mem' := fun hu hv T F hF hFT g hg i => by
        simp only [Pi.add_apply, map_add, hu T F hF hFT g hg i, hv T F hF hFT g hg i, add_zero]
      smul_mem' := fun c u hu T F hF hFT g hg i => by
        simp only [Pi.smul_apply, map_smul, hu T F hF hFT g hg i, smul_zero] }

theorem globalSpace₀_le (k : ℕ) : E.globalSpace₀ M k ≤ E.globalSpace M k := inf_le_left

theorem dPiecewise_mem_globalSpace₀ {k : ℕ} {u : E.Piecewise M k}
    (hu : u ∈ E.globalSpace₀ M k) : E.dPiecewise M k u ∈ E.globalSpace₀ M (k + 1) := by
  refine ⟨E.dPiecewise_mem_globalSpace M hu.1, fun T F hF hFT g hg i => ?_⟩
  rw [dPiecewise_apply, localDof_localD]
  have h := E.dof_congr_of_mem_span (E.dof_extDeriv g k i) (a := ⟨u T, E.le_c1Forms T k (u T).2⟩)
    (b := 0) fun g' hg'g j => by
      rw [map_zero, map_zero]
      exact hu.2 T F hF hFT g' (hg'g.trans hg) j
  rw [h, map_zero]

/-- Fields with vanishing boundary DOFs have vanishing tangential traces on boundary facets. -/
theorem tangentialTraceEq_zero_of_mem_globalSpace₀ {k : ℕ} {u : E.Piecewise M k}
    (hu : u ∈ E.globalSpace₀ M k) {F : Finset (Fin n → ℝ)} (hF : M.IsBoundaryFacet F)
    (T : M.simplices) (hT : F ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)) :
    ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)),
      TangentialTraceEq F k ((u T : FormField n) x) 0 := by
  have h := E.trace hT hT hF.1.1 (u T).2 (Submodule.zero_mem _) fun g hg i => by
    have := hu.2 T F hF hT g hg i
    rw [localDof_apply] at this
    rw [this]
    exact (map_zero _).symm
  simpa using h

/-! ### The global canonical interpolant -/

/-- **The global canonical interpolant** `Π_h : C⁰Λᵏ → Λ_hᵏ(M)`: on each `T`, the local field with
the DOFs of `w`. -/
def globalInterp (k : ℕ) : contForms n →ₗ[ℝ] E.globalSpace M k where
  toFun w := ⟨fun T => (E.unisolvent T k).equiv.symm fun p => E.dof p.1 k p.2 w,
    fun T T' g hg hg' i => by
      rw [localDof_apply, localDof_apply]
      have h1 := (E.unisolvent (T : Affine.Simplex ℝ (Fin n → ℝ) n) k).dof_equiv_symm
        (fun p => E.dof p.1 k p.2 w) ⟨⟨g, mem_powerset.2 hg⟩, i⟩
      have h2 := (E.unisolvent (T' : Affine.Simplex ℝ (Fin n → ℝ) n) k).dof_equiv_symm
        (fun p => E.dof p.1 k p.2 w) ⟨⟨g, mem_powerset.2 hg'⟩, i⟩
      exact h1.trans h2.symm⟩
  map_add' w w' := Subtype.ext (funext fun T => by
    simp only [map_add, Submodule.coe_add, Pi.add_apply]
    rw [← map_add]; rfl)
  map_smul' c w := Subtype.ext (funext fun T => by
    simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    rw [← map_smul]; rfl)

theorem localDof_globalInterp (k : ℕ) (w : contForms n) (T : M.simplices) (g : Finset (Fin n → ℝ))
    (hg : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)) (i : E.DofIdx g k) :
    E.localDof T k g i ((E.globalInterp M k w : E.Piecewise M k) T) = E.dof g k i w :=
  (E.unisolvent (T : Affine.Simplex ℝ (Fin n → ℝ) n) k).dof_equiv_symm
    (fun p => E.dof p.1 k p.2 w) ⟨⟨g, mem_powerset.2 hg⟩, i⟩

/-- **`Π_h` is a projection onto `Λ_hᵏ(M)`.** -/
theorem globalInterp_piecewise (k : ℕ) (u : E.globalSpace M k) (w : contForms n)
    (hw : ∀ T : M.simplices, ∀ g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n), ∀ i,
      E.dof g k i w = E.localDof T k g i ((u : E.Piecewise M k) T)) :
    E.globalInterp M k w = u :=
  Subtype.ext (funext fun T => E.localSpace_ext T k fun g hg i => by
    rw [localDof_globalInterp _ _ _ _ _ _ hg, hw T g hg i])

/-- **The global canonical interpolant commutes with `d`** on `C¹` forms:
`Π_h (dw) = d (Π_h w)`. -/
theorem globalInterp_extDeriv (k : ℕ) (w : c1Forms n) :
    E.globalInterp M (k + 1) (extDerivC1 w) =
      E.dGlobal M k (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w)) := by
  refine Subtype.ext (funext fun T => E.localSpace_ext T (k + 1) fun g hg i => ?_)
  rw [localDof_globalInterp _ _ _ _ _ _ hg]
  change (E.dof g (k + 1) i ∘ₗ extDerivC1) w = E.localDof T (k + 1) g i
    (E.localD T k ((E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) :
      E.Piecewise M k) T))
  rw [localDof_localD]
  refine E.dof_congr_of_mem_span (E.dof_extDeriv g k i) fun g' hg' j => ?_
  have := E.localDof_globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) T g'
    (hg'.trans hg) j
  rw [localDof_apply] at this
  exact this.symm

/-! ### The glued `L²` spaces and the subcomplexes -/

/-- A piecewise field as a family indexed by all simplices (zero off the mesh). -/
def extendPW {k : ℕ} (u : E.Piecewise M k) (T : Affine.Simplex ℝ (Fin n → ℝ) n) : FormField n := by
  classical exact if h : T ∈ M.simplices then (u ⟨T, h⟩ : FormField n) else 0

theorem extendPW_of_mem {k : ℕ} (u : E.Piecewise M k) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ M.simplices) : E.extendPW M u T = (u ⟨T, hT⟩ : FormField n) := by
  simp [extendPW, hT]

theorem extendPW_add {k : ℕ} (u v : E.Piecewise M k) (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    E.extendPW M (u + v) T = E.extendPW M u T + E.extendPW M v T := by
  unfold extendPW; split_ifs <;> simp

theorem extendPW_smul {k : ℕ} (c : ℝ) (u : E.Piecewise M k) (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    E.extendPW M (c • u) T = c • E.extendPW M u T := by
  unfold extendPW; split_ifs <;> simp

theorem contDiff_extendPW {k : ℕ} (u : E.Piecewise M k) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ M.simplices) : ContDiff ℝ 1 (E.extendPW M u T) := by
  rw [extendPW_of_mem _ _ _ hT]; exact E.contDiff_of_mem (u ⟨T, hT⟩).2

theorem isDeg_extendPW {k : ℕ} (u : E.Piecewise M k) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ M.simplices) (x : Fin n → ℝ) : IsDeg k (E.extendPW M u T x) := by
  rw [extendPW_of_mem _ _ _ hT]; exact E.isDeg_of_mem (u ⟨T, hT⟩).2 x

/-- **Gluing**: a piecewise field of degree `k` as an element of `L²(Ω; Λᵏ)`
(`k = k'.toNat` for `k' ≥ 0`; for `k' < 0` the target is the zero space). -/
def glue (k : ℤ) : E.Piecewise M k.toNat →ₗ[ℝ] L2F ℝ M.domain (formIdx n k) where
  toFun u := pieceL2 M M.domain (fun T => formComp (k := k) (E.extendPW M u T))
    (fun T hT s => continuous_formComp (E.contDiff_extendPW M u hT).continuous s)
  map_add' u v := by
    refine (pieceL2_congr M _ _ _ fun T _ => ?_).trans (pieceL2_add M M.domain _ _)
    funext s x
    change E.extendPW M (u + v) T x s.1 = E.extendPW M u T x s.1 + E.extendPW M v T x s.1
    rw [extendPW_add]; rfl
  map_smul' c u := by
    refine (pieceL2_congr M _ _ _ fun T _ => ?_).trans (pieceL2_smul M M.domain c _)
    funext s x
    change E.extendPW M (c • u) T x s.1 = c * E.extendPW M u T x s.1
    rw [extendPW_smul]; rfl

/-- The glued global spaces `Vₕᵏ ⊆ L²(Ω; Λᵏ)`. -/
def V (k : ℤ) : Submodule ℝ (L2F ℝ M.domain (formIdx n k)) :=
  LinearMap.range (E.glue M k ∘ₗ (E.globalSpace M k.toNat).subtype)

/-- The glued global spaces with vanishing boundary DOFs `V̊ₕᵏ`. -/
def V₀ (k : ℤ) : Submodule ℝ (L2F ℝ M.domain (formIdx n k)) :=
  LinearMap.range (E.glue M k ∘ₗ (E.globalSpace₀ M k.toNat).subtype)

instance (k : ℤ) : FiniteDimensional ℝ (E.V M k) := by
  have : FiniteDimensional ℝ (E.globalSpace M k.toNat) := inferInstance
  exact Module.Finite.range _

instance (k : ℤ) : FiniteDimensional ℝ (E.V₀ M k) := by
  have : FiniteDimensional ℝ (E.globalSpace₀ M k.toNat) :=
    FiniteDimensional.finiteDimensional_submodule _
  exact Module.Finite.range _

theorem subsingleton_L2F_negSucc (S : Set (Fin n → ℝ)) (k : ℕ) :
    Subsingleton (L2F ℝ S (formIdx n (Int.negSucc k))) := by
  constructor
  intro x y
  refine PiLp.ext fun s => ?_
  exact absurd s.2 (by have := Int.natCast_nonneg (#s.1); omega)

/-- **Conformity of the global spaces**: `Vₕᵏ ⊆ HΛᵏ(Ω)`, with `d_max` the elementwise `d`. -/
theorem glue_mem_maximal [NeZero n] (hΩ : IsOpen M.domain) (k : ℕ) (u : E.globalSpace M k) :
    ∃ h : E.glue M k (u : E.Piecewise M k) ∈ ((extDerivOp ℝ n k).maximal M.domain).domain,
      (extDerivOp ℝ n k).maximal M.domain ⟨_, h⟩ =
        E.glue M ((k : ℤ) + 1) (E.dPiecewise M k u) := by
  obtain ⟨h, hval⟩ := extDeriv_pieceL2_mem_maximal_domain k M hΩ
    (η := E.extendPW M (u : E.Piecewise M k))
    (fun T hT => E.contDiff_extendPW M _ hT) (fun T hT x => E.isDeg_extendPW M _ hT x)
    fun F hF T hT T' hT' x hx => by
      rw [E.extendPW_of_mem M _ (M.mem_cofaces.1 hT).1,
        E.extendPW_of_mem M _ (M.mem_cofaces.1 hT').1]
      exact E.tangentialTraceEq_of_mem_globalSpace M u.2 hF.1 _ _ (M.mem_cofaces.1 hT).2
        (M.mem_cofaces.1 hT').2 x hx
  refine ⟨h, hval.trans ?_⟩
  change _ = pieceL2 M M.domain
    (fun T => formComp (k := (k : ℤ) + 1) (E.extendPW M (E.dPiecewise M k (u : E.Piecewise M k)) T))
    (fun T hT s => continuous_formComp (E.contDiff_extendPW M _ hT).continuous s)
  refine pieceL2_congr M _ _ _ fun T hT => ?_
  rw [E.extendPW_of_mem M _ hT, E.extendPW_of_mem M _ hT]
  rfl

/-- **Conformity with vanishing boundary DOFs**: `V̊ₕᵏ ⊆ H̊Λᵏ(Ω)` (`Ω` strictly star-shaped). -/
theorem glue_mem_minimal [NeZero n] (hΩ : IsOpen M.domain) (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain)
    (k : ℕ) (u : E.globalSpace₀ M k) :
    ∃ h : E.glue M k (u : E.Piecewise M k) ∈ ((extDerivOp ℝ n k).minimal M.domain).domain,
      (extDerivOp ℝ n k).minimal M.domain ⟨_, h⟩ =
        E.glue M ((k : ℤ) + 1) (E.dPiecewise M k u) := by
  obtain ⟨h, hval⟩ := extDeriv_pieceL2_mem_minimal_domain k M hΩ
    (η := E.extendPW M (u : E.Piecewise M k))
    (fun T hT => E.contDiff_extendPW M _ hT) (fun T hT x => E.isDeg_extendPW M _ hT x)
    (fun F hF T hT T' hT' x hx => by
      rw [E.extendPW_of_mem M _ (M.mem_cofaces.1 hT).1,
        E.extendPW_of_mem M _ (M.mem_cofaces.1 hT').1]
      exact E.tangentialTraceEq_of_mem_globalSpace M u.2.1 hF.1 _ _ (M.mem_cofaces.1 hT).2
        (M.mem_cofaces.1 hT').2 x hx)
    (fun F hF T hT x hx => by
      rw [E.extendPW_of_mem M _ (M.mem_cofaces.1 hT).1]
      exact E.tangentialTraceEq_zero_of_mem_globalSpace₀ M u.2 hF _ (M.mem_cofaces.1 hT).2 x hx)
    x₀ hstar
  refine ⟨h, hval.trans ?_⟩
  change _ = pieceL2 M M.domain
    (fun T => formComp (k := (k : ℤ) + 1) (E.extendPW M (E.dPiecewise M k (u : E.Piecewise M k)) T))
    (fun T hT s => continuous_formComp (E.contDiff_extendPW M _ hT).continuous s)
  refine pieceL2_congr M _ _ _ fun T hT => ?_
  rw [E.extendPW_of_mem M _ hT, E.extendPW_of_mem M _ hT]
  rfl

theorem apply_mem_of_eq {W W' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W']
    [Module ℝ W'] {S S' : W →ₗ.[ℝ] W'} (h : S = S') (y : S.domain) (P : W' → Prop)
    (hP : ∀ y' : S'.domain, (y' : W) = y → P (S' y')) : P (S y) := by
  subst h; exact hP y rfl

theorem V_le_maximal_domain [NeZero n] (hΩ : IsOpen M.domain) (i : ℤ) :
    E.V M i ≤ ((extDerivOp ℝ n i).maximal M.domain).domain := by
  rintro x ⟨u, rfl⟩
  rcases i with k | k
  · exact (E.glue_mem_maximal M hΩ k u).1
  · have := subsingleton_L2F_negSucc M.domain (n := n) k
    rw [Subsingleton.elim (LinearMap.comp _ _ u) 0]
    exact Submodule.zero_mem _

theorem maximal_apply_mem_V [NeZero n] (hΩ : IsOpen M.domain) (i : ℤ)
    (y : ((extDerivOp ℝ n i).maximal M.domain).domain)
    (hy : (y : L2F ℝ M.domain (formIdx n i)) ∈ E.V M i) :
    (extDerivOp ℝ n i).maximal M.domain y ∈ E.V M (i + 1) := by
  obtain ⟨u, hu⟩ := hy
  rcases i with k | k
  · obtain ⟨h, hval⟩ := E.glue_mem_maximal M hΩ k u
    have hy' : y = ⟨_, h⟩ := Subtype.ext hu.symm
    show (extDerivOp ℝ n (k : ℤ)).maximal M.domain y ∈ E.V M ((k : ℤ) + 1)
    rw [hy', hval]
    exact ⟨⟨_, E.dPiecewise_mem_globalSpace M u.2⟩, rfl⟩
  · have := subsingleton_L2F_negSucc M.domain (n := n) k
    have : y = 0 := Subtype.ext (Subsingleton.elim _ _)
    rw [this, LinearPMap.map_zero]
    exact Submodule.zero_mem _

theorem V₀_le_minimal_domain [NeZero n] (hΩ : IsOpen M.domain) (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain)
    (i : ℤ) : E.V₀ M i ≤ ((extDerivOp ℝ n i).minimal M.domain).domain := by
  rintro x ⟨u, rfl⟩
  rcases i with k | k
  · exact (E.glue_mem_minimal M hΩ x₀ hstar k u).1
  · have := subsingleton_L2F_negSucc M.domain (n := n) k
    rw [Subsingleton.elim (LinearMap.comp _ _ u) 0]
    exact Submodule.zero_mem _

theorem minimal_apply_mem_V₀ [NeZero n] (hΩ : IsOpen M.domain) (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain)
    (i : ℤ) (y : ((extDerivOp ℝ n i).minimal M.domain).domain)
    (hy : (y : L2F ℝ M.domain (formIdx n i)) ∈ E.V₀ M i) :
    (extDerivOp ℝ n i).minimal M.domain y ∈ E.V₀ M (i + 1) := by
  obtain ⟨u, hu⟩ := hy
  rcases i with k | k
  · obtain ⟨h, hval⟩ := E.glue_mem_minimal M hΩ x₀ hstar k u
    have hy' : y = ⟨_, h⟩ := Subtype.ext hu.symm
    show (extDerivOp ℝ n (k : ℤ)).minimal M.domain y ∈ E.V₀ M ((k : ℤ) + 1)
    rw [hy', hval]
    exact ⟨⟨_, E.dPiecewise_mem_globalSpace₀ M u.2⟩, rfl⟩
  · have := subsingleton_L2F_negSucc M.domain (n := n) k
    have : y = 0 := Subtype.ext (Subsingleton.elim _ _)
    rw [this, LinearPMap.map_zero]
    exact Submodule.zero_mem _

/-- **The finite element subcomplex** `Vₕ ⊆ HΛ(Ω)` of the maximal de Rham complex: the glued
global spaces `Vₕᵏ` are finite-dimensional, lie in `D(d_max)`, and `d Vₕᵏ ⊆ Vₕᵏ⁺¹`. -/
def subcomplex [NeZero n] (hΩ : IsOpen M.domain) :
    ((deRham ℝ n).maximalComplex hΩ).Subcomplex where
  V := E.V M
  le_domain i j := by
    by_cases hij : i + 1 = j
    · subst hij
      rw [deRham_maximalComplex_d]
      exact E.V_le_maximal_domain M hΩ i
    · rw [HilbertComplex.domain_eq_top_of_not_rel _ (by simpa using hij)]
      exact le_top
  mapsTo i j x hx := by
    by_cases hij : i + 1 = j
    · subst hij
      exact apply_mem_of_eq (deRham_maximalComplex_d hΩ i) _ (· ∈ E.V M (i + 1))
        fun y' hy' => E.maximal_apply_mem_V M hΩ i y' (hy' ▸ hx)
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hij)]
      exact Submodule.zero_mem _

instance [NeZero n] (hΩ : IsOpen M.domain) (k : ℤ) :
    FiniteDimensional ℝ ((E.subcomplex M hΩ).V k) :=
  inferInstanceAs (FiniteDimensional ℝ (E.V M k))

/-- **The finite element subcomplex with vanishing boundary DOFs** `V̊ₕ ⊆ H̊Λ(Ω)` of the minimal
de Rham complex (`Ω` strictly star-shaped, e.g. convex). -/
def subcomplexMin [NeZero n] (hΩ : IsOpen M.domain) (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain) :
    ((deRham ℝ n).minimalComplex hΩ).Subcomplex where
  V := E.V₀ M
  le_domain i j := by
    by_cases hij : i + 1 = j
    · subst hij
      rw [deRham_minimalComplex_d]
      exact E.V₀_le_minimal_domain M hΩ x₀ hstar i
    · rw [HilbertComplex.domain_eq_top_of_not_rel _ (by simpa using hij)]
      exact le_top
  mapsTo i j x hx := by
    by_cases hij : i + 1 = j
    · subst hij
      exact apply_mem_of_eq (deRham_minimalComplex_d hΩ i) _ (· ∈ E.V₀ M (i + 1))
        fun y' hy' => E.minimal_apply_mem_V₀ M hΩ x₀ hstar i y' (hy' ▸ hx)
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hij)]
      exact Submodule.zero_mem _

instance [NeZero n] (hΩ : IsOpen M.domain) (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain)
    (k : ℤ) : FiniteDimensional ℝ ((E.subcomplexMin M hΩ x₀ hstar).V k) :=
  inferInstanceAs (FiniteDimensional ℝ (E.V₀ M k))

/-! ### Injectivity of the gluing and the dimensions of `Vₕᵏ` -/

/-- A local field vanishing on `T` is zero (its DOFs only see traces on the faces of `T`). -/
theorem localSpace_eq_zero_of_eqOn (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ)
    (u : E.space T k) (h : ∀ x ∈ T.closedInterior, (u : FormField n) x = 0) : u = 0 :=
  E.localSpace_ext T k fun g hg i => by
    rw [map_zero, localDof_apply]
    have : E.dof g k i ⟨u, E.le_contForms T k u.2⟩ = E.dof g k i 0 :=
      E.dof_congr i fun x hx V _ => by
        have hxT : x ∈ T.closedInterior := by
          rw [← convexHull_vertexSet]
          exact convexHull_mono (Finset.coe_subset.2 hg) hx
        simp [h x hxT]
    rw [this, map_zero]

theorem glue_injective (hΩ : IsOpen M.domain) (k : ℕ) :
    Function.Injective (E.glue M (k : ℤ)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  funext T
  refine E.localSpace_eq_zero_of_eqOn T k (u T) fun x hx => ?_
  funext s
  by_cases hs : #s = k
  swap
  · exact E.isDeg_of_mem (u T).2 x s hs
  set s' : formIdx n (k : ℤ) := ⟨s, by rw [hs]⟩
  set f : (Fin n → ℝ) → ℝ := fun y => ((u T : E.space T k) : FormField n) y s
  have hf : Continuous f := (continuous_apply s).comp (E.contDiff_of_mem (u T).2).continuous
  set U := interior (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ∩ M.domain
  have hU : IsOpen U := isOpen_interior.inter hΩ
  have hcomp := coeFn_pieceL2 M M.domain (fun T' => formComp (k := (k : ℤ)) (E.extendPW M u T'))
    (fun T' hT' s => continuous_formComp (E.contDiff_extendPW M u hT').continuous s) s'
  have h0 : (E.glue M (k : ℤ) u) s' = 0 := by rw [hu]; rfl
  have hae : f =ᵐ[volume.restrict U] 0 := by
    have h1 : (fun y => pieceFun M (fun T' => formComp (k := (k : ℤ)) (E.extendPW M u T') s') y)
        =ᵐ[volume.restrict M.domain] 0 := by
      refine hcomp.symm.trans ?_
      have := Lp.coeFn_zero ℝ 2 (volume.restrict M.domain)
      change ((E.glue M (k : ℤ) u) s' : (Fin n → ℝ) → ℝ) =ᵐ[_] 0
      rw [h0]
      exact this
    have h2 := ae_restrict_of_ae_restrict_of_subset (s := U) Set.inter_subset_right h1
    filter_upwards [h2, ae_restrict_mem hU.measurableSet] with y hy hyU
    rw [← hy, pieceFun_of_mem_interior M _ T.2 hyU.1, E.extendPW_of_mem M u T.2]
    rfl
  have hEq := Measure.eqOn_open_of_ae_eq hae hU hf.continuousOn continuousOn_const
  have hcl : T.1.closedInterior ⊆ closure U := by
    rw [← SimplicialMesh.closure_interior_closedInterior]
    refine closure_minimal (fun y hy => ?_) isClosed_closure
    rw [mem_closure_iff]
    intro V hV hyV
    have hy' : y ∈ closure M.domain :=
      M.closedInterior_subset_closure T.2 (interior_subset hy)
    obtain ⟨z, hz, hzΩ⟩ := mem_closure_iff.1 hy' (V ∩ interior T.1.closedInterior)
      (hV.inter isOpen_interior) ⟨hyV, hy⟩
    exact ⟨z, hz.1, hz.2, hzΩ⟩
  have hclosed : IsClosed {y | f y = 0} := isClosed_eq hf continuous_const
  exact closure_minimal (fun y hy => hEq hy) hclosed (hcl hx)

/-- **`dim Vₕᵏ = dim Λ_hᵏ(M) = Σ_g #DOF(g)`**: the gluing is injective. -/
theorem finrank_V (hΩ : IsOpen M.domain) (k : ℕ) :
    Module.finrank ℝ (E.V M k) = Fintype.card (E.GlobalDofIdx M k) := by
  have hinj : Function.Injective
      (E.glue M (k : ℤ) ∘ₗ (E.globalSpace M ((k : ℤ).toNat)).subtype) := by
    rw [LinearMap.coe_comp]
    exact (E.glue_injective M hΩ k).comp Subtype.val_injective
  rw [V, LinearMap.finrank_range_of_inj hinj]
  exact finrank_globalSpace E M k

end LocalElement

/-! ### The cases `k = 0` and `k = n` -/

/-- **`k = 0`**: equal tangential traces of `0`-forms means equal values (continuity across the
facet; Lagrange elements). -/
theorem tangentialTraceEq_zero_iff (F : Finset (Fin n → ℝ)) (α β : Finset (Fin n) → ℝ) :
    TangentialTraceEq F 0 α β ↔ α ∅ = β ∅ := by
  have key : ∀ (V : Fin n → Fin 0 → ℝ) (γ : Finset (Fin n) → ℝ), pullback V γ univ = γ ∅ := by
    intro V γ
    have hu : (Finset.univ : Finset (Fin 0)) = ∅ := Finset.univ_eq_empty
    rw [pullback_apply, Finset.sum_eq_single ∅ (fun r _ hr => ?_) (by simp)]
    · simp
    · have hr' : #(Finset.univ : Finset (Fin 0)) ≠ #r := by
        rw [hu, Finset.card_empty]; exact fun h => hr (Finset.card_eq_zero.1 h.symm)
      rw [isDeg_wedgeProd V r _ hr', mul_zero]
  refine ⟨fun h => ?_, fun h V _ => by rw [key, key, h]⟩
  have := h 0 fun l => l.elim0
  rwa [key, key] at this

/-- **`k = n`**: there is no tangential trace of an `n`-form on a facet: the trace condition is
vacuous (discontinuous Galerkin elements). -/
theorem tangentialTraceEq_top {m : ℕ} {F : Finset (Fin (m + 1) → ℝ)} (hc : F.card = m + 1)
    (α β : Finset (Fin (m + 1)) → ℝ) : TangentialTraceEq F (m + 1) α β := by
  classical
  intro V hV
  have hdet : (Matrix.of V).det = 0 := by
    by_contra h0
    have hli : LinearIndependent ℝ (Matrix.of V).col :=
      Matrix.linearIndependent_col_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2
        (Ne.isUnit h0))
    have h1 := finrank_span_eq_card hli
    have h2 : Submodule.span ℝ (Set.range (Matrix.of V).col) ≤
        vectorSpan ℝ (F : Set (Fin (m + 1) → ℝ)) := by
      rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact hV l
    have h3 := Submodule.finrank_mono h2
    have h4 := finrank_vectorSpan_image_finset_le ℝ (id : (Fin (m + 1) → ℝ) → _) F hc
    rw [Finset.image_id] at h4
    rw [h1, Fintype.card_fin] at h3
    omega
  rw [pullback_apply_univ, pullback_apply_univ, hdet, zero_mul, zero_mul]

end Feec.FiniteElement
