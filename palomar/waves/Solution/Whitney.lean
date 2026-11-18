module

public import Solution.Wave
public import Solution.Spaces
public import Solution.Forms
public import Feec.Models.Parallelepiped.StarShaped
public import Feec.Numerics.PlaneWaveCubeError

/-!
# The Whitney schemes of the cube

**Meshes.** The Freudenthal meshes of the cube (`cubeMesh`, the meshes of the challenge of
`Feec.Models.StarShaped.CubeWitness.meshFamily`, `SimplicialMesh.ofFeec`) are named by their
vertices (`points_cube`).

**Whitney spaces.** The Whitney sequence `topSeq` has the spaces of the trimmed sequence `P₁⁻Λ`
(`topSeq_space`), whose element is equivalent to the Whitney element
(`Feec.FiniteElement.whitneyElement_equivalent_trimmed`), so the spaces of `topSeq` on the
Freudenthal meshes are those of `Feec`'s Whitney complexes `Feec.Models.Cube.FEM.whitney` and
`whitneyMin` (`whitney_V_eq`, `whitneyMin_V_eq`).

**The Whitney interpolant.** The challenge's integral over an oriented simplex is `Feec`'s
(`simplexIntegral_eq`); in each degree `j` the challenge's interpolant (`IsWhitneyInterpAt`, the
body of `IsWhitneyInterp`) is the glued global interpolant of the Whitney element on every `Feec`
mesh (`isWhitneyInterpAt_iff`; the face integrals over `faceEnum g` are the challenge's,
`exists_comp_eq_faceEnum`, and other orientations differ by a sign), hence on the cube `Feec`'s
canonical interpolant `Feec.Models.Cube.Inhomogeneous.FEMInterp.canonicalInterp`
(`isWhitneyInterpAt_cube_iff`).

**The schemes.** The window `[0, 3)` of the challenge's `HΛ(Q)` is `ofFeec (complex 3)`
(`ofFeec_complex_d`), whose Whitney forms are the image of `Feec`'s Whitney row `whitneyRow N`
under `dEmb` (`mem_whitney_iff`, `mem_whitneyMin_iff`); the challenge's steps with the boundary
degrees of freedom of `g` are `Feec`'s `IsDirichletCNStep` and `IsDirichletLeapfrogStep` with
zero load (`isCNStep_iff`, `isLeapfrogStep_iff`), and the row solutions are `Feec`'s
(`RowSolution.toFeec`, `RowSolution.ofFeec`), with interpolants `RowSolution.interp`
(`eq_interp`) and representatives `RowSolution.field` (`eq_field`). The plane wave of
[QuennevilleBelair2015], Ch. 7 is a row solution with moving electric field
(`exists_rowSolution`).

## References

* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [H. Whitney, *Geometric Integration Theory*][Whitney1957], Ch. IV
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter MeasureTheory

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.StarShaped
  Feec.ExteriorFibre

variable {n : ℕ}

/-! ### Meshes -/

/-- The Freudenthal meshes of the cube `(0, ½)³`. -/
abbrev cubeMesh (N : ℕ) : SimplicialMesh 3 := SimplicialMesh.ofFeec (mesh 3 N)

theorem isMeshFamily_cube : IsMeshFamily (cubeDomain 3) cubeMesh :=
  isMeshFamily_ofFeec (CubeWitness.meshFamily 3)

theorem meshSize_cubeMesh (N : ℕ) :
    FEEC.meshSize (cubeMesh N) = Feec.Models.Cube.FEM.meshSize N :=
  (Feec.Models.Cube.FEM.meshSize_mesh N).trans (Feec.Models.Cube.FEM.hN_eq_meshSize N)

/-- The simplices of the Freudenthal meshes are the Kuhn simplices `h (z + K_σ)`. -/
theorem points_cube (N : ℕ) : ∀ T ∈ (cubeMesh N).simplices, ∃ (z : Fin 3 → Fin (N + 1))
    (σ : Equiv.Perm (Fin 3)), ∀ j i,
      T.points j i = ((z i : ℝ) + if (σ.symm i : ℕ) < (j : ℕ) then 1 else 0) / (2 * (N + 1)) := by
  intro T hT
  obtain ⟨z, σ, hzσ⟩ := (Feec.Mesh.mem_freudenthalMesh_simplices (hs := by norm_num)).1 hT
  refine ⟨z, σ, fun j i => ?_⟩
  rw [← hzσ]
  simp only [Feec.Mesh.mapEquiv_points, Feec.Mesh.freudenthalSimplex_points,
    Feec.Mesh.boxMap_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_add,
    Feec.Mesh.latticePoint_apply, Feec.Mesh.finLattice, Feec.Mesh.kuhnVertex]
  push_cast
  field_simp

/-! ### The Whitney spaces -/

/-- The trimmed sequence `P₁⁻Λ` in every degree. -/
def whitneySeq : PolySeq where
  full _ := false
  deg _ := 1
  one_le_deg _ := le_rfl
  transition _ := Or.inl ⟨rfl, rfl⟩

theorem whitneySeq_toFeec :
    whitneySeq.toFeec = Feec.FiniteElement.PolySeq.trimmed 1 le_rfl := by
  unfold PolySeq.toFeec Feec.FiniteElement.PolySeq.trimmed
  congr 1

theorem topSeq_space (k : ℕ) : topSeq.space n k = whitneySeq.space n k := by
  rcases k with _ | k
  · change (polyForm ℝ n 1 0).map evalForm = (polyFormMinus ℝ n 1 0).map evalForm
    rw [polyForm_eq, polyFormMinus_eq, Feec.Koszul.polyFormMinus_zero_right le_rfl]
  · rfl

theorem isFemPieces_topSeq {Ω : Set (Fin n → ℝ)} {M : SimplicialMesh n} {k : ℤ} {u : L2Form Ω k}
    {p : Affine.Simplex ℝ (Fin n → ℝ) n → FormField n} :
    IsFemPieces Ω M topSeq k u p ↔ IsFemPieces Ω M whitneySeq k u p := by
  unfold IsFemPieces
  rw [topSeq_space]

theorem femSpace_topSeq (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n)
    (Γ : Set (Finset (Fin n → ℝ))) (k : ℤ) :
    femSpace Ω M topSeq Γ k = femSpace Ω M whitneySeq Γ k := by
  ext u
  exact exists_congr fun p => and_congr_left' isFemPieces_topSeq

/-- **The Whitney spaces `Vₕᵏ` of the Freudenthal meshes are the challenge's.** -/
theorem whitney_V_eq (N : ℕ) (k : ℤ) :
    (SetLike.coe ((whitney 3 N).V k) : Set (L2Form (cube 3) k)) =
      femSpace (cube 3) (cubeMesh N) topSeq ∅ k := by
  have h := maximalSubcomplexOfEq_V whitneySeq (mesh 3 N) (mesh_domain 3 N)
    (isOpen_mesh_domain 3 N) (isOpen_cubeDomain 3) k
  have e : whitney 3 N = (deRham ℝ 3).maximalSubcomplexOfEq (mesh_domain 3 N)
      (isOpen_mesh_domain 3 N) (isOpen_cubeDomain 3)
      (whitneySeq.toFeec.subcomplex (mesh 3 N) (isOpen_mesh_domain 3 N)) := by
    rw [whitneySeq_toFeec]
    unfold whitney whitneySubcomplex Feec.FiniteElement.PolySeq.subcomplex
    rw [whitneyElement_equivalent_trimmed.subcomplex_eq]
  rw [femSpace_topSeq, e]
  exact h

/-- **The Whitney spaces `V̊ₕᵏ` with vanishing boundary DOFs are the challenge's.** -/
theorem whitneyMin_V_eq (N : ℕ) (k : ℤ) :
    (SetLike.coe ((whitneyMin 3 N).V k) : Set (L2Form (cube 3) k)) =
      femSpace (cube 3) (cubeMesh N) topSeq (cubeMesh N).boundaryFacets k := by
  have h := minimalSubcomplexOfEq_V whitneySeq (mesh 3 N) (mesh_domain 3 N)
    (isOpen_mesh_domain 3 N) (isOpen_cubeDomain 3) (center 3) (strictStar_mesh 3 N) k
  have e : whitneyMin 3 N = (deRham ℝ 3).minimalSubcomplexOfEq (mesh_domain 3 N)
      (isOpen_mesh_domain 3 N) (isOpen_cubeDomain 3)
      (whitneySeq.toFeec.subcomplexMin (mesh 3 N) (isOpen_mesh_domain 3 N) (center 3)
        (strictStar_mesh 3 N)) := by
    rw [whitneySeq_toFeec]
    unfold whitneyMin whitneySubcomplexMin Feec.FiniteElement.PolySeq.subcomplexMin
    rw [whitneyElement_equivalent_trimmed.subcomplexMin_eq]
  rw [femSpace_topSeq, e]
  exact h

/-! ### The Whitney interpolant -/

/-- **The challenge's integral over an oriented simplex is `Feec`'s.** -/
theorem simplexIntegral_eq {k : ℕ} (p : Fin (k + 1) → Fin n → ℝ) (w : FormField n) :
    FEEC.simplexIntegral p w = Feec.FiniteElement.simplexIntegral p w := by
  unfold FEEC.simplexIntegral Feec.FiniteElement.simplexIntegral
  have hs : {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} = refSimplex k := by
    ext x; exact mem_refSimplex_iff.symm
  rw [hs]
  refine MeasureTheory.setIntegral_congr_fun (measurableSet_refSimplex k) fun x _ => ?_
  rw [affinePullback_apply, covEval_eq]
  congr 2
  funext j
  simp only [affine_apply, simplexMatrix, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.sub_apply]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- The Whitney element is equivalent to the polynomial element of `whitneySeq`. -/
theorem whitneyElement_equivalent_whitneySeq :
    (whitneyElement n).Equivalent (polyElement n whitneySeq.toFeec) := by
  rw [whitneySeq_toFeec]; exact whitneyElement_equivalent_trimmed

/-- The pieces of `whitneySeq` lie in the Whitney spaces. -/
theorem mem_whitneySpace_of {T : Affine.Simplex ℝ (Fin n → ℝ) n} {k : ℕ} {w : FormField n}
    (h : w ∈ whitneySeq.space n k) : w ∈ (whitneyElement n).space T k := by
  rw [whitneyElement_equivalent_whitneySeq.space_eq]
  exact (mem_space_iff whitneySeq k w).2 h

/-- Every enumeration `faceEnum g` of a `(k + 1)`-face `g ⊆ T` is `T.points ∘ q` for an injective
`q`. -/
theorem exists_comp_eq_faceEnum (T : Affine.Simplex ℝ (Fin n → ℝ) n) {k : ℕ}
    {g : Finset (Fin n → ℝ)} (hg : g ⊆ Feec.Mesh.vertexSet T) (hk : g.card = k + 1) :
    ∃ q : Fin (k + 1) → Fin (n + 1), Function.Injective q ∧
      T.points ∘ q = faceEnum g (k + 1) := by
  have hmem : ∀ j, ∃ i, T.points i = faceEnum g (k + 1) j := fun j => by
    have h1 : faceEnum g (k + 1) j ∈ g := by
      have := Set.mem_range_self (f := faceEnum g (k + 1)) j
      rw [range_faceEnum hk] at this
      exact this
    have h2 := hg h1
    rw [← vertexSet_eq, vertexSet, Finset.mem_image] at h2
    obtain ⟨i, -, hi⟩ := h2
    exact ⟨i, hi⟩
  choose q hq using hmem
  refine ⟨q, fun a b hab => injective_faceEnum hk ?_, funext hq⟩
  rw [← hq a, ← hq b, hab]

/-- The **Whitney interpolant in one degree** `j`: the body of `IsWhitneyInterp`. -/
def IsWhitneyInterpAt (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n) (j : ℤ) (w : FormField n)
    (x : L2Form Ω j) : Prop :=
  ∃ p, IsFemPieces Ω M topSeq j x p ∧ ∀ T ∈ M.simplices,
    ∀ q : Fin (j.toNat + 1) → Fin (n + 1), Function.Injective q →
      FEEC.simplexIntegral (T.points ∘ q) (p T) = FEEC.simplexIntegral (T.points ∘ q) w

theorem isWhitneyInterp_iff {Ω : Set (Fin n → ℝ)} {M : SimplicialMesh n} {a : ℤ} {m : ℕ}
    {w : Fin m → FormField n} {x : Total (L2Form Ω) a m} :
    IsWhitneyInterp Ω M a m w x ↔ ∀ i : Fin m, IsWhitneyInterpAt Ω M (a + (i : ℕ)) (w i) (x i) :=
  Iff.rfl

variable (M : Feec.Mesh.SimplicialMesh n)

/-- **The Whitney interpolant of the challenge is the glued global interpolant** on every `Feec`
mesh, in every degree `j`. -/
theorem isWhitneyInterpAt_iff (j : ℤ) (w : contForms n) (x : L2Form M.domain j) :
    IsWhitneyInterpAt M.domain (SimplicialMesh.ofFeec M) j (w : FormField n) x ↔
      x = (whitneyElement n).glue M j
        ((whitneyElement n).globalInterp M j.toNat w : (whitneyElement n).Piecewise M j.toNat) := by
  have hE := whitneyElement_equivalent_whitneySeq (n := n)
  constructor
  · rintro ⟨p, hp, hdof⟩
    have hp' := isFemPieces_topSeq.1 hp
    set u : (whitneyElement n).Piecewise M j.toNat := fun T =>
      ⟨p T, mem_whitneySpace_of (hp'.1 T T.2)⟩ with hu
    have hcast : hE.castPiecewise M u =
        ofPieces whitneySeq (SimplicialMesh.ofFeec M) M.domain rfl p hp'.1 := rfl
    have hx : x = (whitneyElement n).glue M j u := by
      rw [← hE.glue_castPiecewise M j u, hcast]
      exact (glue_ofPieces whitneySeq (SimplicialMesh.ofFeec M) M.domain rfl hp').symm
    rw [hx]
    congr 1
    funext T
    refine (whitneyElement n).localSpace_ext T j.toNat fun g hg i => ?_
    rw [LocalElement.localDof_globalInterp _ _ _ _ _ _ hg]
    obtain ⟨q, hq, hqe⟩ := exists_comp_eq_faceEnum (T : Affine.Simplex ℝ (Fin n → ℝ) n) hg i.2
    have h := hdof T T.2 q hq
    rw [simplexIntegral_eq, simplexIntegral_eq, hqe] at h
    exact h
  · rintro rfl
    set v := hE.castPiecewise M ((whitneyElement n).globalInterp M j.toNat w :
      (whitneyElement n).Piecewise M j.toNat)
    have hv : v ∈ (polyElement n whitneySeq.toFeec).globalSpace M j.toNat :=
      hE.castPiecewise_mem_globalSpace M ((whitneyElement n).globalInterp M j.toNat w).2
    have hpieces := isFemPieces_glue whitneySeq (SimplicialMesh.ofFeec M) M.domain rfl
      (k := j) ⟨v, hv⟩
    have hg : (polyElement n whitneySeq.toFeec).glue
        ((SimplicialMesh.ofFeec M).toFeec M.domain rfl) j (v : _) =
        (whitneyElement n).glue M j
          ((whitneyElement n).globalInterp M j.toNat w :
            (whitneyElement n).Piecewise M j.toNat) :=
      hE.glue_castPiecewise M j _
    rw [hg] at hpieces
    refine ⟨_, isFemPieces_topSeq.2 hpieces, fun T hT q hq => ?_⟩
    rw [LocalElement.extendPW_of_mem _ ((SimplicialMesh.ofFeec M).toFeec M.domain rfl) _ hT]
    change FEEC.simplexIntegral _
      (((whitneyElement n).globalInterp M j.toNat w :
        (whitneyElement n).Piecewise M j.toNat) ⟨T, hT⟩ : FormField n) = _
    have hinj : Function.Injective (T.points ∘ q) := T.independent.injective.comp hq
    set g : Finset (Fin n → ℝ) := Finset.univ.image (T.points ∘ q) with hgdef
    have hcard : g.card = j.toNat + 1 := by
      rw [hgdef, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hgT : g ⊆ Feec.Mesh.vertexSet T := by
      intro y hy
      rw [hgdef, Finset.mem_image] at hy
      obtain ⟨j, -, rfl⟩ := hy
      rw [← vertexSet_eq, vertexSet]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    obtain ⟨ε, -, hε⟩ := exists_sign_simplexIntegral_eq hinj (injective_faceEnum hcard)
      (by rw [range_faceEnum hcard, hgdef, Finset.coe_image, Finset.coe_univ, Set.image_univ])
    rw [simplexIntegral_eq, simplexIntegral_eq, hε, hε,
      simplexIntegral_globalInterp j.toNat w ⟨T, hT⟩ hgT hcard]

open Feec.Models.Cube.Inhomogeneous in
/-- **On the cube, the Whitney interpolant of the challenge is `Feec`'s canonical interpolant.** -/
theorem isWhitneyInterpAt_cube_iff (N : ℕ) (j : ℤ) (w : contForms 3) (x : L2Form (cube 3) j) :
    IsWhitneyInterpAt (cube 3) (cubeMesh N) j (w : FormField 3) x ↔
      x = FEMInterp.canonicalInterp N j w :=
  FEMInterp.linearMapOfEq_induction (mesh_domain 3 N) (isOpen_mesh_domain 3 N)
    (isOpen_cubeDomain 3) (whitneySubcomplex (mesh 3 N) (isOpen_mesh_domain 3 N)) _
    (fun Ω _ _ f => ∀ x : L2F ℝ Ω (formIdx 3 j),
      IsWhitneyInterpAt Ω (cubeMesh N) j (w : FormField 3) x ↔ x = f w)
    (fun x => isWhitneyInterpAt_iff (mesh 3 N) j w x) x

/-! ### The Whitney schemes on the cube -/

section Schemes

open Feec.Models.Cube.Inhomogeneous HilbertComplex

/-- **`Feec`'s complex of the cube is the challenge's `HΛ(Q)`.** -/
theorem ofFeec_complex_d (k : ℤ) :
    (HilbertComplex.ofFeec (complex 3)).d k (k + 1) = dMax (cube 3) k := by
  rw [dMax_eq]; exact deRham_maximalComplex_d (isOpen_cubeDomain 3) k

variable (N : ℕ)

/-- The Whitney row in the challenge's window `[0, 3)`. -/
abbrev ofD (v : DState (whitneyRow N)) : Total (L2Form (cube 3)) 0 3 := dEmb (whitneyRow N) v

theorem dApply_ofD (u : DState (whitneyRow N)) :
    (HilbertComplex.ofFeec (complex 3)).dApply 0 3 (ofD N u) =
      ofD N (discreteD (whitneyRow N) u) :=
  dApply_dEmb (Subcomplex.ofFeec (whitney 3 N)) u

/-- **The challenge's wave form on the Whitney row is that of `discreteWave`.** -/
theorem waveForm_ofD (u v : DState (whitneyRow N)) :
    (HilbertComplex.ofFeec (complex 3)).waveForm 0 3 (ofD N u) (ofD N v) =
      ⟪discreteWave (whitneyRow N) u, v⟫ := by
  rw [HilbertComplex.waveForm, dApply_ofD, dApply_ofD, inner_discreteWave, inner_dEmb, inner_dEmb]

theorem norm_ofD (v : DState (whitneyRow N)) : ‖ofD N v‖ = ‖v‖ :=
  norm_emb (inner_dEmb (whitneyRow N)) v

theorem ofD_injective : Function.Injective (ofD N) := fun _ _ h =>
  PiLp.ext fun i => Subtype.ext (congrArg (fun z : Total (L2Form (cube 3)) 0 3 => z i) h)

/-- **The Whitney forms of the window are the image of the Whitney row.** -/
theorem mem_whitney_iff (x : Total (L2Form (cube 3)) 0 3) :
    x ∈ femTotal (cube 3) (cubeMesh N) topSeq ∅ 0 3 ↔ ∃ v, x = ofD N v := by
  have e : ∀ i : Fin 3, x i ∈ femSpace (cube 3) (cubeMesh N) topSeq ∅ (0 + (i : ℕ)) ↔
      x i ∈ (whitney 3 N).V (0 + (i : ℕ)) := fun i => by
    rw [← whitney_V_eq N]; rfl
  change (∀ i : Fin 3, _) ↔ _
  simp only [e]
  exact mem_iff_exists_dEmb (Subcomplex.ofFeec (whitney 3 N))

/-- **The Whitney forms with vanishing boundary traces are the image of `whitneyInterior`.** -/
theorem ofD_mem_whitneyMin_iff (v : DState (whitneyRow N)) :
    ofD N v ∈ femTotal (cube 3) (cubeMesh N) topSeq (cubeMesh N).boundaryFacets 0 3 ↔
      v ∈ whitneyInterior N := by
  have e : ∀ i : Fin 3, (ofD N v) i ∈
      femSpace (cube 3) (cubeMesh N) topSeq (cubeMesh N).boundaryFacets (0 + (i : ℕ)) ↔
      ((v i : (whitneyRow N).V i) : L2F ℝ (cubeDomain 3) (formIdx 3 (0 + (i : ℕ)))) ∈
        (whitneyMin 3 N).V (0 + (i : ℕ)) := fun i => by
    rw [← whitneyMin_V_eq N]; rfl
  change (∀ i : Fin 3, _) ↔ _
  simp only [e]
  rfl

theorem mem_whitneyMin_iff (x : Total (L2Form (cube 3)) 0 3) :
    x ∈ femTotal (cube 3) (cubeMesh N) topSeq (cubeMesh N).boundaryFacets 0 3 ↔
      ∃ v ∈ whitneyInterior N, x = ofD N v := by
  constructor
  · intro h
    have hf : x ∈ femTotal (cube 3) (cubeMesh N) topSeq ∅ 0 3 := fun i => by
      have := whitneyMin_le_whitney N _ ((whitneyMin_V_eq N (0 + (i : ℕ))).symm ▸ h i)
      rw [← whitney_V_eq N]
      exact this
    obtain ⟨v, rfl⟩ := (mem_whitney_iff N x).1 hf
    exact ⟨v, (ofD_mem_whitneyMin_iff N v).1 h, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact (ofD_mem_whitneyMin_iff N v).2 hv

theorem mem_whitney_of_mem_whitneyMin {x : Total (L2Form (cube 3)) 0 3}
    (h : x ∈ femTotal (cube 3) (cubeMesh N) topSeq (cubeMesh N).boundaryFacets 0 3) :
    x ∈ femTotal (cube 3) (cubeMesh N) topSeq ∅ 0 3 := by
  obtain ⟨v, -, rfl⟩ := (mem_whitneyMin_iff N x).1 h
  exact (mem_whitney_iff N _).2 ⟨v, rfl⟩

/-- **The challenge's Crank–Nicolson step is `Feec`'s** `IsDirichletCNStep` with zero load. -/
theorem isCNStep_iff (Δt : ℝ) (g u : DState (whitneyRow N)) (x : Total (L2Form (cube 3)) 0 3) :
    (HilbertComplex.ofFeec (complex 3)).IsCNStep 0 3 (femTotal (cube 3) (cubeMesh N) topSeq ∅ 0 3)
      (femTotal (cube 3) (cubeMesh N) topSeq (cubeMesh N).boundaryFacets 0 3) Δt (ofD N g)
      (ofD N u) x ↔ ∃ u', x = ofD N u' ∧
        Feec.TimeStepping.IsDirichletCNStep (whitneyInterior N) (discreteWave (whitneyRow N))
          (Δt / 2) 0 g u u' := by
  constructor
  · rintro ⟨hx, hb, hv⟩
    obtain ⟨u', rfl⟩ := (mem_whitney_iff N x).1 hx
    refine ⟨u', rfl, ?_, fun v hv' => ?_⟩
    · rw [← _root_.map_sub] at hb
      exact (ofD_mem_whitneyMin_iff N _).1 hb
    · have := hv (ofD N v) ((ofD_mem_whitneyMin_iff N v).2 hv')
      rw [← _root_.map_sub, ← _root_.map_add, inner_dEmb, waveForm_ofD] at this
      rw [this, inner_zero_left, add_zero]
  · rintro ⟨u', rfl, hb, hv⟩
    refine ⟨(mem_whitney_iff N _).2 ⟨u', rfl⟩, ?_, fun v hv' => ?_⟩
    · rw [← _root_.map_sub]; exact (ofD_mem_whitneyMin_iff N _).2 hb
    · obtain ⟨v', hv'', rfl⟩ := (mem_whitneyMin_iff N v).1 hv'
      rw [← _root_.map_sub, ← _root_.map_add, inner_dEmb, waveForm_ofD, hv v' hv'',
        inner_zero_left, add_zero]

/-- **The challenge's leapfrog step is `Feec`'s** `IsDirichletLeapfrogStep`. -/
theorem isLeapfrogStep_iff (Δt : ℝ) (g u u' : DState (whitneyRow N))
    (x : Total (L2Form (cube 3)) 0 3) :
    (HilbertComplex.ofFeec (complex 3)).IsLeapfrogStep 0 3
      (femTotal (cube 3) (cubeMesh N) topSeq ∅ 0 3)
      (femTotal (cube 3) (cubeMesh N) topSeq (cubeMesh N).boundaryFacets 0 3) Δt (ofD N g)
      (ofD N u) (ofD N u') x ↔ ∃ u'', x = ofD N u'' ∧
        Feec.TimeStepping.IsDirichletLeapfrogStep (whitneyInterior N)
          (discreteWave (whitneyRow N)) Δt g u u' u'' := by
  constructor
  · rintro ⟨hx, hb, hv⟩
    obtain ⟨u'', rfl⟩ := (mem_whitney_iff N x).1 hx
    refine ⟨u'', rfl, ?_, fun v hv' => ?_⟩
    · rw [← _root_.map_sub] at hb
      exact (ofD_mem_whitneyMin_iff N _).1 hb
    · have := hv (ofD N v) ((ofD_mem_whitneyMin_iff N v).2 hv')
      rwa [← _root_.map_sub, inner_dEmb, waveForm_ofD] at this
  · rintro ⟨u'', rfl, hb, hv⟩
    refine ⟨(mem_whitney_iff N _).2 ⟨u'', rfl⟩, ?_, fun v hv' => ?_⟩
    · rw [← _root_.map_sub]; exact (ofD_mem_whitneyMin_iff N _).2 hb
    · obtain ⟨v', hv'', rfl⟩ := (mem_whitneyMin_iff N v).1 hv'
      rw [← _root_.map_sub, inner_dEmb, waveForm_ofD, hv v' hv'']

/-- Forms of the window in `Vₕ` up to step `m` are the forms of Whitney states. -/
theorem exists_seq_ofD {u : ℕ → Total (L2Form (cube 3)) 0 3} {m : ℕ}
    (h : ∀ k ≤ m, u k ∈ femTotal (cube 3) (cubeMesh N) topSeq ∅ 0 3) :
    ∃ v : ℕ → DState (whitneyRow N), ∀ k ≤ m, u k = ofD N (v k) := by
  classical
  refine ⟨fun k => if hk : u k ∈ femTotal (cube 3) (cubeMesh N) topSeq ∅ 0 3 then
    ((mem_whitney_iff N _).1 hk).choose else 0, fun k hk => ?_⟩
  dsimp only
  rw [dite_eq_left (h k hk)]
  exact ((mem_whitney_iff N _).1 (h k hk)).choose_spec

theorem ofD_zero : ofD N 0 = 0 := _root_.map_zero _

end Schemes

/-! ### Smooth row solutions -/

section RowSolution

open Feec.Models.Cube.Inhomogeneous

/-- A smooth row solution of the challenge as a `Feec` row solution. -/
def RowSolution.toFeec {T L : ℝ} (X : FEEC.RowSolution T L) :
    Feec.Models.Cube.Inhomogeneous.RowSolution T L where
  u := X.u
  u₁ := X.u₁
  u₂ := X.u₂
  u₃ := X.u₃
  isDeg t i y s hs := X.isDeg t i y s hs
  contDiff := X.contDiff
  continuous₁ := X.continuous₁
  continuous₂ := X.continuous₂
  continuous₃ := X.continuous₃
  hasDerivAt₁ := X.hasDerivAt₁
  hasDerivAt₂ := X.hasDerivAt₂
  hasDerivAt₃ := X.hasDerivAt₃
  pde₀ := X.pde₀
  pde₁ := X.pde₁
  pde₂ := X.pde₂
  bound := X.bound
  lipschitz := X.lipschitz
  bound₃ := X.bound₃

/-- A `Feec` row solution as a smooth row solution of the challenge. -/
def RowSolution.ofFeec {T L : ℝ} (X : Feec.Models.Cube.Inhomogeneous.RowSolution T L) :
    FEEC.RowSolution T L where
  u := X.u
  u₁ := X.u₁
  u₂ := X.u₂
  u₃ := X.u₃
  isDeg t i y s hs := X.isDeg t i y s hs
  contDiff := X.contDiff
  continuous₁ := X.continuous₁
  continuous₂ := X.continuous₂
  continuous₃ := X.continuous₃
  hasDerivAt₁ := X.hasDerivAt₁
  hasDerivAt₂ := X.hasDerivAt₂
  hasDerivAt₃ := X.hasDerivAt₃
  pde₀ := X.pde₀
  pde₁ := X.pde₁
  pde₂ := X.pde₂
  bound := X.bound
  lipschitz := X.lipschitz
  bound₃ := X.bound₃

variable {T L : ℝ} (X : FEEC.RowSolution T L)

/-- The Whitney interpolant of the challenge's row is `Feec`'s row interpolant. -/
theorem RowSolution.eq_interp {N : ℕ} {t : ℝ} {w : Total (L2Form (cube 3)) 0 3}
    (h : IsWhitneyInterp (cube 3) (cubeMesh N) 0 3 (X.u t) w) :
    w = ofD N (X.toFeec.interp N t) :=
  PiLp.ext fun i =>
    (isWhitneyInterpAt_cube_iff N _ ⟨X.u t i, X.toFeec.continuous t i⟩ (w i)).1 (h i)

/-- The representatives of `U(t)` are `Feec`'s `RowSolution.field`. -/
theorem RowSolution.eq_field {t : ℝ} {U : Total (L2Form (cube 3)) 0 3}
    (h : IsRepr (cube 3) 0 3 (X.u t) U) : U = X.toFeec.field t :=
  PiLp.ext fun i => PiLp.ext fun s => Lp.ext ((h i s).trans
    (coeFn_formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) _
      ⟨X.u t i, X.toFeec.continuous t i⟩ s).symm)

include X in
theorem RowSolution.zero_le_L {Δt : ℝ} {M : ℕ} (hΔt : 0 < Δt) (hM : (M : ℝ) * Δt ≤ T) :
    0 ≤ L := by
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg M) hΔt.le).trans hM
  have hy : (fun _ : Fin 3 => (1 / 4 : ℝ)) ∈ closure (cube 3) :=
    subset_closure fun i _ => by norm_num
  exact (norm_nonneg _).trans (X.bound 0 ⟨le_rfl, hT⟩ 0 _ hy).1

end RowSolution

/-! ### The plane wave -/

section PlaneWave

open Feec.Numerics.PlaneWaveCube Feec.Numerics.CrankNicolson

/-- The `dx₀` coefficient of the electric field of row `0` of the plane wave. -/
theorem planeWaveRows_apply (T t : ℝ) (y : Fin 3 → ℝ) :
    (planeWaveRows 1 0 1 T 0).u t 1 y {0} = -Real.sin (y 2 - t) := by
  change Feec.Models.Cube.Inhomogeneous.oneForm (fun j => (planeWaveTSD 1 0 1).E t (0, j)) y {0} =
    _
  rw [Feec.Models.Cube.Inhomogeneous.oneForm_apply_singleton]
  simp [planeWaveTSD, planeWave_apply, amplitudeE]

/-- The time derivative of the `dx₀` coefficient of the electric field of row `0` of the plane
wave. -/
theorem planeWaveRows_u₁_apply (T t : ℝ) (y : Fin 3 → ℝ) :
    (planeWaveRows 1 0 1 T 0).u₁ t 1 y {0} = Real.cos (y 2 - t) := by
  have h := ((hasDerivAt_id t).const_sub (y 2)).sin.neg
  simp only [id, mul_neg, mul_one, neg_neg] at h
  refine ((planeWaveRows 1 0 1 T 0).hasDerivAt₁ t 1 y {0}).unique ?_
  simpa only [planeWaveRows_apply, Pi.neg_def] using h

/-- At every time some `y₂ ∈ {1/8, 1/4}` has `sin (2 (y₂ - t)) ≠ 0`: the two arguments differ by
`1/4 ∈ (0, π)`. -/
theorem exists_sin_two_mul_ne_zero (t : ℝ) :
    ∃ a ∈ Ioo (0 : ℝ) (1 / 2), Real.sin (2 * (a - t)) ≠ 0 := by
  by_contra! h
  have h1 := h (1 / 8) ⟨by norm_num, by norm_num⟩
  have h2 := h (1 / 4) ⟨by norm_num, by norm_num⟩
  have hs : 0 < Real.sin (1 / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.two_le_pi])
  have hc : Real.cos (2 * (1 / 8 - t)) ≠ 0 := fun hc => by
    have := Real.sin_sq_add_cos_sq (2 * (1 / 8 - t))
    rw [h1, hc] at this; norm_num at this
  rw [show 2 * ((1 / 4 : ℝ) - t) = 2 * (1 / 8 - t) + 1 / 4 by ring, Real.sin_add, h1, zero_mul,
    zero_add] at h2
  exact mul_ne_zero hc hs.ne' h2

/-- **Row `0` of the plane wave is a smooth row solution** whose electric field `E` and its time
derivative are nonzero at some point of the cube at every time. -/
theorem exists_rowSolution (T : ℝ) :
    ∃ L, ∃ X : FEEC.RowSolution T L, ∀ t, ∃ y ∈ cube 3, X.u t 1 y ≠ 0 ∧ X.u₁ t 1 y ≠ 0 := by
  refine ⟨_, RowSolution.ofFeec (planeWaveRows 1 0 1 T 0), fun t => ?_⟩
  obtain ⟨a, ha, hsin⟩ := exists_sin_two_mul_ne_zero t
  rw [Real.sin_two_mul] at hsin
  refine ⟨fun _ => a, fun i _ => ha, fun h => hsin ?_, fun h => hsin ?_⟩
  · have := congrFun h {0}
    change (planeWaveRows 1 0 1 T 0).u t 1 (fun _ => a) {0} = 0 at this
    rw [planeWaveRows_apply] at this
    have hs : Real.sin (a - t) = 0 := by simpa using this
    simp [hs]
  · have := congrFun h {0}
    change (planeWaveRows 1 0 1 T 0).u₁ t 1 (fun _ => a) {0} = 0 at this
    rw [planeWaveRows_u₁_apply] at this
    have hc : Real.cos (a - t) = 0 := by simpa using this
    simp [hc]

end PlaneWave

end FEEC
