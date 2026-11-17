module

public import Solution.WhitneySpaces

/-!
# The Whitney interpolant of the challenge is `Feec`'s canonical interpolant

The challenge's integral over an oriented simplex is `Feec.FiniteElement.simplexIntegral`
(`simplexIntegral_eq`). On a `Feec` mesh, `IsWhitneyInterp` (the form of `P₁⁻Λᵏ(M)` whose pieces
have the face integrals of `w` on every oriented `k`-face) holds exactly for the glued global
interpolant `glue (Π_h w)` of the Whitney element (`isWhitneyInterp_iff`): the face integral over
`faceEnum g` is one of the challenge's (`exists_comp_eq_faceEnum`), and every other orientation
differs by a sign (`Feec.FiniteElement.exists_sign_simplexIntegral_eq`). On the cube this is
`Feec.Models.Cube.Inhomogeneous.FEMInterp.canonicalInterp` (`isWhitneyInterp_cube_iff`).

## References

* [H. Whitney, *Geometric Integration Theory*][Whitney1957], Ch. IV
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set Finset

@[expose] public noncomputable section

namespace TimeStepping

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.ExteriorFibre

variable {n : ℕ}

/-- **The challenge's integral over an oriented simplex is `Feec`'s.** -/
theorem simplexIntegral_eq {k : ℕ} (p : Fin (k + 1) → Fin n → ℝ) (w : FormField n) :
    TimeStepping.simplexIntegral p w = Feec.FiniteElement.simplexIntegral p w := by
  unfold TimeStepping.simplexIntegral Feec.FiniteElement.simplexIntegral
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

variable (M : Feec.Mesh.SimplicialMesh n)

/-- **The Whitney interpolant of the challenge is the glued global interpolant** on every `Feec`
mesh. -/
theorem isWhitneyInterp_iff (k : ℕ) (w : contForms n) (x : L2Form M.domain k) :
    IsWhitneyInterp M.domain (SimplicialMesh.ofFeec M) k (w : FormField n) x ↔
      x = (whitneyElement n).glue M k
        ((whitneyElement n).globalInterp M k w : (whitneyElement n).Piecewise M k) := by
  have hE := whitneyElement_equivalent_whitneySeq (n := n)
  constructor
  · rintro ⟨p, hp, hdof⟩
    have hp' := isFemPieces_topSeq.1 hp
    set u : (whitneyElement n).Piecewise M k := fun T =>
      ⟨p T, mem_whitneySpace_of (hp'.1 T T.2)⟩ with hu
    have hcast : hE.castPiecewise M u =
        ofPieces whitneySeq (SimplicialMesh.ofFeec M) M.domain rfl p hp'.1 := rfl
    have hx : x = (whitneyElement n).glue M k u := by
      rw [← hE.glue_castPiecewise M k u, hcast]
      exact (glue_ofPieces whitneySeq (SimplicialMesh.ofFeec M) M.domain rfl hp').symm
    rw [hx]
    congr 1
    funext T
    refine (whitneyElement n).localSpace_ext T k fun g hg i => ?_
    rw [LocalElement.localDof_globalInterp _ _ _ _ _ _ hg]
    obtain ⟨q, hq, hqe⟩ := exists_comp_eq_faceEnum (T : Affine.Simplex ℝ (Fin n → ℝ) n) hg i.2
    have h := hdof T T.2 q hq
    rw [simplexIntegral_eq, simplexIntegral_eq, hqe] at h
    exact h
  · rintro rfl
    set v := hE.castPiecewise M ((whitneyElement n).globalInterp M k w :
      (whitneyElement n).Piecewise M k)
    have hv : v ∈ (polyElement n whitneySeq.toFeec).globalSpace M k :=
      hE.castPiecewise_mem_globalSpace M ((whitneyElement n).globalInterp M k w).2
    have hpieces := isFemPieces_glue whitneySeq (SimplicialMesh.ofFeec M) M.domain rfl
      (k := (k : ℤ)) ⟨v, hv⟩
    have hg : (polyElement n whitneySeq.toFeec).glue
        ((SimplicialMesh.ofFeec M).toFeec M.domain rfl) k (v : _) =
        (whitneyElement n).glue M k
          ((whitneyElement n).globalInterp M k w : (whitneyElement n).Piecewise M k) :=
      hE.glue_castPiecewise M k _
    rw [hg] at hpieces
    refine ⟨_, isFemPieces_topSeq.2 hpieces, fun T hT q hq => ?_⟩
    rw [LocalElement.extendPW_of_mem _ ((SimplicialMesh.ofFeec M).toFeec M.domain rfl) _ hT]
    change TimeStepping.simplexIntegral _
      (((whitneyElement n).globalInterp M k w : (whitneyElement n).Piecewise M k) ⟨T, hT⟩ :
        FormField n) = _
    have hinj : Function.Injective (T.points ∘ q) := T.independent.injective.comp hq
    set g : Finset (Fin n → ℝ) := Finset.univ.image (T.points ∘ q) with hgdef
    have hcard : g.card = k + 1 := by
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
      simplexIntegral_globalInterp k w ⟨T, hT⟩ hgT hcard]

open Feec.Models.Cube.Inhomogeneous in
/-- **On the cube, the Whitney interpolant of the challenge is `Feec`'s canonical interpolant.** -/
theorem isWhitneyInterp_cube_iff (N k : ℕ) (w : contForms 3) (x : L2Form (cube 3) k) :
    IsWhitneyInterp (cube 3) (cubeMesh N) k (w : FormField 3) x ↔
      x = FEMInterp.canonicalInterp N k w :=
  FEMInterp.linearMapOfEq_induction (mesh_domain 3 N) (isOpen_mesh_domain 3 N)
    (isOpen_cubeDomain 3) (whitneySubcomplex (mesh 3 N) (isOpen_mesh_domain 3 N)) _
    (fun Ω _ _ f => ∀ x : L2F ℝ Ω (formIdx 3 k),
      IsWhitneyInterp Ω (cubeMesh N) k (w : FormField 3) x ↔ x = f w)
    (fun x => isWhitneyInterp_iff (mesh 3 N) k w x) x

end TimeStepping
