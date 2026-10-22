module

public import Feec.FiniteElement.PolyComplex

/-!
# Global spaces with vanishing degrees of freedom on part of the boundary

For an element family `E` (`Feec.FiniteElement.LocalElement`) on a mesh `M` and a set `Γ` of
facets (typically some boundary facets, e.g. those on the mirror faces of a cube), the global
space `Λ_{h,Γ}ᵏ(M)` (`LocalElement.globalSpacePartial`) consists of the global fields whose
degrees of freedom vanish on every face contained in a facet of `Γ`. This interpolates between
`Λ_hᵏ(M)` (`Γ = ∅`, `globalSpacePartial_empty`) and `Λ̊_hᵏ(M)` (`Γ` = all boundary facets,
`globalSpacePartial_boundary`). At the algebraic (assembly) level:

* `d Λ_{h,Γ}ᵏ ⊆ Λ_{h,Γ}ᵏ⁺¹` (`dPiecewise_mem_globalSpacePartial`), from Stokes compatibility of
  the degrees of freedom, so the spaces form a cochain complex (`dGlobalPartial`);
* the degrees of freedom of the faces not contained in a facet of `Γ` are a linear isomorphism
  `Λ_{h,Γ}ᵏ(M) ≃ ℝ^{free DOFs}` (`partialDofEquiv`), so
  `dim Λ_{h,Γ}ᵏ(M) = #{DOFs of faces not in a facet of Γ}` (`finrank_globalSpacePartial`), and
  the same for the glued spaces in `L²(Ω; Λᵏ)` (`finrank_VPartial`);
* for the families of an admissible sequence, the dimension is
  `Σ_{m ≤ n} #{m-faces not in a facet of Γ} · dim(test forms on m-faces)`
  (`PolySeq.finrank_globalSpacePartial`).
* with boundary conditions in the degrees `k < j` only (`LocalElement.bcFacets`; `j = 2` in `ℝ³`
  is the pattern `V̊ₕ⁰ → V̊ₕ¹ → Vₕ²` of [QuennevilleBelair2015], §6.3) the spaces are again closed
  under `d` (`LocalElement.dPiecewise_mem_globalSpacePartial_bcFacets`),
  contain `Λ̊_hᵏ` (`LocalElement.finrank_V₀_le_finrank_VPartial`), and for the second row of
  Table 6.1 they are nonzero on every Freudenthal mesh of `(0, ½)³`
  (`PolySeq.lagrangeP2_VPartial_bcFacets_ne_bot`).

The conformity `V_{h,Γ} ⊆ D(d)` for the `L²` de Rham complex with boundary conditions on `Γ` is
not treated here.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §5 (assembly from degrees of freedom)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.3, Table 6.1

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Finset

@[expose] public noncomputable section

namespace Feec.FiniteElement

open Feec.Mesh Feec.Domain

variable {n : ℕ}

namespace LocalElement

variable (E : LocalElement n) (M : SimplicialMesh n) (Γ : Set (Finset (Fin n → ℝ)))

/-- **The global space with vanishing degrees of freedom on `Γ`**: global fields whose degrees of
freedom vanish on every face contained in a facet (vertex set) of `Γ`. -/
def globalSpacePartial (k : ℕ) : Submodule ℝ (E.Piecewise M k) :=
  E.globalSpace M k ⊓
    { carrier := {u | ∀ T : M.simplices, ∀ g, g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) →
        (∃ F ∈ Γ, g ⊆ F) → ∀ i, E.localDof T k g i (u T) = 0}
      zero_mem' := fun T g _ _ i => by simp
      add_mem' := fun hu hv T g hg hgΓ i => by
        simp only [Pi.add_apply, map_add, hu T g hg hgΓ i, hv T g hg hgΓ i, add_zero]
      smul_mem' := fun c u hu T g hg hgΓ i => by
        simp only [Pi.smul_apply, map_smul, hu T g hg hgΓ i, smul_zero] }

theorem globalSpacePartial_le (k : ℕ) : E.globalSpacePartial M Γ k ≤ E.globalSpace M k :=
  inf_le_left

/-- `Λ_{h,Γ}ᵏ` decreases with `Γ`. -/
theorem globalSpacePartial_anti {Γ Γ' : Set (Finset (Fin n → ℝ))} (h : Γ ⊆ Γ') (k : ℕ) :
    E.globalSpacePartial M Γ' k ≤ E.globalSpacePartial M Γ k := fun _ hu =>
  ⟨hu.1, fun T g hg ⟨F, hF, hgF⟩ i => hu.2 T g hg ⟨F, h hF, hgF⟩ i⟩

/-- `Γ = ∅`: no boundary condition. -/
theorem globalSpacePartial_empty (k : ℕ) : E.globalSpacePartial M ∅ k = E.globalSpace M k :=
  le_antisymm (E.globalSpacePartial_le M ∅ k) fun _ hu => ⟨hu, fun _ _ _ ⟨_, hF, _⟩ => hF.elim⟩

/-- `Γ` = all boundary facets: the space `Λ̊_hᵏ(M)` with vanishing boundary degrees of
freedom. -/
theorem globalSpacePartial_boundary (k : ℕ) :
    E.globalSpacePartial M {F | M.IsBoundaryFacet F} k = E.globalSpace₀ M k := by
  refine le_antisymm (fun u hu => ⟨hu.1, fun T F hF hFT g hg i =>
    hu.2 T g (hg.trans hFT) ⟨F, hF, hg⟩ i⟩) fun u hu => ⟨hu.1, fun T g hg ⟨F, hF, hgF⟩ i => ?_⟩
  obtain ⟨T', hT', hFT'⟩ := hF.1.2
  rw [hu.1 T ⟨T', hT'⟩ g hg (hgF.trans hFT') i]
  exact hu.2 ⟨T', hT'⟩ F hF hFT' g hgF i

/-- **`d Λ_{h,Γ}ᵏ ⊆ Λ_{h,Γ}ᵏ⁺¹`**: the degrees of freedom of `du` on a face `g ⊆ F ∈ Γ` are
combinations of those of `u` on the subfaces of `g`, which vanish. -/
theorem dPiecewise_mem_globalSpacePartial {k : ℕ} {u : E.Piecewise M k}
    (hu : u ∈ E.globalSpacePartial M Γ k) :
    E.dPiecewise M k u ∈ E.globalSpacePartial M Γ (k + 1) := by
  refine ⟨E.dPiecewise_mem_globalSpace M hu.1, fun T g hg ⟨F, hF, hgF⟩ i => ?_⟩
  rw [dPiecewise_apply, localDof_localD]
  have h := E.dof_congr_of_mem_span (E.dof_extDeriv g k i) (a := ⟨u T, E.le_c1Forms T k (u T).2⟩)
    (b := 0) fun g' hg'g j => by
      rw [map_zero, map_zero]
      exact hu.2 T g' (hg'g.trans hg) ⟨F, hF, hg'g.trans hgF⟩ j
  rw [h, map_zero]

/-- The exterior derivative `Λ_{h,Γ}ᵏ(M) → Λ_{h,Γ}ᵏ⁺¹(M)`. -/
def dGlobalPartial (k : ℕ) : E.globalSpacePartial M Γ k →ₗ[ℝ] E.globalSpacePartial M Γ (k + 1) :=
  (E.dPiecewise M k).restrict fun _ hu => E.dPiecewise_mem_globalSpacePartial M Γ hu

/-- A global DOF **lies on `Γ`** if its face is contained in a facet of `Γ`. -/
def IsDofOn {k : ℕ} (p : E.GlobalDofIdx M k) : Prop :=
  ∃ F ∈ Γ, (p.1 : Finset (Fin n → ℝ)) ⊆ F

/-- The **free DOFs**: the global DOFs of the faces not contained in a facet of `Γ`. -/
abbrev FreeDofIdx (k : ℕ) := {p : E.GlobalDofIdx M k // ¬ E.IsDofOn M Γ p}

instance (k : ℕ) : Fintype (E.FreeDofIdx M Γ k) := Fintype.ofFinite _

/-- `u ∈ Λ_{h,Γ}ᵏ(M)` iff the global DOFs of `u` on `Γ` vanish. -/
theorem mem_globalSpacePartial_iff {k : ℕ} (u : E.globalSpace M k) :
    (u : E.Piecewise M k) ∈ E.globalSpacePartial M Γ k ↔
      ∀ p, E.IsDofOn M Γ p → E.globalDof M k u p = 0 := by
  constructor
  · rintro hu p ⟨F, hF, hpF⟩
    rw [E.globalDof_apply M k u p (faceSimplex M p.1) (subset_faceSimplex M p.1)]
    exact hu.2 _ _ (subset_faceSimplex M p.1) ⟨F, hF, hpF⟩ p.2
  · intro hu
    refine ⟨u.2, fun T g hg hgΓ i => ?_⟩
    rw [← E.globalDof_apply M k u ⟨⟨g, (mem_meshFaces M).2 ⟨T, T.2, hg⟩⟩, i⟩ T hg]
    exact hu _ hgΓ

/-- The free global DOFs on `Λ_{h,Γ}ᵏ(M)`. -/
def partialDof (k : ℕ) : E.globalSpacePartial M Γ k →ₗ[ℝ] (E.FreeDofIdx M Γ k → ℝ) :=
  LinearMap.funLeft ℝ ℝ Subtype.val ∘ₗ E.globalDof M k ∘ₗ
    Submodule.inclusion (E.globalSpacePartial_le M Γ k)

/-- **The free global DOFs are a linear isomorphism** `Λ_{h,Γ}ᵏ(M) ≃ ℝ^{free DOFs}`. -/
def partialDofEquiv (k : ℕ) : E.globalSpacePartial M Γ k ≃ₗ[ℝ] (E.FreeDofIdx M Γ k → ℝ) := by
  classical
  refine LinearEquiv.ofBijective (E.partialDof M Γ k) ⟨fun u v huv => ?_, fun c => ?_⟩
  · set u' := Submodule.inclusion (E.globalSpacePartial_le M Γ k) u
    set v' := Submodule.inclusion (E.globalSpacePartial_le M Γ k) v
    have hu := (E.mem_globalSpacePartial_iff M Γ u').1 u.2
    have hv := (E.mem_globalSpacePartial_iff M Γ v').1 v.2
    have : E.globalDof M k u' = E.globalDof M k v' := funext fun p => by
      by_cases hp : E.IsDofOn M Γ p
      · rw [hu p hp, hv p hp]
      · exact congr_fun huv ⟨p, hp⟩
    exact Submodule.inclusion_injective _ ((E.globalDofEquiv M k).injective this)
  · set c' : E.GlobalDofIdx M k → ℝ := fun p => if hp : E.IsDofOn M Γ p then 0 else c ⟨p, hp⟩
    have hc' : ∀ p, E.globalDof M k ⟨_, E.ofGlobalDof_mem M k c'⟩ p = c' p := fun p => by
      rw [E.globalDof_apply M k _ p (faceSimplex M p.1) (subset_faceSimplex M p.1)]
      exact localDof_ofGlobalDof _ _ _ _ _ _ (subset_faceSimplex M p.1) _
    have hmem : E.ofGlobalDof M k c' ∈ E.globalSpacePartial M Γ k :=
      (E.mem_globalSpacePartial_iff M Γ ⟨_, E.ofGlobalDof_mem M k c'⟩).2 fun p hp => by
        rw [hc']; simp [c', hp]
    refine ⟨⟨_, hmem⟩, funext fun p => ?_⟩
    change E.globalDof M k ⟨_, E.ofGlobalDof_mem M k c'⟩ p.1 = c p
    rw [hc']; simp [c', p.2]

/-- **`dim Λ_{h,Γ}ᵏ(M) = #{free DOFs}`**. -/
theorem finrank_globalSpacePartial (k : ℕ) :
    Module.finrank ℝ (E.globalSpacePartial M Γ k) = Fintype.card (E.FreeDofIdx M Γ k) := by
  rw [(E.partialDofEquiv M Γ k).finrank_eq, Module.finrank_fintype_fun_eq_card]

/-- The glued spaces `V_{h,Γ}ᵏ ⊆ L²(Ω; Λᵏ)`. -/
def VPartial (k : ℤ) : Submodule ℝ (L2F ℝ M.domain (formIdx n k)) :=
  LinearMap.range (E.glue M k ∘ₗ (E.globalSpacePartial M Γ k.toNat).subtype)

/-- **`dim V_{h,Γ}ᵏ = #{free DOFs}`** (the gluing is injective). -/
theorem finrank_VPartial (hΩ : IsOpen M.domain) (k : ℕ) :
    Module.finrank ℝ (E.VPartial M Γ k) = Fintype.card (E.FreeDofIdx M Γ k) := by
  have hinj : Function.Injective
      (E.glue M (k : ℤ) ∘ₗ (E.globalSpacePartial M Γ ((k : ℤ).toNat)).subtype) := by
    rw [LinearMap.coe_comp]
    exact (E.glue_injective M hΩ k).comp Subtype.val_injective
  rw [VPartial, LinearMap.finrank_range_of_inj hinj]
  exact finrank_globalSpacePartial E M Γ k

theorem VPartial_le_V (k : ℤ) : E.VPartial M Γ k ≤ E.V M k := by
  rintro _ ⟨u, rfl⟩
  exact ⟨⟨u, E.globalSpacePartial_le M Γ _ u.2⟩, rfl⟩

end LocalElement

namespace PolySeq

variable (S : PolySeq) (M : SimplicialMesh n) (Γ : Set (Finset (Fin n → ℝ)))

/-- The faces of `M` not contained in a facet of `Γ`. -/
def freeFaces : Finset (Finset (Fin n → ℝ)) := by
  classical
  exact (LocalElement.meshFaces M).filter fun g => ¬ ∃ F ∈ Γ, g ⊆ F

theorem mem_freeFaces {g : Finset (Fin n → ℝ)} :
    g ∈ freeFaces M Γ ↔ g ∈ LocalElement.meshFaces M ∧ ¬ ∃ F ∈ Γ, g ⊆ F := by
  classical
  unfold freeFaces; exact mem_filter

/-- **`dim Λ_{h,Γ}ᵏ(M) = Σ_{m ≤ n} #{m-faces not in a facet of Γ} · dim(test forms)`** for the
families of an admissible sequence. -/
theorem finrank_globalSpacePartial (k : ℕ) :
    Module.finrank ℝ ((polyElement n S).globalSpacePartial M Γ k) =
      ∑ m ∈ range (n + 1), {g | g ∈ M.faces m ∧ ¬ ∃ F ∈ Γ, g ⊆ F}.ncard *
        Module.finrank ℝ (S.test k m) := by
  classical
  have e : (polyElement n S).FreeDofIdx M Γ k ≃
      Σ g : freeFaces M Γ, S.DofIdx (g : Finset (Fin n → ℝ)) k :=
    { toFun := fun p => ⟨⟨p.1.1.1, (mem_freeFaces M Γ).2 ⟨p.1.1.2, p.2⟩⟩, p.1.2⟩
      invFun := fun q => ⟨⟨⟨q.1.1, ((mem_freeFaces M Γ).1 q.1.2).1⟩, q.2⟩,
        ((mem_freeFaces M Γ).1 q.1.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [LocalElement.finrank_globalSpacePartial, Fintype.card_congr e,
    S.card_sigma_dofIdx_eq_sum _ (fun g hg => card_le_of_mem_meshFaces M
      ((mem_freeFaces M Γ).1 hg).1) k]
  refine sum_congr rfl fun m _ => ?_
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext g
  simp only [coe_filter, mem_freeFaces, LocalElement.mem_meshFaces, SimplicialMesh.faces,
    Set.mem_ofPred_eq]
  tauto

end PolySeq

/-! ### Boundary conditions in the low degrees only -/

namespace LocalElement

variable (E : LocalElement n) (M : SimplicialMesh n)

/-- **`d Λ_{h,Γ}ᵏ ⊆ Λ_{h,Γ'}ᵏ⁺¹` for `Γ' ⊆ Γ`**: dropping boundary conditions in the next degree
keeps the complex property. -/
theorem dPiecewise_mem_globalSpacePartial_of_subset {Γ Γ' : Set (Finset (Fin n → ℝ))}
    (h : Γ' ⊆ Γ) {k : ℕ} {u : E.Piecewise M k} (hu : u ∈ E.globalSpacePartial M Γ k) :
    E.dPiecewise M k u ∈ E.globalSpacePartial M Γ' (k + 1) :=
  E.globalSpacePartial_anti M h (k + 1) (E.dPiecewise_mem_globalSpacePartial M Γ hu)

/-- The facets carrying boundary conditions in degree `k` when these are imposed in the degrees
`k < j` only: all boundary facets for `k < j`, none for `k ≥ j`. -/
def bcFacets (j k : ℕ) : Set (Finset (Fin n → ℝ)) :=
  if k < j then {F | M.IsBoundaryFacet F} else ∅

theorem bcFacets_succ_subset (j k : ℕ) : bcFacets M j (k + 1) ⊆ bcFacets M j k := by
  unfold bcFacets
  split_ifs with h1 h2
  · exact le_rfl
  · omega
  · exact Set.empty_subset _
  · exact le_rfl

theorem bcFacets_subset (j k : ℕ) : bcFacets M j k ⊆ {F | M.IsBoundaryFacet F} := by
  unfold bcFacets; split_ifs
  · exact le_rfl
  · exact Set.empty_subset _

/-- **The complex with boundary conditions in the degrees `< j`** is closed under `d`:
`d Λ_{h,bc}ᵏ ⊆ Λ_{h,bc}ᵏ⁺¹`. With `j = 2` in `ℝ³` this is the pattern
`V̊ₕ⁰ → V̊ₕ¹ → Vₕ²` of [QuennevilleBelair2015], §6.3 (boundary conditions on the `0`- and
`1`-forms only). -/
theorem dPiecewise_mem_globalSpacePartial_bcFacets (j : ℕ) {k : ℕ} {u : E.Piecewise M k}
    (hu : u ∈ E.globalSpacePartial M (bcFacets M j k) k) :
    E.dPiecewise M k u ∈ E.globalSpacePartial M (bcFacets M j (k + 1)) (k + 1) :=
  E.dPiecewise_mem_globalSpacePartial_of_subset M (bcFacets_succ_subset M j k) hu

/-- `Λ̊_hᵏ(M) ⊆ Λ_{h,Γ}ᵏ(M)` for every set `Γ` of boundary facets. -/
theorem globalSpace₀_le_globalSpacePartial {Γ : Set (Finset (Fin n → ℝ))}
    (hΓ : Γ ⊆ {F | M.IsBoundaryFacet F}) (k : ℕ) :
    E.globalSpace₀ M k ≤ E.globalSpacePartial M Γ k :=
  (E.globalSpacePartial_boundary M k).symm.le.trans (E.globalSpacePartial_anti M hΓ k)

/-- **`dim V̊ₕᵏ ≤ dim V_{h,Γ}ᵏ`** for every set `Γ` of boundary facets. -/
theorem finrank_V₀_le_finrank_VPartial (hΩ : IsOpen M.domain) {Γ : Set (Finset (Fin n → ℝ))}
    (hΓ : Γ ⊆ {F | M.IsBoundaryFacet F}) (k : ℕ) :
    Module.finrank ℝ (E.V₀ M k) ≤ Module.finrank ℝ (E.VPartial M Γ k) := by
  rw [E.finrank_V₀ M hΩ k, ← E.finrank_globalSpace₀ M k, E.finrank_VPartial M Γ hΩ k,
    ← E.finrank_globalSpacePartial M Γ k]
  exact Submodule.finrank_mono (E.globalSpace₀_le_globalSpacePartial M hΓ k)

end LocalElement

namespace PolySeq

/-- **The Ch. 6 spaces of the second row of Table 6.1 are nonzero**: on the level-`(N+1)`
Freudenthal mesh of `(0, ½)³`, the spaces `V̊ₕ⁰ = P̊₂Λ⁰`, `V̊ₕ¹ = P̊₂⁻Λ¹` (boundary conditions)
and `Vₕ² = P₁Λ²`, `Vₕ³ = P₀Λ³` (no boundary conditions) of [QuennevilleBelair2015], §6.3, are
nonzero, for every `N`. -/
theorem lagrangeP2_VPartial_bcFacets_ne_bot (N k : ℕ) (hk : k ≤ 3) :
    (polyElement 3 lagrangeP2).VPartial (freudenthalMesh 0 (1 / 2) (by norm_num) (N + 1))
      (LocalElement.bcFacets (freudenthalMesh 0 (1 / 2) (by norm_num) (N + 1)) 2 k) k ≠ ⊥ := by
  intro h
  have h0 : (polyElement 3 lagrangeP2).V₀ (freudenthalMesh 0 (1 / 2) (by norm_num) (N + 1)) k ≠ ⊥ :=
    lagrangeP2_V₀_ne_bot N k hk
  have hle := (polyElement 3 lagrangeP2).finrank_V₀_le_finrank_VPartial _
    (isOpen_freudenthalMesh_domain (0 : Fin 3 → ℝ) (1 / 2) (by norm_num) (N + 1))
    (LocalElement.bcFacets_subset _ 2 k) k
  rw [h, finrank_bot, Nat.le_zero, Submodule.finrank_eq_zero] at hle
  exact h0 hle

end PolySeq

end Feec.FiniteElement
