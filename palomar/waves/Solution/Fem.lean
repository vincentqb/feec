module

public import Solution.Complex
public import Solution.Forms
public import Solution.Spaces
public import Solution.Regularity

/-!
# The uniform stability of the finite element de Rham complexes

The part of `FEEC.fem` of `palomar/fem` that `FEEC.fem_wave` uses (`femFamily`, by cases on the
boundary condition, `femFamily_dMax` and `femFamily_dMin`), with the proof of `palomar/fem`: from
the finite element theory of `Feec.Models.StarShaped.PolyFiniteElement` on the star domain and the
mesh family of the challenge (`starDomainOf`, `meshFamilyOf`), the complexes
`MeshFamily.poly` and `MeshFamily.polyMin` of the admissible sequence (whose spaces are the
challenge's, `mem_V_iff`, `mem_V₀_iff`), the uniformly bounded smoothed projections
(`MeshFamily.exists_uniform_polyProj`, `_Min`; defined on all of `L²`, so their `L²` extensions
are themselves) and the interpolation error (`MeshFamily.exists_mem_poly_le_of_isCsForm`,
`_Min`); the complexes are `Feec`'s `HΛ(Ω)` and `H̊Λ(Ω)` (`dMax_eq`, `dMin_eq`), and the uniformly
bounded projections attain the Jackson rate (`HilbertComplex.SubcomplexFamily.Jackson.projRate`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.2, §5.5
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Filter Topology Set

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.StarShaped HilbertComplex

variable {n : ℕ}

theorem dMax_eq_complex [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω) (k : ℤ) :
    (starDomainOf hΩ).complex.d k (k + 1) = dMax Ω k := by
  rw [deRham_maximalComplex_d, dMax_eq]; rfl

theorem dMin_eq_complex [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω) (k : ℤ) :
    (starDomainOf hΩ).complexMin.d k (k + 1) = dMin Ω k := by
  rw [deRham_minimalComplex_d, dMin_eq]; rfl

/-- `femFamily` for `HΛ(Ω)`. -/
theorem femFamily_dMax [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M) (S : PolySeq) :
    ∃ (H : HilbertComplex ℝ (L2Form Ω)) (F : H.SubcomplexFamily ℕ) (J : F.Jackson ℕ),
      (∀ k, H.d k (k + 1) = dMax Ω k) ∧
      (∀ N k, ((F.V N).V k : Set (L2Form Ω k)) = femSpace Ω (M N) S ∅ k) ∧
      (∃ C : ℝ, ∀ N i, ∃ P : L2Form Ω i →L[ℝ] L2Form Ω i, ‖P‖ ≤ C ∧
        (∀ x, P x ∈ (F.V N).V i) ∧
          ∀ x : (H.d i (i + 1)).domain, P x = ((F.π N).π i x : L2Form Ω i)) ∧
      (∀ N, J.meshSize N = meshSize (M N)) ∧ (∀ s, J.ord s = s + 1) ∧
      (∀ s j L x, J.Reg s j L x ↔ S.PolyOrderAt n s j ∧ IsCsForm Ω s j L x) ∧ J.ProjRate := by
  set D := starDomainOf hΩ
  set Fm := meshFamilyOf hΩ hM
  obtain ⟨K, hK1, hK⟩ := Fm.exists_uniform_polyProj S.toFeec
  choose π hπ1 _ using hK
  let H : HilbertComplex ℝ (L2Form Ω) := HilbertComplex.ofFeec D.complex
  let F : H.SubcomplexFamily ℕ :=
    { l := atTop
      V := fun N => Subcomplex.ofFeec (Fm.poly S.toFeec N)
      finiteDimensional := fun N i =>
        inferInstanceAs (FiniteDimensional ℝ ((Fm.poly S.toFeec N).V i))
      π := fun N => CochainProjection.ofFeec (π N) }
  let J : F.Jackson ℕ :=
    { meshSize := fun N => meshSize (M N)
      meshSize_nonneg := fun N => (hM.2.2.1 N).le
      tendsto_meshSize := hM.2.2.2
      Reg := fun s j L x => S.PolyOrderAt n s j ∧ IsCsForm Ω s j L x
      ord := fun s => s + 1
      B := fun _ => Fm.polyInterpBound S.toFeec
      jackson := fun s N i L x hL hx => by
        obtain ⟨v, hv, h1, h2⟩ := Fm.exists_mem_poly_le_of_isCsForm S.toFeec
          ((S.polyOrderAt_iff s i).1 hx.1) ((isCsForm_iff hΩ s i L x).1 hx.2) hL N
        have e : Fm.polyInterpBound S.toFeec i * L * (Fm.mesh N).meshSize ^ (s + 1) =
            Fm.polyInterpBound S.toFeec i * (L * meshSize (M N) ^ ((s : ℝ) + 1)) := by
          rw [show ((s : ℝ) + 1) = ((s + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
            meshFamilyOf_mesh, SimplicialMesh.meshSize_toFeec]
          ring
        exact ⟨v, hv, e ▸ h1, fun j hxj => e ▸ h2 j hxj⟩ }
  have hP : ∀ N i, ∃ P : L2Form Ω i →L[ℝ] L2Form Ω i, ‖P‖ ≤ K ∧ (∀ x, P x ∈ (F.V N).V i) ∧
      ∀ x : (H.d i (i + 1)).domain, P x = ((F.π N).π i x : L2Form Ω i) := fun N i =>
    ⟨(π N).π i |>.mkContinuous K (hπ1 N i), LinearMap.mkContinuous_norm_le _ (by linarith) _,
      (π N).mem i, fun x => rfl⟩
  refine ⟨H, F, J, fun k => dMax_eq_complex hΩ k, fun N k => ?_, ⟨K, hP⟩, fun N => rfl,
    fun s => rfl, fun s j L x => Iff.rfl, J.projRate hP⟩
  ext u
  exact mem_V_iff S (M N) Ω (hM.1 N) u

/-- `femFamily` for `H̊Λ(Ω)`. -/
theorem femFamily_dMin [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M) (S : PolySeq) :
    ∃ (H : HilbertComplex ℝ (L2Form Ω)) (F : H.SubcomplexFamily ℕ) (J : F.Jackson ℕ),
      (∀ k, H.d k (k + 1) = dMin Ω k) ∧
      (∀ N k, ((F.V N).V k : Set (L2Form Ω k)) = femSpace Ω (M N) S (M N).boundaryFacets k) ∧
      (∃ C : ℝ, ∀ N i, ∃ P : L2Form Ω i →L[ℝ] L2Form Ω i, ‖P‖ ≤ C ∧
        (∀ x, P x ∈ (F.V N).V i) ∧
          ∀ x : (H.d i (i + 1)).domain, P x = ((F.π N).π i x : L2Form Ω i)) ∧
      (∀ N, J.meshSize N = meshSize (M N)) ∧ (∀ s, J.ord s = s + 1) ∧
      (∀ s j L x, J.Reg s j L x ↔ S.PolyOrderAt n s j ∧ IsCsFormMin Ω s j L x) ∧ J.ProjRate := by
  set D := starDomainOf hΩ
  set Fm := meshFamilyOf hΩ hM
  obtain ⟨K, hK1, hK⟩ := Fm.exists_uniform_polyProjMin S.toFeec
  choose π hπ1 _ using hK
  let H : HilbertComplex ℝ (L2Form Ω) := HilbertComplex.ofFeec D.complexMin
  let F : H.SubcomplexFamily ℕ :=
    { l := atTop
      V := fun N => Subcomplex.ofFeec (Fm.polyMin S.toFeec N)
      finiteDimensional := fun N i =>
        inferInstanceAs (FiniteDimensional ℝ ((Fm.polyMin S.toFeec N).V i))
      π := fun N => CochainProjection.ofFeec (π N) }
  let J : F.Jackson ℕ :=
    { meshSize := fun N => meshSize (M N)
      meshSize_nonneg := fun N => (hM.2.2.1 N).le
      tendsto_meshSize := hM.2.2.2
      Reg := fun s j L x => S.PolyOrderAt n s j ∧ IsCsFormMin Ω s j L x
      ord := fun s => s + 1
      B := fun _ => Fm.polyInterpBound S.toFeec
      jackson := fun s N i L x hL hx => by
        obtain ⟨v, hv, h1, h2⟩ := Fm.exists_mem_polyMin_le_of_isCsFormMin S.toFeec
          ((S.polyOrderAt_iff s i).1 hx.1) ((isCsFormMin_iff hΩ s i L x).1 hx.2) hL N
        have e : Fm.polyInterpBound S.toFeec i * L * (Fm.mesh N).meshSize ^ (s + 1) =
            Fm.polyInterpBound S.toFeec i * (L * meshSize (M N) ^ ((s : ℝ) + 1)) := by
          rw [show ((s : ℝ) + 1) = ((s + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
            meshFamilyOf_mesh, SimplicialMesh.meshSize_toFeec]
          ring
        exact ⟨v, hv, e ▸ h1, fun j hxj => e ▸ h2 j hxj⟩ }
  have hP : ∀ N i, ∃ P : L2Form Ω i →L[ℝ] L2Form Ω i, ‖P‖ ≤ K ∧ (∀ x, P x ∈ (F.V N).V i) ∧
      ∀ x : (H.d i (i + 1)).domain, P x = ((F.π N).π i x : L2Form Ω i) := fun N i =>
    ⟨(π N).π i |>.mkContinuous K (hπ1 N i), LinearMap.mkContinuous_norm_le _ (by linarith) _,
      (π N).mem i, fun x => rfl⟩
  refine ⟨H, F, J, fun k => dMin_eq_complex hΩ k, fun N k => ?_, ⟨K, hP⟩, fun N => rfl,
    fun s => rfl, fun s j L x => Iff.rfl, J.projRate hP⟩
  ext u
  exact mem_V₀_iff S (M N) Ω (hM.1 N) u

/-- **The uniform stability of `palomar/fem`** (`FEEC.fem` without its graph-norm bounds and
approximation, which `FEEC.fem_wave` does not use): for `HΛ(Ω)` (`b = false`) or `H̊Λ(Ω)`
(`b = true`), the finite element spaces are those of a family of subcomplexes whose cochain
projections extend to uniformly bounded projections of `L²(Ω; Λᵏ)`, with a Jackson estimate of
order `h_N^{s+1}` on `C^{s+2}` forms attained by the projections. -/
theorem femFamily [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M) (S : PolySeq) (b : Bool) :
    ∃ (H : HilbertComplex ℝ (L2Form Ω)) (F : H.SubcomplexFamily ℕ) (J : F.Jackson ℕ),
      (∀ k, H.d k (k + 1) = if b then dMin Ω k else dMax Ω k) ∧
      (∀ N k, ((F.V N).V k : Set (L2Form Ω k)) =
        femSpace Ω (M N) S (if b then (M N).boundaryFacets else ∅) k) ∧
      (∃ C : ℝ, ∀ N i, ∃ P : L2Form Ω i →L[ℝ] L2Form Ω i, ‖P‖ ≤ C ∧
        (∀ x, P x ∈ (F.V N).V i) ∧
          ∀ x : (H.d i (i + 1)).domain, P x = ((F.π N).π i x : L2Form Ω i)) ∧
      (∀ N, J.meshSize N = meshSize (M N)) ∧ (∀ s, J.ord s = s + 1) ∧
      (∀ s j L x, J.Reg s j L x ↔ S.PolyOrderAt n s j ∧
        (if b then IsCsFormMin Ω else IsCsForm Ω) s j L x) ∧ J.ProjRate := by
  cases b
  · exact femFamily_dMax hΩ hM S
  · exact femFamily_dMin hΩ hM S

end FEEC
