module

public import Feec.Models.Cube.EigenDense
public import Feec.Models.Cube.DeRhamIdentFEM
public import Feec.Fourier.SpectralGalerkin
public import Feec.Domain.Rellich
public import Feec.Operator.Multiplication

/-!
# Compactness on bounded domains: Rellich, Weber, and a complete set of eigenvectors

For `H̊¹(Ω; ℝ³) → H̊(curl, Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)`: Rellich compactness (degree `0`) on bounded open
sets, Weber compactness (degree `1`) on open cubes, and the complete set of eigenvectors of the
wave group that Weber compactness gives.

## Main results

* `hasCompactBall_minimal_gradOp`: Rellich's theorem for `H̊¹(Ω; ℝᵐ)`, `Ω ⊆ ℝⁿ` bounded open.
* `hasWeberCompactness_cube`: every open cube has Weber compactness.
* `HasWeberCompactness.weber_of_coeff`: Weber's lemma with a coercive coefficient.
* `eigenDense_gradCurl_of_weber`: Weber compactness gives a dense set of eigenvectors.

## References

* [L. C. Evans, *Partial Differential Equations*][Evans2010]
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ENNReal Topology
open Set MeasureTheory Filter LinearPMap

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {ι : Type*} {c : ComplexShape ι} {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace ℂ (W i)] [∀ i, CompleteSpace (W i)] [∀ i, InnerProductSpace ℝ (W i)]
  [∀ i, IsScalarTower ℝ ℂ (W i)] {H : HilbertComplex ℂ c W}

theorem HasCompactPropertyAt.restrictScalars
    (hre : ∀ i (x y : W i), ⟪x, y⟫_ℝ = RCLike.re ⟪x, y⟫_ℂ) {i : ι}
    (h : H.HasCompactPropertyAt i) : H.restrictScalars.HasCompactPropertyAt i := by
  obtain ⟨K, hK, hsub⟩ := h
  refine ⟨K, hK, fun x hx hx' h1 h2 h3 => ?_⟩
  have hadj : (H.restrictScalars.d (c.prev i) i)† = ((H.d (c.prev i) i)†).restrictScalars :=
    (H.d (c.prev i) i).adjoint_restrictScalars (hre _) (hre _) (H.dense _ _)
  obtain ⟨hy, ey⟩ := LinearPMap.exists_mem_apply_eq_of_eq hadj ⟨x, hx'⟩
  exact hsub x hx hy h1 h2 (by rw [← ey] at h3; exact h3)

end Feec.HilbertComplex

namespace Feec.Models.BoundedDomain

open Feec.Fourier Feec.Fourier.GradCurl Feec.HilbertComplex Feec.Domain Feec.Operator

theorem torus_hasCompactPropertyAt_zero : Models.Torus.GradCurl.complex.HasCompactPropertyAt 0 := by
  refine hasCompactPropertyAt_of_coercive (Torus.symbolComplex Fourier.GradCurl.gradCurl) 0
    (fun k => ‖Torus.freq k‖ ^ 2) ?_ Models.Torus.DeRham.finite_norm_freq_sq_le
  have hn : ComplexShape.fin3.next 0 = 1 := ComplexShape.next_eq' _ (by simp)
  have hp : ComplexShape.fin3.prev 0 = 0 := ComplexShape.prev_eq_self' _ _ (by simp)
  rw [hn, hp]
  intro k
  show ∀ v : Vec, ‖Torus.freq k‖ ^ 2 * ‖v‖ ^ 2 ≤ ‖grad (Torus.freq k) v‖ ^ 2 +
    ‖ContinuousLinearMap.adjoint (0 : Vec →L[ℂ] Vec) v‖ ^ 2
  intro v
  rw [_root_.map_zero, _root_.zero_apply, norm_zero, norm_grad]
  ring_nf; rfl

theorem torus_hasCompactPropertyAt_one : Models.Torus.GradCurl.complex.HasCompactPropertyAt 1 := by
  refine hasCompactPropertyAt_of_coercive (Torus.symbolComplex Fourier.GradCurl.gradCurl) 1
    (fun k => ‖Torus.freq k‖ ^ 2) ?_ Models.Torus.DeRham.finite_norm_freq_sq_le
  have hn : ComplexShape.fin3.next 1 = 2 := ComplexShape.next_eq' _ (by simp)
  have hp : ComplexShape.fin3.prev 1 = 0 := ComplexShape.prev_eq' _ (by simp)
  rw [hn, hp]
  intro k
  show ∀ v : Mat, ‖Torus.freq k‖ ^ 2 * ‖v‖ ^ 2 ≤ ‖curl (Torus.freq k) v‖ ^ 2 +
    ‖ContinuousLinearMap.adjoint (grad (Torus.freq k)) v‖ ^ 2
  intro v
  rw [adjoint_grad, norm_curl_sq_add_norm_div_sq]

section Cube

open Models.Cube

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

attribute [local instance] RealTorus.isScalarTower

theorem realTorus_hasCompactPropertyAt {i : Fin 3} (hi : i ≠ 2) :
    RealTorus.gradCurl.HasCompactPropertyAt i := by
  have h : Models.Torus.GradCurl.complex.HasCompactPropertyAt i := by
    fin_cases i
    · exact torus_hasCompactPropertyAt_zero
    · exact torus_hasCompactPropertyAt_one
    · exact absurd rfl hi
  exact h.restrictScalars RealTorus.real_inner_eq_re

theorem cubeComplex_hasCompactPropertyAt {i : Fin 3} (hi : i ≠ 2) :
    RowWise.cubeComplex.HasCompactPropertyAt i := by
  rw [RowWise.cubeComplex_eq_compress]
  exact hasCompactPropertyAt_compress _ _ _ (realTorus_hasCompactPropertyAt hi)

theorem complexCube_hasCompactPropertyAt (b : R3) {s : ℝ} (hs : 0 < s) {i : Fin 3}
    (hi : i ≠ 2) : (Ident.complexCube b s).HasCompactPropertyAt i := by
  rw [Ident.complexCube_eq hs]
  exact hasCompactPropertyAt_transport (inv_pos.2 (Domain.jac_pos (Ident.scale_ne_zero hs)))
    (Ident.inner_pullC hs) _ (cubeComplex_hasCompactPropertyAt hi)

end Cube

section DeRham

theorem _root_.LinearPMap.exists_adjoint_eq_zero_of_subsingleton {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [Subsingleton E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (T : E →ₗ.[𝕜] F) (y : F) :
    ∃ hy : y ∈ T†.domain, T† ⟨y, hy⟩ = 0 := by
  refine ⟨LinearPMap.mem_adjoint_domain_of_exists y ⟨0, fun x => ?_⟩, Subsingleton.elim _ _⟩
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx, LinearPMap.map_zero, inner_zero_right, inner_zero_left]

instance (n : ℕ) : IsEmpty (formIdx n (-1)) :=
  ⟨fun s => by have h := s.2; have : (0 : ℤ) ≤ (s.1.card : ℤ) := Int.natCast_nonneg _; omega⟩

theorem hasCompactBall_minimal_extDeriv_cube (n : ℕ) :
    HasCompactBall ((extDerivOp ℝ n 0).minimal (Cube.FEM.cubeDomain n)) := by
  have h := (Cube.FEM.hasCompactProperty_min (n := n)) 0
  rw [hasCompactPropertyAt_iff_of_rel (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)
    (show (ComplexShape.up ℤ).Rel 0 (0 + 1) by simp)] at h
  obtain ⟨K, hK, hsub⟩ := h
  have hd := (deRham ℝ n).minimalComplex_d (Cube.FEM.isOpen_cubeDomain n) 0
  refine ⟨K, hK, fun x h1 h2 => ?_⟩
  obtain ⟨hy, ey⟩ := LinearPMap.exists_mem_apply_eq_of_eq hd.symm x
  obtain ⟨hy', ey'⟩ := LinearPMap.exists_adjoint_eq_zero_of_subsingleton
    ((Cube.FEM.complexMin n).d (-1) 0) (x : L2F ℝ (Cube.FEM.cubeDomain n) (formIdx n 0))
  exact hsub _ hy hy' h1 (by
    change ‖((deRham ℝ n).minimalComplex (Cube.FEM.isOpen_cubeDomain n)).d 0 (0 + 1) ⟨_, hy⟩‖ ≤ 1
    rw [ey]; exact h2) (by rw [ey', norm_zero]; exact zero_le_one)

theorem exists_aff_preimage_cubeDomain {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hb : Bornology.IsBounded Ω) : ∃ (a : ℝ) (b : Fin n → ℝ), a ≠ 0 ∧
      Ω ⊆ aff a b ⁻¹' Cube.FEM.cubeDomain n := by
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  set ρ : ℝ := |R| + 1
  have hρ : 0 < ρ := by positivity
  refine ⟨(4 * ρ)⁻¹, fun _ => 1 / 4, by positivity, fun x hx i _ => ?_⟩
  have hxi : |x i| ≤ |R| := by
    have h1 : ‖x‖ ≤ R := by simpa using hR hx
    exact (norm_le_pi_norm x i).trans (h1.trans (le_abs_self R))
  have hlt : |x i| < ρ := by linarith
  rw [abs_lt] at hlt
  simp only [aff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Set.mem_Ioo]
  have h4 : 0 < 4 * ρ := by positivity
  constructor
  · rw [← div_eq_inv_mul]
    have : -(1 / 4) < x i / (4 * ρ) := by rw [lt_div_iff₀ h4]; linarith
    linarith
  · rw [← div_eq_inv_mul]
    have : x i / (4 * ρ) < 1 / 4 := by rw [div_lt_iff₀ h4]; linarith
    linarith

theorem hasCompactBall_minimal_extDeriv_zero {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) : HasCompactBall ((extDerivOp ℝ n 0).minimal Ω) := by
  obtain ⟨a, b, ha, hsub⟩ := exists_aff_preimage_cubeDomain hb
  exact ConstCoeffOp.hasCompactBall_minimal_of_subset_preimage (isHomogeneous_extDerivOp 0) ha
    b hΩ (Cube.FEM.isOpen_cubeDomain n) hsub (hasCompactBall_minimal_extDeriv_cube n)

/-- The element of a `1`-form index `s = {j}`. -/
def formIdxOne {n : ℕ} (s : formIdx n 1) : Fin n :=
  (Finset.card_eq_one.1 (by exact_mod_cast s.2 : s.1.card = 1)).choose

theorem formIdxOne_spec {n : ℕ} (s : formIdx n 1) : s.1 = {formIdxOne s} :=
  (Finset.card_eq_one.1 (by exact_mod_cast s.2 : s.1.card = 1)).choose_spec

theorem eq_formIdxOne {n : ℕ} (s : formIdx n 1) : s = ⟨{formIdxOne s}, by simp⟩ :=
  Subtype.ext (formIdxOne_spec s)

theorem gradOp_apply_formIdxOne {n m : ℕ} (φ : Fin m → (Fin n → ℝ) → ℝ) (i : Fin m) :
    (fun s : formIdx n 1 =>
      (gradOp n m : ConstCoeffOp (Fin n → ℝ) ℝ (Fin m) (Fin m × Fin n)).apply φ (i, formIdxOne s)) =
      (extDerivOp ℝ n 0).apply (fun _ => φ i) := by
  funext s x
  have e := extDerivOp_zero_apply (𝕜 := ℝ) (fun _ => φ i) (formIdxOne s) x
  rw [← eq_formIdxOne] at e
  rw [e, gradOp_apply]

/-- Rellich's theorem for `H̊¹(Ω; ℝᵐ)` on every bounded open `Ω ⊆ ℝⁿ`. [Evans2010], §5.7 -/
theorem hasCompactBall_minimal_gradOp {n m : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) :
    HasCompactBall
      ((gradOp n m : ConstCoeffOp (Fin n → ℝ) ℝ (Fin m) (Fin m × Fin n)).minimal Ω) := by
  let e0 : formIdx n 0 := ⟨∅, by simp⟩
  refine (hasCompactBall_minimal_extDeriv_zero hΩ hb).of_components
    (fun i => compF (𝕜 := ℝ) (Ω := Ω) fun _ : formIdx n 0 => i)
    (fun i => compF (𝕜 := ℝ) (Ω := Ω) (ι' := formIdx n (0 + 1)) fun s => (i, formIdxOne s))
    (fun w => (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => L2 ℝ Ω)).symm fun i => w i e0)
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => L2 ℝ Ω)).symm.continuous.comp
      (continuous_pi fun i =>
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : formIdx n 0 => L2 ℝ Ω) e0).continuous.comp
          (continuous_apply i)))
    (fun x => rfl) fun x i => ?_
  refine (gradOp n m).mem_minimal_of_mapsTo_testGraph hΩ hΩ _ _ (fun φ hφ => ?_) x
  refine ⟨fun _ => φ i, fun _ => hφ i, ?_⟩
  rw [compF_testField, compF_testField]
  exact Prod.ext rfl (testField_congr _ _ (gradOp_apply_formIdxOne φ i))

end DeRham

theorem exists_openCube_superset {d : Type*} [Fintype d] {Ω : Set (d → ℝ)}
    (hb : Bornology.IsBounded Ω) : ∃ (b : d → ℝ) (s : ℝ), 0 < s ∧ Ω ⊆ Cube.Geometry.openCube b s := by
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  refine ⟨fun _ => -(|R| + 1), 2 * |R| + 2, by positivity, fun x hx i _ => ?_⟩
  have hxi : |x i| ≤ |R| := by
    have h1 : ‖x‖ ≤ R := by simpa using hR hx
    exact (norm_le_pi_norm x i).trans (h1.trans (le_abs_self R))
  rw [abs_le] at hxi
  constructor <;> linarith

variable {Ω : Set R3}

theorem hasCompactBall_minimal_grad_iff (hΩ : IsOpen Ω) :
    (gradCurl ℝ hΩ).toHilbertComplex.HasCompactPropertyAt 0 ↔
      HasCompactBall ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).minimal Ω) := by
  rw [hasCompactPropertyAt_iff_of_not_rel_of_rel (fun h hh => by
    simp only [ComplexShape.window_rel] at hh; omega) (show ComplexShape.fin3.Rel 0 1 by simp)]
  constructor
  · rintro ⟨K, hK, hsub⟩
    exact ⟨K, hK, fun x h1 h2 => hsub (x : L2F ℝ Ω (Fin 3)) x.2 h1 h2⟩
  · rintro ⟨K, hK, hsub⟩
    exact ⟨K, hK, fun x hx h1 h2 => hsub ⟨x, hx⟩ h1 h2⟩

theorem hasCompactBall_minimal_grad_openCube (b : R3) {s : ℝ} (hs : 0 < s) :
    HasCompactBall ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).minimal (Cube.Geometry.openCube b s)) :=
  (hasCompactBall_minimal_grad_iff (Cube.Geometry.isOpen_openCube b s)).1
    (complexCube_hasCompactPropertyAt b hs (i := 0) (by decide))

theorem hasCompactBall_minimal_grad (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    HasCompactBall ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).minimal Ω) := by
  obtain ⟨b, s, hs, hsub⟩ := exists_openCube_superset hb
  exact (gradOp 3 3).hasCompactBall_minimal_of_subset hΩ (Cube.Geometry.isOpen_openCube b s) hsub
    (hasCompactBall_minimal_grad_openCube b hs)

theorem gradCurl_hasCompactPropertyAt_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (gradCurl ℝ hΩ).toHilbertComplex.HasCompactPropertyAt 0 :=
  (hasCompactBall_minimal_grad_iff hΩ).2 (hasCompactBall_minimal_grad hΩ hb)

/-- Weber compactness: the unit box of `D(curl_min) ∩ D(div_max)` is precompact in `L²`. -/
def HasWeberCompactness (Ω : Set R3) : Prop :=
  ∃ K : Set (L2F ℝ Ω Ix), IsCompact K ∧ ∀ (u : L2F ℝ Ω Ix)
    (hu : u ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain)
    (hu' : u ∈ ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).formalAdj.maximal Ω).domain),
    ‖u‖ ≤ 1 → ‖(curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω ⟨u, hu⟩‖ ≤ 1 →
      ‖(gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).formalAdj.maximal Ω ⟨u, hu'⟩‖ ≤ 1 → u ∈ K

theorem hasWeberCompactness_iff (hΩ : IsOpen Ω) :
    HasWeberCompactness Ω ↔ (gradCurl ℝ hΩ).toHilbertComplex.HasCompactPropertyAt 1 := by
  rw [hasCompactPropertyAt_iff_of_rel (show ComplexShape.fin3.Rel 0 1 by simp)
    (show ComplexShape.fin3.Rel 1 2 by simp)]
  have hadj := adjoint_gradCurl_d₀ (𝕜 := ℝ) hΩ
  constructor
  · rintro ⟨K, hK, hsub⟩
    refine ⟨K, hK, fun x hx hx' h1 h2 h3 => ?_⟩
    obtain ⟨hy, ey⟩ := LinearPMap.exists_mem_apply_eq_of_eq hadj ⟨x, hx'⟩
    exact hsub x hx hy h1 h2 (by rw [ey]; exact h3)
  · rintro ⟨K, hK, hsub⟩
    refine ⟨K, hK, fun x hx hx' h1 h2 h3 => ?_⟩
    obtain ⟨hy, ey⟩ := LinearPMap.exists_mem_apply_eq_of_eq hadj.symm ⟨x, hx'⟩
    exact hsub x hx hy h1 h2 (by change ‖(gradCurl ℝ hΩ).d₀† ⟨x, hy⟩‖ ≤ 1; rw [ey]; exact h3)

theorem HasWeberCompactness.hasCompactPair (h : HasWeberCompactness Ω) :
    HasCompactPair ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).minimal Ω)
      ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) := by
  obtain ⟨K, hK, hsub⟩ := h
  refine ⟨K, hK, fun x hx hx' h1 h2 h3 => ?_⟩
  obtain ⟨hy, ey⟩ := LinearPMap.exists_mem_apply_eq_of_eq
    ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).adjoint_minimal (Ω := Ω)) ⟨x, hx'⟩
  exact hsub x hx hy h1 h2 (by rw [ey]; exact h3)

/-- Every open cube has Weber compactness. -/
theorem hasWeberCompactness_cube (b : R3) {s : ℝ} (hs : 0 < s) :
    HasWeberCompactness (Cube.Geometry.openCube b s) :=
  (hasWeberCompactness_iff (Cube.Geometry.isOpen_openCube b s)).2
    (complexCube_hasCompactPropertyAt b hs (i := 1) (by decide))

section EigenDense

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

theorem hasCompactCyclePerpAt_one_iff (hΩ : IsOpen Ω) :
    (gradCurl ℝ hΩ).toHilbertComplex.HasCompactCyclePerpAt 1 ↔
      HasCompactPerp ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) := by
  unfold HasCompactCyclePerpAt
  rw [ComplexShape.next_eq' _ (show ComplexShape.fin3.Rel 1 2 by simp)]
  rfl

theorem HasWeberCompactness.hasCompactPerp_curl (hΩ : IsOpen Ω) (hW : HasWeberCompactness Ω) :
    HasCompactPerp ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) :=
  (hasCompactCyclePerpAt_one_iff hΩ).1 ((hasWeberCompactness_iff hΩ).1 hW).hasCompactCyclePerpAt

theorem eigenDense_gradCurl_of_compactCurlPerp (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (h : HasCompactPerp ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω)) :
    (gradCurl ℝ hΩ).EigenDense :=
  eigenDense_wave_fin3 _ (gradCurl_hasCompactPropertyAt_zero hΩ hb).hasCompactCyclePerpAt
    ((hasCompactCyclePerpAt_one_iff hΩ).2 h)

/-- On a bounded open `Ω` with Weber compactness, the wave group of `H̊¹ → H̊(curl) → L²` has a
dense set of eigenvectors. -/
theorem eigenDense_gradCurl_of_weber (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hW : HasWeberCompactness Ω) : (gradCurl ℝ hΩ).EigenDense :=
  eigenDense_gradCurl_of_compactCurlPerp hΩ hb (hW.hasCompactPerp_curl hΩ)

end EigenDense

section Coefficient

/-- The multiplier `u ↦ ε u` on matrix fields, for an a.e. bounded measurable field `ε`. -/
def coeffMul (ε : R3 → EuclideanSpace ℝ Ix →L[ℝ] EuclideanSpace ℝ Ix)
    (hε : AEStronglyMeasurable ε (volume.restrict Ω)) (Λ : ℝ)
    (hΛ : ∀ᵐ x ∂volume.restrict Ω, ‖ε x‖ ≤ Λ) : L2F ℝ Ω Ix →L[ℝ] L2F ℝ Ω Ix :=
  (piL2Equiv (volume.restrict Ω) ℝ Ix).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    mulCLM (volume.restrict Ω) ε hε Λ hΛ ∘L
      (piL2Equiv (volume.restrict Ω) ℝ Ix).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem coeffMul_coercive {ε : R3 → EuclideanSpace ℝ Ix →L[ℝ] EuclideanSpace ℝ Ix}
    {hε : AEStronglyMeasurable ε (volume.restrict Ω)} {Λ : ℝ}
    {hΛ : ∀ᵐ x ∂volume.restrict Ω, ‖ε x‖ ≤ Λ} {lam : ℝ}
    (hlam : ∀ᵐ x ∂volume.restrict Ω, ∀ M, lam * ‖M‖ ^ 2 ≤ ⟪ε x M, M⟫_ℝ) (u : L2F ℝ Ω Ix) :
    lam * ‖u‖ ^ 2 ≤ ⟪coeffMul ε hε Λ hΛ u, u⟫_ℝ := by
  set P := piL2Equiv (volume.restrict Ω) ℝ Ix
  set f := P.symm u
  have hu : u = P f := (P.apply_symm_apply u).symm
  have e1 : ⟪coeffMul ε hε Λ hΛ u, u⟫_ℝ = ⟪mulCLM (volume.restrict Ω) ε hε Λ hΛ f, f⟫_ℝ := by
    have : coeffMul ε hε Λ hΛ u = P (mulCLM (volume.restrict Ω) ε hε Λ hΛ f) := rfl
    rw [this, hu, P.inner_map_map]
  have e2 : ‖u‖ = ‖f‖ := by rw [hu, P.norm_map]
  rw [e1, e2, ← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def, ← integral_const_mul]
  refine integral_mono_ae ((L2.integrable_inner (𝕜 := ℝ) f f).const_mul lam)
    (L2.integrable_inner _ _) ?_
  filter_upwards [coeFn_mulCLM ε hε Λ hΛ f, hlam] with x h1 h2
  rw [h1, real_inner_self_eq_norm_sq]
  exact h2 _

/-- Weber's lemma with a coefficient: on a bounded open `Ω` with Weber compactness,
`H̊(curl) ∩ ε⁻¹ H(div)` embeds compactly in `L²` for bounded coercive `ε`. [Hiptmair2002], §4 -/
theorem HasWeberCompactness.weber_of_coeff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hW : HasWeberCompactness Ω) (ε : R3 → EuclideanSpace ℝ Ix →L[ℝ] EuclideanSpace ℝ Ix)
    (hε : AEStronglyMeasurable ε (volume.restrict Ω)) {lam Λ : ℝ} (hlam0 : 0 < lam)
    (hΛ : ∀ᵐ x ∂volume.restrict Ω, ‖ε x‖ ≤ Λ)
    (hlam : ∀ᵐ x ∂volume.restrict Ω, ∀ M, lam * ‖M‖ ^ 2 ≤ ⟪ε x M, M⟫_ℝ) :
    ∃ K : Set (L2F ℝ Ω Ix), IsCompact K ∧ ∀ (u : L2F ℝ Ω Ix)
      (hu : u ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain)
      (hu' : coeffMul ε hε Λ hΛ u ∈
        ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).formalAdj.maximal Ω).domain),
      ‖u‖ ≤ 1 → ‖(curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω ⟨u, hu⟩‖ ≤ 1 →
        ‖(gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).formalAdj.maximal Ω
          ⟨coeffMul ε hε Λ hΛ u, hu'⟩‖ ≤ 1 → u ∈ K := by
  set T := (gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).minimal Ω
  have hadj : T† = (gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).formalAdj.maximal Ω :=
    (gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).adjoint_minimal
  obtain ⟨K, hK, hsub⟩ := HasCompactPair.exists_isCompact_coeff (T := T)
    (S := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω)
    ((gradOp 3 3).dense_minimal_domain hΩ) ((gradOp 3 3).isClosed_minimal hΩ)
    (ConstCoeffOp.minimal_mapsTo hΩ isComplexPair_grad_curl)
    (ConstCoeffOp.minimal_comp hΩ isComplexPair_grad_curl)
    (hasCompactBall_minimal_grad hΩ hb).hasCompactPerp
    hW.hasCompactPair (coeffMul ε hε Λ hΛ) hlam0 (coeffMul_coercive hlam)
  refine ⟨K, hK, fun u hu hu' h1 h2 h3 => ?_⟩
  obtain ⟨hy, ey⟩ := LinearPMap.exists_mem_apply_eq_of_eq hadj.symm ⟨_, hu'⟩
  exact hsub u hu hy h1 h2 (by rw [ey]; exact h3)

theorem weber_of_coeff (b : R3) {s : ℝ} (hs : 0 < s)
    (ε : R3 → EuclideanSpace ℝ Ix →L[ℝ] EuclideanSpace ℝ Ix)
    (hε : AEStronglyMeasurable ε (volume.restrict (Cube.Geometry.openCube b s))) {lam Λ : ℝ}
    (hlam0 : 0 < lam) (hΛ : ∀ᵐ x ∂volume.restrict (Cube.Geometry.openCube b s), ‖ε x‖ ≤ Λ)
    (hlam : ∀ᵐ x ∂volume.restrict (Cube.Geometry.openCube b s), ∀ M,
      lam * ‖M‖ ^ 2 ≤ ⟪ε x M, M⟫_ℝ) :
    ∃ K : Set (L2F ℝ (Cube.Geometry.openCube b s) Ix), IsCompact K ∧
      ∀ (u : L2F ℝ (Cube.Geometry.openCube b s) Ix)
      (hu : u ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal (Cube.Geometry.openCube b s)).domain)
      (hu' : coeffMul ε hε Λ hΛ u ∈ ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).formalAdj.maximal
        (Cube.Geometry.openCube b s)).domain),
      ‖u‖ ≤ 1 → ‖(curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal (Cube.Geometry.openCube b s) ⟨u, hu⟩‖ ≤ 1 →
        ‖(gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).formalAdj.maximal (Cube.Geometry.openCube b s)
          ⟨coeffMul ε hε Λ hΛ u, hu'⟩‖ ≤ 1 → u ∈ K :=
  (hasWeberCompactness_cube b hs).weber_of_coeff (Cube.Geometry.isOpen_openCube b s)
    (Cube.Geometry.isBounded_openCube b s) ε hε hlam0 hΛ hlam

end Coefficient

end Feec.Models.BoundedDomain
