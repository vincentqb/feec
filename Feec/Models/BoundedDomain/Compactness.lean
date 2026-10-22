module

public import Feec.Models.Cube.EigenDense
public import Feec.Models.Cube.DeRhamIdentFEM
public import Feec.Fourier.SpectralGalerkin
public import Feec.Domain.Rellich
public import Feec.Operator.Multiplication

/-!
# Compactness on bounded domains: Rellich, Weber, and a complete set of eigenvectors

The compact-resolvent criterion cannot give a complete set of eigenvectors for the thesis'
complex `H̊¹(Ω; ℝ³) → H̊(curl, Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)` (`gradCurl`): the kernel of its wave
operator contains `N(d₁†)`, which is infinite-dimensional. This file supplies the compactness
that `Feec.HilbertComplex.eigenDense_wave_fin3` needs instead, in degrees `0` and `1` only.

* **The torus and the cubes.** The grad–curl symbols are coercive,
  `‖grad_ξ v‖² = |ξ|² ‖v‖²`, `‖curl_ξ M‖² + ‖div_ξ M‖² = |ξ|² ‖M‖²`, so the torus complex has
  the compactness property in degrees `0` and `1` (`torus_hasCompactPropertyAt_zero`,
  `torus_hasCompactPropertyAt_one`); it passes to the real complex
  (`HilbertComplex.HasCompactPropertyAt.restrictScalars`), to the cube `Q = (0, ½)³` by
  compression along the parity extension (`cubeComplex_hasCompactPropertyAt`) and to every open
  cube by affine transport (`complexCube_hasCompactPropertyAt`).
* **Rellich on bounded open sets** (`hasCompactBall_minimal_grad`): for every bounded open
  `Ω ⊆ ℝ³`, the unit box
  `‖u‖, ‖grad u‖ ≤ 1` of `D(grad_min) = H̊¹(Ω; ℝ³)` is precompact in `L²(Ω; ℝ³)`, by extension by
  zero into a cube (`Feec.Domain.ConstCoeffOp.hasCompactBall_minimal_of_subset`). In `ℝⁿ`, for
  `H̊¹ = H̊Λ⁰` (`hasCompactBall_minimal_extDeriv_zero`): from `H̊Λ(Q)`
  (`Feec.Models.Cube.FEM.hasCompactProperty_min`) by an affine map and extension by zero; for
  `H̊¹(Ω; ℝᵐ)`, `Ω ⊆ ℝⁿ`, component by component (`hasCompactBall_minimal_gradOp`). Hence
  **(3a)** `gradCurl_hasCompactPropertyAt_zero`.
* **Weber compactness** (`HasWeberCompactness Ω`: the unit box of `D(curl_min) ∩ D(div_max)` on
  matrix fields is precompact) is the compactness property in degree `1`
  (`hasWeberCompactness_iff`); it holds on every open cube (`hasWeberCompactness_cube`).
* **(3b) Weber's lemma with a coefficient** (`HasWeberCompactness.weber_of_coeff`, unconditional
  on cubes `weber_of_coeff`): for a
  bounded measurable coercive `ε`, `{u ∈ D(curl_min) : div(ε u) ∈ L², ‖u‖, ‖curl u‖,
  ‖div(ε u)‖ ≤ 1}` is precompact (`Feec.Operator.HasCompactPair.exists_isCompact_coeff`, the
  Helmholtz argument with Rellich and Weber).
* **(3c) The criterion** `eigenDense_gradCurl_of_compactCurlPerp`: on a bounded open `Ω` such
  that `curl_min` is compact off its kernel (`Operator.HasCompactPerp`), the wave group of
  `gradCurl ℝ hΩ` has a dense set of eigenvectors; `eigenDense_gradCurl_of_weber` is the
  corollary under `HasWeberCompactness Ω`.

**What is proved and what is assumed.** Degree `0` (Rellich) is proved on every bounded open set,
in `ℝ³` for `ℝ³`-valued fields and in `ℝⁿ` for `ℝᵐ`-valued fields (`hasCompactBall_minimal_gradOp`).
Degree `1` is not: `HasWeberCompactness Ω` is exactly the compactness property in degree `1`
(`hasWeberCompactness_iff`), and the weaker hypothesis of
`eigenDense_gradCurl_of_compactCurlPerp` is its half off the kernel of `curl_min`. Both are proved
on open cubes only. For Lipschitz domains Weber compactness is a classical theorem (Weber,
Picard) and follows from regular decompositions ([Hiptmair2002], §4), which are not formalized
here; for an arbitrary bounded open set no proof is available, so it stays a hypothesis.

## References

* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.7 (Rellich–Kondrachov)
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], §4
  (compactness of `H̊(curl) ∩ ε⁻¹ H(div)`, regular decompositions)
* [V. Girault, P.-A. Raviart, *Finite Element Methods for Navier–Stokes Equations*][GiraultRaviart1986],
  Ch. I, §3 (`H(curl) ∩ H(div)`)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1.3 (compactness property), §4.3 (the de Rham complex)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (the complex `H̊¹ → H̊(curl) → L²`, Prop 4.17)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ENNReal Topology
open Set MeasureTheory Filter LinearPMap

@[expose] public noncomputable section

/-! ### Compactness and restriction of scalars -/

namespace Feec.HilbertComplex

variable {ι : Type*} {c : ComplexShape ι} {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace ℂ (W i)] [∀ i, CompleteSpace (W i)] [∀ i, InnerProductSpace ℝ (W i)]
  [∀ i, IsScalarTower ℝ ℂ (W i)] {H : HilbertComplex ℂ c W}

/-- **The compactness property does not depend on the scalars**: the real complex has the same
domains, differentials and adjoints (`LinearPMap.adjoint_restrictScalars`), and the same norms. -/
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

/-! ### The torus and the cube -/

namespace Feec.Models.BoundedDomain

open Feec.Fourier Feec.Fourier.GradCurl Feec.HilbertComplex Feec.Domain Feec.Operator

/-- **Rellich on the torus, degree `0`**: `‖grad_ξ v‖² = |ξ|² ‖v‖²`, coercive off a finite set of
frequencies (`hasCompactPropertyAt_of_coercive`). -/
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

/-- **Weber on the torus, degree `1`**: `‖curl_ξ M‖² + ‖div_ξ M‖² = |ξ|² ‖M‖²`. In degree `2` the
symbol `curl_ξ` kills the gradients and there is no compactness. -/
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

/-- The real torus grad–curl complex has the compactness property in degrees `0` and `1`. -/
theorem realTorus_hasCompactPropertyAt {i : Fin 3} (hi : i ≠ 2) :
    RealTorus.gradCurl.HasCompactPropertyAt i := by
  have h : Models.Torus.GradCurl.complex.HasCompactPropertyAt i := by
    fin_cases i
    · exact torus_hasCompactPropertyAt_zero
    · exact torus_hasCompactPropertyAt_one
    · exact absurd rfl hi
  exact h.restrictScalars RealTorus.real_inner_eq_re

/-- **The thesis' complex on `Q = (0, ½)³` has the compactness property in degrees `0` and `1`**
(Rellich for `H̊¹(Q; ℝ³)` and Weber for `H̊(curl, Q) ∩ H(div, Q)`): it is the compression of the
torus complex along the parity extension (`RowWise.cubeComplex_eq_compress`). -/
theorem cubeComplex_hasCompactPropertyAt {i : Fin 3} (hi : i ≠ 2) :
    RowWise.cubeComplex.HasCompactPropertyAt i := by
  rw [RowWise.cubeComplex_eq_compress]
  exact hasCompactPropertyAt_compress _ _ _ (realTorus_hasCompactPropertyAt hi)

/-- **The thesis' complex on every open cube `∏ (bᵢ, bᵢ + s)` has the compactness property in
degrees `0` and `1`**: it is the transport of the one on `Q` (`Ident.complexCube_eq`). -/
theorem complexCube_hasCompactPropertyAt (b : R3) {s : ℝ} (hs : 0 < s) {i : Fin 3}
    (hi : i ≠ 2) : (Ident.complexCube b s).HasCompactPropertyAt i := by
  rw [Ident.complexCube_eq hs]
  exact hasCompactPropertyAt_transport (inv_pos.2 (Domain.jac_pos (Ident.scale_ne_zero hs)))
    (Ident.inner_pullC hs) _ (cubeComplex_hasCompactPropertyAt hi)

end Cube

/-! ### Rellich on bounded open sets of `ℝⁿ`: `H̊¹ = H̊Λ⁰` -/

section DeRham

/-- An operator out of the zero space has `D(T†) = ⊤` and `T† = 0`. -/
theorem _root_.LinearPMap.exists_adjoint_eq_zero_of_subsingleton {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [Subsingleton E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (T : E →ₗ.[𝕜] F) (y : F) :
    ∃ hy : y ∈ T†.domain, T† ⟨y, hy⟩ = 0 := by
  refine ⟨LinearPMap.mem_adjoint_domain_of_exists y ⟨0, fun x => ?_⟩, Subsingleton.elim _ _⟩
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx, LinearPMap.map_zero, inner_zero_right, inner_zero_left]

instance (n : ℕ) : IsEmpty (formIdx n (-1)) :=
  ⟨fun s => by have h := s.2; have : (0 : ℤ) ≤ (s.1.card : ℤ) := Int.natCast_nonneg _; omega⟩

/-- The exterior derivative is homogeneous of order one. -/
theorem extDerivOp_isHomogeneous (n : ℕ) (k : ℤ) : (extDerivOp ℝ n k).IsHomogeneous 1 := by
  intro t r p hp
  simp only [extDerivOp, List.mem_map] at hp
  obtain ⟨j, -, rfl⟩ := hp
  rfl

/-- **Rellich on the cube `(0, ½)ⁿ`** for `H̊¹ = H̊Λ⁰`: the compactness property of `H̊Λ(Q)` in
degree `0` (`FEM.hasCompactProperty_min`), where `d⁻¹ = 0` comes from the zero space. -/
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

/-- A bounded subset of `ℝⁿ` lies in an affine preimage of the cube `(0, ½)ⁿ`. -/
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

/-- **Rellich's theorem for `H̊¹(Ω) = H̊Λ⁰(Ω)` on every bounded open `Ω ⊆ ℝⁿ`**: the unit box
`‖u‖, ‖d u‖ ≤ 1` of `D(d_min)` (`d = grad` on `0`-forms) lies in a compact subset of `L²(Ω)`.
From the cube by an affine map and extension by zero
(`ConstCoeffOp.hasCompactBall_minimal_of_subset_preimage`); no regularity of `∂Ω`.
[Evans2010], §5.7, Thm 1. -/
theorem hasCompactBall_minimal_extDeriv_zero {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) : HasCompactBall ((extDerivOp ℝ n 0).minimal Ω) := by
  obtain ⟨a, b, ha, hsub⟩ := exists_aff_preimage_cubeDomain hb
  exact ConstCoeffOp.hasCompactBall_minimal_of_subset_preimage (extDerivOp_isHomogeneous n 0) ha
    b hΩ (Cube.FEM.isOpen_cubeDomain n) hsub (hasCompactBall_minimal_extDeriv_cube n)

/-- The element of a `1`-form index `s = {j}`. -/
def formIdxOne {n : ℕ} (s : formIdx n 1) : Fin n :=
  (Finset.card_eq_one.1 (by exact_mod_cast s.2 : s.1.card = 1)).choose

theorem formIdxOne_spec {n : ℕ} (s : formIdx n 1) : s.1 = {formIdxOne s} :=
  (Finset.card_eq_one.1 (by exact_mod_cast s.2 : s.1.card = 1)).choose_spec

theorem eq_formIdxOne {n : ℕ} (s : formIdx n 1) : s = ⟨{formIdxOne s}, by simp⟩ :=
  Subtype.ext (formIdxOne_spec s)

/-- The gradient of the `i`-th component of a field is `d` of the `0`-form `φᵢ`. -/
theorem gradOp_apply_formIdxOne {n m : ℕ} (φ : Fin m → (Fin n → ℝ) → ℝ) (i : Fin m) :
    (fun s : formIdx n 1 =>
      (gradOp n m : ConstCoeffOp (Fin n → ℝ) ℝ (Fin m) (Fin m × Fin n)).apply φ (i, formIdxOne s)) =
      (extDerivOp ℝ n 0).apply (fun _ => φ i) := by
  funext s x
  have e := extDerivOp_zero_apply (𝕜 := ℝ) (fun _ => φ i) (formIdxOne s) x
  rw [← eq_formIdxOne] at e
  rw [e, gradOp_apply]

/-- **Rellich's theorem for `H̊¹(Ω; ℝᵐ)` on every bounded open `Ω ⊆ ℝⁿ`**: the unit box
`‖u‖, ‖grad u‖ ≤ 1` of `D(grad_min)` (`m` components, `gradOp n m`) lies in a compact subset of
`L²(Ω; ℝᵐ)`. Component by component from the scalar case `hasCompactBall_minimal_extDeriv_zero`
(each component of `u ∈ H̊¹(Ω; ℝᵐ)` lies in `H̊Λ⁰(Ω)`,
`ConstCoeffOp.mem_minimal_of_mapsTo_testGraph`;
`Operator.HasCompactBall.of_components`). [Evans2010], §5.7, Thm 1. -/
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

/-! ### Rellich on bounded open sets of `ℝ³` -/

/-- A bounded set of `ℝ^d` lies in an open cube. -/
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

/-- The minimal row-wise gradient of the cube complex: the compactness property in degree `0` of
`H̊¹ → H̊(curl) → L²` is the compact embedding of `D(grad_min) = H̊¹(Ω; ℝ³)`. -/
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

/-- **Rellich on open cubes** for `H̊¹(∏ (bᵢ, bᵢ + s); ℝ³)`. -/
theorem hasCompactBall_minimal_grad_openCube (b : R3) {s : ℝ} (hs : 0 < s) :
    HasCompactBall ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).minimal (Cube.Geometry.openCube b s)) :=
  (hasCompactBall_minimal_grad_iff (Cube.Geometry.isOpen_openCube b s)).1
    (complexCube_hasCompactPropertyAt b hs (i := 0) (by decide))

/-- **Rellich's theorem for `H̊¹(Ω; ℝ³)` on every bounded open `Ω ⊆ ℝ³`**: the unit box
`‖u‖, ‖grad u‖ ≤ 1` of `D(grad_min)` lies in a compact subset of `L²(Ω; ℝ³)`. From an open cube
containing `Ω` by extension by zero (`ConstCoeffOp.hasCompactBall_minimal_of_subset`); no
regularity of `∂Ω`. [Evans2010], §5.7, Thm 1. -/
theorem hasCompactBall_minimal_grad (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    HasCompactBall ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).minimal Ω) := by
  obtain ⟨b, s, hs, hsub⟩ := exists_openCube_superset hb
  exact (gradOp 3 3).hasCompactBall_minimal_of_subset hΩ (Cube.Geometry.isOpen_openCube b s) hsub
    (hasCompactBall_minimal_grad_openCube b hs)

/-- **(3a) The thesis' complex has the compactness property in degree `0` on every bounded open
`Ω ⊆ ℝ³`.** -/
theorem gradCurl_hasCompactPropertyAt_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (gradCurl ℝ hΩ).toHilbertComplex.HasCompactPropertyAt 0 :=
  (hasCompactBall_minimal_grad_iff hΩ).2 (hasCompactBall_minimal_grad hΩ hb)

/-! ### Weber compactness -/

/-- **Weber compactness of `Ω`**: the unit box of `D(curl_min) ∩ D(div_max)` on matrix fields
(rows in `H̊(curl, Ω) ∩ H(div, Ω)`), `‖u‖, ‖curl u‖, ‖div u‖ ≤ 1`, lies in a compact subset of
`L²(Ω; ℝ³ˣ³)`. The divergence is `(gradᵗ)_max = -div_max` (`gradOp_formalAdj_apply`), the
adjoint of `grad_min` (`adjoint_gradCurl_d₀`). A classical theorem on Lipschitz domains (Weber,
Picard; [Hiptmair2002], §4), not formalized; here proved on open cubes (`hasWeberCompactness_cube`)
and a hypothesis elsewhere. -/
def HasWeberCompactness (Ω : Set R3) : Prop :=
  ∃ K : Set (L2F ℝ Ω Ix), IsCompact K ∧ ∀ (u : L2F ℝ Ω Ix)
    (hu : u ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain)
    (hu' : u ∈ ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).formalAdj.maximal Ω).domain),
    ‖u‖ ≤ 1 → ‖(curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω ⟨u, hu⟩‖ ≤ 1 →
      ‖(gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).formalAdj.maximal Ω ⟨u, hu'⟩‖ ≤ 1 → u ∈ K

/-- Weber compactness is the compactness property in degree `1` of `H̊¹ → H̊(curl) → L²`. -/
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

/-- Weber compactness is the compactness of the middle space of `(grad_min, curl_min)`. -/
theorem HasWeberCompactness.hasCompactPair (h : HasWeberCompactness Ω) :
    HasCompactPair ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).minimal Ω)
      ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) := by
  obtain ⟨K, hK, hsub⟩ := h
  refine ⟨K, hK, fun x hx hx' h1 h2 h3 => ?_⟩
  obtain ⟨hy, ey⟩ := LinearPMap.exists_mem_apply_eq_of_eq
    ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).adjoint_minimal (Ω := Ω)) ⟨x, hx'⟩
  exact hsub x hx hy h1 h2 (by rw [ey]; exact h3)

/-- **Weber compactness on every open cube**, unconditionally (non-vacuity of
`HasWeberCompactness`). -/
theorem hasWeberCompactness_cube (b : R3) {s : ℝ} (hs : 0 < s) :
    HasWeberCompactness (Cube.Geometry.openCube b s) :=
  (hasWeberCompactness_iff (Cube.Geometry.isOpen_openCube b s)).2
    (complexCube_hasCompactPropertyAt b hs (i := 1) (by decide))

section EigenDense

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- **Half compactness of `curl_min` in degree `1`**: `HasCompactCyclePerpAt 1` of
`H̊¹ → H̊(curl) → L²` is the compactness of the box of `D(curl_min) ∩ N(curl_min)ᗮ`. -/
theorem hasCompactCyclePerpAt_one_iff (hΩ : IsOpen Ω) :
    (gradCurl ℝ hΩ).toHilbertComplex.HasCompactCyclePerpAt 1 ↔
      HasCompactPerp ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) := by
  unfold HasCompactCyclePerpAt
  rw [ComplexShape.next_eq' _ (show ComplexShape.fin3.Rel 1 2 by simp)]
  rfl

/-- Weber compactness gives the compactness of `curl_min` off its kernel. -/
theorem HasWeberCompactness.hasCompactPerp_curl (hΩ : IsOpen Ω) (hW : HasWeberCompactness Ω) :
    HasCompactPerp ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) :=
  (hasCompactCyclePerpAt_one_iff hΩ).1 ((hasWeberCompactness_iff hΩ).1 hW).hasCompactCyclePerpAt

/-- **(3c) A complete set of eigenvectors from the compactness of `curl_min` off its kernel.**
On a bounded open `Ω ⊆ ℝ³` such that the box `‖u‖, ‖curl u‖ ≤ 1` of
`D(curl_min) ∩ N(curl_min)ᗮ` is precompact, the wave group of `H̊¹ → H̊(curl) → L²` has a dense
set of eigenvectors, although `N(L) ⊇ N(d₁†)` is infinite-dimensional (so that the
compact-resolvent criterion does not apply): half compactness holds in degree `0` (Rellich,
`gradCurl_hasCompactPropertyAt_zero`, unconditional), degree `1` is the hypothesis, and nothing is
needed in degree `2` (`HilbertComplex.eigenDense_wave_fin3`). The hypothesis is implied by Weber
compactness (`HasWeberCompactness.hasCompactPerp_curl`) and does not ask the harmonic fields
`ℌ¹ = N(curl_min) ∩ N(div_max)` to be finite-dimensional: kernel vectors are eigenvectors with
eigenvalue `0`. -/
theorem eigenDense_gradCurl_of_compactCurlPerp (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (h : HasCompactPerp ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω)) :
    (gradCurl ℝ hΩ).EigenDense :=
  eigenDense_wave_fin3 _ (gradCurl_hasCompactPropertyAt_zero hΩ hb).hasCompactCyclePerpAt
    ((hasCompactCyclePerpAt_one_iff hΩ).2 h)

/-- **(3c) A complete set of eigenvectors from Weber compactness**: the corollary of
`eigenDense_gradCurl_of_compactCurlPerp` through `HasWeberCompactness.hasCompactPerp_curl`. -/
theorem eigenDense_gradCurl_of_weber (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hW : HasWeberCompactness Ω) : (gradCurl ℝ hΩ).EigenDense :=
  eigenDense_gradCurl_of_compactCurlPerp hΩ hb (hW.hasCompactPerp_curl hΩ)

end EigenDense

/-! ### Weber's lemma with a coefficient -/

section Coefficient

/-- **The coefficient multiplier** `u ↦ ε u` on matrix fields, `(ε u)(x) = ε(x) (u(x))`, for an a.e.
strongly measurable, a.e. bounded field `ε` of operators on `ℝ³ˣ³` (e.g. a permittivity acting
on each row, `(ε u)_{ab} = Σ_c ε_{bc} u_{ac}`). -/
def coeffMul (ε : R3 → EuclideanSpace ℝ Ix →L[ℝ] EuclideanSpace ℝ Ix)
    (hε : AEStronglyMeasurable ε (volume.restrict Ω)) (Λ : ℝ)
    (hΛ : ∀ᵐ x ∂volume.restrict Ω, ‖ε x‖ ≤ Λ) : L2F ℝ Ω Ix →L[ℝ] L2F ℝ Ω Ix :=
  (piL2Equiv (volume.restrict Ω) ℝ Ix).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    mulCLM (volume.restrict Ω) ε hε Λ hΛ ∘L
      (piL2Equiv (volume.restrict Ω) ℝ Ix).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- **Coercivity of the multiplier**: `λ ‖u‖² ≤ ⟪ε u, u⟫` from the pointwise bound
`λ |M|² ≤ ⟪ε(x) M, M⟫`. -/
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

/-- **Weber's lemma with a coefficient (3b).** Let `Ω ⊆ ℝ³` be bounded and open with Weber
compactness, and let `ε` be an a.e. strongly measurable field of operators on `ℝ³ˣ³` with
`‖ε(x)‖ ≤ Λ` and `λ |M|² ≤ ⟪ε(x) M, M⟫` a.e. (`λ > 0`; symmetry is not needed). Then
`{u ∈ D(curl_min) : div(ε u) ∈ L², ‖u‖, ‖curl u‖, ‖div (ε u)‖ ≤ 1}` lies in a compact subset of
`L²(Ω; ℝ³ˣ³)`: `H̊(curl) ∩ ε⁻¹ H(div)` embeds compactly. From the abstract lemma
`Operator.HasCompactPair.exists_isCompact_coeff` with Rellich (`hasCompactBall_minimal_grad`)
and Weber (`HasWeberCompactness.hasCompactPair`). [Hiptmair2002], §4. -/
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

/-- **Weber's lemma with a coefficient on every open cube**, unconditionally. -/
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
