module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn

/-!
# Coordinate partial derivatives

For `f : (ι → 𝕜) → F` with `ι` finite, `partialDeriv i f x = f'(x) eᵢ` is the derivative of `f`
at `x` along the `i`-th coordinate vector `eᵢ = Pi.single i 1` (junk `0` where `f` is not
differentiable). It is the common definition behind the partial derivatives `∂ₖ` used for fields
on `ℝⁿ`, space-time `ℝ¹⁺ⁿ`, and their components.

* Algebra: `partialDeriv_add`, `_sub`, `_neg`, `_const_smul`, `_mul`, `_sum`,
  `_const`, `partialDeriv_apply_coord` (`∂ₖ xₐ = δₖₐ`), composition with continuous linear maps
  (`ContinuousLinearMap.partialDeriv_comp`);
* Fréchet and one-variable derivatives: `HasFDerivAt.partialDeriv_eq`,
  `DifferentiableAt.hasDerivAt_partialDeriv` (`∂ᵢ f x` is the derivative of
  `s ↦ f (x + s eᵢ)` at `0`);
* Locality: `Filter.EventuallyEq.partialDeriv_eq`;
* Regularity and support: `ContDiff.partialDeriv`, `ContDiff.continuous_partialDeriv`,
  `ContDiff.differentiable_partialDeriv`, `partialDeriv_partialDeriv` (`∂ᵢ∂ⱼ f = f'' eᵢ eⱼ`),
  `HasCompactSupport.partialDeriv`, `tsupport_partialDeriv_subset`,
  `eq_zero_of_partialDeriv_eq_zero` (compact support and `∇f = 0` give `f = 0`);
* **Schwarz**: `partialDeriv_comm` (partial derivatives of a `C²` function commute);
* **Integration by parts**: `integral_partialDeriv_mul_eq_neg` (`∫ ∂ᵢ f · g = -∫ f · ∂ᵢ g` for
  `C¹` functions with `f` compactly supported).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set Filter Topology MeasureTheory

@[expose] public noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The coordinate partial derivative `∂ᵢ f x = f'(x) eᵢ` of `f : (ι → 𝕜) → F`. -/
def partialDeriv (i : ι) (f : (ι → 𝕜) → F) (x : ι → 𝕜) : F :=
  fderiv 𝕜 f x (Pi.single i 1)

omit [Fintype ι] in
theorem partialDeriv_def (i : ι) (f : (ι → 𝕜) → F) (x : ι → 𝕜) :
    partialDeriv i f x = fderiv 𝕜 f x (Pi.single i 1) := rfl

omit [Fintype ι] in
theorem partialDeriv_fun (i : ι) (f : (ι → 𝕜) → F) :
    partialDeriv i f = fun x => fderiv 𝕜 f x (Pi.single i 1) := rfl

omit [Fintype ι] in
/-- `∂ᵢ f x = f'(eᵢ)` from a Fréchet derivative `f'` at `x`. -/
theorem HasFDerivAt.partialDeriv_eq {f : (ι → 𝕜) → F} {f' : (ι → 𝕜) →L[𝕜] F} {x : ι → 𝕜}
    (h : HasFDerivAt f f' x) (i : ι) : partialDeriv i f x = f' (Pi.single i 1) := by
  rw [partialDeriv, h.fderiv]

/-- `∂ᵢ f x` is the derivative of `s ↦ f (x + s eᵢ)` at `s = 0`. -/
theorem DifferentiableAt.hasDerivAt_partialDeriv {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : DifferentiableAt 𝕜 f x) (i : ι) :
    HasDerivAt (fun s : 𝕜 => f (x + s • Pi.single i 1)) (partialDeriv i f x) 0 := by
  have hl : HasDerivAt (fun s : 𝕜 => x + s • (Pi.single i 1 : ι → 𝕜)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : 𝕜)).smul_const (Pi.single i (1 : 𝕜) : ι → 𝕜)).const_add x
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)

omit [Fintype ι] in
/-- Partial derivatives only depend on the germ of `f`. -/
theorem Filter.EventuallyEq.partialDeriv_eq {f g : (ι → 𝕜) → F} {x : ι → 𝕜}
    (h : f =ᶠ[𝓝 x] g) (i : ι) : partialDeriv i f x = partialDeriv i g x := by
  rw [partialDeriv, partialDeriv, h.fderiv_eq]

/-! ### Algebra -/

omit [Fintype ι] in
@[simp] theorem partialDeriv_const (i : ι) (c : F) (x : ι → 𝕜) :
    partialDeriv i (fun _ : ι → 𝕜 => c) x = 0 := by
  simp [partialDeriv]

theorem partialDeriv_add {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : DifferentiableAt 𝕜 f x)
    (hg : DifferentiableAt 𝕜 g x) (i : ι) :
    partialDeriv i (fun y => f y + g y) x = partialDeriv i f x + partialDeriv i g x := by
  rw [partialDeriv, fderiv_fun_add hf hg]; rfl

theorem partialDeriv_sub {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : DifferentiableAt 𝕜 f x)
    (hg : DifferentiableAt 𝕜 g x) (i : ι) :
    partialDeriv i (fun y => f y - g y) x = partialDeriv i f x - partialDeriv i g x := by
  rw [partialDeriv, fderiv_fun_sub hf hg]; rfl

@[simp] theorem partialDeriv_neg (f : (ι → 𝕜) → F) (i : ι) (x : ι → 𝕜) :
    partialDeriv i (fun y => -f y) x = -partialDeriv i f x := by
  simp [partialDeriv]

theorem partialDeriv_const_smul {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : DifferentiableAt 𝕜 f x)
    (c : 𝕜) (i : ι) : partialDeriv i (fun y => c • f y) x = c • partialDeriv i f x := by
  rw [partialDeriv, fderiv_fun_const_smul hf]; rfl

theorem partialDeriv_sum {α : Type*} (s : Finset α) {f : α → (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : ∀ a ∈ s, DifferentiableAt 𝕜 (f a) x) (i : ι) :
    partialDeriv i (fun y => ∑ a ∈ s, f a y) x = ∑ a ∈ s, partialDeriv i (f a) x := by
  rw [partialDeriv, fderiv_fun_sum hf]; simp [partialDeriv]

/-- Product rule (scalar-valued, `𝕜`-normed algebra codomain). -/
theorem partialDeriv_mul {𝔸 : Type*} [NormedCommRing 𝔸] [NormedAlgebra 𝕜 𝔸]
    {f g : (ι → 𝕜) → 𝔸} {x : ι → 𝕜} (hf : DifferentiableAt 𝕜 f x)
    (hg : DifferentiableAt 𝕜 g x) (i : ι) :
    partialDeriv i (fun y => f y * g y) x =
      partialDeriv i f x * g x + f x * partialDeriv i g x := by
  rw [show (fun y => f y * g y) = f * g from rfl,
    (hf.hasFDerivAt.mul hg.hasFDerivAt).partialDeriv_eq, partialDeriv, partialDeriv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

omit [Fintype ι] in
/-- `∂ₖ xₐ = δₖₐ`. -/
theorem partialDeriv_apply_coord (a k : ι) (x : ι → 𝕜) :
    partialDeriv k (fun y : ι → 𝕜 => y a) x = if k = a then 1 else 0 := by
  rw [(hasFDerivAt_apply a x).partialDeriv_eq]
  simp [Pi.single_apply, eq_comm]

/-- Partial derivatives commute with continuous linear maps. -/
theorem ContinuousLinearMap.partialDeriv_comp (L : F →L[𝕜] G) {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : DifferentiableAt 𝕜 f x) (i : ι) :
    partialDeriv i (fun y => L (f y)) x = L (partialDeriv i f x) := by
  rw [show (fun y => L (f y)) = L ∘ f from rfl,
    (L.hasFDerivAt.comp x hf.hasFDerivAt).partialDeriv_eq]; rfl

/-! ### Regularity and support -/

/-- Partial derivatives of `C^{m+1}` functions are `C^m`. -/
theorem ContDiff.partialDeriv {f : (ι → 𝕜) → F} {m n : WithTop ℕ∞} (hf : ContDiff 𝕜 n f)
    (hmn : m + 1 ≤ n) (i : ι) : ContDiff 𝕜 m (_root_.partialDeriv i f) :=
  (hf.fderiv_right hmn).clm_apply contDiff_const

/-- Partial derivatives of `C¹` functions are continuous. -/
theorem ContDiff.continuous_partialDeriv {f : (ι → 𝕜) → F} (hf : ContDiff 𝕜 1 f) (i : ι) :
    Continuous (_root_.partialDeriv i f) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- Partial derivatives of `C²` functions are differentiable. -/
theorem ContDiff.differentiable_partialDeriv {f : (ι → 𝕜) → F} {n : WithTop ℕ∞}
    (hf : ContDiff 𝕜 n f) (hn : 2 ≤ n) (i : ι) : Differentiable 𝕜 (_root_.partialDeriv i f) :=
  (hf.partialDeriv (m := 1) (by simpa [one_add_one_eq_two] using hn) i).differentiable one_ne_zero

/-- Second partial derivatives are entries of the second derivative:
`∂ᵢ ∂ⱼ f x = f''(x) eᵢ eⱼ`. -/
theorem partialDeriv_partialDeriv {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : DifferentiableAt 𝕜 (fderiv 𝕜 f) x) (i j : ι) :
    partialDeriv i (partialDeriv j f) x =
      fderiv 𝕜 (fderiv 𝕜 f) x (Pi.single i 1) (Pi.single j 1) := by
  rw [partialDeriv_fun j f, partialDeriv, fderiv_clm_apply hf (differentiableAt_const _)]
  simp

omit [Fintype ι] in
theorem tsupport_partialDeriv_subset (f : (ι → 𝕜) → F) (i : ι) :
    tsupport (partialDeriv i f) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset 𝕜 _

omit [Fintype ι] in
theorem HasCompactSupport.partialDeriv {f : (ι → 𝕜) → F} (hf : HasCompactSupport f) (i : ι) :
    HasCompactSupport (_root_.partialDeriv i f) :=
  hf.fderiv_apply 𝕜 _

omit [Fintype ι] in
/-- `∂ᵢ f` vanishes outside the closed support of `f`. -/
theorem partialDeriv_eq_zero_of_notMem_tsupport {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hx : x ∉ tsupport f) (i : ι) : partialDeriv i f x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_partialDeriv_subset f i h)

/-- A differentiable, compactly supported function on `𝕜ⁿ` (`n ≥ 1`) with vanishing partial
derivatives is zero. -/
theorem eq_zero_of_partialDeriv_eq_zero {𝕜' : Type*} [RCLike 𝕜'] [Nonempty ι]
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜' F'] {f : (ι → 𝕜') → F'}
    (hf : Differentiable 𝕜' f) (hc : HasCompactSupport f) (h : ∀ i x, partialDeriv i f x = 0)
    (x : ι → 𝕜') : f x = 0 := by
  have hd : ∀ y, fderiv 𝕜' f y = 0 := fun y =>
    ContinuousLinearMap.coe_injective ((Pi.basisFun 𝕜' ι).ext fun i => by
      simpa [partialDeriv] using h i y)
  obtain ⟨y, hy⟩ : ∃ y, y ∉ tsupport f := by
    by_contra! hall
    exact hc.ne_univ (Set.eq_univ_of_forall hall)
  rw [is_const_of_fderiv_eq_zero hf hd x y]
  exact image_eq_zero_of_notMem_tsupport hy

/-! ### Schwarz -/

/-- **Schwarz**: partial derivatives of a `C²` function commute. -/
theorem partialDeriv_comm {f : (ι → ℝ) → F} [NormedSpace ℝ F] (hf : ContDiff ℝ 2 f) (a b : ι)
    (x : ι → ℝ) : partialDeriv a (partialDeriv b f) x = partialDeriv b (partialDeriv a f) x := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have e : ∀ v w : ι → ℝ,
      fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
    intro v w
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  change fderiv ℝ (fun y => fderiv ℝ f y (Pi.single b 1)) x (Pi.single a 1) =
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single a 1)) x (Pi.single b 1)
  rw [e, e]
  exact (ContDiffAt.isSymmSndFDerivAt (hf.contDiffAt (x := x)) (by simp)) _ _

/-! ### Integration by parts -/

/-- **Integration by parts**: `∫ ∂ᵢ f · g = -∫ f · ∂ᵢ g` for `C¹` functions `f, g : ℝⁿ → ℝ`
with `f` compactly supported (Lebesgue measure on `ι → ℝ`). -/
theorem integral_partialDeriv_mul_eq_neg {f g : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f) (hg : ContDiff ℝ 1 g) (i : ι) :
    ∫ x, partialDeriv i f x * g x = -∫ x, f x * partialDeriv i g x := by
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := f) (g := g)
    (v := Pi.single i 1)
    (((hf.continuous_partialDeriv i).mul hg.continuous).integrable_of_hasCompactSupport
      ((hfs.partialDeriv i).mul_right))
    ((hf.continuous.mul (hg.continuous_partialDeriv i)).integrable_of_hasCompactSupport
      hfs.mul_right)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfs.mul_right)
    (fun x _ => (hf.differentiable one_ne_zero) x) (fun x _ => (hg.differentiable one_ne_zero) x)
  simp only [partialDeriv]
  rw [this, neg_neg]
