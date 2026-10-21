module

public import Feec.Models.Cube.DeRham
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Smoothing on the cube by even Fourier multipliers (method of images)

On the torus `𝕋ⁿ` convolution with a kernel `ρ` is the Fourier multiplier `û(q) ↦ ρ̂(q) û(q)`.
For a real kernel even in every variable (`ρ(…, -x_j, …) = ρ(x)`), `ρ̂` is real and invariant under
every frequency reflection `q ↦ flip_j q`; for a probability density `|ρ̂| ≤ 1`. This file treats
the de Rham complex of the cube `Q = (0, ½)ⁿ` in the parity model (`Feec.Models.Cube.DeRham`:
the fixed complex of the reflections of the torus de Rham window) and any such **even
multiplier** `ρ̂` (`EvenMultiplier`):

* `smoothOp`: the multiplier on `L²Λⁱ(𝕋ⁿ) = ℓ²(ℤⁿ; Λⁱ)`, an `L²`-contraction
  (`norm_smoothOp_le`); it **commutes with `d`** (a Fourier multiplier commutes with every symbol,
  `smoothOp_mem_domain`, `d_smoothOp`) and with each **reflection** `R_j^*`
  (`smoothOp_symLp`), so it maps each parity class to itself (`smoothOp_mem_fixed`);
* `smoothFixed`: the induced smoother on the cube complexes (relative and absolute boundary
  conditions), a contraction commuting with their differentials (`norm_smoothFixed_le`,
  `smoothFixed_mem_domain`, `d_smoothFixed`);
* **strong convergence**: `smoothOp m u → u` along any family of even multipliers converging
  pointwise to `1` (`tendsto_smoothOp`), by dominated convergence;
* the **box low-pass multipliers** `boxMultiplier K` (`ρ̂ = 1` on `‖q‖_∞ ≤ K`, `0` elsewhere,
  i.e. convolution with the even Dirichlet kernel of order `K`, the analogue of `ε = 1/K`):
  `boxMultiplier K → 1` (`tendsto_boxMultiplier`), the smoothed field is a trigonometric
  polynomial (`smoothOp_boxMultiplier_eq_zero`), and its derivative coefficient sums are bounded
  explicitly, `∑_q |2πq|^m ‖(R_K u)(q)‖ ≤ (2K + 1)^{n/2} (2π √n K)^m ‖u‖`
  (`sum_norm_freq_pow_mul_le`). This sum bounds `sup_x ‖D^m (R_K u)(x)‖` for the trigonometric
  polynomial `Σ_q (R_K u)(q) e^{2πi q·x}`, giving the bound `C ε^{-m-n/2} ‖u‖`, `ε = 1/K`; only
  the coefficient form is stated here (the parity model works on the Fourier side). The bound
  holds over the box for every even multiplier (`sum_norm_freq_pow_mul_smoothOp_le`);
* the **Fejér multipliers** `fejerMultiplier K` (`ρ̂(q) = ∏ₐ (1 - |qₐ|/(K + 1))₊`, the product
  Fejér kernel): `0 ≤ ρ̂ ≤ 1`, supported in the box, `→ 1` pointwise, hence the same strong
  convergence and derivative bounds (`tendsto_smoothOp_fejerMultiplier`,
  `smoothOp_fejerMultiplier_eq_zero`, `sum_norm_freq_pow_mul_fejer_le`).

**Scope.** The identification of the parity complexes with the domain complexes
`H̊Λ(Q)`, `HΛ(Q)` of `Feec.Domain.deRham` (restriction of the periodic extension) is not
formalized here (see the scope note of `Feec.Models.Cube.DeRham`). The finite element method on
cube meshes (`Feec.Models.Cube.FiniteElementMethod`) does not need it: there the Whitney spaces lie
in `HΛ(Q)` itself, and the smoother is the dilated mollification of
`Feec.Domain.StarShapedSmoothing`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.4 (smoothing operators commuting with `d`)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (the cube by the method of images)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  Ch. 4 (convolution and mollifiers)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory LinearPMap Set Filter Topology Feec.Fourier Feec.Fourier.Exterior

namespace Feec.Models.Cube.DeRham

open Feec.Models.Torus.DeRham (window windowSymbol)

variable {d : Type*} [Fintype d] [LinearOrder d]

variable (d) in
/-- An **even multiplier**: a real symbol `ρ̂ : ℤⁿ → ℝ` with `|ρ̂| ≤ 1`, invariant under every
frequency reflection. The Fourier coefficients of a real, even kernel of total variation `≤ 1`
(e.g. an even probability density) are such a symbol; only these two properties are used. The
instances below are the box multiplier (`boxMultiplier`, the signed Dirichlet kernel) and the
Fejér multiplier (`fejerMultiplier`, `ρ̂ ≥ 0`). -/
structure EvenMultiplier where
  /-- the symbol -/
  ρ : (d → ℤ) → ℝ
  abs_le_one : ∀ q, |ρ q| ≤ 1
  flipAt_invariant : ∀ j q, ρ (flipAt j q) = ρ q

namespace EvenMultiplier

variable (m : EvenMultiplier d)

/-- The fibre symbol `ρ̂(q) · id`. -/
def symbol (k : ℕ) (q : d → ℤ) : Form ℂ d k →L[ℂ] Form ℂ d k :=
  ((m.ρ q : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (Form ℂ d k)

theorem norm_symbol_le (k : ℕ) (q : d → ℤ) : ‖m.symbol k q‖ ≤ 1 := by
  rw [symbol, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc |m.ρ q| * ‖ContinuousLinearMap.id ℂ (Form ℂ d k)‖ ≤ 1 * 1 :=
        mul_le_mul (m.abs_le_one q) (ContinuousLinearMap.norm_id_le) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end EvenMultiplier

/-- **The smoother** `û ↦ ρ̂ û` on `L²Λᵏ(𝕋ⁿ)`. -/
def smoothOp (m : EvenMultiplier d) (k : ℕ) :
    Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ)) →L[ℂ]
      Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ)) :=
  Operator.mulCLM Measure.count (m.symbol k) AEStronglyMeasurable.of_discrete 1
    (ae_of_all _ (m.norm_symbol_le k))

theorem smoothOp_apply (m : EvenMultiplier d) (k : ℕ)
    (u : Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ))) (q : d → ℤ) :
    smoothOp m k u q = ((m.ρ q : ℝ) : ℂ) • u q := by
  have h := MemLp.coeFn_toLp_count (Operator.memLp_clm_apply AEStronglyMeasurable.of_discrete
    (ae_of_all _ (m.norm_symbol_le k)) u)
  change ((Operator.memLp_clm_apply AEStronglyMeasurable.of_discrete
    (ae_of_all _ (m.norm_symbol_le k)) u).toLp _ : (d → ℤ) → Form ℂ d k) q = _
  rw [h]
  rfl

/-- **The smoother is an `L²`-contraction.** -/
theorem norm_smoothOp_le (m : EvenMultiplier d) (k : ℕ)
    (u : Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ))) : ‖smoothOp m k u‖ ≤ ‖u‖ := by
  have h := Operator.norm_mulCLM_apply_le (μ := Measure.count) (m.symbol k)
    AEStronglyMeasurable.of_discrete 1 (ae_of_all _ (m.norm_symbol_le k)) u
  rwa [one_mul] at h

/-! ### Commutation with `d` and with the reflections -/

/-- **The smoother maps `D(d)` into `D(d)`**: `d (ρ̂ û) = ρ̂ d û` is again in `ℓ²`. -/
theorem smoothOp_mem_domain (m : EvenMultiplier d) {i j : Fin (Fintype.card d + 1)}
    (u : ((window d).d i j).domain) :
    smoothOp m i u ∈ ((window d).d i j).domain := by
  have hu := (windowSymbol d).mem_domain_d_iff.1 u.2
  refine (windowSymbol d).mem_domain_d_iff.2 ?_
  refine hu.of_le AEStronglyMeasurable.of_discrete (ae_of_all _ fun q => ?_)
  rw [smoothOp_apply, _root_.map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (m.abs_le_one q)

/-- **The smoother commutes with `d`** (a scalar Fourier multiplier commutes with every symbol). -/
theorem d_smoothOp (m : EvenMultiplier d) {i j : Fin (Fintype.card d + 1)}
    (u : ((window d).d i j).domain) :
    (window d).d i j ⟨smoothOp m i u, smoothOp_mem_domain m u⟩ =
      smoothOp m j ((window d).d i j u) := by
  refine Lp.ext_count fun q => ?_
  have h1 := Measure.ae_count_iff.1 ((windowSymbol d).coeFn_d ⟨smoothOp m i u,
    smoothOp_mem_domain m u⟩) q
  have h2 := Measure.ae_count_iff.1 ((windowSymbol d).coeFn_d u) q
  calc ((window d).d i j ⟨smoothOp m i u, smoothOp_mem_domain m u⟩ : (d → ℤ) → Form ℂ d j) q
      = (windowSymbol d).m i j q (smoothOp m i u q) := h1
    _ = ((m.ρ q : ℝ) : ℂ) • (windowSymbol d).m i j q ((u : Lp (Form ℂ d i) 2 _) q) := by
        rw [smoothOp_apply, _root_.map_smul]
    _ = ((m.ρ q : ℝ) : ℂ) • ((window d).d i j u : (d → ℤ) → Form ℂ d j) q := by
        congr 1; exact h2.symm
    _ = _ := (smoothOp_apply m j _ q).symm

/-- **The smoother commutes with the reflections** `u ↦ ± R_j^* u ∘ flip_j` of each parity
class. -/
theorem smoothOp_symLp (m : EvenMultiplier d) (rel : Bool) (j : d)
    (i : Fin (Fintype.card d + 1)) (u : Lp (Form ℂ d i) 2 (Measure.count : Measure (d → ℤ))) :
    smoothOp m i (symLp ((symmetries d rel).R j) ((symmetries d rel).ρ j i) u) =
      symLp ((symmetries d rel).R j) ((symmetries d rel).ρ j i) (smoothOp m i u) := by
  refine Lp.ext_count fun q => ?_
  have h1 := Measure.ae_count_iff.1 (coeFn_symLp ((symmetries d rel).R j)
    ((symmetries d rel).ρ j i) u) q
  have h2 := Measure.ae_count_iff.1 (coeFn_symLp ((symmetries d rel).R j)
    ((symmetries d rel).ρ j i) (smoothOp m i u)) q
  calc (smoothOp m i (symLp ((symmetries d rel).R j) ((symmetries d rel).ρ j i) u) :
        (d → ℤ) → Form ℂ d i) q
      = ((m.ρ q : ℝ) : ℂ) • (symmetries d rel).ρ j i (u (flipAt j q)) := by
        rw [smoothOp_apply, h1]; rfl
    _ = (symmetries d rel).ρ j i (smoothOp m i u (flipAt j q)) := by
        rw [smoothOp_apply, _root_.map_smul, m.flipAt_invariant]
    _ = _ := h2.symm

/-- **The smoother preserves each parity class** (relative and absolute boundary conditions). -/
theorem smoothOp_mem_fixed (m : EvenMultiplier d) (rel : Bool) {i : Fin (Fintype.card d + 1)}
    {u : Lp (Form ℂ d i) 2 (Measure.count : Measure (d → ℤ))} (hu : u ∈ (action d rel).fixed i) :
    smoothOp m i u ∈ (action d rel).fixed i := by
  classical
  rw [(symmetries d rel).mem_fixed_toAction] at hu ⊢
  intro j
  rw [← smoothOp_symLp, hu j]

/-! ### The smoother on the cube complexes -/

/-- **The smoother on the de Rham complex of the cube** in a parity class. -/
def smoothFixed (m : EvenMultiplier d) (rel : Bool) (i : Fin (Fintype.card d + 1)) :
    (action d rel).fixed i →L[ℂ] (action d rel).fixed i :=
  ((smoothOp m i).comp ((action d rel).fixed i).subtypeL).codRestrict _ fun x =>
    smoothOp_mem_fixed m rel x.2

@[simp] theorem coe_smoothFixed (m : EvenMultiplier d) (rel : Bool)
    (i : Fin (Fintype.card d + 1)) (x : (action d rel).fixed i) :
    (smoothFixed m rel i x : Lp (Form ℂ d i) 2 _) = smoothOp m i x := rfl

/-- `‖R u‖ ≤ ‖u‖` on the cube. -/
theorem norm_smoothFixed_le (m : EvenMultiplier d) (rel : Bool) (i : Fin (Fintype.card d + 1))
    (x : (action d rel).fixed i) : ‖smoothFixed m rel i x‖ ≤ ‖x‖ :=
  norm_smoothOp_le m i x

/-- The smoother maps `D(d)` of the cube complex into itself. -/
theorem smoothFixed_mem_domain (m : EvenMultiplier d) (rel : Bool)
    {i j : Fin (Fintype.card d + 1)} (x : ((complex d rel).d i j).domain) :
    smoothFixed m rel i x ∈ ((complex d rel).d i j).domain :=
  smoothOp_mem_domain m ⟨_, x.2⟩

/-- **The smoother commutes with the differentials of the cube complex.** -/
theorem d_smoothFixed (m : EvenMultiplier d) (rel : Bool) {i j : Fin (Fintype.card d + 1)}
    (x : ((complex d rel).d i j).domain) :
    (complex d rel).d i j ⟨smoothFixed m rel i x, smoothFixed_mem_domain m rel x⟩ =
      smoothFixed m rel j ((complex d rel).d i j x) :=
  Subtype.ext (d_smoothOp m ⟨_, x.2⟩)

/-! ### Strong convergence -/

omit [LinearOrder d] in
/-- `‖v‖² = Σ_q ‖v(q)‖²` in `ℓ²(ℤⁿ; E)`. -/
theorem norm_sq_count {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : Lp E 2 (Measure.count : Measure (d → ℤ))) : ‖v‖ ^ 2 = ∑' q, ‖v q‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    ((lp.equivLpCount ℂ (d → ℤ) E 2).symm v)
  rw [LinearIsometryEquiv.norm_map] at h
  simp only [lp.equivLpCount_symm_apply, ENNReal.toReal_ofNat] at h
  simpa only [Real.rpow_two] using h

omit [LinearOrder d] in
theorem summable_norm_sq_count {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : Lp E 2 (Measure.count : Measure (d → ℤ))) : Summable fun q => ‖v q‖ ^ 2 := by
  have h := (lp.memℓp_count (d → ℤ) E 2 v).summable (by norm_num)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

/-- **Strong convergence of the smoother**: along any family of even multipliers converging
pointwise to `1`, `ρ̂ û → û` in `ℓ²` (dominated convergence, `|ρ̂ - 1|² ≤ 4`). -/
theorem tendsto_smoothOp {ι : Type*} {l : Filter ι} (m : ι → EvenMultiplier d)
    (hm : ∀ q, Tendsto (fun t => (m t).ρ q) l (𝓝 1)) (k : ℕ)
    (u : Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ))) :
    Tendsto (fun t => smoothOp (m t) k u) l (𝓝 u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun t => ‖smoothOp (m t) k u - u‖ ^ 2) l (𝓝 0) := by
    have e : ∀ t, ‖smoothOp (m t) k u - u‖ ^ 2 = ∑' q, ((m t).ρ q - 1) ^ 2 * ‖u q‖ ^ 2 := by
      intro t
      rw [norm_sq_count]
      refine tsum_congr fun q => ?_
      have hq : (smoothOp (m t) k u - u) q = (((m t).ρ q - 1 : ℝ) : ℂ) • u q := by
        rw [Measure.ae_count_iff.1 (Lp.coeFn_sub _ _) q, Pi.sub_apply, smoothOp_apply]
        push_cast
        rw [sub_smul, one_smul]
      rw [hq, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    simp_rw [e]
    have h0 : (∑' q : d → ℤ, (0 : ℝ)) = 0 := tsum_zero
    rw [← h0]
    refine tendsto_tsum_of_dominated_convergence ((summable_norm_sq_count u).mul_left 4)
      (fun q => ?_) (Eventually.of_forall fun t q => ?_)
    · have : Tendsto (fun t => ((m t).ρ q - 1) ^ 2 * ‖u q‖ ^ 2) l
          (𝓝 ((1 - 1) ^ 2 * ‖u q‖ ^ 2)) :=
        (((hm q).sub_const 1).pow 2).mul_const _
      simpa using this
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := (m t).abs_le_one q
      have h2 : ((m t).ρ q - 1) ^ 2 ≤ 4 := by
        rw [abs_le] at h1; nlinarith
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have hs := hsq.sqrt
  simp only [Real.sqrt_zero] at hs
  refine hs.congr fun t => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

/-! ### The box low-pass multipliers -/

variable (d) in
/-- The frequency box `‖q‖_∞ ≤ K`. -/
def box (K : ℕ) : Finset (d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(K : ℤ)) K

theorem mem_box {K : ℕ} {q : d → ℤ} : q ∈ box d K ↔ ∀ a, |q a| ≤ K := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

theorem card_box (K : ℕ) : (box d K).card = (2 * K + 1) ^ Fintype.card d := by
  rw [box, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Int.card_Icc]
  congr 1
  omega

theorem flipAt_mem_box {K : ℕ} (j : d) {q : d → ℤ} : flipAt j q ∈ box d K ↔ q ∈ box d K := by
  simp only [mem_box, flipAt]
  refine forall_congr' fun a => ?_
  split_ifs <;> simp [abs_neg]

variable (d) in
/-- **The box low-pass multiplier** of order `K` (convolution with the even Dirichlet kernel). -/
def boxMultiplier (K : ℕ) : EvenMultiplier d where
  ρ q := if q ∈ box d K then 1 else 0
  abs_le_one q := by
    by_cases hq : q ∈ box d K <;> simp [hq]
  flipAt_invariant j q := by
    simp only [flipAt_mem_box]

theorem boxMultiplier_ρ_of_mem {K : ℕ} {q : d → ℤ} (hq : q ∈ box d K) :
    (boxMultiplier d K).ρ q = 1 := by
  simp [boxMultiplier, hq]

theorem boxMultiplier_ρ_of_notMem {K : ℕ} {q : d → ℤ} (hq : q ∉ box d K) :
    (boxMultiplier d K).ρ q = 0 := by
  simp [boxMultiplier, hq]

/-- `boxMultiplier K → 1` pointwise as `K → ∞`. -/
theorem tendsto_boxMultiplier (q : d → ℤ) :
    Tendsto (fun K => (boxMultiplier d K).ρ q) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℕ, ∀ a, |q a| ≤ K₀ :=
    ⟨Finset.univ.sup fun a => (q a).natAbs, fun a => by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast Finset.le_sup (f := fun a => (q a).natAbs) (Finset.mem_univ a)⟩
  filter_upwards [eventually_ge_atTop K₀] with K hK
  rw [boxMultiplier_ρ_of_mem (mem_box.2 fun a => (hK₀ a).trans (by exact_mod_cast hK))]

/-- **Strong convergence of the low-pass smoothers**: `R_K u → u` in `L²` as `K → ∞`. -/
theorem tendsto_smoothOp_boxMultiplier (k : ℕ)
    (u : Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ))) :
    Tendsto (fun K => smoothOp (boxMultiplier d K) k u) atTop (𝓝 u) :=
  tendsto_smoothOp _ tendsto_boxMultiplier k u

/-- **`R_K u` is a trigonometric polynomial**: its coefficients vanish off the box. -/
theorem smoothOp_boxMultiplier_eq_zero {K k : ℕ}
    (u : Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ))) {q : d → ℤ} (hq : q ∉ box d K) :
    smoothOp (boxMultiplier d K) k u q = 0 := by
  rw [smoothOp_apply, boxMultiplier_ρ_of_notMem hq]
  simp

theorem norm_freq_le_of_mem_box {K : ℕ} {q : d → ℤ} (hq : q ∈ box d K) :
    ‖Fourier.Torus.freq q‖ ≤ 2 * Real.pi * √(Fintype.card d) * K := by
  rw [EuclideanSpace.norm_eq]
  have hb : ∀ a, ‖(Fourier.Torus.freq q) a‖ ^ 2 ≤ (2 * Real.pi * K) ^ 2 := by
    intro a
    rw [Fourier.Torus.freq_apply, Real.norm_eq_abs, sq_abs, mul_pow, mul_pow]
    have h := mem_box.1 hq a
    have h' : ((q a : ℤ) : ℝ) ^ 2 ≤ (K : ℝ) ^ 2 := by
      have : |((q a : ℤ) : ℝ)| ≤ (K : ℝ) := by exact_mod_cast h
      nlinarith [abs_nonneg ((q a : ℤ) : ℝ), sq_abs ((q a : ℤ) : ℝ)]
    have hp : 0 ≤ (2 : ℝ) ^ 2 * Real.pi ^ 2 := by positivity
    nlinarith
  calc √(∑ a, ‖(Fourier.Torus.freq q) a‖ ^ 2) ≤ √(∑ _a : d, (2 * Real.pi * K) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun a _ => hb a)
    _ = 2 * Real.pi * √(Fintype.card d) * K := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by positivity)]
        ring

/-- **Derivative bounds over the frequency box** for any even multiplier: the `m`-th derivative
coefficient sum of `R u` over `‖q‖_∞ ≤ K` satisfies
`∑_{q ∈ box K} |2πq|^m ‖(R u)(q)‖ ≤ (2K + 1)^{n/2} (2π √n K)^m ‖u‖` (Cauchy–Schwarz over the
`(2K + 1)ⁿ` frequencies of the box). For multipliers supported in the box (`boxMultiplier`,
`fejerMultiplier`) this is the full coefficient sum of the trigonometric polynomial `R u`. -/
theorem sum_norm_freq_pow_mul_smoothOp_le (ρ : EvenMultiplier d) (K k m : ℕ)
    (u : Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ))) :
    ∑ q ∈ box d K, ‖Fourier.Torus.freq q‖ ^ m * ‖smoothOp ρ k u q‖ ≤
      √((2 * K + 1 : ℝ) ^ Fintype.card d) * (2 * Real.pi * √(Fintype.card d) * K) ^ m * ‖u‖ := by
  set B : ℝ := 2 * Real.pi * √(Fintype.card d) * K
  have hB : 0 ≤ B := by positivity
  have hR : ∀ q, ‖smoothOp ρ k u q‖ ≤ ‖u q‖ := fun q => by
    rw [smoothOp_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (ρ.abs_le_one q)
  have h1 : ∑ q ∈ box d K, ‖Fourier.Torus.freq q‖ ^ m * ‖smoothOp ρ k u q‖ ≤
      ∑ q ∈ box d K, B ^ m * ‖u q‖ := by
    refine Finset.sum_le_sum fun q hq => ?_
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_freq_le_of_mem_box hq) m) (hR q)
      (norm_nonneg _) (by positivity)
  -- Cauchy–Schwarz: `∑_box ‖u q‖ ≤ √#box · (∑ ‖u q‖²)^{1/2} ≤ √#box ‖u‖`
  have hcs : (∑ q ∈ box d K, ‖u q‖) ^ 2 ≤ ((box d K).card : ℝ) * ∑ q ∈ box d K, ‖u q‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := box d K) (f := fun q => ‖u q‖)
    simpa using this
  have htail : ∑ q ∈ box d K, ‖u q‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [norm_sq_count]
    exact (summable_norm_sq_count u).sum_le_tsum _ fun q _ => by positivity
  have h2 : ∑ q ∈ box d K, ‖u q‖ ≤ √((2 * K + 1 : ℝ) ^ Fintype.card d) * ‖u‖ := by
    have hcard : ((box d K).card : ℝ) = (2 * K + 1 : ℝ) ^ Fintype.card d := by
      rw [card_box]; push_cast; ring
    have hsq : (∑ q ∈ box d K, ‖u q‖) ^ 2 ≤ (√((2 * K + 1 : ℝ) ^ Fintype.card d) * ‖u‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), ← hcard]
      exact hcs.trans (mul_le_mul_of_nonneg_left htail (by positivity))
    exact (abs_le_of_sq_le_sq' hsq (by positivity)).2
  calc _ ≤ ∑ q ∈ box d K, B ^ m * ‖u q‖ := h1
    _ = B ^ m * ∑ q ∈ box d K, ‖u q‖ := by rw [Finset.mul_sum]
    _ ≤ B ^ m * (√((2 * K + 1 : ℝ) ^ Fintype.card d) * ‖u‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- **Derivative bounds of the low-pass smoothers**: the `m`-th derivative coefficient sum of
`R_K u` satisfies `∑_q |2πq|^m ‖(R_K u)(q)‖ ≤ (2K + 1)^{n/2} (2π √n K)^m ‖u‖`; this sum bounds
`sup ‖D^m (R_K u)‖` of the trigonometric polynomial `R_K u`, i.e. `C ε^{-m-n/2} ‖u‖` with
`ε = 1/K` (Cauchy–Schwarz over the `(2K + 1)ⁿ` frequencies of the box). -/
theorem sum_norm_freq_pow_mul_le (K k m : ℕ)
    (u : Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ))) :
    ∑ q ∈ box d K, ‖Fourier.Torus.freq q‖ ^ m * ‖smoothOp (boxMultiplier d K) k u q‖ ≤
      √((2 * K + 1 : ℝ) ^ Fintype.card d) * (2 * Real.pi * √(Fintype.card d) * K) ^ m * ‖u‖ :=
  sum_norm_freq_pow_mul_smoothOp_le _ K k m u

/-! ### The Fejér multipliers -/

/-- The one-dimensional Fejér weight `(1 - |z| / (K + 1))₊`. -/
def fejerWeight (K : ℕ) (z : ℤ) : ℝ := max 0 (1 - |(z : ℝ)| / (K + 1))

theorem fejerWeight_nonneg (K : ℕ) (z : ℤ) : 0 ≤ fejerWeight K z := le_max_left _ _

theorem fejerWeight_le_one (K : ℕ) (z : ℤ) : fejerWeight K z ≤ 1 :=
  max_le zero_le_one (sub_le_self _ (by positivity))

theorem fejerWeight_eq_zero {K : ℕ} {z : ℤ} (hz : (K : ℤ) < |z|) : fejerWeight K z = 0 := by
  refine max_eq_left ?_
  have h : (K : ℝ) + 1 ≤ |(z : ℝ)| := by
    have : (K : ℤ) + 1 ≤ |z| := hz
    exact_mod_cast this
  rw [sub_nonpos, one_le_div (by positivity)]
  exact h

theorem tendsto_fejerWeight (z : ℤ) : Tendsto (fun K => fejerWeight K z) atTop (𝓝 1) := by
  have h : Tendsto (fun K : ℕ => |(z : ℝ)| / ((K : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h2 := ((tendsto_const_nhds (x := (1 : ℝ))).sub h).max (tendsto_const_nhds (x := (0 : ℝ)))
  simp only [sub_zero, max_eq_left zero_le_one] at h2
  refine h2.congr fun K => ?_
  rw [fejerWeight, max_comm]

variable (d) in
/-- **The Fejér multiplier** of order `K`: `ρ̂(q) = ∏ₐ (1 - |qₐ| / (K + 1))₊`, the Fourier
coefficients of the product Fejér kernel (Cesàro means of the box multipliers), with
`0 ≤ ρ̂ ≤ 1` and `ρ̂ = 0` off the box `‖q‖_∞ ≤ K`. -/
def fejerMultiplier (K : ℕ) : EvenMultiplier d where
  ρ q := ∏ a, fejerWeight K (q a)
  abs_le_one q := by
    rw [abs_of_nonneg (Finset.prod_nonneg fun a _ => fejerWeight_nonneg K _)]
    exact Finset.prod_le_one₀ (fun a _ => fejerWeight_nonneg K _) fun a _ => fejerWeight_le_one K _
  flipAt_invariant j q := by
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [flipAt]
    split_ifs
    · simp [fejerWeight, abs_neg]
    · rfl

theorem fejerMultiplier_ρ (K : ℕ) (q : d → ℤ) :
    (fejerMultiplier d K).ρ q = ∏ a, fejerWeight K (q a) := rfl

theorem fejerMultiplier_ρ_nonneg (K : ℕ) (q : d → ℤ) : 0 ≤ (fejerMultiplier d K).ρ q := by
  rw [fejerMultiplier_ρ]
  exact Finset.prod_nonneg fun a _ => fejerWeight_nonneg K _

theorem fejerMultiplier_ρ_of_notMem {K : ℕ} {q : d → ℤ} (hq : q ∉ box d K) :
    (fejerMultiplier d K).ρ q = 0 := by
  rw [mem_box] at hq
  push Not at hq
  obtain ⟨a, ha⟩ := hq
  rw [fejerMultiplier_ρ]
  exact Finset.prod_eq_zero (Finset.mem_univ a) (fejerWeight_eq_zero ha)

/-- `fejerMultiplier K → 1` pointwise as `K → ∞`. -/
theorem tendsto_fejerMultiplier (q : d → ℤ) :
    Tendsto (fun K => (fejerMultiplier d K).ρ q) atTop (𝓝 1) := by
  have h := tendsto_finsetProd (Finset.univ : Finset d) fun a _ => tendsto_fejerWeight (q a)
  simp only [Finset.prod_const_one] at h
  simpa only [fejerMultiplier_ρ] using h

/-- **Strong convergence of the Fejér smoothers**: `R_K u → u` in `L²` as `K → ∞`. -/
theorem tendsto_smoothOp_fejerMultiplier (k : ℕ)
    (u : Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ))) :
    Tendsto (fun K => smoothOp (fejerMultiplier d K) k u) atTop (𝓝 u) :=
  tendsto_smoothOp _ tendsto_fejerMultiplier k u

/-- **The Fejér-smoothed field is a trigonometric polynomial**: its coefficients vanish off the
box. -/
theorem smoothOp_fejerMultiplier_eq_zero {K k : ℕ}
    (u : Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ))) {q : d → ℤ} (hq : q ∉ box d K) :
    smoothOp (fejerMultiplier d K) k u q = 0 := by
  rw [smoothOp_apply, fejerMultiplier_ρ_of_notMem hq]
  simp

/-- **Derivative bounds of the Fejér smoothers**:
`∑_q |2πq|^m ‖(R_K u)(q)‖ ≤ (2K + 1)^{n/2} (2π √n K)^m ‖u‖`, the sum running over the whole
support of the coefficients of `R_K u` (`smoothOp_fejerMultiplier_eq_zero`). -/
theorem sum_norm_freq_pow_mul_fejer_le (K k m : ℕ)
    (u : Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ))) :
    ∑ q ∈ box d K, ‖Fourier.Torus.freq q‖ ^ m * ‖smoothOp (fejerMultiplier d K) k u q‖ ≤
      √((2 * K + 1 : ℝ) ^ Fintype.card d) * (2 * Real.pi * √(Fintype.card d) * K) ^ m * ‖u‖ :=
  sum_norm_freq_pow_mul_smoothOp_le _ K k m u

end Feec.Models.Cube.DeRham
