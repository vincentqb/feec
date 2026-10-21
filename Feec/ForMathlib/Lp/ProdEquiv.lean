module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# `Lᵖ` of a finite `ℓᵖ` product is the `ℓᵖ` product of the `Lᵖ` spaces

For `1 ≤ p < ∞`:

* `MeasureTheory.Lp.piEquiv`: `Lᵖ(μ; PiLp p E) ≃ₗᵢ[𝕜] PiLp p (fun i => Lᵖ(μ; E i))` for a finite
  family `E`, acting componentwise (`coeFn_piEquiv_apply`, `coeFn_piEquiv_symm`);
* `MeasureTheory.Lp.prodEquiv`: `Lᵖ(μ; WithLp p (E × F)) ≃ₗᵢ[𝕜] WithLp p (Lᵖ(μ; E) × Lᵖ(μ; F))`
  (`coeFn_prodEquiv_fst`, `coeFn_prodEquiv_snd`, `coeFn_prodEquiv_symm`).

Membership: `memLp_piLp_iff`, `memLp_prodLp_iff` (a field is `Lᵖ` iff all its components
are), and the identities behind the isometries `eLpNorm_piLp_rpow`, `eLpNorm_withLp_prod_rpow`
(`‖f‖ₚᵖ = Σᵢ ‖fᵢ‖ₚᵖ`).

For `p = 2` these are unitary. They identify the total space `L²(μ; W₀ ⊕ W₁ ⊕ …)` of a
multiplication-operator complex with the orthogonal sum of the `L²(μ; Wᵢ)`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped ENNReal NNReal
open MeasureTheory

@[expose] public noncomputable section

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

section Pi

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)]

omit [Fact (1 ≤ p)] in
/-- `‖x‖ₑ ^ p = Σᵢ ‖xᵢ‖ₑ ^ p` in `PiLp p E` (`p ≠ 0, ∞`). -/
theorem PiLp.enorm_rpow_eq_sum [Fact (1 ≤ p)] (hpt : p ≠ ∞) (x : PiLp p E) :
    ‖x‖ₑ ^ p.toReal = ∑ i, ‖x i‖ₑ ^ p.toReal := by
  have hp : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hpt
  have h : ‖x‖₊ ^ p.toReal = ∑ i, ‖x i‖₊ ^ p.toReal := by
    rw [PiLp.nnnorm_eq_sum hpt, one_div, NNReal.rpow_inv_rpow hp.ne']
  simp only [enorm_eq_nnnorm, ← ENNReal.coe_rpow_of_nonneg _ hp.le, h, ENNReal.ofNNReal_finsetSum]

/-- `‖f‖ₚᵖ = Σᵢ ‖fᵢ‖ₚᵖ` for a `PiLp p E`-valued field (`1 ≤ p < ∞`). -/
theorem eLpNorm_piLp_rpow (hpt : p ≠ ∞) {f : α → PiLp p E} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f p μ ^ p.toReal = ∑ i, eLpNorm (fun a => f a i) p μ ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hfi : ∀ i, AEStronglyMeasurable (fun a => f a i) μ := fun i =>
    (continuous_apply i).comp_aestronglyMeasurable
      ((PiLp.lipschitzWith_ofLp p E).continuous.comp_aestronglyMeasurable hf)
  rw [eLpNorm_eq_eLpNorm' hp0 hpt hf, ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp]
  simp_rw [PiLp.enorm_rpow_eq_sum hpt]
  rw [lintegral_finsetSum' _ fun i _ => (hfi i).enorm.pow_const _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eLpNorm_eq_eLpNorm' hp0 hpt (hfi i), ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp]

namespace Lp

omit [∀ i, NormedSpace 𝕜 (E i)] in
theorem memLp_toLp_pi (g : PiLp p fun i => Lp (E i) p μ) :
    MemLp (fun a => WithLp.toLp p fun i => (g i : α → E i) a) p μ :=
  (memLp_piLp_iff (f := fun a => WithLp.toLp p fun i => (g i : α → E i) a)).2 fun i =>
    Lp.memLp (g i)

variable (𝕜) in
/-- **`Lᵖ(μ; PiLp p E) ≃ₗᵢ PiLp p (Lᵖ(μ; E i))`** for a finite family and `1 ≤ p < ∞`. -/
def piEquiv (hpt : p ≠ ∞) : Lp (PiLp p E) p μ ≃ₗᵢ[𝕜] PiLp p fun i => Lp (E i) p μ where
  toFun f := WithLp.toLp p fun i => (PiLp.proj (𝕜 := 𝕜) p E i).compLp f
  invFun g := (memLp_toLp_pi g).toLp _
  map_add' f g := by
    ext i : 1
    exact ((PiLp.proj (𝕜 := 𝕜) p E i).compLpₗ p μ).map_add f g
  map_smul' c f := by
    ext i : 1
    exact ((PiLp.proj (𝕜 := 𝕜) p E i).compLpₗ p μ).map_smul c f
  left_inv f := by
    refine Lp.ext ?_
    have hc := fun i => (PiLp.proj (𝕜 := 𝕜) p E i).coeFn_compLp f
    filter_upwards [MemLp.coeFn_toLp (memLp_toLp_pi (WithLp.toLp p fun i =>
      (PiLp.proj (𝕜 := 𝕜) p E i).compLp f)),
      ae_all_iff.2 hc] with a h1 h2
    rw [h1]
    ext i
    simp only [h2 i]
    rfl
  right_inv g := by
    ext i : 1
    refine Lp.ext ?_
    filter_upwards [(PiLp.proj (𝕜 := 𝕜) p E i).coeFn_compLp ((memLp_toLp_pi g).toLp _),
      MemLp.coeFn_toLp (memLp_toLp_pi g)] with a h1 h2
    rw [PiLp.toLp_apply, h1, h2]
    rfl
  norm_map' f := by
    change ‖(WithLp.toLp p fun i => (PiLp.proj (𝕜 := 𝕜) p E i).compLp f :
      PiLp p fun i => Lp (E i) p μ)‖ = ‖f‖
    have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
    rw [PiLp.norm_eq_sum hp, Lp.norm_def]
    have hcomp : ∀ i, ‖(PiLp.proj (𝕜 := 𝕜) p E i).compLp f‖ =
        (eLpNorm (fun a => (f a : PiLp p E) i) p μ).toReal := fun i => by
      rw [Lp.norm_def]
      congr 1
      exact eLpNorm_congr_ae ((PiLp.proj (𝕜 := 𝕜) p E i).coeFn_compLp f)
    simp only [hcomp]
    have hfin : ∀ i, eLpNorm (fun a => (f a : PiLp p E) i) p μ ≠ ∞ := fun i =>
      ((PiLp.proj (𝕜 := 𝕜) p E i).comp_memLp' (Lp.memLp f)).ne_top
    simp only [ENNReal.toReal_rpow]
    rw [← ENNReal.toReal_sum fun i _ => ENNReal.rpow_ne_top_of_nonneg hp.le (hfin i),
      ENNReal.toReal_rpow, ← eLpNorm_piLp_rpow hpt (Lp.aestronglyMeasurable f), one_div,
      ENNReal.rpow_rpow_inv hp.ne']

variable (hpt : p ≠ ∞)

theorem coeFn_piEquiv_apply (f : Lp (PiLp p E) p μ) (i : ι) :
    (piEquiv 𝕜 hpt f i : α → E i) =ᵐ[μ] fun a => (f a : PiLp p E) i :=
  (PiLp.proj (𝕜 := 𝕜) p E i).coeFn_compLp f

theorem coeFn_piEquiv_symm (g : PiLp p fun i => Lp (E i) p μ) :
    ((piEquiv 𝕜 hpt).symm g : α → PiLp p E) =ᵐ[μ] fun a => WithLp.toLp p fun i => g i a :=
  MemLp.coeFn_toLp (memLp_toLp_pi g)

end Lp

end Pi

section Prod

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]

omit [Fact (1 ≤ p)] in
/-- `‖x‖ₑ ^ p = ‖x.1‖ₑ ^ p + ‖x.2‖ₑ ^ p` in `WithLp p (E × F)` (`p ≠ 0, ∞`). -/
theorem WithLp.prod_enorm_rpow_eq_add [Fact (1 ≤ p)] (hpt : p ≠ ∞) (x : WithLp p (E × F)) :
    ‖x‖ₑ ^ p.toReal = ‖x.fst‖ₑ ^ p.toReal + ‖x.snd‖ₑ ^ p.toReal := by
  have hp : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hpt
  have h : ‖x‖₊ ^ p.toReal = ‖x.fst‖₊ ^ p.toReal + ‖x.snd‖₊ ^ p.toReal := by
    rw [WithLp.prod_nnnorm_eq_add hpt, one_div, NNReal.rpow_inv_rpow hp.ne']
  simp only [enorm_eq_nnnorm, ← ENNReal.coe_rpow_of_nonneg _ hp.le, h, ENNReal.coe_add]

/-- `‖f‖ₚᵖ = ‖f₁‖ₚᵖ + ‖f₂‖ₚᵖ` for a `WithLp p (E × F)`-valued field (`1 ≤ p < ∞`). -/
theorem eLpNorm_withLp_prod_rpow (hpt : p ≠ ∞) {f : α → WithLp p (E × F)}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f p μ ^ p.toReal = eLpNorm (fun a => (f a).fst) p μ ^ p.toReal +
      eLpNorm (fun a => (f a).snd) p μ ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have h1 : AEStronglyMeasurable (fun a => (f a).fst) μ :=
    (by fun_prop : Continuous fun x : WithLp p (E × F) => x.fst).comp_aestronglyMeasurable hf
  have h2 : AEStronglyMeasurable (fun a => (f a).snd) μ :=
    (by fun_prop : Continuous fun x : WithLp p (E × F) => x.snd).comp_aestronglyMeasurable hf
  rw [eLpNorm_eq_eLpNorm' hp0 hpt hf, ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp,
    eLpNorm_eq_eLpNorm' hp0 hpt h1, ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp,
    eLpNorm_eq_eLpNorm' hp0 hpt h2, ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp]
  simp_rw [WithLp.prod_enorm_rpow_eq_add hpt]
  exact lintegral_add_left' (h1.enorm.pow_const _) _

namespace Lp

omit [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] in
theorem memLp_toLp_prod (g : WithLp p (Lp E p μ × Lp F p μ)) :
    MemLp (fun a => WithLp.toLp p ((g.fst : α → E) a, (g.snd : α → F) a)) p μ :=
  memLp_prodLp_iff.2 ⟨Lp.memLp g.fst, Lp.memLp g.snd⟩

variable (𝕜) in
/-- **`Lᵖ(μ; WithLp p (E × F)) ≃ₗᵢ WithLp p (Lᵖ(μ; E) × Lᵖ(μ; F))`** for `1 ≤ p < ∞`. -/
def prodEquiv (hpt : p ≠ ∞) :
    Lp (WithLp p (E × F)) p μ ≃ₗᵢ[𝕜] WithLp p (Lp E p μ × Lp F p μ) where
  toFun f := WithLp.toLp p ((WithLp.fstL p 𝕜 E F).compLp f, (WithLp.sndL p 𝕜 E F).compLp f)
  invFun g := (memLp_toLp_prod g).toLp _
  map_add' f g := by
    refine (WithLp.ext_iff _).2 (Prod.ext ?_ ?_)
    · exact ((WithLp.fstL p 𝕜 E F).compLpₗ p μ).map_add f g
    · exact ((WithLp.sndL p 𝕜 E F).compLpₗ p μ).map_add f g
  map_smul' c f := by
    refine (WithLp.ext_iff _).2 (Prod.ext ?_ ?_)
    · exact ((WithLp.fstL p 𝕜 E F).compLpₗ p μ).map_smul c f
    · exact ((WithLp.sndL p 𝕜 E F).compLpₗ p μ).map_smul c f
  left_inv f := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_toLp_prod (WithLp.toLp p
        ((WithLp.fstL p 𝕜 E F).compLp f, (WithLp.sndL p 𝕜 E F).compLp f))),
      (WithLp.fstL p 𝕜 E F).coeFn_compLp f, (WithLp.sndL p 𝕜 E F).coeFn_compLp f]
      with a h1 h2 h3
    rw [h1]
    refine (WithLp.ext_iff _).2 (Prod.ext ?_ ?_)
    · change (WithLp.fstL p 𝕜 E F).compLp f a = _; rw [h2]; rfl
    · change (WithLp.sndL p 𝕜 E F).compLp f a = _; rw [h3]; rfl
  right_inv g := by
    have h0 := MemLp.coeFn_toLp (memLp_toLp_prod g)
    refine (WithLp.ext_iff _).2 (Prod.ext ?_ ?_)
    · refine Lp.ext ?_
      filter_upwards [(WithLp.fstL p 𝕜 E F).coeFn_compLp ((memLp_toLp_prod g).toLp _),
        h0] with a h1 h2
      rw [h1, h2]; rfl
    · refine Lp.ext ?_
      filter_upwards [(WithLp.sndL p 𝕜 E F).coeFn_compLp ((memLp_toLp_prod g).toLp _),
        h0] with a h1 h2
      rw [h1, h2]; rfl
  norm_map' f := by
    change ‖(WithLp.toLp p ((WithLp.fstL p 𝕜 E F).compLp f, (WithLp.sndL p 𝕜 E F).compLp f) :
      WithLp p (Lp E p μ × Lp F p μ))‖ = ‖f‖
    have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
    rw [WithLp.prod_norm_eq_add hp, Lp.norm_def]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, Lp.norm_def]
    rw [eLpNorm_congr_ae ((WithLp.fstL p 𝕜 E F).coeFn_compLp f),
      eLpNorm_congr_ae ((WithLp.sndL p 𝕜 E F).coeFn_compLp f)]
    have hf1 : eLpNorm (fun a => (f a : WithLp p (E × F)).fst) p μ ≠ ∞ :=
      (memLp_prodLp_iff.1 (Lp.memLp f)).1.ne_top
    have hf2 : eLpNorm (fun a => (f a : WithLp p (E × F)).snd) p μ ≠ ∞ :=
      (memLp_prodLp_iff.1 (Lp.memLp f)).2.ne_top
    simp only [WithLp.fstL_apply, WithLp.sndL_apply, ENNReal.toReal_rpow]
    rw [← ENNReal.toReal_add
        (ENNReal.rpow_ne_top_of_nonneg hp.le hf1) (ENNReal.rpow_ne_top_of_nonneg hp.le hf2),
      ENNReal.toReal_rpow,
      ← eLpNorm_withLp_prod_rpow hpt (Lp.aestronglyMeasurable f), one_div,
      ENNReal.rpow_rpow_inv hp.ne']

variable (hpt : p ≠ ∞)

theorem coeFn_prodEquiv_fst (f : Lp (WithLp p (E × F)) p μ) :
    ((prodEquiv 𝕜 hpt f).fst : α → E) =ᵐ[μ] fun a => (f a : WithLp p (E × F)).fst :=
  (WithLp.fstL p 𝕜 E F).coeFn_compLp f

theorem coeFn_prodEquiv_snd (f : Lp (WithLp p (E × F)) p μ) :
    ((prodEquiv 𝕜 hpt f).snd : α → F) =ᵐ[μ] fun a => (f a : WithLp p (E × F)).snd :=
  (WithLp.sndL p 𝕜 E F).coeFn_compLp f

theorem coeFn_prodEquiv_symm (g : WithLp p (Lp E p μ × Lp F p μ)) :
    ((prodEquiv 𝕜 hpt).symm g : α → WithLp p (E × F)) =ᵐ[μ]
      fun a => WithLp.toLp p ((g.fst : α → E) a, (g.snd : α → F) a) :=
  MemLp.coeFn_toLp (memLp_toLp_prod g)

end Lp

end Prod

end MeasureTheory
