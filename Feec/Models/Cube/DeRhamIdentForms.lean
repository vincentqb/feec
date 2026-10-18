module

public import Feec.Models.Cube.DeRhamIdentCutoff
public import Feec.Models.Cube.DeRham
public import Feec.Domain.DeRham

/-!
# The parity extension of `k`-forms on `Q = (0, ½)ⁿ` and the exterior derivative

A real `k`-form `u = Σ_s u_s dx_s` on `Q = (0, ½)ⁿ` (`Feec.Domain.L2F ℝ Q (formIdx n k)`) is
extended to the torus `𝕋ⁿ = ℝⁿ/ℤⁿ` by the method of images in one of the two parity classes of
`Feec.Models.Cube.DeRham`: `u_s ∘ R_j = ± ε_j(s) u_s` (`pc`; `-` for the relative class,
fixed by `-R_j^*`, `+` for the absolute class, fixed by `R_j^*`). On the Fourier side this is the
real-linear map `Jf rel k : L²(Q; Λᵏ) → ℓ²(ℤⁿ; Λᵏ)`, a scaled isometry
(`⟪Jf u, Jf v⟫ = 2ⁿ ⟪u, v⟫`, `inner_Jf`) onto the real coefficient sequences of the parity class
(`RealPar`, `Jf_realPar`, `Jf_Jinvf`).

**The exterior derivative.** If `(u, w)` satisfies Green's identity
`⟪w, ψ⟫ = ⟪u, dᵗ ψ⟫` against the smooth `(k + 1)`-forms `ψ` with one component (`GreenFor`;
for the absolute class only those whose normal component vanishes on `∂Q`), then the torus
symbol `d_ξ = i ξ ∧ ·` maps the coefficients of `Jf u` to those of `Jf w`
(`coeff_d_of_greenFor`): the pairing of the extension with a character is the pairing on `Q`
with the folded character (`Feec.Models.Cube.DeRhamIdent.coeff_JR`), whose derivatives are folds
in the neighbouring parity class. Green's identity holds

* on `D(d_min)` (`H̊Λ(Q)`) against every smooth form (`greenFor_minimal`, relative class), and
* on `D(d_max)` (`HΛ(Q)`) against smooth forms with vanishing normal trace
  (`greenFor_maximal`, absolute class): these lie in the minimal domain of `dᵗ` by the cut-off
  argument (`Feec.Models.Cube.DeRhamIdent.mem_closure_testGraph_of_cutoff`).

## Main definitions

* `pc`, `pcF`, `idx`, `reidx`, `Jf`, `Jinvf`, `RealPar`, `GreenFor`.

## Main results

* **`inner_Jf`**, `Jinvf_Jf`, `Jf_realPar`, **`Jf_Jinvf`**, `injective_Jf`.
* `deRham_m_apply`, `ext_Jf`, `formalAdj_single1_apply`, `greenFor_of_inner`,
  **`coeff_d_of_greenFor`**.
* **`greenFor_minimal`**, `mem_closure_formalAdj_single1`, **`greenFor_maximal`**;
  `coeff_d_minimal`, `coeff_d_maximal`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4.3 (relative and absolute boundary conditions)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6 (the de Rham complex with
  boundary conditions)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (the cube by the method of images)
-/

open scoped InnerProductSpace ComplexConjugate ContDiff Topology
open Set MeasureTheory Filter UnitAddTorus Feec.Fourier.TorusWeak Finset

@[expose] public noncomputable section

namespace Feec.Models.Cube.DeRhamIdent

open Geometry MirrorExt
open Feec.Domain (formIdx formExt formExt_of_card formExt_val extDerivOp L2F L2 toL2F)
open Feec.Fourier.Exterior (Form Lam)

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Fourier.TorusWeak`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The local Haar measure on `ℝ/ℤ` is an additive Haar measure. -/
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The local Haar measure on `ℝ/ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {n : ℕ}

/-! ### Parity vectors and index sets -/

/-- The parity vector of the coefficient of `dx_s` in the class `rel`: `u_s ∘ R_j = c_j u_s` with
`c_j = ± ε_j(s)` (`-` for the relative class). -/
def pcF (rel : Bool) (s : Finset (Fin n)) (j : Fin n) : ℂ :=
  DeRham.parSign rel * DeRham.reflSign j s

/-- The parity vector of a component `s` of a `k`-form. -/
def pc (rel : Bool) {k : ℤ} (s : formIdx n k) : Fin n → ℂ := pcF rel s.1

theorem pcF_mul_self (rel : Bool) (s : Finset (Fin n)) (j : Fin n) :
    pcF rel s j * pcF rel s j = 1 := by
  unfold pcF DeRham.parSign DeRham.reflSign; split_ifs <;> norm_num

theorem pc_mul_self (rel : Bool) {k : ℤ} (s : formIdx n k) (j : Fin n) :
    pc rel s j * pc rel s j = 1 := pcF_mul_self rel s.1 j

theorem conj_pc (rel : Bool) {k : ℤ} (s : formIdx n k) (j : Fin n) :
    conj (pc rel s j) = pc rel s j := by
  unfold pc pcF DeRham.parSign DeRham.reflSign; split_ifs <;> simp

/-- **Removing `j` reverses the parity of `x_j`**: `c(s ∖ j) = c(s)` with the sign of `x_j`
flipped. -/
theorem update_pcF_erase (rel : Bool) {s : Finset (Fin n)} {j : Fin n} (hj : j ∈ s) :
    Function.update (pcF rel s) j (-pcF rel s j) = pcF rel (s.erase j) := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp [pcF, DeRham.reflSign, hj]
  · rw [Function.update_of_ne hi]
    simp [pcF, DeRham.reflSign, Finset.mem_erase, hi]

/-- `formIdx n k` and the `k`-subsets of `Fin n` (the index set of `Form ℂ (Fin n) k`). -/
def idx (k : ℕ) : formIdx n (k : ℤ) ≃ {s : Finset (Fin n) // #s = k} :=
  Equiv.subtypeEquivRight fun _ => Nat.cast_inj

@[simp] theorem idx_val (k : ℕ) (s : formIdx n (k : ℤ)) : ((idx k s) : Finset (Fin n)) = s.1 := rfl

@[simp] theorem idx_symm_val (k : ℕ) (t : {s : Finset (Fin n) // #s = k}) :
    (((idx k).symm t) : Finset (Fin n)) = t.1 := rfl

/-- The coefficient sequences of `L²` fields indexed by `formIdx n k`, as `ℓ²(ℤⁿ; Λᵏ)`. -/
def reidx (k : ℕ) : Lp (EuclideanSpace ℂ (formIdx n (k : ℤ))) 2 (Measure.count : Measure (Fin n → ℤ))
    ≃ₗᵢ[ℂ] Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)) :=
  DeRham.lpCongr (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (idx k))

theorem reidx_apply (k : ℕ)
    (w : Lp (EuclideanSpace ℂ (formIdx n (k : ℤ))) 2 (Measure.count : Measure (Fin n → ℤ)))
    (m : Fin n → ℤ) (t : {s : Finset (Fin n) // #s = k}) :
    (reidx k w : (Fin n → ℤ) → Form ℂ (Fin n) k) m t = w m ((idx k).symm t) := by
  rw [reidx, DeRham.lpCongr_apply, LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl

theorem reidx_symm_apply (k : ℕ)
    (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)))
    (m : Fin n → ℤ) (s : formIdx n (k : ℤ)) :
    ((reidx k).symm x : (Fin n → ℤ) → EuclideanSpace ℂ (formIdx n (k : ℤ))) m s = x m (idx k s) := by
  conv_rhs => rw [← (reidx k).apply_symm_apply x]
  rw [reidx_apply, Equiv.symm_apply_apply]

/-! ### The extension of `k`-forms -/

/-- **The parity extension of real `k`-forms on `Q`**, on the Fourier side of `𝕋ⁿ`. -/
def Jf (rel : Bool) (k : ℕ) : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)) →L[ℝ]
    Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)) :=
  ((reidx k).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
    (JR (pc_mul_self rel))

theorem Jf_apply (rel : Bool) (k : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    Jf rel k u = reidx k (JR (pc_mul_self rel) u) := rfl

/-- **The coefficients of `Jf`**: `(Jf u)(m)_t = ∫_Q u_t · fold_{c(t)} e_{-m}`. -/
theorem coeff_Jf (rel : Bool) (k : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)))
    (m : Fin n → ℤ) (t : {s : Finset (Fin n) // #s = k}) :
    (Jf rel k u : (Fin n → ℤ) → Form ℂ (Fin n) k) m t =
      ∫ y in Q (Fin n), (((u ((idx k).symm t) : (Fin n → ℝ) → ℝ) y : ℝ) : ℂ) *
        fold (pcF rel t.1) (mFourier (-m)) y := by
  rw [Jf_apply, reidx_apply, coeff_JR]
  rfl

/-- The restriction of Fourier-side `k`-forms to `Q`, real part. -/
def Jinvf (k : ℕ) : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)) →L[ℝ]
    L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)) :=
  (Jinv (Fin n) (formIdx n (k : ℤ))).comp
    ((reidx k).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)

theorem Jinvf_Jf (rel : Bool) (k : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    Jinvf k (Jf rel k u) = u := by
  change Jinv (Fin n) (formIdx n (k : ℤ)) ((reidx k).symm (reidx k (JR (pc_mul_self rel) u))) = u
  rw [LinearIsometryEquiv.symm_apply_apply, Jinv_JR]

theorem injective_Jf (rel : Bool) (k : ℕ) : Function.Injective (Jf (n := n) rel k) :=
  fun u v h => by rw [← Jinvf_Jf rel k u, h, Jinvf_Jf]

/-- **The extension scales inner products by `2ⁿ`.** -/
theorem inner_Jf (rel : Bool) (k : ℕ) (u v : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    ⟪Jf rel k u, Jf rel k v⟫_ℝ = 2 ^ n * ⟪u, v⟫_ℝ := by
  rw [MeasureTheory.L2.real_inner_eq_re_inner EuclideanSpace.real_inner_eq_re_inner, Jf_apply,
    Jf_apply, LinearIsometryEquiv.inner_map_map,
    ← MeasureTheory.L2.real_inner_eq_re_inner EuclideanSpace.real_inner_eq_re_inner, inner_JR,
    Fintype.card_fin]

theorem norm_Jf (rel : Bool) (k : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    ‖Jf rel k u‖ = Real.sqrt (2 ^ n) * ‖u‖ := by
  have h := inner_Jf rel k u u
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [← Real.sqrt_sq (norm_nonneg (Jf rel k u)), h, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (norm_nonneg u)]

/-- **The real coefficient sequences of the parity class `rel`**: `x(-m) = conj x(m)` and
`x(flip_j m)_t = ± ε_j(t) x(m)_t`. -/
def RealPar (rel : Bool) (k : ℕ)
    (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))) : Prop :=
  (∀ m t, (x : (Fin n → ℤ) → Form ℂ (Fin n) k) (-m) t =
      conj ((x : (Fin n → ℤ) → Form ℂ (Fin n) k) m t)) ∧
    ∀ j m t, (x : (Fin n → ℤ) → Form ℂ (Fin n) k) (DeRham.flipAt j m) t =
      DeRham.parSign rel * DeRham.reflSign j t.1 * (x : (Fin n → ℤ) → Form ℂ (Fin n) k) m t

theorem flipAt_eq (j : Fin n) (m : Fin n → ℤ) : MirrorExt.flipAt j m = DeRham.flipAt j m := by
  funext i; rw [MirrorExt.flipAt_apply]; rfl

theorem Jf_realPar (rel : Bool) (k : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    RealPar rel k (Jf rel k u) := by
  refine ⟨fun m t => ?_, fun j m t => ?_⟩
  · rw [Jf_apply, reidx_apply, reidx_apply]
    exact JR_isReal (pc_mul_self rel) (conj_pc rel) u m _
  · rw [Jf_apply, reidx_apply, reidx_apply, ← flipAt_eq]
    exact (mem_fieldParity_iff.1 (JR_mem_fieldParity (pc_mul_self rel) u)) j m _

/-- **Real parity sequences are extensions of `k`-forms on `Q`.** -/
theorem Jf_Jinvf {rel : Bool} {k : ℕ}
    {x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))} (hx : RealPar rel k x) :
    Jf rel k (Jinvf k x) = x := by
  set w := (reidx k).symm x
  have hw : w ∈ fieldParity (pc (n := n) (k := (k : ℤ)) rel) := mem_fieldParity_iff.2 fun j m s => by
    rw [reidx_symm_apply, reidx_symm_apply, flipAt_eq, hx.2]
    rfl
  have hr : IsReal w := fun m s => by
    rw [reidx_symm_apply, reidx_symm_apply, hx.1]
  change reidx k (JR (pc_mul_self rel) (Jinv (Fin n) (formIdx n (k : ℤ)) w)) = x
  rw [JR_Jinv (pc_mul_self rel) hw hr, LinearIsometryEquiv.apply_symm_apply]

theorem range_Jf (rel : Bool) (k : ℕ) :
    Set.range (Jf (n := n) rel k) = {x | RealPar rel k x} := by
  ext x
  exact ⟨fun ⟨u, hu⟩ => hu ▸ Jf_realPar rel k u, fun hx => ⟨_, Jf_Jinvf hx⟩⟩

/-! ### The torus symbol and the coefficients of `Jf` on all index sets -/

/-- `u` extended by zero to a family indexed by all subsets of `Fin n` (`formExt`). -/
abbrev uExt {k : ℤ} (u : L2F ℝ (Q (Fin n)) (formIdx n k)) (r : Finset (Fin n)) :
    L2 ℝ (Q (Fin n)) :=
  formExt (fun s => (u s : L2 ℝ (Q (Fin n)))) r

/-- **The de Rham symbol in coordinates**: `(d_ξ v)_t = i Σ_{j ∈ t} ε(j, t) ξ_j v_{t ∖ j}`. -/
theorem deRham_m_apply (k : ℕ) (ξ : EuclideanSpace ℝ (Fin n)) (v : Form ℂ (Fin n) k)
    (t : {s : Finset (Fin n) // #s = k + 1}) :
    (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) ξ v t =
      Complex.I * ∑ j ∈ t.1, (Feec.Fourier.Exterior.sgn j t.1 : ℂ) * (ξ j : ℂ) *
        Feec.Fourier.Exterior.ext k v (t.1.erase j) := by
  rw [Feec.Fourier.Exterior.deRham_m_succ, smul_apply,
    Feec.Fourier.Exterior.koszulDeg_apply]
  rfl

/-- **The coefficients of `Jf` on all index sets**: `ext (Jf u (m)) r = ∫_Q u_r · fold_{c(r)}
e_{-m}` (both sides vanish off the `k`-subsets). -/
theorem ext_Jf (rel : Bool) (k : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)))
    (m : Fin n → ℤ) (r : Finset (Fin n)) :
    Feec.Fourier.Exterior.ext k ((Jf rel k u : (Fin n → ℤ) → Form ℂ (Fin n) k) m) r =
      ∫ y in Q (Fin n), (((uExt u r : (Fin n → ℝ) → ℝ) y : ℝ) : ℂ) *
        fold (pcF rel r) (mFourier (-m)) y := by
  by_cases h : #r = k
  · rw [Feec.Fourier.Exterior.ext_apply k _ h, coeff_Jf, uExt,
      formExt_of_card _ (by exact_mod_cast h)]
    rfl
  · rw [Feec.Fourier.Exterior.ext_apply_of_ne k _ h, uExt, formExt,
      dite_eq_right (by exact_mod_cast h)]
    symm
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Q (Fin n)))] with y hy
    rw [hy]; simp

/-! ### Green's identity against one-component forms -/

theorem isBounded_Qn : Bornology.IsBounded (Q (Fin n)) := isBounded_openCube _ _

/-- A one-component `(k + 1)`-form `φ dx_t`. -/
abbrev single1 {k : ℤ} (t : formIdx n (k + 1)) (φ : (Fin n → ℝ) → ℝ) :
    formIdx n (k + 1) → (Fin n → ℝ) → ℝ :=
  Pi.single t φ

theorem formExt_single1 {k : ℤ} (t : formIdx n (k + 1)) (φ : (Fin n → ℝ) → ℝ)
    (r : Finset (Fin n)) : formExt (single1 t φ) r = if r = t.1 then φ else 0 := by
  unfold formExt
  split_ifs with h1 h2 h2
  · subst h2; simp [single1]
  · rw [single1, Pi.single_apply, ite_eq_right]
    exact fun h => h2 (congrArg Subtype.val h)
  · exact absurd (h2 ▸ t.2) h1
  · rfl

/-- **The formal adjoint of `d` on a one-component form**:
`(dᵗ (φ dx_t))_s = -Σ_{j ∈ t, t ∖ j = s} ε(j, t) ∂_j φ`. -/
theorem formalAdj_single1_apply {k : ℤ} (t : formIdx n (k + 1)) {φ : (Fin n → ℝ) → ℝ}
    (s : formIdx n k) (y : Fin n → ℝ) :
    (extDerivOp ℝ n k).formalAdj.apply (single1 t φ) s y =
      -∑ j ∈ t.1, if t.1.erase j = s.1 then
        (ExteriorFibre.sgn j t.1 : ℝ) * fderiv ℝ φ y (Pi.single j 1) else 0 := by
  rw [Feec.Domain.formalAdj_extDerivOp_apply, Feec.Domain.extDAdj]
  congr 1
  have key : ∀ j, (if j ∈ s.1ᶜ then (ExteriorFibre.sgn j s.1 : ℝ) *
      fderiv ℝ (formExt (single1 t φ) (insert j s.1)) y (Feec.Domain.coordDir j) else 0) =
      (if j ∈ t.1 then (if t.1.erase j = s.1 then
        (ExteriorFibre.sgn j t.1 : ℝ) * fderiv ℝ φ y (Pi.single j 1) else 0) else 0) := by
    intro j
    rw [formExt_single1]
    by_cases h1 : j ∈ t.1 ∧ t.1.erase j = s.1
    · have hjs : j ∉ s.1 := h1.2 ▸ Finset.notMem_erase j t.1
      have hins : insert j s.1 = t.1 := by rw [← h1.2, Finset.insert_erase h1.1]
      rw [ite_eq_left (Finset.mem_compl.2 hjs), ite_eq_left hins, ite_eq_left h1.1, ite_eq_left h1.2, ← hins,
        ExteriorFibre.sgn_insert_self]
    · have hR : (if j ∈ t.1 then (if t.1.erase j = s.1 then
          (ExteriorFibre.sgn j t.1 : ℝ) * fderiv ℝ φ y (Pi.single j 1) else 0) else 0) = 0 := by
        split_ifs with h2 h3
        · exact absurd ⟨h2, h3⟩ h1
        · rfl
        · rfl
      rw [hR]
      split_ifs with h2 h3
      · exfalso
        refine h1 ⟨h3 ▸ Finset.mem_insert_self j s.1, ?_⟩
        rw [← h3, Finset.erase_insert (Finset.mem_compl.1 h2)]
      · simp
      · rfl
  calc ∑ j ∈ s.1ᶜ, (ExteriorFibre.sgn j s.1 : ℝ) *
        fderiv ℝ (formExt (single1 t φ) (insert j s.1)) y (Feec.Domain.coordDir j)
      = ∑ j, (if j ∈ s.1ᶜ then (ExteriorFibre.sgn j s.1 : ℝ) *
          fderiv ℝ (formExt (single1 t φ) (insert j s.1)) y (Feec.Domain.coordDir j) else 0) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ j, (if j ∈ t.1 then (if t.1.erase j = s.1 then
          (ExteriorFibre.sgn j t.1 : ℝ) * fderiv ℝ φ y (Pi.single j 1) else 0) else 0) :=
        Finset.sum_congr rfl fun j _ => key j
    _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter]

/-! ### Green's identity in coordinates -/

theorem integrable_real_mul_bdd_Q (f : L2 ℝ (Q (Fin n))) {h : (Fin n → ℝ) → ℝ}
    (hh : Continuous h) {C : ℝ} (hC : ∀ y, ‖h y‖ ≤ C) :
    Integrable (fun y => (f : (Fin n → ℝ) → ℝ) y * h y) (volume.restrict (Q (Fin n))) := by
  have := isFiniteMeasure_Q (d := Fin n)
  exact ((Lp.memLp f).integrable one_le_two).mul_bdd hh.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

/-- `∫_Q f G = ∫_Q f Re G + i ∫_Q f Im G` for real `f` and bounded continuous complex `G`. -/
theorem integral_ofReal_mul_eq (f : L2 ℝ (Q (Fin n))) {G : (Fin n → ℝ) → ℂ} (hG : Continuous G)
    {C : ℝ} (hC : ∀ y, ‖G y‖ ≤ C) :
    ∫ y in Q (Fin n), (((f : (Fin n → ℝ) → ℝ) y : ℝ) : ℂ) * G y =
      ((∫ y in Q (Fin n), (f : (Fin n → ℝ) → ℝ) y * (G y).re : ℝ) : ℂ) +
        Complex.I * ((∫ y in Q (Fin n), (f : (Fin n → ℝ) → ℝ) y * (G y).im : ℝ) : ℂ) := by
  have h1 := integrable_real_mul_bdd_Q f (Complex.continuous_re.comp hG) (C := C)
    fun y => (Complex.abs_re_le_norm _).trans (hC y)
  have h2 := integrable_real_mul_bdd_Q f (Complex.continuous_im.comp hG) (C := C)
    fun y => (Complex.abs_im_le_norm _).trans (hC y)
  have e : (fun y => (((f : (Fin n → ℝ) → ℝ) y : ℝ) : ℂ) * G y) = fun y =>
      (((f : (Fin n → ℝ) → ℝ) y * (G y).re : ℝ) : ℂ) +
        Complex.I * (((f : (Fin n → ℝ) → ℝ) y * (G y).im : ℝ) : ℂ) := by
    funext y
    apply Complex.ext <;> simp
  rw [e, integral_add h1.ofReal (h2.ofReal.const_mul _), integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal]

/-- `∑_s [r = s] F(u_s) = F(u_r)` (`u_r = 0` off the `k`-subsets). -/
theorem sum_ite_eq_uExt {k : ℤ} (u : L2F ℝ (Q (Fin n)) (formIdx n k)) (r : Finset (Fin n))
    (F : L2 ℝ (Q (Fin n)) → ℝ) (hF : F 0 = 0) :
    ∑ s : formIdx n k, (if r = s.1 then F (u s) else 0) = F (uExt u r) := by
  by_cases h : (#r : ℤ) = k
  · have e : ∀ s : formIdx n k, (r = s.1) ↔ s = ⟨r, h⟩ := fun s => by
      rw [Subtype.ext_iff]; exact eq_comm
    simp only [e, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [uExt, formExt_of_card _ h]
  · have e : ∀ s : formIdx n k, ¬ (r = s.1) := fun s hs => h (hs ▸ s.2)
    simp only [e, ite_false, Finset.sum_const_zero]
    rw [uExt, formExt, dite_eq_right (by exact_mod_cast h), hF]

/-- **Green's identity of `(u, w)` against the one-component forms `φ dx_t`**, in coordinates:
`∫_Q w_t φ = -Σ_{j ∈ t} ε(j, t) ∫_Q u_{t ∖ j} ∂_j φ`, for smooth `φ` bounded with bounded first
derivatives; for the absolute class (`rel = false`) only for `φ` vanishing on the faces normal to
`t` (vanishing normal trace). -/
def GreenFor (rel : Bool) (k : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)))
    (w : L2F ℝ (Q (Fin n)) (formIdx n ((k : ℤ) + 1))) : Prop :=
  ∀ (t : formIdx n ((k : ℤ) + 1)) (φ : (Fin n → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
    (∃ M, ∀ y, |φ y| ≤ M) → (∃ L, ∀ j y, |fderiv ℝ φ y (Pi.single j 1)| ≤ L) →
    (rel = false → ∀ j ∈ t.1, ∀ y : Fin n → ℝ, (y j = 0 ∨ y j = 1 / 2) → φ y = 0) →
    ∫ y in Q (Fin n), (w t : (Fin n → ℝ) → ℝ) y * φ y =
      -∑ j ∈ t.1, (ExteriorFibre.sgn j t.1 : ℝ) *
        ∫ y in Q (Fin n), (uExt u (t.1.erase j) : (Fin n → ℝ) → ℝ) y *
          fderiv ℝ φ y (Pi.single j 1)

theorem contDiff_single1 {k : ℤ} (t : formIdx n (k + 1)) {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (s : formIdx n (k + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (single1 t φ s) := by
  by_cases h : s = t
  · subst h; simpa [single1] using hφ
  · simp only [single1, Pi.single_apply, h, ite_false]; exact contDiff_const

theorem memLp_single1 {k : ℤ} (t : formIdx n (k + 1)) {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (s : formIdx n (k + 1)) :
    MemLp (single1 t φ s) 2 (volume.restrict (Q (Fin n))) :=
  Feec.Domain.memLp_of_continuous measurableSet_Q isBounded_Qn (contDiff_single1 t hφ s).continuous

theorem memLp_formalAdj_single1 {k : ℤ} (t : formIdx n (k + 1)) {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (s : formIdx n k) :
    MemLp ((extDerivOp ℝ n k).formalAdj.apply (single1 t φ) s) 2 (volume.restrict (Q (Fin n))) :=
  Feec.Domain.memLp_of_continuous measurableSet_Q isBounded_Qn
    ((extDerivOp ℝ n k).formalAdj.continuous_apply (Feec.Domain.formalAdj_extDerivOp_isOrderLE k)
      (fun s' => (contDiff_single1 t hφ s').of_le (by exact_mod_cast le_top)) s)

theorem integral_real_mul_fderiv_integrable {k : ℤ} (u : L2F ℝ (Q (Fin n)) (formIdx n k))
    {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {L : ℝ}
    (hL : ∀ j y, |fderiv ℝ φ y (Pi.single j 1)| ≤ L) (s : formIdx n k) (j : Fin n) :
    Integrable (fun y => (u s : (Fin n → ℝ) → ℝ) y * fderiv ℝ φ y (Pi.single j 1))
      (volume.restrict (Q (Fin n))) :=
  integrable_real_mul_bdd_Q (u s)
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (C := L) fun y => hL j y

/-- **Green's identity from the inner products**: if `⟪w, φ dx_t⟫ = ⟪u, dᵗ (φ dx_t)⟫` for the
admissible `φ`, then `GreenFor rel k u w`. -/
theorem greenFor_of_inner {rel : Bool} {k : ℕ} {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    {w : L2F ℝ (Q (Fin n)) (formIdx n ((k : ℤ) + 1))}
    (h : ∀ (t : formIdx n ((k : ℤ) + 1)) (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ),
      (∃ M, ∀ y, |φ y| ≤ M) → (∃ L, ∀ j y, |fderiv ℝ φ y (Pi.single j 1)| ≤ L) →
      (rel = false → ∀ j ∈ t.1, ∀ y : Fin n → ℝ, (y j = 0 ∨ y j = 1 / 2) → φ y = 0) →
      ⟪w, toL2F (memLp_single1 t hφ)⟫_ℝ = ⟪u, toL2F (memLp_formalAdj_single1 t hφ)⟫_ℝ) :
    GreenFor rel k u w := by
  intro t φ hφ hM hL hV
  have e := h t φ hφ hM hL hV
  obtain ⟨L, hL'⟩ := hL
  rw [Feec.Domain.inner_toL2F, Feec.Domain.inner_toL2F] at e
  simp only [starRingEnd_apply, star_trivial] at e
  rw [Finset.sum_eq_single t (fun s _ hs => by simp [single1, hs]) (by simp)] at e
  rw [show ∫ y in Q (Fin n), (w t : (Fin n → ℝ) → ℝ) y * φ y = _ from by
    simpa [single1] using e]
  have hs : ∀ s : formIdx n (k : ℤ), ∫ y in Q (Fin n), (u s : (Fin n → ℝ) → ℝ) y *
      (extDerivOp ℝ n (k : ℤ)).formalAdj.apply (single1 t φ) s y =
      -∑ j ∈ t.1, (ExteriorFibre.sgn j t.1 : ℝ) * (if t.1.erase j = s.1 then
        ∫ y in Q (Fin n), (u s : (Fin n → ℝ) → ℝ) y * fderiv ℝ φ y (Pi.single j 1) else 0) := by
    intro s
    simp only [formalAdj_single1_apply, mul_neg, Finset.mul_sum]
    rw [integral_neg, integral_finsetSum _ fun j _ => ?_]
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · rw [← integral_const_mul]; congr 1; funext y; ring
      · simp
    · split_ifs
      · exact (integral_real_mul_fderiv_integrable u hφ hL' s j).const_mul _ |>.congr
          (Eventually.of_forall fun y => by simp only; ring)
      · simp
  simp only [hs, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  refine sum_ite_eq_uExt u (t.1.erase j)
    (fun v => ∫ y in Q (Fin n), (v : (Fin n → ℝ) → ℝ) y * fderiv ℝ φ y (Pi.single j 1)) ?_
  refine integral_eq_zero_of_ae ?_
  filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Q (Fin n)))] with y hy
  rw [hy]; simp

/-! ### The torus symbol on the extension -/

theorem sgn_cast (j : Fin n) (s : Finset (Fin n)) :
    ((ExteriorFibre.sgn j s : ℝ) : ℂ) = Feec.Fourier.Exterior.sgn j s := by
  simp [ExteriorFibre.sgn, Feec.Fourier.Exterior.sgn]

theorem fold_const_mul (c : Fin n → ℂ) (a : ℂ) (g : UnitAddTorus (Fin n) → ℂ) (y : Fin n → ℝ) :
    fold c (fun x => a * g x) y = a * fold c g y := by
  simp only [fold, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ε _ => by ring

theorem fderiv_re_comp {F : (Fin n → ℝ) → ℂ} {y : Fin n → ℝ} (hF : DifferentiableAt ℝ F y)
    (v : Fin n → ℝ) : fderiv ℝ (fun y => (F y).re) y v = (fderiv ℝ F y v).re := by
  have h := (Complex.reCLM.hasFDerivAt (x := F y)).comp y hF.hasFDerivAt
  rw [show (fun y => (F y).re) = Complex.reCLM ∘ F from rfl, h.fderiv]
  rfl

theorem fderiv_im_comp {F : (Fin n → ℝ) → ℂ} {y : Fin n → ℝ} (hF : DifferentiableAt ℝ F y)
    (v : Fin n → ℝ) : fderiv ℝ (fun y => (F y).im) y v = (fderiv ℝ F y v).im := by
  have h := (Complex.imCLM.hasFDerivAt (x := F y)).comp y hF.hasFDerivAt
  rw [show (fun y => (F y).im) = Complex.imCLM ∘ F from rfl, h.fderiv]
  rfl

/-- The derivatives of a folded character: `∂_j fold_c e_{-m} = -2πi m_j fold_{c'} e_{-m}`. -/
theorem fderiv_fold_mFourier (c : Fin n → ℂ) (m : Fin n → ℤ) (j : Fin n) (y : Fin n → ℝ) :
    fderiv ℝ (fold c (mFourier (-m))) y (Pi.single j 1) =
      2 * Real.pi * Complex.I * (((-m) j : ℤ) : ℂ) *
        fold (Function.update c j (-c j)) (mFourier (-m)) y := by
  rw [fderiv_fold _ (isSmooth_mFourier _)]
  have e : partialT j (mFourier (-m)) = fun x =>
      (2 * Real.pi * Complex.I * (((-m) j : ℤ) : ℂ)) * mFourier (-m) x := by
    funext x; rw [partialT_mFourier]
  rw [e, fold_const_mul]

theorem update_mul_self {c : Fin n → ℂ} (hc : ∀ j, c j * c j = 1) (j i : Fin n) :
    Function.update c j (-c j) i * Function.update c j (-c j) i = 1 := by
  by_cases h : i = j
  · subst h; simp [hc i]
  · rw [Function.update_of_ne h]; exact hc i

/-- **The torus symbol on the extension**: if `(u, w)` satisfies Green's identity `GreenFor`,
then `d_ξ (Jf u)(m) = (Jf w)(m)` at every frequency `m` (`ξ = 2πm`). -/
theorem coeff_d_of_greenFor {rel : Bool} {k : ℕ} {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    {w : L2F ℝ (Q (Fin n)) (formIdx n ((k : ℤ) + 1))} (h : GreenFor rel k u w)
    (m : Fin n → ℤ) :
    (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (Feec.Fourier.Torus.freq m)
        ((Jf rel k u : (Fin n → ℤ) → Form ℂ (Fin n) k) m) =
      (Jf rel (k + 1) w : (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m := by
  refine PiLp.ext fun t' => ?_
  set e := mFourier (-m)
  have hc := pcF_mul_self (n := n) rel
  set t : formIdx n ((k : ℤ) + 1) := ⟨t'.1, by exact_mod_cast t'.2⟩
  set F := fold (pcF rel t'.1) e
  have hFs : ContDiff ℝ (⊤ : ℕ∞) F := contDiff_fold _ (isSmooth_mFourier _)
  have hFd : Differentiable ℝ F := hFs.differentiable (by simp)
  have hFc : Continuous F := hFs.continuous
  set B := 2 ^ Fintype.card (Fin n) * ‖e‖
  have hFb : ∀ y, ‖F y‖ ≤ B := norm_fold_le (hc _) e
  set a : Fin n → ℂ := fun i => 2 * Real.pi * Complex.I * (((-m) i : ℤ) : ℂ)
  set L := ∑ i, ‖a i‖ * B
  have hdFb : ∀ j y, ‖fderiv ℝ F y (Pi.single j 1)‖ ≤ L := by
    intro j y
    rw [fderiv_fold_mFourier, norm_mul]
    calc ‖a j‖ * ‖fold (Function.update (pcF rel t'.1) j (-pcF rel t'.1 j)) e y‖ ≤ ‖a j‖ * B :=
          mul_le_mul_of_nonneg_left (norm_fold_le (update_mul_self (hc _) j) e y) (norm_nonneg _)
      _ ≤ L := Finset.single_le_sum (f := fun i => ‖a i‖ * B)
          (fun i _ => mul_nonneg (norm_nonneg _) (by positivity)) (Finset.mem_univ j)
  have hV : ∀ (g : ℂ → ℝ), g 0 = 0 → rel = false → ∀ j ∈ t.1, ∀ y : Fin n → ℝ,
      (y j = 0 ∨ y j = 1 / 2) → g (F y) = 0 := by
    intro g hg hrel j hj y hy
    subst hrel
    have hj' : j ∈ t'.1 := hj
    have h0 : F y = 0 := fold_eq_zero_of_face (c := pcF false t'.1) (hc _) (j := j)
      (by simp [pcF, DeRham.parSign, DeRham.reflSign, hj']) e hy
    rw [h0, hg]
  have hre := h t (fun y => (F y).re) (Complex.reCLM.contDiff.comp hFs)
    ⟨B, fun y => (Complex.abs_re_le_norm _).trans (hFb y)⟩
    ⟨L, fun j y => by rw [fderiv_re_comp (hFd y)]; exact (Complex.abs_re_le_norm _).trans (hdFb j y)⟩
    (hV Complex.re Complex.zero_re)
  have him := h t (fun y => (F y).im) (Complex.imCLM.contDiff.comp hFs)
    ⟨B, fun y => (Complex.abs_im_le_norm _).trans (hFb y)⟩
    ⟨L, fun j y => by rw [fderiv_im_comp (hFd y)]; exact (Complex.abs_im_le_norm _).trans (hdFb j y)⟩
    (hV Complex.im Complex.zero_im)
  have hj : ∀ j, ∫ y in Q (Fin n), (((uExt u (t'.1.erase j) : (Fin n → ℝ) → ℝ) y : ℝ) : ℂ) *
      fderiv ℝ F y (Pi.single j 1) =
      ((∫ y in Q (Fin n), (uExt u (t'.1.erase j) : (Fin n → ℝ) → ℝ) y *
          fderiv ℝ (fun y => (F y).re) y (Pi.single j 1) : ℝ) : ℂ) +
        Complex.I * ((∫ y in Q (Fin n), (uExt u (t'.1.erase j) : (Fin n → ℝ) → ℝ) y *
          fderiv ℝ (fun y => (F y).im) y (Pi.single j 1) : ℝ) : ℂ) := by
    intro j
    rw [integral_ofReal_mul_eq _ ((hFs.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hdFb j)]
    simp only [fderiv_re_comp (hFd _), fderiv_im_comp (hFd _)]
  have hG : ∫ y in Q (Fin n), (((w t : (Fin n → ℝ) → ℝ) y : ℝ) : ℂ) * F y =
      -∑ j ∈ t'.1, ((ExteriorFibre.sgn j t'.1 : ℝ) : ℂ) *
        ∫ y in Q (Fin n), (((uExt u (t'.1.erase j) : (Fin n → ℝ) → ℝ) y : ℝ) : ℂ) *
          fderiv ℝ F y (Pi.single j 1) := by
    rw [integral_ofReal_mul_eq (w t) hFc hFb]
    change ((∫ y in Q (Fin n), (w t : (Fin n → ℝ) → ℝ) y * (fun y => (F y).re) y : ℝ) : ℂ) +
      Complex.I * ((∫ y in Q (Fin n), (w t : (Fin n → ℝ) → ℝ) y * (fun y => (F y).im) y : ℝ) : ℂ) = _
    have ht : (t : Finset (Fin n)) = t'.1 := rfl
    rw [hre, him, ht]
    simp only [hj]
    push_cast
    simp only [← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [deRham_m_apply, coeff_Jf]
  change _ = ∫ y in Q (Fin n), (((w t : (Fin n → ℝ) → ℝ) y : ℝ) : ℂ) * F y
  rw [hG, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hd : ∀ y, fderiv ℝ F y (Pi.single j 1) = a j * fold (pcF rel (t'.1.erase j)) e y := by
    intro y
    rw [fderiv_fold_mFourier, update_pcF_erase rel hj]
  simp only [hd]
  have hi : ∫ y in Q (Fin n), (((uExt u (t'.1.erase j) : (Fin n → ℝ) → ℝ) y : ℝ) : ℂ) *
      (a j * fold (pcF rel (t'.1.erase j)) e y) =
      a j * Feec.Fourier.Exterior.ext k ((Jf rel k u : (Fin n → ℤ) → Form ℂ (Fin n) k) m)
        (t'.1.erase j) := by
    rw [ext_Jf, ← integral_const_mul]
    congr 1; funext y; ring
  rw [hi, sgn_cast, Feec.Fourier.Torus.freq_apply]
  simp only [a, Pi.neg_apply, Int.cast_neg]
  push_cast
  ring

/-! ### Green's identity on `H̊Λ(Q)` and on `HΛ(Q)` -/

/-- **Green's identity on `D(d_min)`** against every smooth form: the boundary term vanishes by
the boundary condition of `u`. -/
theorem greenFor_minimal (rel : Bool) (k : ℕ)
    (u : ((extDerivOp ℝ n (k : ℤ)).minimal (Q (Fin n))).domain) :
    GreenFor rel k u ((extDerivOp ℝ n (k : ℤ)).minimal (Q (Fin n)) u) :=
  greenFor_of_inner fun t φ hφ _ _ _ =>
    (extDerivOp ℝ n (k : ℤ)).minimal_green isOpen_Q (Feec.Domain.extDerivOp_isOrderLE (k : ℤ)) u
      (fun s => (contDiff_single1 t hφ s).of_le (by exact_mod_cast le_top))
      (memLp_single1 t hφ) (memLp_formalAdj_single1 t hφ)

theorem chi_mul_single1 {k : ℤ} (t : formIdx n (k + 1)) (φ : (Fin n → ℝ) → ℝ) (m : ℕ) :
    (fun p y => chi m y * single1 t φ p y) = single1 t fun y => chi m y * φ y := by
  funext p y
  by_cases h : p = t
  · subst h; simp [single1]
  · simp [single1, h]

/-- **One-component forms with vanishing normal trace lie in `D(dᵗ_min)`**: if `φ = 0` on the
faces `{y_j ∈ {0, ½}}` for `j ∈ t`, then `(φ dx_t, dᵗ(φ dx_t))` lies in the closure of the graph
of `dᵗ` on test forms (cut-off argument). -/
theorem mem_closure_formalAdj_single1 {k : ℤ} (t : formIdx n (k + 1)) {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) {L : ℝ}
    (hL : ∀ j y, |fderiv ℝ φ y (Pi.single j 1)| ≤ L)
    (hV : ∀ j ∈ t.1, ∀ y : Fin n → ℝ, (y j = 0 ∨ y j = 1 / 2) → φ y = 0) :
    (toL2F (memLp_single1 t hφ), toL2F (memLp_formalAdj_single1 t hφ)) ∈
      closure ((extDerivOp ℝ n k).formalAdj.testGraph (Q (Fin n)) :
        Set (L2F ℝ (Q (Fin n)) (formIdx n (k + 1)) × L2F ℝ (Q (Fin n)) (formIdx n k))) := by
  obtain ⟨M₀, -, hM₀⟩ := RowWise.exists_bound_deriv_smoothTransition
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  refine mem_closure_testGraph_of_cutoff _ (contDiff_single1 t hφ) (M := M)
    (fun p y _ => ?_) _ _ (K := ∑ _j : Fin n, (L + 4 * M₀ * L)) fun m q y hy => ?_
  · by_cases h : p = t
    · subst h; simpa [single1] using hM y
    · simp [single1, h, hM0]
  · rw [chi_mul_single1, formalAdj_single1_apply, abs_neg]
    have hχd : Differentiable ℝ (chi (d := Fin n) m) := (contDiff_chi m).differentiable (by simp)
    have hterm : ∀ j ∈ t.1, |(if t.1.erase j = q.1 then (ExteriorFibre.sgn j t.1 : ℝ) *
        fderiv ℝ (fun y => chi m y * φ y) y (Pi.single j 1) else 0)| ≤ L + 4 * M₀ * L := by
      intro j hj
      split_ifs
      · rw [abs_mul, show |(ExteriorFibre.sgn j t.1 : ℝ)| = 1 by simp [ExteriorFibre.sgn], one_mul,
          fderiv_fun_mul (hχd y) (hφd y)]
        simp only [add_apply, smul_apply, smul_eq_mul]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]
          calc |chi m y| * |fderiv ℝ φ y (Pi.single j 1)| ≤ 1 * L :=
                mul_le_mul (abs_chi_le_one m y) (hL j y) (abs_nonneg _) zero_le_one
            _ = L := one_mul L
        · rw [mul_comm]
          exact abs_fderiv_chi_mul_le hM₀ m hφd (hL j) (hV j hj) hy
      · have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL j y)
        have hM00 : 0 ≤ M₀ := (abs_nonneg _).trans (hM₀ 0)
        simp only [abs_zero]; positivity
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => ?_
    have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL j y)
    have hM00 : 0 ≤ M₀ := (abs_nonneg _).trans (hM₀ 0)
    positivity

/-- **Green's identity on `D(d_max)`** against the smooth forms with vanishing normal trace:
these lie in `D(dᵗ_min)` (`mem_closure_formalAdj_single1`) and `d_max = (dᵗ_min)†`. -/
theorem greenFor_maximal (k : ℕ)
    (u : ((extDerivOp ℝ n (k : ℤ)).maximal (Q (Fin n))).domain) :
    GreenFor false k u ((extDerivOp ℝ n (k : ℤ)).maximal (Q (Fin n)) u) := by
  refine greenFor_of_inner fun t φ hφ ⟨M, hM⟩ ⟨L, hL⟩ hV => ?_
  have hcl := mem_closure_formalAdj_single1 t hφ hM hL (hV rfl)
  rw [← Submodule.topologicalClosure_coe, SetLike.mem_coe,
    ← (extDerivOp ℝ n (k : ℤ)).formalAdj.minimal_graph isOpen_Q] at hcl
  obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff _).1 hcl
  have := LinearPMap.adjoint_isFormalAdjoint
    ((extDerivOp ℝ n (k : ℤ)).formalAdj.dense_minimal_domain isOpen_Q) u x
  change ⟪(extDerivOp ℝ n (k : ℤ)).maximal (Q (Fin n)) u, (x : L2F ℝ (Q (Fin n)) _)⟫_ℝ =
    ⟪(u : L2F ℝ (Q (Fin n)) _), (extDerivOp ℝ n (k : ℤ)).formalAdj.minimal (Q (Fin n)) x⟫_ℝ at this
  rw [hx1, hx2] at this
  exact this

/-- **`d_ξ (Jf u) = Jf (d_min u)`** fibrewise, for `u ∈ H̊Λᵏ(Q)` (any class). -/
theorem coeff_d_minimal (rel : Bool) (k : ℕ)
    (u : ((extDerivOp ℝ n (k : ℤ)).minimal (Q (Fin n))).domain) (m : Fin n → ℤ) :
    (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (Feec.Fourier.Torus.freq m)
        ((Jf rel k u : (Fin n → ℤ) → Form ℂ (Fin n) k) m) =
      (Jf rel (k + 1) ((extDerivOp ℝ n (k : ℤ)).minimal (Q (Fin n)) u) :
        (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m :=
  coeff_d_of_greenFor (greenFor_minimal rel k u) m

/-- **`d_ξ (Jf u) = Jf (d_max u)`** fibrewise, for `u ∈ HΛᵏ(Q)` (absolute class). -/
theorem coeff_d_maximal (k : ℕ) (u : ((extDerivOp ℝ n (k : ℤ)).maximal (Q (Fin n))).domain)
    (m : Fin n → ℤ) :
    (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (Feec.Fourier.Torus.freq m)
        ((Jf false k u : (Fin n → ℤ) → Form ℂ (Fin n) k) m) =
      (Jf false (k + 1) ((extDerivOp ℝ n (k : ℤ)).maximal (Q (Fin n)) u) :
        (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m :=
  coeff_d_of_greenFor (greenFor_maximal k u) m

end Feec.Models.Cube.DeRhamIdent
