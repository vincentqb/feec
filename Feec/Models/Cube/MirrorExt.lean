module

public import Feec.Models.Cube.Basic
public import Feec.Fourier.Torus
public import Feec.Fourier.Reality
public import Feec.ForMathlib.Lp.ProdEquiv

/-!
# Extension by parity of fields on the cube `Q = (0, ½)ᵈ`

The cube `Q = (0, ½)ᵈ` is a fundamental domain of the reflections `x_j ↦ -x_j` of the torus
`𝕋ᵈ = ℝᵈ/ℤᵈ`. For a sign vector `c ∈ {±1}ᵈ`, the functions on `𝕋ᵈ` with parity `c_j` in each
variable `x_j` are the `L²` functions whose Fourier coefficients satisfy
`f̂(…, -n_j, …) = c_j f̂(n)` (`paritySub c`). Restriction to `Q` is, on these, a scaled isometry
(`‖f‖² = 2ᵈ ‖f|_Q‖²`, `Feec.Models.Cube.Geometry.norm_sq_eq_two_pow`) onto `L²(Q)` (its range is
closed and contains the extensions of all test functions, `Feec.Models.Cube.Geometry.ext`), so it
has an inverse: the **extension by parity** `extL2 c : L²(Q) → L²(𝕋ᵈ)`. This is the method of
images: a homogeneous condition "`f = 0` on the faces `x_j ∈ {0, ½}`" is imposed by extending `f`
oddly in `x_j`, a Neumann-type condition by extending evenly.

For fields `L²(Q; ℂᴾ)` with a parity vector `c p` per component, `extF c` extends componentwise
and takes Fourier coefficients (`Feec.Fourier.Torus.fieldFourier`): a scaled isometric embedding
`L²(Q; ℂᴾ) → ℓ²(ℤᵈ; ℂᴾ)` onto the coefficient sequences with the parities `c`
(`range_extF`). These are the embeddings of the mirror cube complexes into the torus complexes
(`Feec.Models.Cube.Mirror`, `MirrorSym`, `MirrorBGG`).

## Main definitions

* `flipAt k`: the frequency reflection `n ↦ (…, -n_k, …)`.
* `paritySub c`, `extL2 c`: the parity subspace of `L²(𝕋ᵈ)` and the extension `L²(Q) → L²(𝕋ᵈ)`.
* `fieldParity c`, `extF c`: the same for fields, on the Fourier side.

## Main results

* `resQ_extL2`, `extL2_resQ`, `inner_extL2` (`⟪ext f, ext g⟫ = 2ᵈ ⟪f, g⟫`), `range_extL2`,
  `extL2_toL2` (on test functions `extL2` is the classical extension `Geometry.ext`).
* `inner_extF`, `range_extF`, `resQF_extF`, `extF_testField`.

## References

* [QuennevilleBelair2015], §4.10
* [Brezis2011], §9.2 (extension by reflection)
-/

open scoped InnerProductSpace ENNReal
open Set MeasureTheory Filter UnitAddTorus Feec.Fourier.TorusWeak

@[expose] public noncomputable section

namespace Feec.Models.Cube.MirrorExt

open Geometry

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Fourier.TorusWeak`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- `L²(𝕋ᵈ)`. -/
abbrev T2 (d : Type*) [Fintype d] := Lp ℂ 2 (volume : Measure (UnitAddTorus d))

/-! ### Frequency reflections -/

/-- The reflection `n ↦ (…, -n_k, …)` of the frequencies (`Geometry.flipB` for one variable). -/
def flipAt (k : d) : (d → ℤ) → (d → ℤ) := flipB fun j => decide (j = k)

omit [Fintype d] in
theorem flipAt_apply (k : d) (n : d → ℤ) (j : d) :
    flipAt k n j = if j = k then -n j else n j := by
  simp [flipAt, flipB]

omit [Fintype d] in
@[simp] theorem flipAt_flipAt (k : d) (n : d → ℤ) : flipAt k (flipAt k n) = n :=
  flipB_flipB _ n

omit [Fintype d] in
theorem flipAt_comm (k l : d) (n : d → ℤ) : flipAt k (flipAt l n) = flipAt l (flipAt k n) := by
  funext j; simp only [flipAt_apply]; split_ifs <;> simp

/-- The Bool vector of a finite set of variables. -/
def boolOf (s : Finset d) : d → Bool := fun j => decide (j ∈ s)

omit [Fintype d] in
theorem flipB_boolOf_insert {k : d} {s : Finset d} (hk : k ∉ s) (n : d → ℤ) :
    flipB (boolOf (insert k s)) n = flipAt k (flipB (boolOf s) n) := by
  funext j
  by_cases hj : j = k
  · subst hj; simp [flipB, boolOf, flipAt_apply, hk]
  · simp [flipB, boolOf, flipAt_apply, hj]

theorem sign_boolOf_insert (c : d → ℂ) {k : d} {s : Finset d} (hk : k ∉ s) :
    sign c (boolOf (insert k s)) = c k * sign c (boolOf s) := by
  simp only [sign, boolOf, Finset.mem_insert, decide_eq_true_eq]
  rw [← Finset.prod_filter, ← Finset.prod_filter,
    show (Finset.univ.filter fun j => j = k ∨ j ∈ s) = insert k (Finset.univ.filter (· ∈ s)) by
      ext j; simp, Finset.prod_insert (by simpa using hk)]

omit [Fintype d] in
theorem boolOf_eq (ε : d → Bool) [Fintype d] : boolOf (Finset.univ.filter fun j => ε j) = ε := by
  funext j; simp [boolOf]

/-! ### Fourier coefficients as functionals -/

/-- The `n`-th Fourier coefficient as a continuous linear functional on `L²(𝕋ᵈ)`. -/
def coeffCLM (n : d → ℤ) : T2 d →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (E := fun _ : d → ℤ => ℂ) (p := 2) n).comp
    (mFourierBasis (d := d)).repr.toContinuousLinearEquiv.toContinuousLinearMap

omit [DecidableEq d] in
theorem coeffCLM_apply (n : d → ℤ) (f : T2 d) :
    coeffCLM n f = mFourierCoeff (f : UnitAddTorus d → ℂ) n :=
  mFourierBasis_repr f n

/-! ### Parity functions -/

/-- **The functions on `𝕋ᵈ` with parity `c`**: `f̂(flip_k n) = c_k f̂(n)` for every variable `k`
(for `c_k = ±1`: `f` even or odd in `x_k`). -/
def paritySub (c : d → ℂ) : Submodule ℂ (T2 d) :=
  ⨅ k, ⨅ n, LinearMap.ker ((coeffCLM (flipAt k n) - c k • coeffCLM n : T2 d →L[ℂ] ℂ) :
    T2 d →ₗ[ℂ] ℂ)

theorem mem_paritySub {c : d → ℂ} {f : T2 d} :
    f ∈ paritySub c ↔ ∀ k n, mFourierCoeff (f : UnitAddTorus d → ℂ) (flipAt k n) =
      c k * mFourierCoeff (f : UnitAddTorus d → ℂ) n := by
  simp only [paritySub, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sub_apply, smul_apply, coeffCLM_apply, smul_eq_mul,
    sub_eq_zero]

theorem isClosed_paritySub (c : d → ℂ) : IsClosed (paritySub c : Set (T2 d)) := by
  have e : (paritySub c : Set (T2 d)) =
      ⋂ k, ⋂ n, {f | coeffCLM (flipAt k n) f = c k * coeffCLM n f} := by
    ext f; simp [mem_paritySub, coeffCLM_apply]
  rw [e]
  exact isClosed_iInter fun k => isClosed_iInter fun n =>
    isClosed_eq (coeffCLM _).continuous (continuous_const.mul (coeffCLM _).continuous)

instance (c : d → ℂ) : CompleteSpace (paritySub c) := (isClosed_paritySub c).completeSpace_coe

/-- Parity under one reflection gives parity under every reflection `R_ε`, with the sign
`sign c ε = ∏_{ε_j} c_j`. -/
theorem mFourierCoeff_flipB {c : d → ℂ} {f : T2 d} (hf : f ∈ paritySub c) (ε : d → Bool)
    (n : d → ℤ) : mFourierCoeff (f : UnitAddTorus d → ℂ) (flipB ε n) =
      sign c ε * mFourierCoeff (f : UnitAddTorus d → ℂ) n := by
  rw [← boolOf_eq ε]
  induction (Finset.univ.filter fun j => ε j) using Finset.induction_on generalizing n with
  | empty =>
    have e : flipB (boolOf (∅ : Finset d)) n = n := funext fun j => by simp [flipB, boolOf]
    simp [e, sign, boolOf]
  | insert k s hk ih =>
    rw [flipB_boolOf_insert hk, mem_paritySub.1 hf, ih, sign_boolOf_insert c hk, mul_assoc]

/-- A parity function has `|f ∘ R_ε| = |f|` a.e. -/
theorem norm_comp_reflB_of_mem {c : d → ℂ} (hc : ∀ j, c j * c j = 1) {f : T2 d}
    (hf : f ∈ paritySub c) (ε : d → Bool) :
    (fun x => ‖(f : UnitAddTorus d → ℂ) (reflB ε x)‖) =ᵐ[volume]
      fun x => ‖(f : UnitAddTorus d → ℂ) x‖ :=
  norm_comp_reflB_ae (norm_sign hc ε) (mFourierCoeff_flipB hf ε)

/-- **The norm of a parity function**: `‖f‖² = 2ᵈ ‖f|_Q‖²`. -/
theorem norm_sq_of_mem {c : d → ℂ} (hc : ∀ j, c j * c j = 1) {f : T2 d}
    (hf : f ∈ paritySub c) : ‖f‖ ^ 2 = 2 ^ Fintype.card d * ‖resQ f‖ ^ 2 :=
  norm_sq_eq_two_pow (norm_comp_reflB_of_mem hc hf)

/-- The classical extension of a test function has the parity `c`. -/
theorem toL2_ext_mem {c : d → ℂ} (hc : ∀ j, c j * c j = 1) {Φ : (d → ℝ) → ℂ}
    (hΦ : Domain.IsTest (Q d) Φ) : toL2 (continuous_ext c hΦ) ∈ paritySub c := by
  refine mem_paritySub.2 fun k n => ?_
  rw [mFourierCoeff_toL2, mFourierCoeff_toL2, flipAt, ← mFourierCoeff_comp_reflB]
  have e : (fun x => ext c Φ (reflB (fun j => decide (j = k)) x)) =
      fun x => c k * ext c Φ x := by
    funext x
    rw [ext_reflB hc]
    congr 1
    simp only [sign, decide_eq_true_eq]
    rw [Finset.prod_ite_eq' Finset.univ k]
    simp
  rw [e]
  simp only [mFourierCoeff, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

/-! ### Restriction to `Q` and its inverse -/

variable {c : d → ℂ} (hc : ∀ j, c j * c j = 1)

/-- Restriction to `Q` on the parity functions. -/
def resP (c : d → ℂ) : paritySub c →L[ℂ] Domain.L2 ℂ (Q d) := resQ.comp (paritySub c).subtypeL

theorem resP_apply (f : paritySub c) : resP c f = resQ (f : T2 d) := rfl

include hc

theorem norm_resP (f : paritySub c) :
    ‖(f : T2 d)‖ = Real.sqrt (2 ^ Fintype.card d) * ‖resP c f‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (f : T2 d)), norm_sq_of_mem hc f.2,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  rfl

theorem injective_resP : Function.Injective (resP c) := by
  intro f g h
  have := norm_resP hc (f - g)
  rw [_root_.map_sub, h, sub_self, norm_zero, mul_zero] at this
  exact sub_eq_zero.1 (Subtype.ext (by simpa using norm_eq_zero.1 this))

theorem isClosed_range_resP : IsClosed (Set.range (resP c)) := by
  have hb : ∀ f, ‖f‖ ≤ (Real.toNNReal (Real.sqrt (2 ^ Fintype.card d)) : ℝ) * ‖resP c f‖ :=
    fun f => by
      rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _), ← norm_resP hc]
      rfl
  exact ((resP c).antilipschitz_of_bound hb).isClosed_range (resP c).uniformContinuous

theorem surjective_resP : Function.Surjective (resP c) := by
  have hR : (LinearMap.range (resP c : paritySub c →ₗ[ℂ] Domain.L2 ℂ (Q d)) :
      Set (Domain.L2 ℂ (Q d))) = Set.range (resP c) := LinearMap.coe_range _
  have hcl : IsClosed (LinearMap.range (resP c : paritySub c →ₗ[ℂ] Domain.L2 ℂ (Q d)) :
      Set (Domain.L2 ℂ (Q d))) := hR ▸ isClosed_range_resP hc
  have htop : LinearMap.range (resP c : paritySub c →ₗ[ℂ] Domain.L2 ℂ (Q d)) = ⊤ := by
    have : CompleteSpace (LinearMap.range (resP c : paritySub c →ₗ[ℂ] Domain.L2 ℂ (Q d))) :=
      hcl.completeSpace_coe
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro v hv
    refine Domain.L2.eq_zero_of_forall_inner_toL2 isOpen_Q v fun Φ hΦ => ?_
    have hm : Domain.toL2 hΦ ∈ LinearMap.range (resP c : paritySub c →ₗ[ℂ] Domain.L2 ℂ (Q d)) :=
      ⟨⟨_, toL2_ext_mem hc hΦ⟩, resQ_toL2_ext c hΦ⟩
    rw [← inner_conj_symm, Submodule.inner_right_of_mem_orthogonal hm hv, map_zero]
  intro g
  have : g ∈ LinearMap.range (resP c : paritySub c →ₗ[ℂ] Domain.L2 ℂ (Q d)) := htop ▸ trivial
  obtain ⟨f, hf⟩ := this
  exact ⟨f, hf⟩

/-- Restriction to `Q` is an isomorphism from the parity functions onto `L²(Q)`. -/
def resEquiv : paritySub c ≃L[ℂ] Domain.L2 ℂ (Q d) :=
  ContinuousLinearEquiv.ofBijective (resP c) (LinearMap.ker_eq_bot.2 (injective_resP hc))
    (LinearMap.range_eq_top.2 (surjective_resP hc))

@[simp] theorem resEquiv_apply (f : paritySub c) : resEquiv hc f = resQ (f : T2 d) := rfl

/-- **The extension by parity** `L²(Q) → L²(𝕋ᵈ)`: the parity function with parity `c`
restricting to the given function on `Q`. -/
def extL2 : Domain.L2 ℂ (Q d) →L[ℂ] T2 d :=
  (paritySub c).subtypeL.comp (resEquiv hc).symm.toContinuousLinearMap

theorem extL2_mem (g : Domain.L2 ℂ (Q d)) : extL2 hc g ∈ paritySub c :=
  ((resEquiv hc).symm g).2

/-- **The extension restricts back**: `(ext g)|_Q = g`. -/
theorem resQ_extL2 (g : Domain.L2 ℂ (Q d)) : resQ (extL2 hc g) = g :=
  (resEquiv hc).apply_symm_apply g

/-- **A parity function is the extension of its restriction.** -/
theorem extL2_resQ {f : T2 d} (hf : f ∈ paritySub c) : extL2 hc (resQ f) = f := by
  change (((resEquiv hc).symm (resEquiv hc ⟨f, hf⟩) : paritySub c) : T2 d) = f
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem eq_extL2_iff {f : T2 d} {g : Domain.L2 ℂ (Q d)} :
    f = extL2 hc g ↔ f ∈ paritySub c ∧ resQ f = g := by
  constructor
  · rintro rfl; exact ⟨extL2_mem hc g, resQ_extL2 hc g⟩
  · rintro ⟨hf, rfl⟩; exact (extL2_resQ hc hf).symm

theorem range_extL2 : LinearMap.range (extL2 hc : Domain.L2 ℂ (Q d) →ₗ[ℂ] T2 d) = paritySub c := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩; exact extL2_mem hc g
  · intro hf; exact ⟨resQ f, extL2_resQ hc hf⟩

theorem norm_sq_extL2 (g : Domain.L2 ℂ (Q d)) :
    ‖extL2 hc g‖ ^ 2 = 2 ^ Fintype.card d * ‖g‖ ^ 2 := by
  rw [norm_sq_of_mem hc (extL2_mem hc g), resQ_extL2]

theorem norm_extL2 (g : Domain.L2 ℂ (Q d)) :
    ‖extL2 hc g‖ = Real.sqrt (2 ^ Fintype.card d) * ‖g‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (extL2 hc g)), norm_sq_extL2, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (norm_nonneg _)]

/-- **The extension multiplies inner products by `2ᵈ`.** -/
theorem inner_extL2 (f g : Domain.L2 ℂ (Q d)) :
    ⟪extL2 hc f, extL2 hc g⟫_ℂ = ((2 ^ Fintype.card d : ℝ) : ℂ) * ⟪f, g⟫_ℂ := by
  set r : ℝ := Real.sqrt (2 ^ Fintype.card d)
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  let L : Domain.L2 ℂ (Q d) →ₗᵢ[ℂ] T2 d :=
    { toLinearMap := ((r⁻¹ : ℝ) : ℂ) • (extL2 hc : Domain.L2 ℂ (Q d) →ₗ[ℂ] T2 d)
      norm_map' := fun x => by
        simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, norm_smul,
          Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hr, norm_extL2]
        rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul] }
  have h := L.inner_map_map f g
  have e : ∀ x, extL2 hc x = (r : ℂ) • L x := fun x => by
    change extL2 hc x = (r : ℂ) • (((r⁻¹ : ℝ) : ℂ) • extL2 hc x)
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
  rw [e f, e g, inner_smul_left, inner_smul_right, h, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]

/-- **On test functions the extension is the classical one** (`Geometry.ext`). -/
theorem extL2_toL2 {Φ : (d → ℝ) → ℂ} (hΦ : Domain.IsTest (Q d) Φ) :
    extL2 hc (Domain.toL2 hΦ) = toL2 (continuous_ext c hΦ) :=
  ((eq_extL2_iff hc).2 ⟨toL2_ext_mem hc hΦ, resQ_toL2_ext c hΦ⟩).symm

omit hc

/-! ### Fields -/

variable {P : Type*} [Fintype P] {c : P → d → ℂ} (hc : ∀ p j, c p j * c p j = 1)

/-- The componentwise extension by parity of fields, `(ext u)_p = extL2 (c p) u_p`. -/
def extPi : Domain.L2F ℂ (Q d) P →L[ℂ] Field d P where
  toFun u := WithLp.toLp 2 fun p => extL2 (hc p) (u p)
  map_add' u v := by ext p; simp
  map_smul' z u := by ext p; simp
  cont := (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p =>
    (extL2 (hc p)).continuous.comp (PiLp.continuous_apply 2 _ p))

omit [Fintype P] in
@[simp] theorem extPi_apply (u : Domain.L2F ℂ (Q d) P) (p : P) :
    extPi hc u p = extL2 (hc p) (u p) :=
  rfl

omit [Fintype P] in
theorem resQF_extPi (u : Domain.L2F ℂ (Q d) P) : resQF (extPi hc u) = u := by
  ext1 p; rw [resQF_apply, extPi_apply, resQ_extL2]

theorem inner_extPi (u v : Domain.L2F ℂ (Q d) P) :
    ⟪extPi hc u, extPi hc v⟫_ℂ = ((2 ^ Fintype.card d : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => inner_extL2 (hc p) _ _

/-- **The extension by parity of fields, on the Fourier side**: `L²(Q; ℂᴾ) → ℓ²(ℤᵈ; ℂᴾ)`. -/
def extF : Domain.L2F ℂ (Q d) P →L[ℂ] Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (d → ℤ)) :=
  (Fourier.Torus.fieldFourier d P).toContinuousLinearEquiv.toContinuousLinearMap.comp (extPi hc)

theorem extF_apply (u : Domain.L2F ℂ (Q d) P) :
    extF hc u = Fourier.Torus.fieldFourier d P (extPi hc u) := rfl

theorem fieldFourier_symm_extF (u : Domain.L2F ℂ (Q d) P) :
    (Fourier.Torus.fieldFourier d P).symm (extF hc u) = extPi hc u :=
  (Fourier.Torus.fieldFourier d P).symm_apply_apply _

theorem extF_coeff (u : Domain.L2F ℂ (Q d) P) (n : d → ℤ) (p : P) :
    (extF hc u : (d → ℤ) → EuclideanSpace ℂ P) n p =
      mFourierCoeff (extL2 (hc p) (u p) : UnitAddTorus d → ℂ) n :=
  Fourier.Torus.fieldFourier_apply _ n p

/-- **The extension multiplies inner products by `2ᵈ`.** -/
theorem inner_extF (u v : Domain.L2F ℂ (Q d) P) :
    ⟪extF hc u, extF hc v⟫_ℂ = ((2 ^ Fintype.card d : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  rw [extF_apply, extF_apply, LinearIsometryEquiv.inner_map_map, inner_extPi]

theorem resQF_symm_extF (u : Domain.L2F ℂ (Q d) P) :
    resQF ((Fourier.Torus.fieldFourier d P).symm (extF hc u)) = u := by
  rw [fieldFourier_symm_extF, resQF_extPi]

theorem injective_extF : Function.Injective (extF hc) := fun u v h => by
  rw [← resQF_symm_extF hc u, h, resQF_symm_extF]

omit hc in
variable (c) in
/-- **Coefficient sequences with the parities `c`**: `û(flip_k n)_p = c_{p,k} û(n)_p`. -/
def fieldParity : Submodule ℂ (Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (d → ℤ))) where
  carrier := {w | ∀ p, (Fourier.Torus.fieldFourier d P).symm w p ∈ paritySub (c p)}
  zero_mem' p := by simp
  add_mem' {v w} hv hw p := by
    simp only [_root_.map_add, PiLp.add_apply]
    exact Submodule.add_mem _ (hv p) (hw p)
  smul_mem' z w hw p := by
    simp only [_root_.map_smul, PiLp.smul_apply]
    exact Submodule.smul_mem _ z (hw p)

omit hc [DecidableEq d] in
theorem coeff_fieldFourier_symm (w : Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (d → ℤ)))
    (n : d → ℤ) (p : P) :
    mFourierCoeff ((Fourier.Torus.fieldFourier d P).symm w p : UnitAddTorus d → ℂ) n =
      (w : (d → ℤ) → EuclideanSpace ℂ P) n p := by
  rw [← Fourier.Torus.fieldFourier_apply, LinearIsometryEquiv.apply_symm_apply]

omit hc in
theorem mem_fieldParity_iff {w : Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (d → ℤ))} :
    w ∈ fieldParity c ↔ ∀ k n p, (w : (d → ℤ) → EuclideanSpace ℂ P) (flipAt k n) p =
      c p k * (w : (d → ℤ) → EuclideanSpace ℂ P) n p := by
  change (∀ p, _ ∈ paritySub (c p)) ↔ _
  simp only [mem_paritySub, coeff_fieldFourier_symm]
  exact ⟨fun h k n p => h p k n, fun h p k n => h k n p⟩

theorem extF_mem (u : Domain.L2F ℂ (Q d) P) : extF hc u ∈ fieldParity c := fun p => by
  rw [fieldFourier_symm_extF, extPi_apply]; exact extL2_mem (hc p) _

/-- **A coefficient sequence with the parities `c` is the extension of its restriction.** -/
theorem extF_resQF {w : Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (d → ℤ))}
    (hw : w ∈ fieldParity c) :
    extF hc (resQF ((Fourier.Torus.fieldFourier d P).symm w)) = w := by
  rw [extF_apply, ← LinearIsometryEquiv.eq_symm_apply]
  ext1 p
  rw [extPi_apply, resQF_apply]
  exact extL2_resQ (hc p) (hw p)

/-- **The range of the extension is the parity subspace.** -/
theorem range_extF : LinearMap.range (extF hc : Domain.L2F ℂ (Q d) P →ₗ[ℂ] _) = fieldParity c := by
  ext w
  constructor
  · rintro ⟨u, rfl⟩; exact extF_mem hc u
  · intro hw; exact ⟨_, extF_resQF hc hw⟩

omit [Fintype P] in
/-- **On test fields the extension is the classical one.** -/
theorem extPi_testField {Φ : P → (d → ℝ) → ℂ} (hΦ : Domain.IsTestField (Q d) Φ) :
    extPi hc (Domain.testField hΦ) = WithLp.toLp 2 fun p => toL2 (continuous_ext (c p) (hΦ p)) := by
  ext1 p
  rw [extPi_apply]
  exact extL2_toL2 (hc p) (hΦ p)

theorem extF_testField_coeff {Φ : P → (d → ℝ) → ℂ} (hΦ : Domain.IsTestField (Q d) Φ)
    (n : d → ℤ) (p : P) :
    (extF hc (Domain.testField hΦ) : (d → ℤ) → EuclideanSpace ℂ P) n p =
      mFourierCoeff (ext (c p) (Φ p)) n := by
  rw [extF_coeff, show extL2 (hc p) (Domain.testField hΦ p) =
      toL2 (continuous_ext (c p) (hΦ p)) from
    extL2_toL2 (hc p) (hΦ p), mFourierCoeff_toL2]

/-! ### Fourier coefficients of extensions of test functions -/

omit [Fintype P] in
/-- `ext c` is linear in the test function. -/
theorem ext_sum (c : d → ℂ) {ι : Type*} (s : Finset ι) (a : ι → ℂ) (f : ι → (d → ℝ) → ℂ) :
    ext c (fun y => ∑ i ∈ s, a i * f i y) = fun x => ∑ i ∈ s, a i * ext c (f i) x := by
  funext x
  simp only [Geometry.ext, Geometry.per, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ε _ => by ring

omit [DecidableEq d] [Fintype P] in
/-- Fourier coefficients of finite linear combinations of continuous functions. -/
theorem mFourierCoeff_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) {f : ι → UnitAddTorus d → ℂ}
    (hf : ∀ i, Continuous (f i)) (n : d → ℤ) :
    mFourierCoeff (fun x => ∑ i ∈ s, a i * f i x) n = ∑ i ∈ s, a i * mFourierCoeff (f i) n := by
  simp only [mFourierCoeff, smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum s fun i _ => (integrable_of_continuous
    ((mFourier (-n)).continuous.mul (continuous_const.mul (hf i))) :
      Integrable fun t => mFourier (-n) t * (a i * f i t))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_const_mul]
  congr 1; funext x; ring

omit [Fintype P] in
/-- `(ext Σ aᵢ fᵢ)^ = Σ aᵢ (ext fᵢ)^` for test functions. -/
theorem mFourierCoeff_ext_sum (c : d → ℂ) {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    {f : ι → (d → ℝ) → ℂ} (hf : ∀ i, Domain.IsTest (Q d) (f i)) (n : d → ℤ) :
    mFourierCoeff (ext c fun y => ∑ i ∈ s, a i * f i y) n =
      ∑ i ∈ s, a i * mFourierCoeff (ext c (f i)) n := by
  rw [ext_sum]
  exact mFourierCoeff_sum s a (fun i => continuous_ext c (hf i)) n

omit [Fintype P] in
theorem mFourierCoeff_ext_sub (c : d → ℂ) {f g : (d → ℝ) → ℂ} (hf : Domain.IsTest (Q d) f)
    (hg : Domain.IsTest (Q d) g) (n : d → ℤ) :
    mFourierCoeff (ext c fun y => f y - g y) n =
      mFourierCoeff (ext c f) n - mFourierCoeff (ext c g) n := by
  have h := mFourierCoeff_ext_sum c Finset.univ ![1, -1] (f := ![f, g])
    (fun i => by fin_cases i <;> simpa) n
  have e : (fun y => f y - g y) =
      fun y => ∑ i, (![1, -1] : Fin 2 → ℂ) i * (![f, g] : Fin 2 → _) i y := by
    funext y; simp [Fin.sum_univ_two, sub_eq_add_neg]
  rw [e, h]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

omit [Fintype P] in
/-- **Integration by parts for extensions**: the extension of `∂_k Φ` with the parity of `x_k`
reversed has coefficients `2πi n_k` times those of the extension of `Φ`. -/
theorem mFourierCoeff_ext_fderiv (c : d → ℂ) {Φ : (d → ℝ) → ℂ} (hΦ : Domain.IsTest (Q d) Φ)
    (k : d) (n : d → ℤ) :
    mFourierCoeff (ext (Function.update c k (-c k)) fun y => fderiv ℝ Φ y (Pi.single k 1)) n =
      2 * Real.pi * Complex.I * n k * mFourierCoeff (ext c Φ) n := by
  rw [← partialT_ext c hΦ k, mFourierCoeff_partialT (isSmooth_ext c hΦ).contDiff_one]

omit [Fintype P] in
/-- The same, for a parity vector `c'` equal to `c` with the parity of `x_k` reversed. -/
theorem mFourierCoeff_ext_fderiv' {c c' : d → ℂ} (k : d) (hc : c' = Function.update c k (-c k))
    {Φ : (d → ℝ) → ℂ} (hΦ : Domain.IsTest (Q d) Φ) (n : d → ℤ) :
    mFourierCoeff (ext c' fun y => fderiv ℝ Φ y (Pi.single k 1)) n =
      2 * Real.pi * Complex.I * n k * mFourierCoeff (ext c Φ) n := by
  subst hc; exact mFourierCoeff_ext_fderiv c hΦ k n

/-! ### Finitely supported coefficient sequences -/

omit [Fintype d] [DecidableEq d] [Fintype P] in
/-- A finitely supported function is in `L²` of the counting measure. -/
theorem memLp_count_of_finite {α E : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] [NormedAddCommGroup E] {f : α → E} (S : Finset α) (hS : ∀ a ∉ S, f a = 0) :
    MemLp f 2 (Measure.count : Measure α) :=
  (memLp_count_iff two_ne_zero).2 (memℓp_gen (summable_of_ne_finset_zero (s := S) fun a ha => by
    simp [hS a ha]))

omit [Fintype d] [DecidableEq d] [Fintype P] in
/-- **Finitely supported sequences lie in the domain of every `ℓ²` multiplier.** -/
theorem mem_mulDomain_of_finite {α E F : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (m : α → E →L[ℂ] F) {u : Lp E 2 (Measure.count : Measure α)}
    (S : Finset α) (hS : ∀ a ∉ S, (u : α → E) a = 0) : u ∈ Operator.mulDomain Measure.count m :=
  (Operator.mem_mulDomain_count_iff m).2 (memℓp_gen (summable_of_ne_finset_zero (s := S)
    fun a ha => by simp [hS a ha]))

/-! ### Parities as fixed points of fibre symmetries -/

omit hc

/-- The frequency reflection `flip_k` as a reflection of the counting measure on `ℤᵈ`. -/
def flipRefl (k : d) : Fourier.Reflection (Measure.count : Measure (d → ℤ)) :=
  Fourier.Reflection.count_of_involutive (flipAt k) (flipAt_flipAt k)

@[simp] theorem flipRefl_σ (k : d) : (flipRefl k).σ = flipAt k := rfl

omit [Fintype d] [DecidableEq d] in
variable (P) in
/-- The diagonal map `v ↦ (s_p v_p)_p` of `ℂᴾ`. -/
def sgnCLM (s : P → ℂ) : EuclideanSpace ℂ P →L[ℂ] EuclideanSpace ℂ P :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 fun p => s p * v p
      map_add' := fun v w => by ext p; simp; ring
      map_smul' := fun z v => by ext p; simp; ring }

omit [Fintype d] [DecidableEq d] in
@[simp] theorem sgnCLM_apply (s : P → ℂ) (v : EuclideanSpace ℂ P) (p : P) :
    sgnCLM P s v p = s p * v p := rfl

omit [Fintype d] [DecidableEq d] in
theorem sgnCLM_sgnCLM {s : P → ℂ} (hs : ∀ p, s p * s p = 1) (v : EuclideanSpace ℂ P) :
    sgnCLM P s (sgnCLM P s v) = v := by
  ext p; rw [sgnCLM_apply, sgnCLM_apply, ← mul_assoc, hs, one_mul]

omit [Fintype d] [DecidableEq d] in
theorem inner_sgnCLM {s : P → ℂ} (hs : ∀ p, s p * s p = 1) (hs' : ∀ p, starRingEnd ℂ (s p) = s p)
    (v w : EuclideanSpace ℂ P) : ⟪sgnCLM P s v, sgnCLM P s w⟫_ℂ = ⟪v, w⟫_ℂ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    RCLike.star_def]
  refine Finset.sum_congr rfl fun p _ => ?_
  change s p * w p * (starRingEnd ℂ) (s p * v p) = w p * (starRingEnd ℂ) (v p)
  rw [map_mul, hs']
  linear_combination (w p * (starRingEnd ℂ) (v p)) * hs p

omit [Fintype d] [DecidableEq d] in
theorem sgnCLM_comm (s t : P → ℂ) (v : EuclideanSpace ℂ P) :
    sgnCLM P s (sgnCLM P t v) = sgnCLM P t (sgnCLM P s v) := by
  ext p; simp only [sgnCLM_apply]; ring

/-- **Parities are fixed points of the fibre symmetries**: `w` has the parities `c` iff it is
fixed by every `u ↦ D_k u ∘ flip_k`, `D_k = diag(c_{·,k})`. -/
theorem mem_fieldParity_iff_symLp (hc : ∀ p j, c p j * c p j = 1)
    {w : Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (d → ℤ))} :
    w ∈ fieldParity c ↔
      ∀ k, Fourier.symLp (flipRefl k) (sgnCLM P fun p => c p k) w = w := by
  rw [mem_fieldParity_iff]
  refine forall_congr' fun k => ?_
  have h : ∀ n, _ := fun n => Measure.ae_count_iff.1
    (Fourier.coeFn_symLp (flipRefl k) (sgnCLM P fun p => c p k) w) n
  constructor
  · intro hw
    refine Lp.ext_count fun n => ?_
    rw [h n]
    ext p
    rw [sgnCLM_apply, flipRefl_σ, hw n p, ← mul_assoc, hc, one_mul]
  · intro hw n p
    have := congrArg (fun u : Lp (EuclideanSpace ℂ P) 2 Measure.count =>
      (u : (d → ℤ) → EuclideanSpace ℂ P) n p) hw
    simp only at this
    rw [h n, sgnCLM_apply, flipRefl_σ] at this
    rw [← this, ← mul_assoc, hc, one_mul]

/-! ### Scalar fields on the Fourier side -/

variable (d) in
/-- **Fourier coefficients of scalar functions**: `L²(𝕋ᵈ) ≃ₗᵢ ℓ²(ℤᵈ)`, as `L²` of the counting
measure. -/
def scalarFourier : T2 d ≃ₗᵢ[ℂ] Lp ℂ 2 (Measure.count : Measure (d → ℤ)) :=
  (mFourierBasis (d := d)).repr.trans (lp.equivLpCount ℂ (d → ℤ) ℂ 2)

omit [DecidableEq d] in
theorem scalarFourier_apply (f : T2 d) (n : d → ℤ) :
    (scalarFourier d f : (d → ℤ) → ℂ) n = mFourierCoeff (f : UnitAddTorus d → ℂ) n := by
  simp [scalarFourier, mFourierBasis_repr]

omit [DecidableEq d] in
theorem coeff_scalarFourier_symm (u : Lp ℂ 2 (Measure.count : Measure (d → ℤ))) (n : d → ℤ) :
    mFourierCoeff ((scalarFourier d).symm u : UnitAddTorus d → ℂ) n = (u : (d → ℤ) → ℂ) n := by
  rw [← scalarFourier_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **The extension by parity of scalar functions, on the Fourier side**. -/
def extS {c : d → ℂ} (hc : ∀ j, c j * c j = 1) :
    Domain.L2 ℂ (Q d) →L[ℂ] Lp ℂ 2 (Measure.count : Measure (d → ℤ)) :=
  (scalarFourier d).toContinuousLinearEquiv.toContinuousLinearMap.comp (extL2 hc)

theorem extS_coeff {c : d → ℂ} (hc : ∀ j, c j * c j = 1) (g : Domain.L2 ℂ (Q d)) (n : d → ℤ) :
    (extS hc g : (d → ℤ) → ℂ) n = mFourierCoeff (extL2 hc g : UnitAddTorus d → ℂ) n :=
  scalarFourier_apply _ n

theorem scalarFourier_symm_extS {c : d → ℂ} (hc : ∀ j, c j * c j = 1) (g : Domain.L2 ℂ (Q d)) :
    (scalarFourier d).symm (extS hc g) = extL2 hc g :=
  (scalarFourier d).symm_apply_apply _

theorem inner_extS {c : d → ℂ} (hc : ∀ j, c j * c j = 1) (f g : Domain.L2 ℂ (Q d)) :
    ⟪extS hc f, extS hc g⟫_ℂ = ((2 ^ Fintype.card d : ℝ) : ℂ) * ⟪f, g⟫_ℂ := by
  change ⟪scalarFourier d (extL2 hc f), scalarFourier d (extL2 hc g)⟫_ℂ = _
  rw [LinearIsometryEquiv.inner_map_map, inner_extL2]

variable (d) in
/-- Scalar coefficient sequences with the parity `c`. -/
def scalarParity (c : d → ℂ) : Submodule ℂ (Lp ℂ 2 (Measure.count : Measure (d → ℤ))) :=
  (paritySub c).comap ((scalarFourier d).symm.toLinearEquiv.toLinearMap)

theorem mem_scalarParity_iff {c : d → ℂ} {u : Lp ℂ 2 (Measure.count : Measure (d → ℤ))} :
    u ∈ scalarParity d c ↔ ∀ k n, (u : (d → ℤ) → ℂ) (flipAt k n) = c k * (u : (d → ℤ) → ℂ) n := by
  change (scalarFourier d).symm u ∈ paritySub c ↔ _
  simp only [mem_paritySub, coeff_scalarFourier_symm]

theorem range_extS {c : d → ℂ} (hc : ∀ j, c j * c j = 1) :
    LinearMap.range (extS hc : Domain.L2 ℂ (Q d) →ₗ[ℂ] _) = scalarParity d c := by
  ext u
  constructor
  · rintro ⟨g, rfl⟩
    change (scalarFourier d).symm (extS hc g) ∈ paritySub c
    rw [scalarFourier_symm_extS]; exact extL2_mem hc g
  · intro hu
    have hu' : (scalarFourier d).symm u ∈ paritySub c := hu
    refine ⟨resQ ((scalarFourier d).symm u), ?_⟩
    change scalarFourier d (extL2 hc _) = u
    rw [extL2_resQ hc hu', LinearIsometryEquiv.apply_symm_apply]

theorem extS_resQ {c : d → ℂ} (hc : ∀ j, c j * c j = 1)
    {u : Lp ℂ 2 (Measure.count : Measure (d → ℤ))} (hu : u ∈ scalarParity d c) :
    extS hc (resQ ((scalarFourier d).symm u)) = u := by
  have hu' : (scalarFourier d).symm u ∈ paritySub c := hu
  change scalarFourier d (extL2 hc _) = u
  rw [extL2_resQ hc hu', LinearIsometryEquiv.apply_symm_apply]

theorem extS_injective {c : d → ℂ} (hc : ∀ j, c j * c j = 1) : Function.Injective (extS hc) :=
  fun f g h => by
    rw [← resQ_extL2 hc f, ← resQ_extL2 hc g, ← scalarFourier_symm_extS hc f,
      ← scalarFourier_symm_extS hc g, h]

/-- **Scalar parities are fixed points of the scalar fibre symmetries** `u ↦ c_k · u ∘ flip_k`. -/
theorem mem_scalarParity_iff_symLp {c : d → ℂ} (hc : ∀ j, c j * c j = 1)
    {u : Lp ℂ 2 (Measure.count : Measure (d → ℤ))} :
    u ∈ scalarParity d c ↔
      ∀ k, Fourier.symLp (flipRefl k) (c k • ContinuousLinearMap.id ℂ ℂ) u = u := by
  rw [mem_scalarParity_iff]
  refine forall_congr' fun k => ?_
  have h : ∀ n, _ := fun n => Measure.ae_count_iff.1
    (Fourier.coeFn_symLp (flipRefl k) (c k • ContinuousLinearMap.id ℂ ℂ) u) n
  constructor
  · intro hu
    refine Lp.ext_count fun n => ?_
    rw [h n]
    change c k * (u : (d → ℤ) → ℂ) (flipAt k n) = _
    rw [hu n, ← mul_assoc, hc, one_mul]
  · intro hu n
    have := congrArg (fun v : Lp ℂ 2 Measure.count => (v : (d → ℤ) → ℂ) n) hu
    rw [h n] at this
    change c k * (u : (d → ℤ) → ℂ) (flipAt k n) = _ at this
    rw [← this, ← mul_assoc, hc, one_mul]

/-! ### Sequences with values in a subspace -/

section LiftLp

variable {α E F : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The isometry `L²(α; F) → L²(α; E)` induced by an isometric embedding `ι : F → E` (counting
measure). -/
def liftLp (ι : F →ₗᵢ[ℂ] E) :
    Lp F 2 (Measure.count : Measure α) →ₗᵢ[ℂ] Lp E 2 (Measure.count : Measure α) where
  toLinearMap := (ι.toContinuousLinearMap.compLpL 2 (Measure.count : Measure α)).toLinearMap
  norm_map' u := by
    show ‖(ι.toContinuousLinearMap.compLpL 2 (Measure.count : Measure α)) u‖ = ‖u‖
    have h : ∀ᵐ a ∂(Measure.count : Measure α),
        ‖(ι.toContinuousLinearMap.compLpL 2 (Measure.count : Measure α) u : α → E) a‖ =
          ‖(u : α → F) a‖ := by
      filter_upwards [ι.toContinuousLinearMap.coeFn_compLpL (p := 2)
        (μ := (Measure.count : Measure α)) u] with a ha
      rw [ha]; exact ι.norm_map _
    rw [Lp.norm_def, Lp.norm_def,
      eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) h]

omit [MeasurableSingletonClass α] [Countable α] in
theorem liftLp_apply (ι : F →ₗᵢ[ℂ] E) (u : Lp F 2 (Measure.count : Measure α)) (a : α) :
    (liftLp ι u : α → E) a = ι ((u : α → F) a) :=
  Measure.ae_count_iff.1 (ι.toContinuousLinearMap.coeFn_compLpL (p := 2)
    (μ := (Measure.count : Measure α)) u) a

theorem mem_range_liftLp_iff (ι : F →ₗᵢ[ℂ] E) {w : Lp E 2 (Measure.count : Measure α)} :
    w ∈ LinearMap.range (liftLp ι).toLinearMap ↔
      ∀ a, (w : α → E) a ∈ LinearMap.range ι.toLinearMap := by
  constructor
  · rintro ⟨u, rfl⟩ a
    change (liftLp ι u : α → E) a ∈ _
    rw [liftLp_apply]; exact LinearMap.mem_range_self _ _
  · intro hw
    let g : α → F := fun a => ι.equivRange.symm ⟨(w : α → E) a, hw a⟩
    have hg : ∀ a, ι (g a) = (w : α → E) a := fun a => by
      rw [← LinearIsometry.equivRange_apply_coe, LinearIsometryEquiv.apply_symm_apply]
    have hn : ∀ a, ‖g a‖ = ‖(w : α → E) a‖ := fun a => by rw [← hg, ι.norm_map]
    have hw' : Memℓp (fun a => ‖(w : α → E) a‖) 2 :=
      memℓp_norm_iff.2 (lp.memℓp_count (α := α) (E := E) (p := 2) w)
    have hm : MemLp g 2 (Measure.count : Measure α) :=
      (memLp_count_iff two_ne_zero).2 (memℓp_norm_iff.1 (by simpa only [hn] using hw'))
    refine ⟨hm.toLp _, Lp.ext_count fun a => ?_⟩
    change (liftLp ι (hm.toLp _) : α → E) a = _
    rw [liftLp_apply, MemLp.coeFn_toLp_count, hg]

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (ι : F →ₗᵢ[ℂ] E)
  (L : X →L[ℂ] Lp E 2 (Measure.count : Measure α))
  (hL : ∀ x a, (L x : α → E) a ∈ LinearMap.range ι.toLinearMap)

/-- The corestriction of a map into `L²(α; E)` with values in `ι F` pointwise to `L²(α; F)`. -/
def corestrictLp : X →L[ℂ] Lp F 2 (Measure.count : Measure α) :=
  (liftLp ι).equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (L.codRestrict _ fun x => (mem_range_liftLp_iff ι).2 (hL x))

theorem liftLp_corestrictLp (x : X) : liftLp ι (corestrictLp ι L hL x) = L x := by
  rw [← LinearIsometry.equivRange_apply_coe]
  change (((liftLp ι).equivRange ((liftLp ι).equivRange.symm
    (L.codRestrict _ (fun x => (mem_range_liftLp_iff ι).2 (hL x)) x)) :
      LinearMap.range (liftLp ι).toLinearMap) : Lp E 2 Measure.count) = L x
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem corestrictLp_apply (x : X) (a : α) :
    ι (((corestrictLp ι L hL x : Lp F 2 Measure.count) : α → F) a) = (L x : α → E) a := by
  rw [← liftLp_apply, liftLp_corestrictLp]

theorem inner_corestrictLp (x y : X) :
    ⟪corestrictLp ι L hL x, corestrictLp ι L hL y⟫_ℂ = ⟪L x, L y⟫_ℂ := by
  rw [← (liftLp ι).inner_map_map, liftLp_corestrictLp, liftLp_corestrictLp]

omit [MeasurableSingletonClass α] [Countable α] in
/-- `liftLp` intertwines the fibre symmetries `u ↦ ρ ∘ u ∘ σ`. -/
theorem liftLp_symLp (R : Fourier.Reflection (Measure.count : Measure α)) {ρ : F →L[ℂ] F}
    {ρ' : E →L[ℂ] E} (h : ∀ v, ι (ρ v) = ρ' (ι v)) (u : Lp F 2 (Measure.count : Measure α)) :
    liftLp ι (Fourier.symLp R ρ u) = Fourier.symLp R ρ' (liftLp ι u) := by
  refine Lp.ext (Measure.ae_count_iff.2 fun a => ?_)
  rw [liftLp_apply, Measure.ae_count_iff.1 (Fourier.coeFn_symLp R ρ u) a,
    Measure.ae_count_iff.1 (Fourier.coeFn_symLp R ρ' (liftLp ι u)) a]
  simp only
  rw [liftLp_apply, h]

omit [MeasurableSingletonClass α] [Countable α] in
theorem liftLp_injective : Function.Injective (liftLp (α := α) ι) := (liftLp ι).injective

end LiftLp

/-! ### Products of coefficient sequences -/

section ProdLp

variable {α E F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- `ℓ²(α; E) × ℓ²(α; F) ≃ ℓ²(α; E × F)` (counting measure, `ℓ²` product norms). -/
def prodLp : WithLp 2 (Lp E 2 (Measure.count : Measure α) × Lp F 2 (Measure.count : Measure α))
    ≃ₗᵢ[ℂ] Lp (WithLp 2 (E × F)) 2 (Measure.count : Measure α) :=
  (Lp.prodEquiv ℂ (p := 2) ENNReal.ofNat_ne_top).symm

theorem prodLp_apply (g : WithLp 2 (Lp E 2 (Measure.count : Measure α) ×
    Lp F 2 (Measure.count : Measure α))) (a : α) :
    (prodLp g : α → WithLp 2 (E × F)) a =
      WithLp.toLp 2 ((g.fst : α → E) a, (g.snd : α → F) a) :=
  Measure.ae_count_iff.1 (Lp.coeFn_prodEquiv_symm (𝕜 := ℂ) (p := 2) ENNReal.ofNat_ne_top g) a

theorem prodLp_symm_fst (u : Lp (WithLp 2 (E × F)) 2 (Measure.count : Measure α)) (a : α) :
    ((prodLp.symm u).fst : α → E) a = ((u : α → WithLp 2 (E × F)) a).fst :=
  Measure.ae_count_iff.1 (Lp.coeFn_prodEquiv_fst (𝕜 := ℂ) (p := 2) ENNReal.ofNat_ne_top u) a

theorem prodLp_symm_snd (u : Lp (WithLp 2 (E × F)) 2 (Measure.count : Measure α)) (a : α) :
    ((prodLp.symm u).snd : α → F) a = ((u : α → WithLp 2 (E × F)) a).snd :=
  Measure.ae_count_iff.1 (Lp.coeFn_prodEquiv_snd (𝕜 := ℂ) (p := 2) ENNReal.ofNat_ne_top u) a

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [NormedAddCommGroup Y]
  [InnerProductSpace ℂ Y]

/-- Two maps into coefficient sequences, combined into a map into sequences of pairs. -/
def pairLp (L₁ : X →L[ℂ] Lp E 2 (Measure.count : Measure α))
    (L₂ : Y →L[ℂ] Lp F 2 (Measure.count : Measure α)) :
    WithLp 2 (X × Y) →L[ℂ] Lp (WithLp 2 (E × F)) 2 (Measure.count : Measure α) :=
  prodLp.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp
      ((L₁.prodMap L₂).comp (WithLp.prodContinuousLinearEquiv 2 ℂ X Y).toContinuousLinearMap))

theorem pairLp_apply (L₁ : X →L[ℂ] Lp E 2 (Measure.count : Measure α))
    (L₂ : Y →L[ℂ] Lp F 2 (Measure.count : Measure α)) (w : WithLp 2 (X × Y)) :
    pairLp L₁ L₂ w = prodLp (WithLp.toLp 2 (L₁ (WithLp.ofLp w).1, L₂ (WithLp.ofLp w).2)) := rfl

theorem pairLp_coeff (L₁ : X →L[ℂ] Lp E 2 (Measure.count : Measure α))
    (L₂ : Y →L[ℂ] Lp F 2 (Measure.count : Measure α)) (w : WithLp 2 (X × Y)) (a : α) :
    (pairLp L₁ L₂ w : α → WithLp 2 (E × F)) a =
      WithLp.toLp 2 ((L₁ (WithLp.ofLp w).1 : α → E) a, (L₂ (WithLp.ofLp w).2 : α → F) a) := by
  rw [pairLp_apply, prodLp_apply]; rfl

theorem inner_pairLp {L₁ : X →L[ℂ] Lp E 2 (Measure.count : Measure α)}
    {L₂ : Y →L[ℂ] Lp F 2 (Measure.count : Measure α)} {s : ℂ}
    (h₁ : ∀ x x', ⟪L₁ x, L₁ x'⟫_ℂ = s * ⟪x, x'⟫_ℂ) (h₂ : ∀ y y', ⟪L₂ y, L₂ y'⟫_ℂ = s * ⟪y, y'⟫_ℂ)
    (w w' : WithLp 2 (X × Y)) : ⟪pairLp L₁ L₂ w, pairLp L₁ L₂ w'⟫_ℂ = s * ⟪w, w'⟫_ℂ := by
  rw [pairLp_apply, pairLp_apply, LinearIsometryEquiv.inner_map_map, WithLp.prod_inner_apply,
    WithLp.prod_inner_apply]
  rw [h₁, h₂, mul_add]

end ProdLp

/-! ### `ℓ²` multipliers pointwise -/

/-- **A pointwise identity gives the multiplier graph**: if `m a (u a) = v a` for every `a`, then
`u ∈ D(mulOp m)` and `mulOp m u = v` (counting measure). -/
theorem exists_mulOp_count_eq {α E F : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (m : α → E →L[ℂ] F) {u : Lp E 2 (Measure.count : Measure α)}
    {v : Lp F 2 (Measure.count : Measure α)} (h : ∀ a, m a ((u : α → E) a) = (v : α → F) a) :
    ∃ hu : u ∈ Operator.mulDomain Measure.count m, Operator.mulOp Measure.count m ⟨u, hu⟩ = v := by
  have hu : u ∈ Operator.mulDomain Measure.count m := by
    refine (Operator.mem_mulDomain_count_iff m).2 ?_
    rw [show (fun a => m a ((u : α → E) a)) = (v : α → F) from funext h]
    exact lp.memℓp_count (α := α) (E := F) (p := 2) v
  exact ⟨hu, Lp.ext_count fun a => (Operator.coeFn_mulOp_count m ⟨u, hu⟩ a).trans (h a)⟩

end Feec.Models.Cube.MirrorExt
