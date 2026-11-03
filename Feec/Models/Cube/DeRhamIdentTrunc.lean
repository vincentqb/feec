module

public import Feec.Models.Cube.DeRhamIdentForms

/-!
# The parity extension reflects the domains of `d`: Fourier truncation and traces

If the parity extension `Jf rel k u` of a `k`-form on `Q = (0, ½)ⁿ` lies in the domain of the torus
exterior derivative (`d_ξ (Jf u)(m) = y(m)` with `y ∈ ℓ²`), then `u` lies in the domain of `d` on
`Q` with the boundary condition of its class:

* relative class: `u ∈ H̊Λᵏ(Q)` (`mem_minimal_of_Jf`);
* absolute class: `u ∈ HΛᵏ(Q)` (`mem_maximal_of_Jf`).

The Fourier truncations `x_N` of `Jf u` (to `|m|_∞ ≤ N`, `trunc`) stay in the real parity class
(`realPar_trunc`) and converge in the graph norm (`tendsto_trunc`, `symbol_trunc`). Their
restrictions to `Q` are restrictions of real trigonometric polynomials (`Jinvf_eq_toL2F`), smooth
with bounded derivatives; in the relative class their tangential components vanish on the faces
(`trigLift_eq_zero_of_face`), so the cut-off argument puts them in `H̊Λᵏ(Q)`
(`mem_closure_extDerivOp_of_tangential`); in the absolute class they are smooth, hence in
`HΛᵏ(Q)`. The forward computation (`coeff_d_minimal`, `coeff_d_maximal`) identifies their
differentials with the restrictions of the truncations of `y`, and closedness of `d` passes to the
limit.

## Main results

* `trunc`, `coeFn_trunc`, `tendsto_trunc`, `realPar_trunc`, `symbol_trunc`.
* `trigLift`, `Jinvf_eq_toL2F`, `trigLift_eq_zero_of_face`.
* **`mem_closure_extDerivOp_of_tangential`**.
* **`mem_minimal_of_Jf`**, **`mem_maximal_of_Jf`**.

## References

* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.4 (cut-off arguments)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (the cube by the method of images)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate ContDiff Topology
open Set MeasureTheory Filter UnitAddTorus Feec.Fourier.TorusWeak Finset

@[expose] public noncomputable section

namespace Feec.Models.Cube.DeRhamIdent

open Geometry MirrorExt
open Feec.Domain (formIdx formExt formExt_of_card formExt_val extDerivOp L2F L2 toL2F)
open Feec.Fourier.Exterior (Form Lam)
open Feec.Fourier.Torus (bandN finite_bandN)

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Fourier.TorusWeak`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The local Haar measure on `ℝ/ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {n : ℕ}

/-! ### Fourier truncation -/

/-- The torus symbol complex of the de Rham complex of `𝕋ⁿ`. -/
abbrev TS (n : ℕ) := Fourier.Torus.symbolComplex (Feec.Fourier.Exterior.deRham (Fin n))

instance (N k : ℕ) : ((TS n).band (bandN N) k).HasOrthogonalProjection :=
  Fourier.hasOrthogonalProjection_band (TS n) (finite_bandN N).measurableSet k

/-- The Fourier truncation to the band `|m|_∞ ≤ N`. -/
abbrev trunc (N k : ℕ) : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)) →L[ℂ]
    Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)) :=
  ((TS n).band (bandN N) k).starProjection

open scoped Classical in
theorem coeFn_trunc (N k : ℕ) (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)))
    (m : Fin n → ℤ) :
    (trunc N k x : (Fin n → ℤ) → Form ℂ (Fin n) k) m =
      if m ∈ bandN N then (x : (Fin n → ℤ) → Form ℂ (Fin n) k) m else 0 := by
  have := Measure.ae_count_iff.1 (Operator.coeFn_starProjection_fibreSub
    (μ := (Measure.count : Measure (Fin n → ℤ)))
    (Fourier.bandFibre (𝕜 := ℂ) (E := Form ℂ (Fin n)) (bandN N) k)
    AEStronglyMeasurable.of_discrete x) m
  rw [this]
  dsimp only
  rw [Fourier.starProjection_bandFibre]
  by_cases hm : m ∈ bandN N
  · simp [hm, Operator.cutoff_apply_of_mem hm]
  · simp [hm, Operator.cutoff_apply_of_notMem hm]

theorem tendsto_trunc (k : ℕ) (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))) :
    Tendsto (fun N => trunc N k x) atTop (𝓝 x) :=
  Fourier.tendsto_starProjection_band (TS n) (fun N => (finite_bandN N).measurableSet)
    Fourier.Torus.bandN_mono Fourier.Torus.exists_mem_bandN k x

theorem neg_mem_bandN {N : ℕ} {m : Fin n → ℤ} : -m ∈ bandN N ↔ m ∈ bandN N := by
  simp [bandN]

open scoped Classical in
/-- **Truncation preserves the real parity classes.** -/
theorem realPar_trunc {rel : Bool} {k : ℕ}
    {x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))} (hx : RealPar rel k x)
    (N : ℕ) : RealPar rel k (trunc N k x) := by
  refine ⟨fun m t => ?_, fun j m t => ?_⟩
  · rw [coeFn_trunc, coeFn_trunc]
    by_cases hm : m ∈ bandN N
    · simp [hm, neg_mem_bandN.2 hm, hx.1 m t]
    · simp [hm, mt neg_mem_bandN.1 hm]
  · rw [coeFn_trunc, coeFn_trunc]
    by_cases hm : m ∈ bandN N
    · simp [hm, (Fourier.Torus.flipAt_mem_bandN j).2 hm, hx.2 j m t]
    · simp [hm, mt (Fourier.Torus.flipAt_mem_bandN j).1 hm]

open scoped Classical in
/-- **Truncation commutes with the symbol.** -/
theorem symbol_trunc {k : ℕ} {x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))}
    {y : Lp (Form ℂ (Fin n) (k + 1)) 2 (Measure.count : Measure (Fin n → ℤ))}
    (h : ∀ m, (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (Feec.Fourier.Torus.freq m)
      ((x : (Fin n → ℤ) → Form ℂ (Fin n) k) m) = (y : (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m)
    (N : ℕ) (m : Fin n → ℤ) :
    (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (Feec.Fourier.Torus.freq m)
      ((trunc N k x : (Fin n → ℤ) → Form ℂ (Fin n) k) m) =
      (trunc N (k + 1) y : (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m := by
  rw [coeFn_trunc, coeFn_trunc]
  by_cases hm : m ∈ bandN N
  · simp [hm, h m]
  · simp [hm]

/-! ### Restrictions of trigonometric polynomials -/

/-- The physical field of a coefficient sequence of `k`-forms (indexed by `formIdx n k`). -/
abbrev physF (k : ℕ) (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))) :
    Field (Fin n) (formIdx n (k : ℤ)) :=
  (Fourier.Torus.fieldFourier (Fin n) (formIdx n (k : ℤ))).symm ((reidx k).symm x)

theorem repr_physF (k : ℕ) (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)))
    (s : formIdx n (k : ℤ)) (m : Fin n → ℤ) :
    mFourierBasis.repr (physF k x s) m = (x : (Fin n → ℤ) → Form ℂ (Fin n) k) m (idx k s) := by
  rw [mFourierBasis_repr, coeff_fieldFourier_symm, reidx_symm_apply]

theorem isSmooth_trigPoly (f : lp (fun _ : Fin n → ℤ => ℂ) 2) (S : Finset (Fin n → ℤ)) :
    IsSmooth (trigPoly f S) := by
  unfold IsSmooth
  have e : (trigPoly f S : UnitAddTorus (Fin n) → ℂ) ∘ proj =
      fun y => ∑ m ∈ S, f m * mFourier m (proj y) := by
    funext y
    simp [trigPoly, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, smul_eq_mul]
  rw [e]
  exact ContDiff.sum fun m _ => contDiff_const.mul (isSmooth_mFourier m)

/-- The real lift `y ↦ Re P_s(proj y)` of the trigonometric polynomial of a coefficient sequence on
the finite set `S`, component `s`. -/
def trigLift (k : ℕ) (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)))
    (S : Finset (Fin n → ℤ)) (s : formIdx n (k : ℤ)) (y : Fin n → ℝ) : ℝ :=
  (trigPoly (mFourierBasis.repr (physF k x s)) S (proj y)).re

theorem contDiff_trigLift (k : ℕ) (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)))
    (S : Finset (Fin n → ℤ)) (s : formIdx n (k : ℤ)) :
    ContDiff ℝ (⊤ : ℕ∞) (trigLift k x S s) :=
  Complex.reCLM.contDiff.comp (isSmooth_trigPoly _ S)

theorem abs_trigLift_le (k : ℕ) (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)))
    (S : Finset (Fin n → ℤ)) (s : formIdx n (k : ℤ)) (y : Fin n → ℝ) :
    |trigLift k x S s y| ≤ ‖trigPoly (mFourierBasis.repr (physF k x s)) S‖ :=
  (Complex.abs_re_le_norm _).trans (ContinuousMap.norm_coe_le_norm _ _)

theorem fderiv_trigLift (k : ℕ) (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)))
    (S : Finset (Fin n → ℤ)) (s : formIdx n (k : ℤ)) (j : Fin n) (y : Fin n → ℝ) :
    fderiv ℝ (trigLift k x S s) y (Pi.single j 1) =
      (partialT j (trigPoly (mFourierBasis.repr (physF k x s)) S) (proj y)).re := by
  have hd : Differentiable ℝ ((trigPoly (mFourierBasis.repr (physF k x s)) S :
      UnitAddTorus (Fin n) → ℂ) ∘ proj) :=
    (isSmooth_trigPoly _ S).contDiff_one.differentiable one_ne_zero
  rw [partialT_proj hd]
  exact fderiv_re_comp (hd y) _

theorem abs_fderiv_trigLift_le (k : ℕ)
    (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)))
    (S : Finset (Fin n → ℤ)) (s : formIdx n (k : ℤ)) (j : Fin n) (y : Fin n → ℝ) :
    |fderiv ℝ (trigLift k x S s) y (Pi.single j 1)| ≤
      ‖(⟨partialT j (trigPoly (mFourierBasis.repr (physF k x s)) S),
        continuous_partialT (isSmooth_trigPoly _ S).contDiff_one j⟩ :
          C(UnitAddTorus (Fin n), ℂ))‖ := by
  rw [fderiv_trigLift]
  exact (Complex.abs_re_le_norm _).trans (ContinuousMap.norm_coe_le_norm
    (⟨partialT j (trigPoly (mFourierBasis.repr (physF k x s)) S),
      continuous_partialT (isSmooth_trigPoly _ S).contDiff_one j⟩ : C(UnitAddTorus (Fin n), ℂ)) _)

theorem memLp_trigLift (k : ℕ) (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)))
    (S : Finset (Fin n → ℤ)) (s : formIdx n (k : ℤ)) :
    MemLp (trigLift k x S s) 2 (volume.restrict (Q (Fin n))) :=
  Feec.Domain.memLp_of_continuous measurableSet_Q isBounded_Qn
    (contDiff_trigLift k x S s).continuous

/-- **The restriction of a finitely supported coefficient sequence is the restriction of its real
trigonometric polynomials.** -/
theorem Jinvf_eq_toL2F {k : ℕ} {x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))}
    {S : Finset (Fin n → ℤ)} (hS : ∀ m ∉ S, (x : (Fin n → ℤ) → Form ℂ (Fin n) k) m = 0) :
    Jinvf k x = toL2F (memLp_trigLift k x S) := by
  refine PiLp.ext fun s => Lp.ext ?_
  have hS' : ∀ m ∉ S, mFourierBasis.repr (physF k x s) m = 0 := fun m hm => by
    rw [repr_physF, hS m hm]; rfl
  set T := trigPoly (mFourierBasis.repr (physF k x s)) S with hT
  have he : physF k x s = T.toLp 2 volume ℂ := by
    rw [hT, ← ofCoeff_eq_toLp S hS', ofCoeff, LinearIsometryEquiv.symm_apply_apply]
  change (RowWise.reL _ (resQ (physF k x s)) : (Fin n → ℝ) → ℝ) =ᵐ[_] _
  have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
    (μ := (volume : Measure (UnitAddTorus (Fin n)))) T
  have h' : (physF k x s : UnitAddTorus (Fin n) → ℂ) =ᵐ[volume] T := by rw [he]; exact h
  filter_upwards [RowWise.coeFn_reL (resQ (physF k x s)), coeFn_resQ (physF k x s),
    ae_Q_of_ae_boxSet (ae_restrict_of_ae h'),
    MemLp.coeFn_toLp (memLp_trigLift k x S s)] with y h1 h2 h3 h4
  change _ = (toL2F (memLp_trigLift k x S) s : (Fin n → ℝ) → ℝ) y
  rw [h1, h2, h3]
  exact h4.symm

/-- **Odd trigonometric polynomials vanish on the faces**: in the relative class the tangential
components (`j ∉ s`) of the lift vanish on `{y_j ∈ {0, ½}}`. -/
theorem trigLift_eq_zero_of_face {k : ℕ}
    {x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))} (hx : RealPar true k x)
    {S : Finset (Fin n → ℤ)} (hSr : ∀ j, ∀ m ∈ S, Fourier.Torus.flipAt j m ∈ S)
    {s : formIdx n (k : ℤ)} {j : Fin n} (hj : j ∉ s.1) {y : Fin n → ℝ}
    (hy : y j = 0 ∨ y j = 1 / 2) : trigLift k x S s y = 0 := by
  have hf : ∀ m, mFourierBasis.repr (physF k x s) (flipB (single j) m) =
      -1 * mFourierBasis.repr (physF k x s) m := fun m => by
    have e : flipB (single j) m = Fourier.Torus.flipAt j m := flipB_single j m
    rw [e, repr_physF, repr_physF, hx.2]
    simp [DeRham.parSign, DeRham.reflSign, hj]
  have h := trigPoly_reflB (ε := single j) (S := S)
    (fun m hm => by rw [show flipB (single j) m = Fourier.Torus.flipAt j m from flipB_single j m];
                    exact hSr j m hm) hf (proj y)
  rw [show reflB (single j) (proj y) = proj y from reflB_single_proj_of_face hy] at h
  have h0 : trigPoly (mFourierBasis.repr (physF k x s)) S (proj y) = 0 := by
    linear_combination h / 2
  simp [trigLift, h0]

/-! ### The cut-off argument for `d` -/

theorem formExt_chi_mul {k : ℤ} (ψ : formIdx n k → (Fin n → ℝ) → ℝ) (m : ℕ) (r : Finset (Fin n)) :
    formExt (fun p y => chi m y * ψ p y) r = fun y => chi m y * formExt ψ r y := by
  unfold formExt
  split_ifs
  · rfl
  · funext y; simp

/-- **Smooth forms with vanishing tangential trace lie in `H̊Λ(Q)`**: a smooth `k`-form on `ℝⁿ`,
bounded with bounded first derivatives, whose tangential components vanish on the faces
(`ψ_s = 0` on `{y_j ∈ {0, ½}}` for `j ∉ s`), restricts to `Q` in the closure of the graph of `d`
on test forms. -/
theorem mem_closure_extDerivOp_of_tangential {k : ℤ} {ψ : formIdx n k → (Fin n → ℝ) → ℝ}
    (hψ : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (ψ s)) {M : ℝ} (hM : ∀ s y, |ψ s y| ≤ M) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ s j y, |fderiv ℝ (ψ s) y (Pi.single j 1)| ≤ L)
    (hV : ∀ s j, j ∉ s.1 → ∀ y : Fin n → ℝ, (y j = 0 ∨ y j = 1 / 2) → ψ s y = 0)
    (hψL : ∀ s, MemLp (ψ s) 2 (volume.restrict (Q (Fin n))))
    (hdψL : ∀ t, MemLp ((extDerivOp ℝ n k).apply ψ t) 2 (volume.restrict (Q (Fin n)))) :
    (toL2F hψL, toL2F hdψL) ∈
      closure ((extDerivOp ℝ n k).testGraph (Q (Fin n)) :
        Set (L2F ℝ (Q (Fin n)) (formIdx n k) × L2F ℝ (Q (Fin n)) (formIdx n (k + 1)))) := by
  obtain ⟨M₀, -, hM₀⟩ := RowWise.exists_bound_deriv_smoothTransition
  have hM00 : 0 ≤ M₀ := (abs_nonneg _).trans (hM₀ 0)
  have hFs : ∀ r, ContDiff ℝ ∞ (formExt ψ r) := Feec.Domain.contDiff_formExt hψ
  have hFd : ∀ r, Differentiable ℝ (formExt ψ r) := fun r => (hFs r).differentiable (by simp)
  have hFL : ∀ r j y, |fderiv ℝ (formExt ψ r) y (Pi.single j 1)| ≤ L := by
    intro r j y
    unfold formExt
    split_ifs with h
    · exact hL _ j y
    · simpa using hL0
  have hFV : ∀ r j, j ∉ r → ∀ y : Fin n → ℝ, (y j = 0 ∨ y j = 1 / 2) → formExt ψ r y = 0 := by
    intro r j hj y hy
    unfold formExt
    split_ifs with h
    · exact hV _ j hj y hy
    · rfl
  refine mem_closure_testGraph_of_cutoff _ hψ (M := M) (fun s y _ => hM s y) hψL hdψL
    (K := ∑ _j : Fin n, (L + 4 * M₀ * L)) fun m t y hy => ?_
  rw [Feec.Domain.extDerivOp_apply, Feec.Domain.extD]
  have hχd : Differentiable ℝ (chi (d := Fin n) m) := (contDiff_chi m).differentiable (by simp)
  have hterm : ∀ j ∈ t.1, |(ExteriorFibre.sgn j t.1 : ℝ) * fderiv ℝ (formExt (fun p y =>
      chi m y * ψ p y) (t.1.erase j)) y (Feec.Domain.coordDir j)| ≤ L + 4 * M₀ * L := by
    intro j hj
    rw [abs_mul, show |(ExteriorFibre.sgn j t.1 : ℝ)| = 1 by simp [ExteriorFibre.sgn], one_mul,
      formExt_chi_mul, fderiv_fun_mul (hχd y) (hFd _ y)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      calc |chi m y| * |fderiv ℝ (formExt ψ (t.1.erase j)) y (Pi.single j 1)| ≤ 1 * L :=
            mul_le_mul (abs_chi_le_one m y) (hFL _ j y) (abs_nonneg _) zero_le_one
        _ = L := one_mul L
    · rw [mul_comm]
      exact abs_fderiv_chi_mul_le hM₀ m (hFd _) (hFL _ j)
        (hFV _ j (Finset.notMem_erase j t.1)) hy
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => by positivity

/-! ### The trace part: the extension reflects the domains -/

/-- The finite band as a `Finset`. -/
abbrev bandS (N : ℕ) : Finset (Fin n → ℤ) := (finite_bandN N).toFinset

open scoped Classical in
theorem trunc_eq_zero_of_notMem {N k : ℕ}
    (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))) {m : Fin n → ℤ}
    (hm : m ∉ bandS N) : (trunc N k x : (Fin n → ℤ) → Form ℂ (Fin n) k) m = 0 := by
  rw [coeFn_trunc, ite_eq_right (fun h => hm ((Set.Finite.mem_toFinset _).2 h))]

theorem flipAt_mem_bandS {N : ℕ} (j : Fin n) {m : Fin n → ℤ} (hm : m ∈ bandS N) :
    Fourier.Torus.flipAt j m ∈ bandS N :=
  (Set.Finite.mem_toFinset _).2
    ((Fourier.Torus.flipAt_mem_bandN j).2 ((Set.Finite.mem_toFinset _).1 hm))

/-- Bounds for the lifts of the truncations. -/
theorem trigLift_bounds (k : ℕ) (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)))
    (S : Finset (Fin n → ℤ)) :
    ∃ M L : ℝ, 0 ≤ L ∧ (∀ s y, |trigLift k x S s y| ≤ M) ∧
      ∀ s j y, |fderiv ℝ (trigLift k x S s) y (Pi.single j 1)| ≤ L := by
  set P : formIdx n (k : ℤ) → C(UnitAddTorus (Fin n), ℂ) := fun s =>
    trigPoly (mFourierBasis.repr (physF k x s)) S
  set D : formIdx n (k : ℤ) → Fin n → C(UnitAddTorus (Fin n), ℂ) := fun s j =>
    ⟨partialT j (P s), continuous_partialT (isSmooth_trigPoly _ S).contDiff_one j⟩
  refine ⟨∑ s, ‖P s‖, ∑ s, ∑ j, ‖D s j‖, by positivity, fun s y => ?_, fun s j y => ?_⟩
  · exact (abs_trigLift_le k x S s y).trans (Finset.single_le_sum (f := fun s => ‖P s‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ s))
  · refine (abs_fderiv_trigLift_le k x S s j y).trans ?_
    calc ‖D s j‖ ≤ ∑ j', ‖D s j'‖ := Finset.single_le_sum (f := fun j' => ‖D s j'‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ s', ∑ j', ‖D s' j'‖ := Finset.single_le_sum (f := fun s' => ∑ j', ‖D s' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ s)

theorem memLp_d_trigLift (k : ℕ)
    (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))) (S : Finset (Fin n → ℤ))
    (t : formIdx n ((k : ℤ) + 1)) :
    MemLp ((extDerivOp ℝ n (k : ℤ)).apply (trigLift k x S) t) 2 (volume.restrict (Q (Fin n))) :=
  Feec.Domain.memLp_of_continuous measurableSet_Q isBounded_Qn
    ((extDerivOp ℝ n (k : ℤ)).continuous_apply (Feec.Domain.extDerivOp_isOrderLE (k : ℤ))
      (fun s => (contDiff_trigLift k x S s).of_le (by exact_mod_cast le_top)) t)

/-- **`J⁻¹ (HΛ(𝕋ⁿ) ∩ relative parity class) ⊆ H̊Λ(Q)`**: if the coefficients of the extension of `u`
are mapped by the torus symbol onto an `ℓ²` sequence `y`, then `u ∈ D(d_min)` and
`Jf (d_min u) = y`. -/
theorem mem_minimal_of_Jf {k : ℕ} {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    {y : Lp (Form ℂ (Fin n) (k + 1)) 2 (Measure.count : Measure (Fin n → ℤ))}
    (h : ∀ m, (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (Feec.Fourier.Torus.freq m)
      ((Jf true k u : (Fin n → ℤ) → Form ℂ (Fin n) k) m) =
        (y : (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m) :
    ∃ hu : u ∈ ((extDerivOp ℝ n (k : ℤ)).minimal (Q (Fin n))).domain,
      Jf true (k + 1) ((extDerivOp ℝ n (k : ℤ)).minimal (Q (Fin n)) ⟨u, hu⟩) = y := by
  set x := Jf true k u
  have hx : RealPar true k x := Jf_realPar true k u
  have hmem : ∀ N, (Jinvf k (trunc N k x), Jinvf (k + 1) (trunc N (k + 1) y)) ∈
      ((extDerivOp ℝ n (k : ℤ)).minimal (Q (Fin n))).graph := by
    intro N
    have hxN := realPar_trunc hx N
    obtain ⟨M, L, hL0, hM, hL⟩ := trigLift_bounds k (trunc N k x) (bandS N)
    have hcl := mem_closure_extDerivOp_of_tangential (contDiff_trigLift k (trunc N k x) (bandS N))
      hM hL0 hL (fun s j hj y hy => trigLift_eq_zero_of_face hxN (fun j m hm => flipAt_mem_bandS j hm)
        hj hy) (memLp_trigLift k _ _) (memLp_d_trigLift k _ _)
    rw [← Submodule.topologicalClosure_coe, SetLike.mem_coe,
      ← (extDerivOp ℝ n (k : ℤ)).minimal_graph isOpen_Q,
      ← Jinvf_eq_toL2F fun m hm => trunc_eq_zero_of_notMem x hm] at hcl
    obtain ⟨v, hv1, hv2⟩ := (LinearPMap.mem_graph_iff _).1 hcl
    have hd := coeff_d_minimal true k v
    have hJ : Jf true (k + 1) ((extDerivOp ℝ n (k : ℤ)).minimal (Q (Fin n)) v) =
        trunc N (k + 1) y := by
      refine Lp.ext_count fun m => ?_
      rw [← hd m]
      rw [← symbol_trunc h N m, show (v : L2F ℝ (Q (Fin n)) _) = Jinvf k (trunc N k x) from hv1,
        Jf_Jinvf hxN]
    rw [(LinearPMap.mem_graph_iff _)]
    refine ⟨v, hv1, ?_⟩
    rw [← hJ, Jinvf_Jf]
  have hlim : Tendsto (fun N => (Jinvf k (trunc N k x), Jinvf (k + 1) (trunc N (k + 1) y)))
      atTop (𝓝 (Jinvf k x, Jinvf (k + 1) y)) :=
    Tendsto.prodMk_nhds (((Jinvf k).continuous.tendsto _).comp (tendsto_trunc k x))
      (((Jinvf (k + 1)).continuous.tendsto _).comp (tendsto_trunc (k + 1) y))
  have hg := ((extDerivOp ℝ n (k : ℤ)).isClosed_minimal isOpen_Q).mem_of_tendsto hlim
    (Eventually.of_forall hmem)
  rw [show Jinvf k x = u from Jinvf_Jf true k u] at hg
  obtain ⟨v, hv1, -⟩ := (LinearPMap.mem_graph_iff _).1 hg
  have hu : u ∈ ((extDerivOp ℝ n (k : ℤ)).minimal (Q (Fin n))).domain := by
    have : (v : L2F ℝ (Q (Fin n)) _) = u := hv1
    exact this ▸ v.2
  refine ⟨hu, Lp.ext_count fun m => ?_⟩
  rw [← coeff_d_minimal true k ⟨u, hu⟩ m]
  exact h m

/-- **`J⁻¹ (HΛ(𝕋ⁿ) ∩ absolute parity class) ⊆ HΛ(Q)`**: if the coefficients of the extension of `u`
are mapped by the torus symbol onto an `ℓ²` sequence `y`, then `u ∈ D(d_max)` and
`Jf (d_max u) = y`. -/
theorem mem_maximal_of_Jf {k : ℕ} {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    {y : Lp (Form ℂ (Fin n) (k + 1)) 2 (Measure.count : Measure (Fin n → ℤ))}
    (h : ∀ m, (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (Feec.Fourier.Torus.freq m)
      ((Jf false k u : (Fin n → ℤ) → Form ℂ (Fin n) k) m) =
        (y : (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m) :
    ∃ hu : u ∈ ((extDerivOp ℝ n (k : ℤ)).maximal (Q (Fin n))).domain,
      Jf false (k + 1) ((extDerivOp ℝ n (k : ℤ)).maximal (Q (Fin n)) ⟨u, hu⟩) = y := by
  set x := Jf false k u
  have hx : RealPar false k x := Jf_realPar false k u
  have hmem : ∀ N, (Jinvf k (trunc N k x), Jinvf (k + 1) (trunc N (k + 1) y)) ∈
      ((extDerivOp ℝ n (k : ℤ)).maximal (Q (Fin n))).graph := by
    intro N
    have hxN := realPar_trunc hx N
    obtain ⟨hmax, -⟩ := Feec.Domain.extDerivOp_smooth_mem_maximal_domain isOpen_Q
      (fun s => (contDiff_trigLift k (trunc N k x) (bandS N) s).of_le (by exact_mod_cast le_top))
      (memLp_trigLift k _ _) (memLp_d_trigLift k (trunc N k x) (bandS N))
    rw [← Jinvf_eq_toL2F fun m hm => trunc_eq_zero_of_notMem x hm] at hmax
    set v : ((extDerivOp ℝ n (k : ℤ)).maximal (Q (Fin n))).domain := ⟨_, hmax⟩
    have hd := coeff_d_maximal k v
    have hJ : Jf false (k + 1) ((extDerivOp ℝ n (k : ℤ)).maximal (Q (Fin n)) v) =
        trunc N (k + 1) y := by
      refine Lp.ext_count fun m => ?_
      rw [← hd m]
      rw [← symbol_trunc h N m]
      change (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (Feec.Fourier.Torus.freq m)
        ((Jf false k (Jinvf k (trunc N k x)) : (Fin n → ℤ) → Form ℂ (Fin n) k) m) = _
      rw [Jf_Jinvf hxN]
    rw [(LinearPMap.mem_graph_iff _)]
    refine ⟨v, rfl, ?_⟩
    rw [← hJ, Jinvf_Jf]
  have hlim : Tendsto (fun N => (Jinvf k (trunc N k x), Jinvf (k + 1) (trunc N (k + 1) y)))
      atTop (𝓝 (Jinvf k x, Jinvf (k + 1) y)) :=
    Tendsto.prodMk_nhds (((Jinvf k).continuous.tendsto _).comp (tendsto_trunc k x))
      (((Jinvf (k + 1)).continuous.tendsto _).comp (tendsto_trunc (k + 1) y))
  have hg := ((extDerivOp ℝ n (k : ℤ)).isClosed_maximal isOpen_Q).mem_of_tendsto hlim
    (Eventually.of_forall hmem)
  rw [show Jinvf k x = u from Jinvf_Jf false k u] at hg
  obtain ⟨v, hv1, -⟩ := (LinearPMap.mem_graph_iff _).1 hg
  have hu : u ∈ ((extDerivOp ℝ n (k : ℤ)).maximal (Q (Fin n))).domain := by
    have : (v : L2F ℝ (Q (Fin n)) _) = u := hv1
    exact this ▸ v.2
  refine ⟨hu, Lp.ext_count fun m => ?_⟩
  rw [← coeff_d_maximal k ⟨u, hu⟩ m]
  exact h m

end Feec.Models.Cube.DeRhamIdent
